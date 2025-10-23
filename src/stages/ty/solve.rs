use std::collections::{HashMap, hash_map::Entry};

use crate::ir2::hir::{ExprId, Type};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Solution {
    None,
    Solved(Type),
    Guess(Guess),
}

impl Solution {
    pub fn merge(&mut self, other: Self) {
        match (&self, other) {
            (result, other) if **result == other => {}
            (Self::Solved(ty), Self::Guess(guess)) if guess.compatible_with(ty) => {}
            (Self::Guess(guess), Self::Solved(ty)) if guess.compatible_with(&ty) => {
                *self = Self::Solved(ty);
            }
            (Self::None, result) => {
                *self = result;
            }
            (Self::Guess(left), Self::Guess(right)) => {
                *self = Self::Guess(left.clone().merge(right));
            }
            (_, Self::None) => {}
            (Self::Solved(current), Self::Solved(other)) => {
                panic!("{current:?} and {other:?} are not compatible")
            }
            (current, other) => panic!("cannot merge: {current:?}, {other:?}"),
        };
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Guess {
    AnyInteger,
    SignedInteger,
    UnsignedInteger,
}

impl Guess {
    fn compatible_with(&self, ty: &Type) -> bool {
        matches!(
            (self, ty),
            (Self::AnyInteger, Type::I8 | Type::U8)
                | (Self::SignedInteger, Type::I8)
                | (Self::UnsignedInteger, Type::U8)
        )
    }

    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (left, right) if left == right => left,
            (Self::AnyInteger, result) | (result, Self::AnyInteger) => result,
            (left, right) => {
                panic!("cannot merge {left:?} with {right:?}");
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Solver {
    constraints: Vec<(ExprId, ExprId)>,
    pending: Vec<usize>,
    solutions: HashMap<ExprId, Solution>,
}

impl Solver {
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
            pending: Vec::new(),
            solutions: HashMap::new(),
        }
    }

    pub fn add_constraint(&mut self, left: ExprId, right: ExprId) {
        self.pending.push(self.constraints.len());
        self.constraints.push((left, right));

        self.solutions.entry(left).or_insert(Solution::None);
        self.solutions.entry(right).or_insert(Solution::None);
    }

    pub fn add_solution(&mut self, expr: ExprId, solution: Type) {
        match self.solutions.entry(expr) {
            Entry::Occupied(mut occupied_entry) => {
                occupied_entry.get_mut().merge(Solution::Solved(solution));
            }
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(Solution::Solved(solution));
            }
        }
    }

    pub fn add_guess(&mut self, expr: ExprId, guess: Guess) {
        match self.solutions.entry(expr) {
            Entry::Occupied(mut occupied_entry) => {
                occupied_entry.get_mut().merge(Solution::Guess(guess));
            }
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(Solution::Guess(guess));
            }
        }
    }

    pub fn solve(mut self) -> Option<HashMap<ExprId, Type>> {
        loop {
            let changed = self.step();

            if !changed {
                break;
            }
        }

        if self.pending.is_empty() {
            Some(
                self.solutions
                    .into_iter()
                    .map(|(expr, solution)| {
                        let Solution::Solved(ty) = solution else {
                            panic!("expected solve for {expr:?}, but found: {solution:?}");
                        };

                        (expr, ty)
                    })
                    .collect(),
            )
        } else {
            None
        }
    }

    fn step(&mut self) -> bool {
        let mut changed = false;

        for i in std::mem::take(&mut self.pending) {
            let (left, right) = &self.constraints[i];

            let before = (self.solutions[left].clone(), self.solutions[right].clone());

            let r_sol = self.solutions[right].clone();
            self.solutions.get_mut(left).unwrap().merge(r_sol);

            let after = (self.solutions[left].clone(), self.solutions[right].clone());

            if before == after {
                self.pending.push(i);
            } else {
                changed = true;
            }
        }

        changed
    }
}

#[cfg(test)]
mod test {
    use crate::ir2::hir::ExprId;

    use super::*;

    // #[test]
    // fn it_works() {
    //     let constraints = [
    //         Constraint::Eq(ExprId::new(0).into(), Type::U8.into()),
    //         // Constraint::Eq(ExprId::new(0).into(), ExprId::new(1).into()),
    //         Constraint::Eq(Type::U8.into(), Type::Boolean.into()),
    //     ];
    //
    //     let solution = solve(&constraints);
    //
    //     dbg!(&solution);
    //     assert!(false);
    //
    //     assert_eq!(solution[&ExprId::new(0).into()], Type::U8);
    //     assert_eq!(solution[&ExprId::new(1).into()], Type::U8);
    // }
}
