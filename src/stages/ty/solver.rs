use super::*;

use std::collections::{HashMap, VecDeque, hash_map::Entry};

#[derive(Clone, Debug)]
pub struct Solver {
    root: UnionFind,
    solutions: HashMap<TypeVarId, Solution>,
}

impl Solver {
    pub fn new() -> Self {
        Self {
            root: UnionFind::new(),
            solutions: HashMap::new(),
        }
    }

    pub fn run(constraints: &[Constraint]) -> HashMap<TypeVarId, Type> {
        let mut solver = Self::new();

        solver.solutions.extend(
            [Type::Unit, Type::U8, Type::I8, Type::Boolean]
                .map(|ty| (ty.clone().into(), ty.into())),
        );

        let mut constraints = VecDeque::from_iter(constraints);

        while let Some(constraint) = constraints.pop_front() {
            let solved = solver.solve_constraint(constraint);

            if !solved {
                // constraints.push_back(constraint);
            }
        }

        solver
            .solutions
            .keys()
            .map(|key| (key.clone(), solver.get_ty(key)))
            .collect()
    }

    fn solve(&mut self, var: TypeVarId, solution: impl Into<Solution>) {
        assert!(!self.solutions.contains_key(&var));
        self.solutions.insert(var, solution.into());
    }

    pub fn prefill(values: impl IntoIterator<Item = (TypeVarId, Type)>) -> Self {
        let mut solver = Self::new();

        values
            .into_iter()
            .for_each(|(var, solution)| solver.solve(var, solution));

        solver
    }

    fn solve_constraint(&mut self, constraint: &Constraint) -> bool {
        match constraint {
            Constraint::Eq(left, right) => {
                // 'Resolve' the nodes, to handle duplicate types.
                let (left, left_depth) = self.root.get(left);
                let (right, right_depth) = self.root.get(right);

                // Find the current solutions.
                let left_solution = self.solutions.get(left);
                let right_solution = self.solutions.get(right);

                match (left_solution, right_solution) {
                    // Both nodes have reached the same solution, constraint satisfied.
                    (Some(left), Some(right)) if left == right => true,
                    // Left has solution.
                    (Some(solution), None) => {
                        // Since left and right must be equal, the solution can be re-used,
                        // satisfying the constraint.
                        self.solutions.insert(right.clone(), solution.clone());
                        true
                    }
                    // Same as above, but with right solution.
                    (None, Some(solution)) => {
                        self.solutions.insert(left.clone(), solution.clone());
                        true
                    }
                    // Neither node has a solution, however they must be the same, so merge them.
                    (None, None) => {
                        if left_depth < right_depth {
                            self.root.set_parent(left.clone(), right.clone());
                        } else {
                            self.root.set_parent(right.clone(), left.clone());
                        }

                        false
                    }
                    (left, right) => panic!(
                        "cannot solve constraint ({left:?} == {right:?}): {left_solution:?} != {right_solution:?}"
                    ),
                }
            }
            Constraint::Integer(var, kind) => {
                let var = self.root.resolve(var);

                match self.solutions.entry(var.clone()) {
                    // Solution already exists, make sure that it can be an integer.
                    Entry::Occupied(solution) => match solution.get() {
                        // Concrete type, which is an integer.
                        Solution::Type(ty) if ty.is_integer() => true,
                        // Already expecting integer literal.
                        Solution::Literal(Literal::Integer(_)) => true,
                        solution => panic!(
                            "expected integer literal from constraint, but found {solution:?}"
                        ),
                    },
                    // No solution currently exists, so input that an integer literal is expected.
                    Entry::Vacant(solution) => {
                        solution.insert(Solution::Literal(IntegerKind::Any.into()));
                        true
                    }
                }
            }
            _ => unimplemented!(),
        }
    }

    fn get_ty(&self, var: &TypeVarId) -> Type {
        let root = self.root.resolve(var);

        match self.solutions.get(root).expect("solution") {
            Solution::Type(ty) => ty.clone(),
            Solution::Literal(literal) => literal.to_type(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn prefilled() {
        let expr0 = TypeVarId::Expr(ExprId::new(0));
        let solver = Solver::prefill([(expr0.clone(), Type::I8)]);
        assert_eq!(solver.get_ty(&expr0), Type::I8);
    }

    #[test]
    fn simple_constraint() {
        let [expr0, expr1] = [0, 1].map(|i| TypeVarId::Expr(ExprId::new(i)));
        let mut solver = Solver::prefill([(expr0.clone(), Type::I8)]);

        assert!(solver.solve_constraint(&Constraint::Eq(expr0, expr1.clone())));
        assert_eq!(solver.get_ty(&expr1), Type::I8);
    }

    #[test]
    fn deep_constraint() {
        let [expr0, expr1, expr2] = [0, 1, 2].map(|i| TypeVarId::Expr(ExprId::new(i)));
        let mut solver = Solver::prefill([(expr0.clone(), Type::I8)]);

        assert!(solver.solve_constraint(&Constraint::Eq(expr0, expr1.clone())));
        assert!(solver.solve_constraint(&Constraint::Eq(expr1.clone(), expr2.clone())));
        assert_eq!(solver.get_ty(&expr1), Type::I8);
        assert_eq!(solver.get_ty(&expr2), Type::I8);
    }

    #[test]
    fn deep_constraint_reversed() {
        let [expr0, expr1, expr2] = [0, 1, 2].map(|i| TypeVarId::Expr(ExprId::new(i)));
        let mut solver = Solver::prefill([(expr0.clone(), Type::I8)]);

        // Solve equality constraint before constraint with solution.
        assert!(!solver.solve_constraint(&Constraint::Eq(expr1.clone(), expr2.clone())));
        assert!(solver.solve_constraint(&Constraint::Eq(expr0, expr1.clone())));
        assert_eq!(solver.get_ty(&expr1), Type::I8);
        assert_eq!(solver.get_ty(&expr2), Type::I8);
    }

    #[test]
    fn literal() {
        let expr0 = TypeVarId::Expr(ExprId::new(0));
        let mut solver = Solver::new();

        // Manually solve expression as literal.
        solver.solve(expr0.clone(), Literal::Integer(IntegerKind::Unsigned));
        // Should default to type if none specified.
        assert_eq!(solver.get_ty(&expr0), Type::U8);
    }

    #[test]
    fn literal_constraint() {
        let expr0 = TypeVarId::Expr(ExprId::new(0));
        let mut solver = Solver::new();

        assert!(solver.solve_constraint(&Constraint::Integer(expr0.clone(), IntegerKind::Any)));
        assert_eq!(solver.get_ty(&expr0), Type::I8);
    }
}
