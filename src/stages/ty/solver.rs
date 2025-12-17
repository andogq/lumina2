use crate::stages::ty::Literal;

use super::*;

use std::collections::{HashMap, VecDeque, hash_map::Entry};

#[derive(Clone, Debug)]
pub struct Solver {
    root: DisjointUnionSet,
    solutions: HashMap<TypeVarId, Solution>,
}

impl Solver {
    /// Create an empty solver.
    pub fn new() -> Self {
        Self {
            root: DisjointUnionSet::new(),
            solutions: HashMap::new(),
        }
    }

    /// Run the solver to solve the provided constraints. This will pre-fill the solver with
    /// primitive types.
    pub fn run(constraints: &[Constraint]) -> HashMap<TypeVarId, Type> {
        let mut solver = Self::new();

        // Pre-fill with primitive types.
        solver.solutions.extend(
            [Type::Unit, Type::U8, Type::I8, Type::Boolean, Type::Never]
                .map(|ty| (ty.clone().into(), ty.into())),
        );

        let mut constraints = VecDeque::from_iter(constraints);
        let mut retry = Vec::new();

        while !constraints.is_empty() {
            let mut progress = false;
            while let Some(constraint) = constraints.pop_front() {
                let solved = solver.solve_constraint(constraint);

                progress |= solved;

                if !solved {
                    retry.push(constraint);
                }
            }

            if !progress {
                eprintln!("couldn't progress type solving");
                dbg!(retry);
                dbg!(solver.solutions);
                panic!();
            }

            constraints = std::mem::take(&mut retry).into_iter().collect();
        }

        // HACK: Combine all the set items with the solution items.
        solver
            .root
            .keys()
            .chain(solver.solutions.keys())
            .map(|key| (key.clone(), solver.get_ty(key)))
            .collect()
    }

    /// Save the solution for the provided [`TypeVarId`].
    fn solve(&mut self, var: TypeVarId, solution: impl Into<Solution>) {
        assert!(!self.solutions.contains_key(&var));
        self.solutions.insert(var, solution.into());
    }

    /// Create a solver prefilled with provided solutions.
    pub fn prefill(values: impl IntoIterator<Item = (TypeVarId, Type)>) -> Self {
        let mut solver = Self::new();

        values
            .into_iter()
            .for_each(|(var, solution)| solver.solve(var, solution));

        solver
    }

    /// Attempt to solve the given constraint. Will return `true` if it was successfully solved.
    fn solve_constraint(&mut self, constraint: &Constraint) -> bool {
        match constraint {
            Constraint::Eq(left, right) => {
                // 'Resolve' the nodes, to handle duplicate types.
                let left = self.root.find_set(left).clone();
                let right = self.root.find_set(right).clone();

                // Find the current solutions.
                let left_solution = self.solutions.get(&left);
                let right_solution = self.solutions.get(&right);

                // Merge the nodes.
                let root = self.root.union_sets(left.clone(), right.clone());

                let solution = match (left_solution, right_solution) {
                    // Try simplify the solutions
                    (Some(left_solution), Some(right_solution)) => {
                        Some(solve_solutions(left_solution, right_solution))
                    }
                    // Left has solution.
                    (Some(solution), None) | (None, Some(solution)) => {
                        // Since left and right must be equal, the solution can be re-used,
                        // satisfying the constraint.
                        Some(solution.clone())
                    }
                    // Neither node has a solution, however they must be the same, so merge them.
                    (None, None) => None,
                };

                if let Some(solution) = solution {
                    self.solutions.insert(root, solution);
                    true
                } else {
                    false
                }
            }
            Constraint::Integer(var, kind) => {
                let var = self.root.find_set(var);

                match self.solutions.entry(var.clone()) {
                    // Solution already exists, make sure that it can be an integer.
                    Entry::Occupied(solution) => match solution.get() {
                        // Concrete type, which is an integer.
                        Solution::Type(ty) if ty.is_integer() => true,
                        // Already expecting integer literal.
                        Solution::Literal(Literal::Integer(solution_kind))
                            if solution_kind == kind =>
                        {
                            true
                        }
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
        }
    }

    /// Fetch the type of a type variable.
    fn get_ty(&self, var: &TypeVarId) -> Type {
        let root = self.root.find_set(var);

        match self.solutions.get(root).expect("solution") {
            Solution::Type(ty) => ty.clone(),
            Solution::Literal(literal) => literal.to_type(),
        }
    }
}

fn solve_solutions(left: &Solution, right: &Solution) -> Solution {
    match (left, right) {
        // Solved as types, and they are identical.
        (Solution::Type(left), Solution::Type(right)) if left == right => left.clone().into(),
        // One type, and one literal. Requires further checks.
        (Solution::Type(ty), Solution::Literal(lit))
        | (Solution::Literal(lit), Solution::Type(ty)) => match (lit, ty) {
            // Integer literal, against some integer type.
            (Literal::Integer(kind), ty @ (Type::U8 | Type::I8)) => match (kind, ty) {
                // Any integer literal can be used with any integer type.
                (IntegerKind::Any, ty @ (Type::I8 | Type::U8)) => ty.clone().into(),
                // Signed integer literal must be used with signed integer type.
                (IntegerKind::Signed, Type::I8) => Type::I8.into(),
                // Unsigned integer literal can be used with any integer type.
                (IntegerKind::Unsigned, ty @ (Type::I8 | Type::U8)) => ty.clone().into(),
                (kind, ty) => panic!("invalid integer literal kind {kind:?} for type {ty:?}"),
            },
            (lit, ty) => panic!("incompatible literal {lit:?} with type {ty:?}"),
        },
        // Two literals.
        (Solution::Literal(left), Solution::Literal(right)) => match (left, right) {
            // Literals are identical, no further information to be gathered.
            (left, right) if left == right => left.clone().into(),
            // Make integer literal more specific, if possible.
            (Literal::Integer(IntegerKind::Any), Literal::Integer(kind))
            | (Literal::Integer(kind), Literal::Integer(IntegerKind::Any)) => {
                Literal::Integer(kind.clone()).into()
            }
            (left, right) => panic!("invalid literal solutions: {left:?} != {right:?}"),
        },
        // Propagate never types.
        (Solution::Type(Type::Never), solution) | (solution, Solution::Type(Type::Never)) => {
            solution.clone()
        }
        (left, right) => panic!("incompatible solutions: {left:?} != {right:?}"),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use rstest::*;

    #[fixture]
    fn expr<const N: usize>() -> [TypeVarId; N] {
        (0..N)
            .map(|i| TypeVarId::from(ExprId::new(i)))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    #[fixture]
    fn binding<const N: usize>() -> [TypeVarId; N] {
        (0..N)
            .map(|i| TypeVarId::from(BindingId::new(i)))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    #[rstest]
    fn prefilled(expr: [TypeVarId; 1]) {
        let solver = Solver::prefill([(expr[0].clone(), Type::I8)]);
        assert_eq!(solver.get_ty(&expr[0]), Type::I8);
    }

    #[rstest]
    fn simple_constraint(expr: [TypeVarId; 2]) {
        let mut solver = Solver::prefill([(expr[0].clone(), Type::I8)]);

        assert!(solver.solve_constraint(&Constraint::Eq(expr[0].clone(), expr[1].clone())));
        assert_eq!(solver.get_ty(&expr[1]), Type::I8);
    }

    #[rstest]
    fn deep_constraint(expr: [TypeVarId; 3]) {
        let mut solver = Solver::prefill([(expr[0].clone(), Type::I8)]);

        assert!(solver.solve_constraint(&Constraint::Eq(expr[0].clone(), expr[1].clone())));
        assert!(solver.solve_constraint(&Constraint::Eq(expr[1].clone(), expr[2].clone())));
        assert_eq!(solver.get_ty(&expr[1]), Type::I8);
        assert_eq!(solver.get_ty(&expr[2]), Type::I8);
    }

    #[rstest]
    fn deep_constraint_reversed(expr: [TypeVarId; 3]) {
        let mut solver = Solver::prefill([(expr[0].clone(), Type::I8)]);

        // Solve equality constraint before constraint with solution.
        assert!(!solver.solve_constraint(&Constraint::Eq(expr[1].clone(), expr[2].clone())));
        assert!(solver.solve_constraint(&Constraint::Eq(expr[0].clone(), expr[1].clone())));
        assert_eq!(solver.get_ty(&expr[1]), Type::I8);
        assert_eq!(solver.get_ty(&expr[2]), Type::I8);
    }

    #[rstest]
    fn literal(expr: [TypeVarId; 1]) {
        let mut solver = Solver::new();

        // Manually solve expression as literal.
        solver.solve(expr[0].clone(), Literal::Integer(IntegerKind::Unsigned));
        // Should default to type if none specified.
        assert_eq!(solver.get_ty(&expr[0]), Type::U8);
    }

    #[rstest]
    fn literal_constraint(expr: [TypeVarId; 1]) {
        let mut solver = Solver::new();

        assert!(solver.solve_constraint(&Constraint::Integer(expr[0].clone(), IntegerKind::Any)));
        assert_eq!(solver.get_ty(&expr[0]), Type::I8);
    }

    #[rstest]
    fn simple_infer(expr: [TypeVarId; 2]) {
        // {
        //   1 <-- Integer
        // }   <-- U8
        let [block, one] = expr;

        let solutions = Solver::run(&[
            Constraint::Integer(one.clone(), IntegerKind::Any),
            Constraint::Eq(block.clone(), one.clone()),
            Constraint::Eq(block.clone(), Type::U8.into()),
        ]);
        assert_eq!(solutions[&one], Type::U8);
    }

    #[rstest]
    fn unsigned_infer(expr: [TypeVarId; 4], binding: [TypeVarId; 2]) {
        // {
        //   let a = 1; <-- Integer
        //   let b = 2; <-- Integer
        //   a + b
        // }            <-- U8

        let [a, b] = binding;
        let [one, two, a_plus_b, block] = expr;

        let solutions = Solver::run(&[
            // Literals
            Constraint::Integer(one.clone(), IntegerKind::Any),
            Constraint::Integer(two.clone(), IntegerKind::Any),
            // Variable bindings
            Constraint::Eq(a.clone(), one.clone()),
            Constraint::Eq(b.clone(), two.clone()),
            // Expression
            Constraint::Eq(a_plus_b.clone(), a.clone()),
            Constraint::Eq(a_plus_b.clone(), b.clone()),
            // Implicit return
            Constraint::Eq(a_plus_b.clone(), block.clone()),
            // Block constraint (eg function signature)
            Constraint::Eq(block.clone(), Type::U8.into()),
        ]);

        assert_eq!(solutions[&a], Type::U8);
        assert_eq!(solutions[&b], Type::U8);
    }

    mod solutions_solver {
        use super::*;

        #[rstest]
        fn identical_types() {
            assert_eq!(
                solve_solutions(&Solution::Type(Type::U8), &Solution::Type(Type::U8)),
                Solution::Type(Type::U8)
            );
        }

        #[rstest]
        fn type_and_any_integer_literal() {
            assert_eq!(
                solve_solutions(
                    &Solution::Type(Type::U8),
                    &Solution::Literal(Literal::Integer(IntegerKind::Any))
                ),
                Solution::Type(Type::U8)
            );
        }

        #[rstest]
        fn type_and_signed_integer_literal() {
            assert_eq!(
                solve_solutions(
                    &Solution::Type(Type::I8),
                    &Solution::Literal(Literal::Integer(IntegerKind::Signed))
                ),
                Solution::Type(Type::I8)
            );
        }

        #[rstest]
        fn type_and_unsigned_integer_literal_i8() {
            assert_eq!(
                solve_solutions(
                    &Solution::Type(Type::I8),
                    &Solution::Literal(Literal::Integer(IntegerKind::Unsigned))
                ),
                Solution::Type(Type::I8)
            );
        }

        #[rstest]
        fn type_and_unsigned_integer_literal_u8() {
            assert_eq!(
                solve_solutions(
                    &Solution::Type(Type::U8),
                    &Solution::Literal(Literal::Integer(IntegerKind::Unsigned))
                ),
                Solution::Type(Type::U8)
            );
        }

        #[rstest]
        fn literal_identical() {
            assert_eq!(
                solve_solutions(
                    &Solution::Literal(Literal::Integer(IntegerKind::Unsigned)),
                    &Solution::Literal(Literal::Integer(IntegerKind::Unsigned))
                ),
                Solution::Literal(Literal::Integer(IntegerKind::Unsigned))
            );
        }

        #[rstest]
        fn literal_any_integer() {
            assert_eq!(
                solve_solutions(
                    &Solution::Literal(Literal::Integer(IntegerKind::Unsigned)),
                    &Solution::Literal(Literal::Integer(IntegerKind::Any))
                ),
                Solution::Literal(Literal::Integer(IntegerKind::Unsigned))
            );
        }
    }
}
