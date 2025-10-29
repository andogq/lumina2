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
            [Type::Unit, Type::U8, Type::I8, Type::Boolean]
                .map(|ty| (ty.clone().into(), ty.into())),
        );

        let mut constraints = VecDeque::from_iter(constraints);

        while let Some(constraint) = constraints.pop_front() {
            let solved = solver.solve_constraint(constraint);

            if !solved {
                constraints.push_back(constraint);
            }
        }

        solver
            .solutions
            .keys()
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
                let left = self.root.find_set(left);
                let right = self.root.find_set(right);

                // Find the current solutions.
                let left_solution = self.solutions.get(left);
                let right_solution = self.solutions.get(right);

                match (left_solution, right_solution) {
                    // Try simplify the solutions
                    (Some(left_solution), Some(right_solution)) => {
                        let solution = solve_solutions(left_solution, right_solution);
                        self.solutions.insert(left.clone(), solution.clone());
                        self.solutions.insert(right.clone(), solution.clone());
                        true
                    }
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
                        self.root.union_sets(left.clone(), right.clone());
                        false
                    }
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
