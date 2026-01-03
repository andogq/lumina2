use super::*;
use crate::ty::Literal;

#[derive(Clone, Debug, PartialEq, Eq)]
enum MergeResult {
    /// Merge the nodes, and substitute the provided solution as the solution.
    Substitute(Solution),
    /// Merge the provided type variables, and substitute with a solution referencing the resulting
    /// root node.
    MergeAndReference(TypeVarId, TypeVarId),
    /// Merge is not possible due to an incompatibility.
    Incompatible(IncompatibleKind),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum IncompatibleKind {
    /// Types are not equal.
    Type(Type, Type),
    /// Literal cannot be coerced into type.
    Coercion(Literal, Type),
    /// Literals cannot be narrowed.
    Narrow(Literal, Literal),
    /// Type is not a reference.
    NotReference(Type),
    /// Reference cannot be used as a literal.
    ReferenceLiteral,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum NonConcreteType {
    Type(Type),
    Literal(Literal),
}

#[derive(Clone, Debug)]
pub struct Solver {
    root: DisjointUnionSet,
    solutions: HashMap<TypeVarId, Solution>,
}

impl Solver {
    pub fn new() -> Self {
        Self {
            root: DisjointUnionSet::new(),
            solutions: HashMap::new(),
        }
    }

    pub fn run(constraints: &[(TypeVarId, Constraint)]) -> HashMap<TypeVarId, Type> {
        let mut solver = Self::new();

        for (var, constraint) in constraints {
            assert!(solver.process_constraint(var, constraint));
        }

        solver.get_types()
    }

    pub fn process_constraint(&mut self, var: &TypeVarId, constraint: &Constraint) -> bool {
        match constraint {
            Constraint::Eq(eq_var) => self.solve_eq(var, eq_var),
            Constraint::Integer(integer_kind) => self.solve_integer(var, integer_kind),
            Constraint::Reference(ref_var) => self.solve_reference(var, ref_var),
            Constraint::Function {
                parameters,
                return_ty,
            } => self.solve_function(var, parameters, return_ty),
        }
    }

    fn solve_eq(&mut self, var: &TypeVarId, eq_var: &TypeVarId) -> bool {
        self.merge(var, eq_var).is_some()
    }

    fn solve_integer(&mut self, var: &TypeVarId, integer_kind: &IntegerKind) -> bool {
        let var = self.root.find_set(var).clone();
        let var_solution = self.get_solution(&var);
        let integer_solution = Solution::Literal(Literal::Integer(integer_kind.clone()));

        let Ok((solution, should_insert)) =
            self.simple_merge(var_solution.as_ref(), Some(&integer_solution))
        else {
            return false;
        };

        assert!(should_insert);

        self.solutions.insert(
            var.clone(),
            solution.expect("no nodes to merge for reference"),
        );

        true
    }

    fn solve_reference(&mut self, var: &TypeVarId, ref_var: &TypeVarId) -> bool {
        let var = self.root.find_set(var).clone();
        let ref_var = self.root.find_set(ref_var).clone();

        let var_solution = self.get_solution(&var);
        let ref_solution = Solution::Reference(ref_var.clone());

        let Ok((solution, should_insert)) =
            self.simple_merge(var_solution.as_ref(), Some(&ref_solution))
        else {
            return false;
        };

        assert!(should_insert);

        self.solutions.insert(
            var.clone(),
            solution.expect("no nodes to merge for reference"),
        );

        true
    }

    fn solve_function(
        &mut self,
        var: &TypeVarId,
        parameter_vars: &[TypeVarId],
        return_ty_var: &TypeVarId,
    ) -> bool {
        let Some(Solution::Type(Type::Function {
            parameters,
            return_ty,
        })) = self.get_solution(var)
        else {
            unimplemented!();
        };

        assert_eq!(parameter_vars.len(), parameters.len());

        let solved_parameters = parameter_vars
            .iter()
            .zip(parameters)
            .filter_map(|(parameter_var, parameter)| {
                let var = self
                    .merge(parameter_var, &parameter.clone().into())
                    .unwrap();
                self.get_type(&var)
            })
            .collect::<Vec<_>>();

        let solved_return_ty = {
            let var = self.merge(return_ty_var, &(*return_ty).into()).unwrap();
            self.get_type(&var)
        };

        solved_return_ty.is_some() && solved_parameters.len() == parameter_vars.len()
    }

    fn merge(&mut self, lhs: &TypeVarId, rhs: &TypeVarId) -> Option<TypeVarId> {
        let lhs = self.root.find_set(lhs);
        let rhs = self.root.find_set(rhs);

        if lhs == rhs {
            // Already merged!
            return Some(lhs.clone());
        }

        let lhs_solution = self.get_solution(lhs);
        let rhs_solution = self.get_solution(rhs);

        let lhs = lhs.clone();
        let rhs = rhs.clone();

        // Ensure that if the variables have a solution, they're compatible and can be merged.
        let (solution, should_insert) = self
            .simple_merge(lhs_solution.as_ref(), rhs_solution.as_ref())
            .ok()?;

        // Remove any existing solutions so they don't get re-used.
        self.solutions.remove(&lhs);
        self.solutions.remove(&rhs);

        // Merge the nodes.
        let root = self.root.union_sets(lhs.clone(), rhs.clone());

        if should_insert {
            // If no solution is provided, use the merged root.
            let solution = solution.unwrap_or_else(|| Solution::Reference(root.clone()));

            // Insert the solution.
            self.solutions.insert(root.clone(), solution);
        }

        Some(root)
    }

    fn simple_merge(
        &mut self,
        lhs: Option<&Solution>,
        rhs: Option<&Solution>,
    ) -> Result<(Option<Solution>, bool), IncompatibleKind> {
        Ok(match (lhs, rhs) {
            (Some(lhs_solution), Some(rhs_solution)) => (
                match self.merge_solutions(lhs_solution, rhs_solution) {
                    MergeResult::Substitute(solution) => Some(solution),
                    MergeResult::MergeAndReference(lhs, rhs) => {
                        self.merge(&lhs, &rhs).map(Solution::Reference)
                    }
                    MergeResult::Incompatible(kind) => return Err(kind),
                },
                true,
            ),
            (Some(solution), None) | (None, Some(solution)) => (Some(solution.clone()), true),
            (None, None) => (None, false),
        })
    }

    fn merge_solutions(&self, lhs: &Solution, rhs: &Solution) -> MergeResult {
        match (lhs, rhs) {
            // Already identical solutions.
            (lhs, rhs) if lhs == rhs => MergeResult::Substitute(lhs.clone()),
            // One side is already solved as a type reference, and other side is a reference of an
            // unknown type.
            (Solution::Type(ty @ Type::Ref(ref_ty)), Solution::Reference(ref_var))
            | (Solution::Reference(ref_var), Solution::Type(ty @ Type::Ref(ref_ty))) => {
                match self.get_non_concrete_type(ref_var) {
                    // Solution already exists, and it's compatible.
                    Some(NonConcreteType::Type(solved_ty)) if solved_ty == **ref_ty => {
                        MergeResult::Substitute(Solution::Type(ty.clone()))
                    }
                    Some(NonConcreteType::Literal(literal)) if literal.can_coerce(ref_ty) => {
                        MergeResult::Substitute(Solution::Type(ty.clone()))
                    }
                    // Solution doesn't exist, so existing solution is fine.
                    None => MergeResult::Substitute(Solution::Type(ty.clone())),
                    // Existing solution isn't compatible.
                    Some(NonConcreteType::Type(solved_ty)) => MergeResult::Incompatible(
                        IncompatibleKind::Type(solved_ty, *ref_ty.clone()),
                    ),
                    Some(NonConcreteType::Literal(literal)) => MergeResult::Incompatible(
                        IncompatibleKind::Coercion(literal, *ref_ty.clone()),
                    ),
                }
            }
            (Solution::Type(ty), Solution::Reference(ref_var))
            | (Solution::Reference(ref_var), Solution::Type(ty)) => {
                MergeResult::Incompatible(match self.get_non_concrete_type(ref_var) {
                    Some(NonConcreteType::Type(solved_ty)) => {
                        IncompatibleKind::Type(ty.clone(), Type::Ref(Box::new(solved_ty)))
                    }
                    Some(NonConcreteType::Literal(_)) => IncompatibleKind::ReferenceLiteral,
                    None => IncompatibleKind::NotReference(ty.clone()),
                })
            }
            // One side is a type, and other side is a literal.
            (Solution::Type(ty), Solution::Literal(literal))
            | (Solution::Literal(literal), Solution::Type(ty)) => {
                if literal.can_coerce(ty) {
                    MergeResult::Substitute(Solution::Type(ty.clone()))
                } else {
                    MergeResult::Incompatible(IncompatibleKind::Coercion(
                        literal.clone(),
                        ty.clone(),
                    ))
                }
            }
            // One side is a reference to an unknown type, and other side is a literal. This can
            // never be merged, as literal references are not popular.
            (Solution::Reference(_), Solution::Literal(_))
            | (Solution::Literal(_), Solution::Reference(_)) => {
                MergeResult::Incompatible(IncompatibleKind::ReferenceLiteral)
            }
            // Both sides are references.
            (Solution::Reference(lhs), Solution::Reference(rhs)) => {
                MergeResult::MergeAndReference(lhs.clone(), rhs.clone())
            }
            // Both sides are literals.
            (Solution::Literal(lhs), Solution::Literal(rhs)) => {
                if let Some(literal) = lhs.narrow(rhs) {
                    MergeResult::Substitute(Solution::Literal(literal))
                } else {
                    MergeResult::Incompatible(IncompatibleKind::Narrow(lhs.clone(), rhs.clone()))
                }
            }
            // Propagate any non-never types.
            (Solution::Type(Type::Never), Solution::Type(ty))
            | (Solution::Type(ty), Solution::Type(Type::Never)) => {
                MergeResult::Substitute(Solution::Type(ty.clone()))
            }
            // Equal solutions are already checked, so if this is reached they are not equal.
            (Solution::Type(lhs), Solution::Type(rhs)) => {
                MergeResult::Incompatible(IncompatibleKind::Type(lhs.clone(), rhs.clone()))
            }
        }
    }

    fn get_solution(&self, var: &TypeVarId) -> Option<Solution> {
        // Types always have a solution.
        if let TypeVarId::Type(ty) = var {
            return Some(Solution::Type(ty.clone()));
        }

        let var = self.root.find_set(var);
        self.solutions.get(var).cloned()
    }

    fn get_non_concrete_type(&self, var: &TypeVarId) -> Option<NonConcreteType> {
        match self.get_solution(var)? {
            Solution::Type(solution) => Some(NonConcreteType::Type(solution.clone())),
            Solution::Reference(type_var_id) => Some(NonConcreteType::Type(Type::Ref(Box::new(
                self.get_type(&type_var_id)?,
            )))),
            Solution::Literal(literal) => Some(NonConcreteType::Literal(literal.clone())),
        }
    }

    fn get_type(&self, var: &TypeVarId) -> Option<Type> {
        Some(match self.get_non_concrete_type(var)? {
            NonConcreteType::Type(ty) => ty,
            NonConcreteType::Literal(literal) => literal.to_type(),
        })
    }

    pub fn get_types(&self) -> HashMap<TypeVarId, Type> {
        self.root
            .keys()
            .chain(self.solutions.keys())
            .map(|var| (var.clone(), self.get_type(var).unwrap()))
            .collect()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[fixture]
    fn expression<const N: usize>() -> [TypeVarId; N] {
        (0..N)
            .map(|i| TypeVarId::from(ExpressionId::from_id(i)))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    #[fixture]
    fn binding<const N: usize>() -> [TypeVarId; N] {
        (0..N)
            .map(|i| TypeVarId::from(BindingId::from_id(i)))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    #[fixture]
    fn solver() -> Solver {
        Solver::new()
    }

    #[rstest]
    fn prefilled(mut solver: Solver, expression: [TypeVarId; 1]) {
        solver
            .solutions
            .extend([(expression[0].clone(), Solution::Type(Type::I8))]);
        assert_eq!(solver.get_type(&expression[0]).unwrap(), Type::I8);
    }

    #[rstest]
    fn simple_constraint(mut solver: Solver, expression: [TypeVarId; 2]) {
        solver
            .solutions
            .extend([(expression[0].clone(), Solution::Type(Type::I8))]);

        assert!(solver.process_constraint(&expression[0], &Constraint::Eq(expression[1].clone())));
        assert_eq!(solver.get_type(&expression[1]).unwrap(), Type::I8);
    }

    #[rstest]
    fn deep_constraint(mut solver: Solver, expression: [TypeVarId; 3]) {
        solver
            .solutions
            .extend([(expression[0].clone(), Solution::Type(Type::I8))]);

        assert!(solver.process_constraint(&expression[0], &Constraint::Eq(expression[1].clone())));
        assert!(solver.process_constraint(&expression[1], &Constraint::Eq(expression[2].clone())));
        assert_eq!(solver.get_type(&expression[1]).unwrap(), Type::I8);
        assert_eq!(solver.get_type(&expression[2]).unwrap(), Type::I8);
    }

    #[rstest]
    fn deep_constraint_reversed(mut solver: Solver, expression: [TypeVarId; 3]) {
        solver
            .solutions
            .extend([(expression[0].clone(), Solution::Type(Type::I8))]);

        // Solve equality constraint before constraint with solution.
        assert!(solver.process_constraint(&expression[1], &Constraint::Eq(expression[2].clone())));
        assert!(solver.process_constraint(&expression[0], &Constraint::Eq(expression[1].clone())));
        assert_eq!(solver.get_type(&expression[1]).unwrap(), Type::I8);
        assert_eq!(solver.get_type(&expression[2]).unwrap(), Type::I8);
    }

    #[rstest]
    fn literal(mut solver: Solver, expression: [TypeVarId; 1]) {
        solver.solutions.extend([
            // Manually solve expression as literal.
            (
                expression[0].clone(),
                Solution::Literal(Literal::Integer(IntegerKind::Unsigned)),
            ),
        ]);

        // Should default to type if none specified.
        assert_eq!(solver.get_type(&expression[0]).unwrap(), Type::U8);
    }

    #[rstest]
    fn literal_constraint(expression: [TypeVarId; 1]) {
        let mut solver = Solver::new();

        assert!(solver.process_constraint(&expression[0], &Constraint::Integer(IntegerKind::Any)));
        assert_eq!(solver.get_type(&expression[0]).unwrap(), Type::I8);
    }

    #[rstest]
    fn simple_infer(expression: [TypeVarId; 2]) {
        // {
        //   1 <-- Integer
        // }   <-- U8
        let [block, one] = expression;

        let solutions = Solver::run(&[
            (one.clone(), Constraint::Integer(IntegerKind::Any)),
            (block.clone(), Constraint::Eq(one.clone())),
            (block.clone(), Constraint::Eq(Type::U8.into())),
        ]);
        assert_eq!(solutions[&one], Type::U8);
    }

    #[rstest]
    fn unsigned_infer(expression: [TypeVarId; 4], binding: [TypeVarId; 2]) {
        // {
        //   let a = 1; <-- Integer
        //   let b = 2; <-- Integer
        //   a + b
        // }            <-- U8

        let [a, b] = binding;
        let [one, two, a_plus_b, block] = expression;

        let solutions = Solver::run(&[
            // Literals
            (one.clone(), Constraint::Integer(IntegerKind::Any)),
            (two.clone(), Constraint::Integer(IntegerKind::Any)),
            // Variable bindings
            (a.clone(), Constraint::Eq(one.clone())),
            (b.clone(), Constraint::Eq(two.clone())),
            // Expression
            (a_plus_b.clone(), Constraint::Eq(a.clone())),
            (a_plus_b.clone(), Constraint::Eq(b.clone())),
            // Implicit return
            (a_plus_b.clone(), Constraint::Eq(block.clone())),
            // Block constraint (eg function signature)
            (block.clone(), Constraint::Eq(Type::U8.into())),
        ]);

        assert_eq!(solutions[&a], Type::U8);
        assert_eq!(solutions[&b], Type::U8);
    }

    #[rstest]
    fn reference_infer(expression: [TypeVarId; 4], binding: [TypeVarId; 2]) {
        // {
        //   let a = 1;  <- Integer
        //   let b = &a; <- Reference(a)
        //   *b
        // }             <- U8
        let [a, b] = binding;
        let [one, ref_a, deref_b, block] = expression;

        let solutions = Solver::run(&[
            // Literal
            (one.clone(), Constraint::Integer(IntegerKind::Any)),
            // Expressions
            (ref_a.clone(), Constraint::Reference(a.clone())), // &a
            (b.clone(), Constraint::Reference(deref_b.clone())), // *b
            // Variable bindings
            (a.clone(), Constraint::Eq(one.clone())),
            (b.clone(), Constraint::Eq(ref_a.clone())),
            // Implicit return
            (block.clone(), Constraint::Eq(deref_b.clone())),
            // Block constraint
            (block.clone(), Constraint::Eq(Type::U8.into())),
        ]);

        assert_eq!(solutions[&a], Type::U8);
        assert_eq!(solutions[&b], Type::Ref(Box::new(Type::U8)));
    }

    #[rstest]
    fn more_references(expression: [TypeVarId; 4], binding: [TypeVarId; 2]) {
        // {
        //   let a = 123; <- Integer
        //   let b = &a;  <- Reference(a)
        //   *b
        // }              <- U8
        let [num, ref_a, deref_b, block] = expression;
        let [a, b] = binding;

        let solutions = Solver::run(&[
            // Literal
            (num.clone(), Constraint::Integer(IntegerKind::Any)),
            // Expressions
            (ref_a.clone(), Constraint::Reference(a.clone())),
            (b.clone(), Constraint::Reference(deref_b.clone())),
            // Bindings
            (a.clone(), Constraint::Eq(num.clone())),
            (b.clone(), Constraint::Eq(ref_a.clone())),
            // Block
            (block.clone(), Constraint::Eq(deref_b)),
            (block.clone(), Constraint::Eq(Type::U8.into())),
        ]);

        assert_eq!(solutions[&block], Type::U8);
        assert_eq!(solutions[&a], Type::U8);
        assert_eq!(solutions[&b], Type::Ref(Box::new(Type::U8)));
    }

    #[rstest]
    fn overriding(expression: [TypeVarId; 4]) {
        let solutions = Solver::run(&[
            (expression[0].clone(), Constraint::Integer(IntegerKind::Any)),
            (
                expression[1].clone(),
                Constraint::Reference(expression[0].clone()),
            ),
            (
                expression[2].clone(),
                Constraint::Reference(expression[3].clone()),
            ),
            (expression[2].clone(), Constraint::Eq(expression[1].clone())),
            (expression[3].clone(), Constraint::Eq(Type::U8.into())),
        ]);

        assert_eq!(solutions[&expression[0]], Type::U8);
        assert_eq!(solutions[&expression[3]], Type::U8);
    }

    mod merge_solutions {
        use super::*;

        #[rstest]
        fn identical_types(solver: Solver) {
            assert_eq!(
                solver.merge_solutions(&Solution::Type(Type::U8), &Solution::Type(Type::U8)),
                MergeResult::Substitute(Solution::Type(Type::U8))
            );
        }

        #[rstest]
        fn type_and_any_integer_literal(solver: Solver) {
            assert_eq!(
                solver.merge_solutions(
                    &Solution::Type(Type::U8),
                    &Solution::Literal(Literal::Integer(IntegerKind::Any))
                ),
                MergeResult::Substitute(Solution::Type(Type::U8))
            );
        }

        #[rstest]
        fn type_and_signed_integer_literal(solver: Solver) {
            assert_eq!(
                solver.merge_solutions(
                    &Solution::Type(Type::I8),
                    &Solution::Literal(Literal::Integer(IntegerKind::Signed))
                ),
                MergeResult::Substitute(Solution::Type(Type::I8))
            );
        }

        #[rstest]
        fn type_and_unsigned_integer_literal_u8(solver: Solver) {
            assert_eq!(
                solver.merge_solutions(
                    &Solution::Type(Type::U8),
                    &Solution::Literal(Literal::Integer(IntegerKind::Unsigned))
                ),
                MergeResult::Substitute(Solution::Type(Type::U8))
            );
        }

        #[rstest]
        fn literal_identical(solver: Solver) {
            assert_eq!(
                solver.merge_solutions(
                    &Solution::Literal(Literal::Integer(IntegerKind::Unsigned)),
                    &Solution::Literal(Literal::Integer(IntegerKind::Unsigned))
                ),
                MergeResult::Substitute(Solution::Literal(Literal::Integer(IntegerKind::Unsigned)))
            );
        }

        #[rstest]
        fn literal_any_integer(solver: Solver) {
            assert_eq!(
                solver.merge_solutions(
                    &Solution::Literal(Literal::Integer(IntegerKind::Unsigned)),
                    &Solution::Literal(Literal::Integer(IntegerKind::Any))
                ),
                MergeResult::Substitute(Solution::Literal(Literal::Integer(IntegerKind::Unsigned)))
            );
        }
    }
}
