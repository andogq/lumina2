use super::*;
use crate::ty::Literal;

#[derive(Clone, Debug, PartialEq, Eq)]
enum MergeResult {
    /// Merge the nodes, and substitute the provided solution as the solution.
    Substitute(Solution),
    /// Merge the provided type variables, and substitute with a solution referencing the resulting
    /// root node.
    MergeAndReference(TypeVarId, TypeVarId),
    /// Merge each pair of nodes returned, and substitute with [`Solution::Tuple`].
    TupleMergeAndSubstitute(Vec<(TypeVarId, TypeVarId)>),
    /// Merge is not possible due to an incompatibility.
    Incompatible(IncompatibleKind),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum IncompatibleKind {
    /// Types are not equal.
    Type(TypeId, TypeId),
    /// Literal cannot be coerced into type.
    Coercion(Literal, TypeId),
    /// Literals cannot be narrowed.
    Narrow(Literal, Literal),
    /// Type is not a reference.
    NotReference(TypeId),
    /// Solution cannot be used as a reference.
    ReferenceSolution(Solution),
    /// Type is not a tuple.
    NotTuple(TypeId),
    /// Solution cannot be used as a tuple.
    TupleSolution(Solution),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum NonConcreteType {
    Type(TypeId),
    Literal(Literal),
    Tuple(Vec<TypeVarId>),
}

#[derive(Debug)]
pub struct Solver<'types, 'type_vars> {
    types: &'types mut Types,
    type_vars: &'type_vars mut TypeVars,
    root: DisjointUnionSet<TypeVarId>,
    solutions: HashMap<TypeVarId, Solution>,
}

impl<'types, 'type_vars> Solver<'types, 'type_vars> {
    pub fn new(types: &'types mut Types, type_vars: &'type_vars mut TypeVars) -> Self {
        Self {
            types,
            type_vars,
            root: DisjointUnionSet::new(),
            solutions: HashMap::new(),
        }
    }

    pub fn run(
        types: &'types mut Types,
        type_vars: &'type_vars mut TypeVars,
        constraints: &[(TypeVarId, Constraint)],
    ) -> HashMap<TypeVarId, TypeId> {
        let mut solver = Self::new(types, type_vars);

        for (var, constraint) in constraints {
            solver.process_constraint(*var, constraint);
        }

        solver.get_types()
    }

    pub fn process_constraint(&mut self, var: TypeVarId, constraint: &Constraint) {
        match constraint {
            Constraint::Eq(eq_var) => self.solve_eq(var, *eq_var),
            Constraint::Integer(integer_kind) => self.solve_integer(var, integer_kind),
            Constraint::Reference(ref_var) => self.solve_reference(var, *ref_var),
            Constraint::Function {
                parameters,
                return_ty,
            } => self.solve_function(var, parameters, *return_ty),
            Constraint::Aggregate(values) => self.solve_aggregate(var, values),
            Constraint::Field { aggregate, field } => self.solve_field(var, *aggregate, *field),
        }
    }

    fn solve_eq(&mut self, var: TypeVarId, eq_var: TypeVarId) {
        self.merge(var, eq_var).unwrap();
    }

    fn solve_integer(&mut self, var: TypeVarId, integer_kind: &IntegerKind) {
        let var = self.root.find_set(var);
        let var_solution = self.get_solution(var);
        let integer_solution = Solution::Literal(Literal::Integer(integer_kind.clone()));

        self.simple_merge_and_insert(var, var_solution.as_ref(), Some(&integer_solution))
            .unwrap();
    }

    fn solve_reference(&mut self, var: TypeVarId, ref_var: TypeVarId) {
        let var = self.root.find_set(var);
        let ref_var = self.root.find_set(ref_var);

        let var_solution = self.get_solution(var);
        let ref_solution = Solution::Reference(ref_var);

        self.simple_merge_and_insert(var, var_solution.as_ref(), Some(&ref_solution))
            .unwrap();
    }

    fn solve_function(
        &mut self,
        var: TypeVarId,
        parameter_vars: &[TypeVarId],
        return_ty_var: TypeVarId,
    ) {
        let Some((parameters, return_ty)) = self.get_solution(var).and_then(|solution| {
            let Solution::Type(ty) = solution else {
                return None;
            };
            let Type::Function {
                parameters,
                return_ty,
            } = &self.types[ty]
            else {
                return None;
            };
            Some((parameters.clone(), *return_ty))
        }) else {
            unimplemented!();
        };

        assert_eq!(parameter_vars.len(), parameters.len());

        let solved_parameters = parameter_vars
            .iter()
            .zip(parameters)
            .filter_map(|(parameter_var, parameter)| {
                let parameter = self.type_vars.intern(parameter);
                let var = self.root.union_sets(*parameter_var, parameter);
                self.get_type(var)
            })
            .collect::<Vec<_>>();

        let solved_return_ty = {
            let return_ty = self.type_vars.intern(return_ty);
            let var = self.root.union_sets(return_ty_var, return_ty);
            self.get_type(var)
        };

        assert!(solved_return_ty.is_some());
        assert!(solved_parameters.len() == parameter_vars.len());
    }

    fn solve_aggregate(&mut self, var: TypeVarId, values: &[TypeVarId]) {
        let var = self.root.find_set(var);

        let solution = self.get_solution(var);
        let tuple_solution = Solution::Tuple(Vec::from_iter(
            values.iter().map(|value| self.root.find_set(*value)),
        ));

        self.simple_merge_and_insert(var, solution.as_ref(), Some(&tuple_solution))
            .unwrap();
    }

    fn solve_field(&mut self, var: TypeVarId, aggregate: TypeVarId, field: usize) {
        let var = self.root.find_set(var);
        let aggregate = self.root.find_set(aggregate);

        match self.get_solution(aggregate) {
            Some(solution) => match solution {
                Solution::Type(type_id) => match &self.types[type_id] {
                    Type::Tuple(fields) => {
                        if field >= fields.len() {
                            panic!("field not in aggregate");
                        }

                        let ty = self.type_vars.intern(fields[field]);
                        self.root.union_sets(var, ty);
                    }
                    _ => panic!("cannot access field in type"),
                },
                Solution::Tuple(type_var_ids) => {
                    if field >= type_var_ids.len() {
                        panic!("field not in aggregate");
                    }

                    let ty_var = type_var_ids[field];
                    self.root.union_sets(var, ty_var);
                }
                _ => todo!("deal with other solutions"),
            },
            None => todo!("handle aggregate field without existing solution"),
        }
    }

    fn merge(&mut self, lhs: TypeVarId, rhs: TypeVarId) -> Option<TypeVarId> {
        let lhs = self.root.find_set(lhs);
        let rhs = self.root.find_set(rhs);

        if lhs == rhs {
            // Already merged!
            return Some(lhs);
        }

        let lhs_solution = self.get_solution(lhs);
        let rhs_solution = self.get_solution(rhs);

        // Merge the nodes.
        let root = self.root.union_sets(lhs, rhs);

        // Remove any existing solutions so they don't get re-used.
        self.solutions.remove(&lhs);
        self.solutions.remove(&rhs);

        // Ensure that if the variables have a solution, they're compatible and can be merged.
        self.simple_merge_and_insert(root, lhs_solution.as_ref(), rhs_solution.as_ref())
            .unwrap();

        Some(root)
    }

    /// Simplify the provided solution, attempting to convert to [`Solution::Type`] where possible.
    fn simplify_solution(&mut self, solution: Solution) -> Solution {
        match solution {
            Solution::Type(type_id) => Solution::Type(type_id),
            Solution::Reference(ref_var) => {
                if let Some(Solution::Type(ref_ty)) = self.get_solution(ref_var) {
                    // Referenced type is already resolved, so generate a reference type to it.
                    Solution::Type(self.types.ref_of(ref_ty))
                } else {
                    // Re-use existing solution.
                    Solution::Reference(ref_var)
                }
            }
            Solution::Literal(literal) => Solution::Literal(literal),
            Solution::Tuple(type_var_ids) => {
                let items = type_var_ids
                    .iter()
                    .filter_map(|var| self.get_non_concrete_type(*var))
                    .filter_map(|ty| {
                        if let NonConcreteType::Type(ty) = ty {
                            Some(ty)
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>();

                if items.len() == type_var_ids.len() {
                    Solution::Type(self.types.tuple(items))
                } else {
                    Solution::Tuple(type_var_ids)
                }
            }
        }
    }

    /// Merge the `lhs` and `rhs` solutions, and store them in the solutions map under `var`.
    fn simple_merge_and_insert(
        &mut self,
        var: TypeVarId,
        lhs: Option<&Solution>,
        rhs: Option<&Solution>,
    ) -> Result<(), IncompatibleKind> {
        let solution = match (lhs, rhs) {
            // Both solutions exist, so they must be merged.
            (Some(lhs_solution), Some(rhs_solution)) => {
                match self.merge_solutions(lhs_solution, rhs_solution) {
                    MergeResult::Substitute(solution) => Some(solution),
                    MergeResult::MergeAndReference(lhs, rhs) => {
                        self.merge(lhs, rhs).map(Solution::Reference)
                    }
                    MergeResult::TupleMergeAndSubstitute(values) => Some(Solution::Tuple(
                        values
                            .into_iter()
                            .map(|(lhs, rhs)| self.merge(lhs, rhs).unwrap())
                            .collect(),
                    )),
                    MergeResult::Incompatible(kind) => return Err(kind),
                }
            }
            // Only one solution exists, so it can be propagated.
            (Some(solution), None) | (None, Some(solution)) => Some(solution.clone()),
            // Neither of the solutions exist, so ignore.
            (None, None) => None,
        };

        if let Some(solution) = solution {
            let solution = self.simplify_solution(solution);

            // TODO: Assert that no solution existed?
            self.solutions.insert(var, solution);
        }

        Ok(())
    }

    /// Attempt to merge the provided solutions into a single solution.
    ///
    /// This is where most of the type system rules are enforced.
    fn merge_solutions(&mut self, lhs: &Solution, rhs: &Solution) -> MergeResult {
        match (lhs, rhs) {
            // Already identical solutions.
            (lhs, rhs) if lhs == rhs => MergeResult::Substitute(lhs.clone()),

            // One side has solution, other side is a reference.
            (Solution::Type(ty), Solution::Reference(ref_var))
            | (Solution::Reference(ref_var), Solution::Type(ty)) => {
                if let Type::Ref(ref_ty) = &self.types[*ty] {
                    let ref_ty = *ref_ty;

                    match self.get_non_concrete_type(*ref_var) {
                        // Solution already exists, and it's compatible.
                        Some(NonConcreteType::Type(solved_ty)) if solved_ty == ref_ty => {
                            MergeResult::Substitute(Solution::Type(*ty))
                        }
                        Some(NonConcreteType::Literal(literal))
                            if literal.can_coerce(self.types, ref_ty) =>
                        {
                            MergeResult::Substitute(Solution::Type(*ty))
                        }
                        Some(NonConcreteType::Tuple(values)) => {
                            if let Type::Tuple(value_tys) = &self.types[ref_ty] {
                                // Referenced type is a tuple, so values can be zipped.
                                MergeResult::TupleMergeAndSubstitute(
                                    value_tys
                                        .iter()
                                        .map(|ty| self.type_vars.intern(*ty))
                                        .zip(values.iter().cloned())
                                        .collect(),
                                )
                            } else {
                                // Referenced type must be a tuple.
                                MergeResult::Incompatible(IncompatibleKind::NotTuple(ref_ty))
                            }
                        }
                        // Solution doesn't exist, so existing solution is fine.
                        None => MergeResult::Substitute(Solution::Type(*ty)),
                        // Existing solution isn't compatible.
                        Some(NonConcreteType::Type(solved_ty)) => {
                            MergeResult::Incompatible(IncompatibleKind::Type(solved_ty, ref_ty))
                        }
                        Some(NonConcreteType::Literal(literal)) => {
                            MergeResult::Incompatible(IncompatibleKind::Coercion(literal, ref_ty))
                        }
                    }
                } else {
                    MergeResult::Incompatible(match self.get_non_concrete_type(*ref_var) {
                        Some(NonConcreteType::Type(solved_ty)) => {
                            IncompatibleKind::Type(*ty, self.types.ref_of(solved_ty))
                        }
                        Some(NonConcreteType::Literal(literal)) => {
                            IncompatibleKind::ReferenceSolution(literal.into())
                        }
                        Some(NonConcreteType::Tuple(_)) | None => {
                            IncompatibleKind::NotReference(*ty)
                        }
                    })
                }
            }

            // One side is a type, and other side is a literal.
            (Solution::Type(ty), Solution::Literal(literal))
            | (Solution::Literal(literal), Solution::Type(ty)) => {
                if literal.can_coerce(self.types, *ty) {
                    MergeResult::Substitute(Solution::Type(*ty))
                } else {
                    MergeResult::Incompatible(IncompatibleKind::Coercion(literal.clone(), *ty))
                }
            }

            // One side is a reference to an unknown type, and other side is a literal. This can
            // never be merged, as literal references are not popular.
            (Solution::Reference(_), solution @ Solution::Literal(_))
            | (solution @ Solution::Literal(_), Solution::Reference(_)) => {
                MergeResult::Incompatible(IncompatibleKind::ReferenceSolution(solution.clone()))
            }

            // One side is a tuple, the other is a type.
            (Solution::Tuple(tuple), Solution::Type(ty))
            | (Solution::Type(ty), Solution::Tuple(tuple)) => {
                // Ensure the type is a tuple.
                if let Type::Tuple(values) = &self.types[*ty] {
                    MergeResult::TupleMergeAndSubstitute(
                        tuple
                            .iter()
                            .cloned()
                            .zip(values.iter().map(|value| self.type_vars.intern(*value)))
                            .collect(),
                    )
                } else {
                    MergeResult::Incompatible(IncompatibleKind::NotTuple(*ty))
                }
            }

            // Both sides are tuples.
            (Solution::Tuple(lhs), Solution::Tuple(rhs)) => MergeResult::TupleMergeAndSubstitute(
                lhs.iter().cloned().zip(rhs.iter().cloned()).collect(),
            ),

            // Tuple with some other solution, which is invalid.
            (Solution::Tuple(_), solution) | (solution, Solution::Tuple(_)) => {
                MergeResult::Incompatible(IncompatibleKind::TupleSolution(solution.clone()))
            }

            // Both sides are references.
            (Solution::Reference(lhs), Solution::Reference(rhs)) => {
                MergeResult::MergeAndReference(*lhs, *rhs)
            }

            // Both sides are literals.
            (Solution::Literal(lhs), Solution::Literal(rhs)) => {
                if let Some(literal) = lhs.narrow(rhs) {
                    MergeResult::Substitute(Solution::Literal(literal))
                } else {
                    MergeResult::Incompatible(IncompatibleKind::Narrow(lhs.clone(), rhs.clone()))
                }
            }

            // Equal solutions are already checked.
            (Solution::Type(lhs), Solution::Type(rhs)) => {
                if matches!(&self.types[*lhs], Type::Never) {
                    // Propagate any non-never types.
                    MergeResult::Substitute(Solution::Type(*rhs))
                } else if matches!(&self.types[*rhs], Type::Never) {
                    // Propagate any non-never types.
                    MergeResult::Substitute(Solution::Type(*lhs))
                } else {
                    // Solutions aren't equal.
                    MergeResult::Incompatible(IncompatibleKind::Type(*lhs, *rhs))
                }
            }
        }
    }

    fn get_solution(&self, var: TypeVarId) -> Option<Solution> {
        // Types always have a solution.
        if let TypeVar::Type(ty) = &self.type_vars[var] {
            return Some(Solution::Type(*ty));
        }

        let var = self.root.find_set(var);
        self.solutions.get(&var).cloned()
    }

    fn get_non_concrete_type(&mut self, var: TypeVarId) -> Option<NonConcreteType> {
        match self.get_solution(var)? {
            Solution::Type(solution) => Some(NonConcreteType::Type(solution)),
            Solution::Reference(type_var_id) => {
                let inner_ty = self.get_type(type_var_id)?;
                Some(NonConcreteType::Type(self.types.ref_of(inner_ty)))
            }
            Solution::Literal(literal) => Some(NonConcreteType::Literal(literal.clone())),
            Solution::Tuple(values) => Some(NonConcreteType::Tuple(values.clone())),
        }
    }

    fn get_type(&mut self, var: TypeVarId) -> Option<TypeId> {
        Some(match self.get_non_concrete_type(var)? {
            NonConcreteType::Type(ty) => ty,
            NonConcreteType::Literal(literal) => literal.to_type(self.types),
            NonConcreteType::Tuple(values) => {
                // Attempt to cast each value to a concrete type.
                let tys = values
                    .iter()
                    .flat_map(|value| self.get_type(*value))
                    .collect::<Vec<_>>();

                // Every type must be successfully converted.
                if tys.len() != values.len() {
                    return None;
                }

                self.types.tuple(tys)
            }
        })
    }

    pub fn get_types(&mut self) -> HashMap<TypeVarId, TypeId> {
        self.root
            .keys()
            .chain(self.solutions.keys())
            .cloned()
            // HACK: Buffer iterator to deal with borrow checker.
            .collect::<Vec<_>>()
            .into_iter()
            .map(|var| {
                let ty = self.get_type(var).unwrap();
                (var, ty)
            })
            .collect()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[fixture]
    fn expression<const N: usize>() -> [TypeVar; N] {
        (0..N)
            .map(|i| TypeVar::from(ExpressionId::from_id(i)))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    #[fixture]
    fn binding<const N: usize>() -> [TypeVar; N] {
        (0..N)
            .map(|i| TypeVar::from(BindingId::from_id(i)))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    #[fixture]
    fn types() -> Types {
        Types::new()
    }

    #[fixture]
    fn type_vars() -> TypeVars {
        TypeVars::new()
    }

    #[rstest]
    fn prefilled(mut types: Types, mut type_vars: TypeVars, expression: [TypeVar; 1]) {
        let expression = expression.map(|expression| type_vars.intern(expression));
        let i8 = types.i8();
        let mut solver = Solver::new(&mut types, &mut type_vars);
        solver
            .solutions
            .extend([(expression[0], Solution::Type(i8))]);
        assert_eq!(solver.get_type(expression[0]).unwrap(), i8);
    }

    #[rstest]
    fn simple_constraint(mut types: Types, mut type_vars: TypeVars, expression: [TypeVar; 2]) {
        let expression = expression.map(|expression| type_vars.intern(expression));
        let i8 = types.i8();
        let mut solver = Solver::new(&mut types, &mut type_vars);
        solver
            .solutions
            .extend([(expression[0], Solution::Type(i8))]);

        solver.process_constraint(expression[0], &Constraint::Eq(expression[1]));
        assert_eq!(solver.get_type(expression[1]).unwrap(), i8);
    }

    #[rstest]
    fn deep_constraint(mut types: Types, mut type_vars: TypeVars, expression: [TypeVar; 3]) {
        let expression = expression.map(|expression| type_vars.intern(expression));
        let i8 = types.i8();
        let mut solver = Solver::new(&mut types, &mut type_vars);
        solver
            .solutions
            .extend([(expression[0], Solution::Type(i8))]);

        solver.process_constraint(expression[0], &Constraint::Eq(expression[1]));
        solver.process_constraint(expression[1], &Constraint::Eq(expression[2]));
        assert_eq!(solver.get_type(expression[1]).unwrap(), i8);
        assert_eq!(solver.get_type(expression[2]).unwrap(), i8);
    }

    #[rstest]
    fn deep_constraint_reversed(
        mut types: Types,
        mut type_vars: TypeVars,
        expression: [TypeVar; 3],
    ) {
        let expression = expression.map(|expression| type_vars.intern(expression));
        let i8 = types.i8();
        let mut solver = Solver::new(&mut types, &mut type_vars);
        solver
            .solutions
            .extend([(expression[0], Solution::Type(i8))]);

        // Solve equality constraint before constraint with solution.
        solver.process_constraint(expression[1], &Constraint::Eq(expression[2]));
        solver.process_constraint(expression[0], &Constraint::Eq(expression[1]));
        assert_eq!(solver.get_type(expression[1]).unwrap(), i8);
        assert_eq!(solver.get_type(expression[2]).unwrap(), i8);
    }

    #[rstest]
    fn literal(mut types: Types, mut type_vars: TypeVars, expression: [TypeVar; 1]) {
        let expression = expression.map(|expression| type_vars.intern(expression));
        let u8 = types.u8();
        let mut solver = Solver::new(&mut types, &mut type_vars);
        solver.solutions.extend([
            // Manually solve expression as literal.
            (
                expression[0],
                Solution::Literal(Literal::Integer(IntegerKind::Unsigned)),
            ),
        ]);

        // Should default to type if none specified.
        assert_eq!(solver.get_type(expression[0]).unwrap(), u8);
    }

    #[rstest]
    fn literal_constraint(mut types: Types, mut type_vars: TypeVars, expression: [TypeVar; 1]) {
        let expression = expression.map(|expression| type_vars.intern(expression));
        let i8 = types.i8();
        let mut solver = Solver::new(&mut types, &mut type_vars);

        solver.process_constraint(expression[0], &Constraint::Integer(IntegerKind::Any));
        assert_eq!(solver.get_type(expression[0]).unwrap(), i8);
    }

    #[rstest]
    fn simple_infer(mut types: Types, mut type_vars: TypeVars, expression: [TypeVar; 2]) {
        // {
        //   1 <-- Integer
        // }   <-- U8
        let [block, one] = expression.map(|expression| type_vars.intern(expression));

        let u8 = types.u8();
        let u8_ty = type_vars.intern(u8);

        let solutions = Solver::run(
            &mut types,
            &mut type_vars,
            &[
                (one, Constraint::Integer(IntegerKind::Any)),
                (block, Constraint::Eq(one)),
                (block, Constraint::Eq(u8_ty)),
            ],
        );
        assert_eq!(solutions[&one], u8);
    }

    #[rstest]
    fn unsigned_infer(
        mut types: Types,
        mut type_vars: TypeVars,
        expression: [TypeVar; 4],
        binding: [TypeVar; 2],
    ) {
        // {
        //   let a = 1; <-- Integer
        //   let b = 2; <-- Integer
        //   a + b
        // }            <-- U8

        let [a, b] = binding.map(|expression| type_vars.intern(expression));
        let [one, two, a_plus_b, block] = expression.map(|expression| type_vars.intern(expression));

        let u8 = types.u8();
        let u8_ty = type_vars.intern(u8);

        let solutions = Solver::run(
            &mut types,
            &mut type_vars,
            &[
                // Literals
                (one, Constraint::Integer(IntegerKind::Any)),
                (two, Constraint::Integer(IntegerKind::Any)),
                // Variable bindings
                (a, Constraint::Eq(one)),
                (b, Constraint::Eq(two)),
                // Expression
                (a_plus_b, Constraint::Eq(a)),
                (a_plus_b, Constraint::Eq(b)),
                // Implicit return
                (a_plus_b, Constraint::Eq(block)),
                // Block constraint (eg function signature)
                (block, Constraint::Eq(u8_ty)),
            ],
        );

        assert_eq!(solutions[&a], u8);
        assert_eq!(solutions[&b], u8);
    }

    #[rstest]
    fn reference_infer(
        mut types: Types,
        mut type_vars: TypeVars,
        expression: [TypeVar; 4],
        binding: [TypeVar; 2],
    ) {
        // {
        //   let a = 1;  <- Integer
        //   let b = &a; <- Reference(a)
        //   *b
        // }             <- U8
        let [a, b] = binding.map(|binding| type_vars.intern(binding));
        let [one, ref_a, deref_b, block] =
            expression.map(|expression| type_vars.intern(expression));

        let u8 = types.u8();
        let ref_u8 = types.ref_of(u8);

        let u8_ty = type_vars.intern(u8);

        let solutions = Solver::run(
            &mut types,
            &mut type_vars,
            &[
                // Literal
                (one, Constraint::Integer(IntegerKind::Any)),
                // Expressions
                (ref_a, Constraint::Reference(a)),   // &a
                (b, Constraint::Reference(deref_b)), // *b
                // Variable bindings
                (a, Constraint::Eq(one)),
                (b, Constraint::Eq(ref_a)),
                // Implicit return
                (block, Constraint::Eq(deref_b)),
                // Block constraint
                (block, Constraint::Eq(u8_ty)),
            ],
        );

        assert_eq!(solutions[&a], u8);
        assert_eq!(solutions[&b], ref_u8);
    }

    #[rstest]
    fn more_references(
        mut types: Types,
        mut type_vars: TypeVars,
        expression: [TypeVar; 4],
        binding: [TypeVar; 2],
    ) {
        // {
        //   let a = 123; <- Integer
        //   let b = &a;  <- Reference(a)
        //   *b
        // }              <- U8
        let [num, ref_a, deref_b, block] =
            expression.map(|expression| type_vars.intern(expression));
        let [a, b] = binding.map(|expression| type_vars.intern(expression));

        let u8 = types.u8();
        let ref_u8 = types.ref_of(u8);

        let u8_ty = type_vars.intern(u8);

        let solutions = Solver::run(
            &mut types,
            &mut type_vars,
            &[
                // Literal
                (num, Constraint::Integer(IntegerKind::Any)),
                // Expressions
                (ref_a, Constraint::Reference(a)),
                (b, Constraint::Reference(deref_b)),
                // Bindings
                (a, Constraint::Eq(num)),
                (b, Constraint::Eq(ref_a)),
                // Block
                (block, Constraint::Eq(deref_b)),
                (block, Constraint::Eq(u8_ty)),
            ],
        );

        assert_eq!(solutions[&block], u8);
        assert_eq!(solutions[&a], u8);
        assert_eq!(solutions[&b], ref_u8);
    }

    #[rstest]
    fn tuple(
        mut types: Types,
        mut type_vars: TypeVars,
        expression: [TypeVar; 5],
        binding: [TypeVar; 3],
    ) {
        // {
        //   let a = 123;  <- Integer
        //   let b = true; <- Boolean
        //   let c = &a;   <- Reference(a)
        //   (a, b c)      <- Tuple([a, b, c])
        // } <- ??? (should be (i8, bool, &i8))
        let [num, e_true, ref_a, e_tuple, block] =
            expression.map(|expression| type_vars.intern(expression));
        let [a, b, c] = binding.map(|expression| type_vars.intern(expression));

        let i8 = types.i8();
        let bool = types.boolean();
        let ref_i8 = types.ref_of(i8);
        let tuple = types.tuple([i8, bool, ref_i8]);

        let bool_ty = type_vars.intern(bool);

        let solutions = Solver::run(
            &mut types,
            &mut type_vars,
            &[
                // Literal
                (num, Constraint::Integer(IntegerKind::Any)),
                (e_true, Constraint::Eq(bool_ty)),
                // Expressions
                (ref_a, Constraint::Reference(a)),
                (e_tuple, Constraint::Aggregate(vec![a, b, c])),
                // Bindings
                (a, Constraint::Eq(num)),
                (b, Constraint::Eq(e_true)),
                (c, Constraint::Eq(ref_a)),
                // Block
                (block, Constraint::Eq(e_tuple)),
            ],
        );

        assert_eq!(solutions[&block], tuple);
    }

    #[rstest]
    fn overriding(mut types: Types, mut type_vars: TypeVars, expression: [TypeVar; 4]) {
        let u8 = types.u8();
        let u8_ty = type_vars.intern(u8);

        let expression = expression.map(|expression| type_vars.intern(expression));

        let solutions = Solver::run(
            &mut types,
            &mut type_vars,
            &[
                (expression[0], Constraint::Integer(IntegerKind::Any)),
                (expression[1], Constraint::Reference(expression[0])),
                (expression[2], Constraint::Reference(expression[3])),
                (expression[2], Constraint::Eq(expression[1])),
                (expression[3], Constraint::Eq(u8_ty)),
            ],
        );

        assert_eq!(solutions[&expression[0]], u8);
        assert_eq!(solutions[&expression[3]], u8);
    }

    mod merge_solutions {
        use super::*;

        #[rstest]
        fn identical_types(mut types: Types, mut type_vars: TypeVars) {
            let u8 = types.u8();
            let mut solver = Solver::new(&mut types, &mut type_vars);
            assert_eq!(
                solver.merge_solutions(&Solution::Type(u8), &Solution::Type(u8)),
                MergeResult::Substitute(Solution::Type(u8))
            );
        }

        #[rstest]
        fn type_and_any_integer_literal(mut types: Types, mut type_vars: TypeVars) {
            let u8 = types.u8();
            let mut solver = Solver::new(&mut types, &mut type_vars);
            assert_eq!(
                solver.merge_solutions(
                    &Solution::Type(u8),
                    &Solution::Literal(Literal::Integer(IntegerKind::Any))
                ),
                MergeResult::Substitute(Solution::Type(u8))
            );
        }

        #[rstest]
        fn type_and_signed_integer_literal(mut types: Types, mut type_vars: TypeVars) {
            let i8 = types.i8();
            let mut solver = Solver::new(&mut types, &mut type_vars);
            assert_eq!(
                solver.merge_solutions(
                    &Solution::Type(i8),
                    &Solution::Literal(Literal::Integer(IntegerKind::Signed))
                ),
                MergeResult::Substitute(Solution::Type(i8))
            );
        }

        #[rstest]
        fn type_and_unsigned_integer_literal_u8(mut types: Types, mut type_vars: TypeVars) {
            let u8 = types.u8();
            let mut solver = Solver::new(&mut types, &mut type_vars);
            assert_eq!(
                solver.merge_solutions(
                    &Solution::Type(u8),
                    &Solution::Literal(Literal::Integer(IntegerKind::Unsigned))
                ),
                MergeResult::Substitute(Solution::Type(u8))
            );
        }

        #[rstest]
        fn literal_identical(mut types: Types, mut type_vars: TypeVars) {
            let mut solver = Solver::new(&mut types, &mut type_vars);
            assert_eq!(
                solver.merge_solutions(
                    &Solution::Literal(Literal::Integer(IntegerKind::Unsigned)),
                    &Solution::Literal(Literal::Integer(IntegerKind::Unsigned))
                ),
                MergeResult::Substitute(Solution::Literal(Literal::Integer(IntegerKind::Unsigned)))
            );
        }

        #[rstest]
        fn literal_any_integer(mut types: Types, mut type_vars: TypeVars) {
            let mut solver = Solver::new(&mut types, &mut type_vars);
            assert_eq!(
                solver.merge_solutions(
                    &Solution::Literal(Literal::Integer(IntegerKind::Unsigned)),
                    &Solution::Literal(Literal::Integer(IntegerKind::Any))
                ),
                MergeResult::Substitute(Solution::Literal(Literal::Integer(IntegerKind::Unsigned)))
            );
        }

        #[rstest]
        fn tuple_and_tuple_type(
            mut types: Types,
            mut type_vars: TypeVars,
            expression: [TypeVar; 2],
        ) {
            let i8 = types.i8();
            let u8 = types.u8();
            let tuple = types.tuple([i8, u8]);

            let i8_ty = type_vars.intern(i8);
            let u8_ty = type_vars.intern(u8);

            let [field_0, field_1] = expression.map(|expression| type_vars.intern(expression));

            let mut solver = Solver::new(&mut types, &mut type_vars);
            assert_eq!(
                solver.merge_solutions(
                    &Solution::Tuple(vec![field_0, field_1]),
                    &Solution::Type(tuple),
                ),
                MergeResult::TupleMergeAndSubstitute(vec![(field_0, i8_ty), (field_1, u8_ty)]),
            );
        }

        #[rstest]
        fn tuple_and_tuple_known(
            mut types: Types,
            mut type_vars: TypeVars,
            expression: [TypeVar; 2],
        ) {
            let i8 = types.i8();
            let u8 = types.u8();

            let i8_ty = type_vars.intern(i8);
            let u8_ty = type_vars.intern(u8);

            let [field_0, field_1] = expression.map(|expression| type_vars.intern(expression));

            let mut solver = Solver::new(&mut types, &mut type_vars);
            assert_eq!(
                solver.merge_solutions(
                    &Solution::Tuple(vec![field_0, u8_ty]),
                    &Solution::Tuple(vec![i8_ty, field_1]),
                ),
                MergeResult::TupleMergeAndSubstitute(vec![(field_0, i8_ty), (u8_ty, field_1,)]),
            );
        }

        #[rstest]
        fn tuple_and_tuple_unknown(
            mut types: Types,
            mut type_vars: TypeVars,
            expression: [TypeVar; 4],
        ) {
            let [field_0, field_1, field_2, field_3] =
                expression.map(|expression| type_vars.intern(expression));

            let mut solver = Solver::new(&mut types, &mut type_vars);
            assert_eq!(
                solver.merge_solutions(
                    &Solution::Tuple(vec![field_0, field_1]),
                    &Solution::Tuple(vec![field_2, field_3]),
                ),
                MergeResult::TupleMergeAndSubstitute(vec![(field_0, field_2), (field_1, field_3)]),
            );
        }

        /// Test combining a reference tuple expression with an explicit tuple reference type.
        ///
        /// ```text
        /// &(i8, u8) == &(field_0, field_1)
        ///     = Tuple([
        ///         (i8 == field_0),
        ///         (u8 == field_1),
        ///     ])
        /// ```
        #[rstest]
        fn tuple_and_tuple_ref_ty(
            mut types: Types,
            mut type_vars: TypeVars,
            expression: [TypeVar; 4],
        ) {
            let field_0_ty = types.i8();
            let field_1_ty = types.u8();
            let tuple_ty = types.tuple([field_0_ty, field_1_ty]);
            let tuple_ref_ty = types.ref_of(tuple_ty);

            let [field_0, field_1, tuple, _] =
                expression.map(|expression| type_vars.intern(expression));

            let field_0_ty_var = type_vars.intern(field_0_ty);
            let field_1_ty_var = type_vars.intern(field_1_ty);

            let mut solver = Solver::new(&mut types, &mut type_vars);
            // Pretend that `tuple` has already been solved to `(field_0, field_1)`.
            solver
                .solutions
                .insert(tuple, Solution::Tuple(vec![field_0, field_1]));
            assert_eq!(
                solver.merge_solutions(&Solution::Type(tuple_ref_ty), &Solution::Reference(tuple)),
                MergeResult::TupleMergeAndSubstitute(vec![
                    (field_0_ty_var, field_0),
                    (field_1_ty_var, field_1)
                ]),
            );
        }
    }

    mod simplify_solution {
        use super::*;

        #[rstest]
        fn tuple_resolved_tys(mut types: Types, mut type_vars: TypeVars) {
            let u8 = types.u8();
            let i8 = types.i8();

            let u8_ty = type_vars.intern(u8);
            let i8_ty = type_vars.intern(i8);

            let tuple_ty = types.tuple([u8, i8]);

            let mut solver = Solver::new(&mut types, &mut type_vars);
            assert!(matches!(
                solver.simplify_solution(Solution::Tuple(vec![u8_ty, i8_ty])),
                Solution::Type(ty) if ty == tuple_ty,
            ));
        }

        #[rstest]
        fn tuple_partially_resolved_tys(
            mut types: Types,
            mut type_vars: TypeVars,
            expression: [TypeVar; 1],
        ) {
            let u8 = types.u8();
            let u8_ty = type_vars.intern(u8);

            let [expression] = expression.map(|expression| type_vars.intern(expression));

            let mut solver = Solver::new(&mut types, &mut type_vars);
            let solution = Solution::Tuple(vec![u8_ty, expression]);
            assert_eq!(solver.simplify_solution(solution.clone()), solution,);
        }

        #[rstest]
        fn tuple_literal(mut types: Types, mut type_vars: TypeVars) {
            let mut solver = Solver::new(&mut types, &mut type_vars);
            let solution = Solution::Literal(Literal::Integer(IntegerKind::Any));
            assert_eq!(solver.simplify_solution(solution.clone()), solution)
        }
    }
}
