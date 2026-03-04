use crate::prelude::*;

use super::disjoint_union_set::DisjointUnionSet;

create_id!(SolutionId);

/// Solution within the [`UnificationTable`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Solution {
    /// Unknown solution.
    Unknown,
    /// Concrete [`Type`].
    Concrete(TypeId),
    /// An inferred [`CompositeType`].
    Inferred(CompositeType<SolutionId>),
    /// Some integer.
    AnyInteger,
    /// Some unsigned integer.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "unsigned integer may be used in the future")
    )]
    UnsignedInteger,
    /// Some signed integer.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "signed integer may be used in the future")
    )]
    SignedInteger,
    /// An error.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "error may be used in the future")
    )]
    Error,
}

/// Table for performing unification operations.
#[derive(Clone, Debug, Default)]
pub struct UnificationTable {
    set: DisjointUnionSet<SolutionId, Solution>,
    /// Cache [`Solution`]s for types, so that the same [`SolutionId`] is returned.
    type_cache: BTreeMap<TypeId, SolutionId>,
}

impl UnificationTable {
    /// Create a new unification.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new [`Solution::Concrete`] type variable.
    pub fn unknown(&mut self) -> SolutionId {
        self.set.insert(Solution::Unknown)
    }

    /// Create a new [`Solution::Concrete`] type variable. If the type already has a [`Solution`],
    /// it will be re-used.
    pub fn concrete(&mut self, ty: TypeId) -> SolutionId {
        *self
            .type_cache
            .entry(ty)
            .or_insert_with(|| self.set.insert(Solution::Concrete(ty)))
    }

    /// Create a new [`Solution::AnyInteger`] type variable.
    pub fn any_integer(&mut self) -> SolutionId {
        self.set.insert(Solution::AnyInteger)
    }

    /// Create a new [`Solution::Inferred`] type variable.
    pub fn inferred(&mut self, inferred: CompositeType<SolutionId>) -> SolutionId {
        self.set.insert(Solution::Inferred(inferred))
    }

    /// Get the [`Solution`] of a given [`SolutionId`].
    pub fn get(&mut self, id: SolutionId) -> &Solution {
        self.set.get(id)
    }

    /// Unify the given types. The resulting root type will be returned.
    pub fn unify(&mut self, types: &Types, lhs: SolutionId, rhs: SolutionId) -> SolutionId {
        let lhs = self.set.find_root(lhs);
        let rhs = self.set.find_root(rhs);

        if lhs == rhs {
            return lhs;
        }

        let [lhs_node, rhs_node] = self.set.get_multiple([lhs, rhs]);

        match ((lhs, lhs_node), (rhs, rhs_node)) {
            // One is unknown, point at other root.
            ((unknown, Solution::Unknown), (root, _))
            | ((root, _), (unknown, Solution::Unknown)) => {
                assert_eq!(
                    self.set.redirect(unknown, root).expect("nodes must differ"),
                    Solution::Unknown,
                    "should replace unknown node"
                );
                root
            }
            // One of the types is concrete, it always takes precedence.
            ((concrete, Solution::Concrete(concrete_ty)), (other, other_ty))
            | ((other, other_ty), (concrete, Solution::Concrete(concrete_ty))) => {
                if *concrete_ty == types.never() {
                    // Concrete type is `never`, so return the other type.
                    return other;
                }

                match other_ty {
                    Solution::Concrete(other_ty) => {
                        if concrete_ty != other_ty {
                            if *other_ty == types.never() {
                                // Other type is `never`, so return the concrete type.
                                return concrete;
                            }

                            panic!("cannot unify different concrete types");
                        }
                    }
                    Solution::Inferred(inferred_ty) => {
                        let Type::Composite(composite_ty) = &types[*concrete_ty] else {
                            panic!("cannot infer with primitive");
                        };

                        // Collect the fields from the composite type.
                        let (concrete_fields, inferred_fields) = match (composite_ty, inferred_ty) {
                            (
                                CompositeType::Ref(composite_inner_ty),
                                CompositeType::Ref(inferred_inner_ty),
                            ) => (vec![*composite_inner_ty], vec![*inferred_inner_ty]),
                            (
                                CompositeType::Function {
                                    parameters: composite_parameters,
                                    return_ty: composite_return_ty,
                                },
                                CompositeType::Function {
                                    parameters: inferred_parameters,
                                    return_ty: inferred_return_ty,
                                },
                            ) => (
                                composite_parameters
                                    .iter()
                                    .cloned()
                                    .chain([*composite_return_ty])
                                    .collect(),
                                inferred_parameters
                                    .iter()
                                    .cloned()
                                    .chain([*inferred_return_ty])
                                    .collect(),
                            ),
                            (
                                CompositeType::Tuple(composite_fields),
                                CompositeType::Tuple(inferred_fields),
                            ) => (composite_fields.clone(), inferred_fields.clone()),
                            _ => panic!("cannot unify"),
                        };

                        assert_eq!(concrete_fields.len(), inferred_fields.len());
                        for (concrete, inferred) in concrete_fields.into_iter().zip(inferred_fields)
                        {
                            // Generate a solver type for the concrete type.
                            let parameter_concrete = self.concrete(concrete);

                            // Unify the types.
                            self.unify(types, parameter_concrete, inferred);
                        }
                    }
                    Solution::AnyInteger => {
                        if !matches!(&types[*concrete_ty], Type::I8 | Type::U8) {
                            panic!("type is not any integer");
                        }
                    }
                    Solution::UnsignedInteger => {
                        if !matches!(&types[*concrete_ty], Type::U8) {
                            panic!("type is not unsigned integer");
                        }
                    }
                    Solution::SignedInteger => {
                        if !matches!(&types[*concrete_ty], Type::I8) {
                            panic!("type is not signed integer");
                        }
                    }
                    Solution::Error => todo!(),
                    Solution::Unknown => unreachable!("covered in other branch"),
                }

                // Always redirect to concrete type.
                self.set.redirect(other, concrete).expect("different nodes");
                concrete
            }
            // Both are inferred.
            ((_, Solution::Inferred(inferred_lhs)), (_, Solution::Inferred(inferred_rhs))) => {
                // Collect fields for inferred composite types.
                let (lhs_fields, rhs_fields) = match (inferred_lhs, inferred_rhs) {
                    // Structured types, recursively unify children.
                    (CompositeType::Ref(inner_lhs), CompositeType::Ref(inner_rhs)) => {
                        (vec![*inner_lhs], vec![*inner_rhs])
                    }
                    (
                        CompositeType::Function {
                            parameters: lhs_parameters,
                            return_ty: lhs_return_ty,
                        },
                        CompositeType::Function {
                            parameters: rhs_parameters,
                            return_ty: rhs_return_ty,
                        },
                    ) => (
                        lhs_parameters
                            .iter()
                            .cloned()
                            .chain([*lhs_return_ty])
                            .collect(),
                        rhs_parameters
                            .iter()
                            .cloned()
                            .chain([*rhs_return_ty])
                            .collect(),
                    ),
                    (CompositeType::Tuple(lhs_fields), CompositeType::Tuple(rhs_fields)) => {
                        (lhs_fields.clone(), rhs_fields.clone())
                    }

                    // Type mismatches.
                    _ => panic!("cannot merge mismatched inferred types"),
                };

                // Used later for assertion.
                let inferred_lhs = inferred_lhs.clone();

                // Merge the fields together.
                assert_eq!(
                    lhs_fields.len(),
                    rhs_fields.len(),
                    "cannot merge inferred types of different sizes"
                );
                for (lhs, rhs) in lhs_fields.into_iter().zip(rhs_fields.into_iter()) {
                    self.unify(types, lhs, rhs);
                }

                assert_eq!(
                    self.set.redirect(lhs, rhs).expect("different nodes"),
                    Solution::Inferred(inferred_lhs),
                );
                rhs
            }

            (
                (
                    integer,
                    kind @ (Solution::AnyInteger
                    | Solution::SignedInteger
                    | Solution::UnsignedInteger),
                ),
                (other, solution),
            )
            | (
                (other, solution),
                (
                    integer,
                    kind @ (Solution::AnyInteger
                    | Solution::SignedInteger
                    | Solution::UnsignedInteger),
                ),
            ) => {
                assert!(
                    matches!(
                        solution,
                        Solution::AnyInteger | Solution::UnsignedInteger | Solution::SignedInteger
                    ),
                    "cannot unify an integer with a non-integer"
                );

                match (kind, solution) {
                    (Solution::AnyInteger, _) => {
                        assert_eq!(
                            self.set.redirect(integer, other).expect("different nodes"),
                            Solution::AnyInteger,
                        );
                        other
                    }
                    (lhs, rhs) if lhs == rhs => {
                        let lhs = lhs.clone();
                        assert_eq!(
                            self.set.redirect(integer, other).expect("different nodes"),
                            lhs,
                        );
                        other
                    }
                    _ => panic!("cannot merge incompatible integers"),
                }
            }
            _ => {
                todo!()
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[fixture]
    fn table() -> UnificationTable {
        UnificationTable::new()
    }

    #[fixture]
    fn types() -> Types {
        Types::new()
    }

    #[rstest]
    #[case::unknown(
            |_, _| Solution::Unknown
        )]
    #[case::concrete(
            |_, u8| Solution::Concrete(u8)
        )]
    #[case::inferred(
            |unknown, _| Solution::Inferred(
                CompositeType::Ref(unknown)
            )
        )]
    #[case::any_integer(
            |_, _| Solution::AnyInteger
        )]
    #[case::unsigned_integer(
            |_, _| Solution::UnsignedInteger
        )]
    #[case::signed_integer(
            |_, _| Solution::SignedInteger
        )]
    fn unknown(
        mut table: UnificationTable,
        types: Types,
        #[case] solution: impl FnOnce(SolutionId, TypeId) -> Solution,
    ) {
        let solution = solution(table.set.insert(Solution::Unknown), types.u8());

        let unknown = table.set.insert(Solution::Unknown);
        let other = table.set.insert(solution.clone());

        let result = table.unify(&types, unknown, other);
        assert_eq!(
            table.get(result),
            &solution,
            "unifying with `Unknown` should always result in the other solution"
        );
    }

    mod concrete {
        use super::*;

        #[rstest]
        fn concrete_match(mut table: UnificationTable, types: Types) {
            let lhs = table.set.insert(Solution::Concrete(types.u8()));
            let rhs = table.set.insert(Solution::Concrete(types.u8()));

            let result = table.unify(&types, lhs, rhs);
            assert_eq!(table.get(result), &Solution::Concrete(types.u8()));
        }

        #[rstest]
        #[should_panic(expected = "cannot unify different concrete types")]
        fn concrete_mismatch(mut table: UnificationTable, types: Types) {
            let lhs = table.set.insert(Solution::Concrete(types.u8()));
            let rhs = table.set.insert(Solution::Concrete(types.i8()));

            table.unify(&types, lhs, rhs);
        }

        #[rstest]
        fn propagate_non_never_type(mut table: UnificationTable, types: Types) {
            let lhs = table.set.insert(Solution::Concrete(types.u8()));
            let rhs = table.set.insert(Solution::Concrete(types.never()));

            let result = table.unify(&types, lhs, rhs);
            assert_eq!(table.get(result), &Solution::Concrete(types.u8()));
        }

        #[rstest]
        #[should_panic(expected = "cannot infer with primitive")]
        fn primitive_with_inferred(mut table: UnificationTable, types: Types) {
            let lhs = table.set.insert(Solution::Concrete(types.u8()));
            let unknown = table.set.insert(Solution::Unknown);
            let rhs = table
                .set
                .insert(Solution::Inferred(CompositeType::Ref(unknown)));

            table.unify(&types, lhs, rhs);
        }

        #[rstest]
        #[case::reference(
                |types: &mut Types, ids: [_; 1]| types.ref_of(ids[0]),
                |solutions: [_; 1]| CompositeType::Ref(solutions[0])
            )]
        #[case::tuple(
                |types: &mut Types, ids: [_; 2]| types.tuple(ids),
                |solutions: [_; 2]| CompositeType::Tuple(vec![solutions[0], solutions[1]])
            )]
        #[case::function(
                |types: &mut Types, ids: [_; 3]| types.function([ids[0], ids[1]], ids[2]),
                |solutions: [_; 3]| CompositeType::Function{ parameters: vec![solutions[0], solutions[1]], return_ty: solutions[2] }
            )]
        fn composite_with_inferred<const N: usize>(
            mut table: UnificationTable,
            mut types: Types,
            #[case] composite: impl FnOnce(&mut Types, [TypeId; N]) -> TypeId,
            #[case] inferred: impl FnOnce([SolutionId; N]) -> CompositeType<SolutionId>,
        ) {
            let type_selection = [types.u8(), types.i8(), types.boolean()];
            let unknowns = std::array::from_fn(|_| table.unknown());

            let composite_ty = composite(&mut types, *type_selection[0..N].as_array().unwrap());
            let inferred = inferred(unknowns);

            let composite = table.set.insert(Solution::Concrete(composite_ty));
            let inferred = table.set.insert(Solution::Inferred(inferred));

            let result = table.unify(&types, composite, inferred);

            // Must result in concrete type.
            assert_eq!(table.get(result), &Solution::Concrete(composite_ty));

            // Unknowns should be merged.
            for (ty, unknown) in type_selection.into_iter().zip(unknowns) {
                assert_eq!(table.get(unknown), &Solution::Concrete(ty));
            }
        }

        #[rstest]
        #[case::any_u8(Solution::AnyInteger, |types: &mut Types| types.u8())]
        #[case::any_i8(Solution::AnyInteger, |types: &mut Types| types.i8())]
        #[should_panic(expected = "type is not any integer")]
        #[case::any_boolean(Solution::AnyInteger, |types: &mut Types| types.boolean())]
        #[case::unsigned_u8(Solution::UnsignedInteger, |types: &mut Types| types.u8())]
        #[should_panic(expected = "type is not unsigned integer")]
        #[case::unsigned_i8(Solution::UnsignedInteger, |types: &mut Types| types.i8())]
        #[should_panic(expected = "type is not unsigned integer")]
        #[case::unsigned_boolean(Solution::UnsignedInteger, |types: &mut Types| types.boolean())]
        #[should_panic(expected = "type is not signed integer")]
        #[case::signed_u8(Solution::SignedInteger, |types: &mut Types| types.u8())]
        #[case::signed_i8(Solution::SignedInteger, |types: &mut Types| types.i8())]
        #[should_panic(expected = "type is not signed integer")]
        #[case::signed_boolean(Solution::SignedInteger, |types: &mut Types| types.boolean())]
        fn integer_solutions(
            mut table: UnificationTable,
            mut types: Types,
            #[case] solution: Solution,
            #[case] concrete: impl FnOnce(&mut Types) -> TypeId,
        ) {
            let ty = concrete(&mut types);

            let concrete = table.set.insert(Solution::Concrete(ty));
            let integer_solution = table.set.insert(solution);

            let result = table.unify(&types, concrete, integer_solution);

            assert_eq!(table.get(result), &Solution::Concrete(ty));
        }
    }

    mod inferred {
        use super::*;

        #[rstest]
        #[case::reference(|solutions: [_; 1]| CompositeType::Ref(solutions[0]))]
        #[case::function_no_parameters(|solutions: [_; 1]| CompositeType::Function { parameters: vec![], return_ty: solutions[0] })]
        #[case::function_one_parameter(|solutions: [_; 2]| CompositeType::Function { parameters: vec![solutions[0]], return_ty: solutions[1] })]
        #[case::function_many_parameters(|solutions: [_; 4]| CompositeType::Function { parameters: vec![solutions[0], solutions[1], solutions[2]], return_ty: solutions[3] })]
        #[case::tuple_empty(|_: [_; 0]| CompositeType::Tuple(vec![]))]
        #[case::tuple_one(|solutions: [_; 1]| CompositeType::Tuple(Vec::from_iter(solutions)))]
        #[case::tuple_many(|solutions: [_; 4]| CompositeType::Tuple(Vec::from_iter(solutions)))]
        fn matching<const N: usize>(
            mut table: UnificationTable,
            types: Types,
            #[case] get_inferred: impl Fn([SolutionId; N]) -> CompositeType<SolutionId>,
        ) {
            let [lhs_unknowns, rhs_unknowns] = std::array::from_fn(|_| {
                std::array::from_fn(|_| table.set.insert(Solution::Unknown))
            });

            let lhs = table
                .set
                .insert(Solution::Inferred(get_inferred(lhs_unknowns)));
            let rhs = table
                .set
                .insert(Solution::Inferred(get_inferred(rhs_unknowns)));

            let result = table.unify(&types, lhs, rhs);

            // Unknowns should be merged.
            for (lhs, rhs) in lhs_unknowns.iter().zip(rhs_unknowns.iter()) {
                assert_eq!(table.set.find_root(*lhs), table.set.find_root(*rhs));
            }

            // Result should be inferred based on merged unknown components.
            let expected = get_inferred(lhs_unknowns.map(|unknown| table.set.find_root(unknown)));
            assert_eq!(table.get(result), &Solution::Inferred(expected));
        }

        #[rstest]
        #[should_panic(expected = "cannot merge mismatched inferred types")]
        #[case::reference_and_function(
            |solutions: [_; 1]| CompositeType::Ref(solutions[0]),
            |solutions: [_; 1]| CompositeType::Function { parameters: vec![], return_ty: solutions[0] },
        )]
        #[should_panic(expected = "cannot merge inferred types of different sizes")]
        #[case::function_different_parameters(
            |solutions: [_; 1]| CompositeType::Function { parameters: vec![], return_ty: solutions[0] },
            |solutions: [_; 3]| CompositeType::Function { parameters: vec![solutions[0], solutions[1]], return_ty: solutions[2] },
        )]
        #[should_panic(expected = "cannot merge inferred types of different sizes")]
        #[case::tuple_different_sizes(
            |solutions: [_; 1]| CompositeType::Tuple(Vec::from_iter(solutions)),
            |solutions: [_; 3]| CompositeType::Tuple(Vec::from_iter(solutions)),
        )]
        fn mismatched<const N: usize, const M: usize>(
            mut table: UnificationTable,
            types: Types,
            #[case] get_lhs: impl Fn([SolutionId; N]) -> CompositeType<SolutionId>,
            #[case] get_rhs: impl Fn([SolutionId; M]) -> CompositeType<SolutionId>,
        ) {
            let lhs_unknowns = std::array::from_fn(|_| table.set.insert(Solution::Unknown));
            let rhs_unknowns = std::array::from_fn(|_| table.set.insert(Solution::Unknown));

            let lhs = table.set.insert(Solution::Inferred(get_lhs(lhs_unknowns)));
            let rhs = table.set.insert(Solution::Inferred(get_rhs(rhs_unknowns)));

            table.unify(&types, lhs, rhs);
        }
    }

    #[rstest]
    #[case::both_any(Solution::AnyInteger, Solution::AnyInteger, Solution::AnyInteger)]
    #[case::both_signed(
        Solution::SignedInteger,
        Solution::SignedInteger,
        Solution::SignedInteger
    )]
    #[case::both_unsigned(
        Solution::UnsignedInteger,
        Solution::UnsignedInteger,
        Solution::UnsignedInteger
    )]
    #[case::any_and_signed(Solution::AnyInteger, Solution::SignedInteger, Solution::SignedInteger)]
    #[case::any_and_unsigned(
        Solution::AnyInteger,
        Solution::UnsignedInteger,
        Solution::UnsignedInteger
    )]
    #[should_panic(expected = "cannot merge incompatible integers")]
    #[case::signed_and_unsigned(
        Solution::SignedInteger,
        Solution::UnsignedInteger,
        // NOTE: Outcome doesn't matter as it will panic.
        Solution::Error
    )]
    fn integer(
        mut table: UnificationTable,
        types: Types,
        #[case] lhs: Solution,
        #[case] rhs: Solution,
        #[case] outcome: Solution,
    ) {
        let lhs = table.set.insert(lhs);
        let rhs = table.set.insert(rhs);

        let result = table.unify(&types, lhs, rhs);

        assert_eq!(table.get(result), &outcome);
    }
}
