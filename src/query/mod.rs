#![cfg_attr(
    not(test),
    expect(dead_code, reason = "queries are not used yet"),
    expect(unused_imports, reason = "queries are not used yet")
)]

use crate::prelude::*;
use hir::*;

pub use self::traits::*;

/// Query builder for searching through the [`Hir`] for some [`Queryable`].
pub struct Query<O: Queryable> {
    /// Current filter.
    filter: O::Filter,
}

impl<O: Queryable> Query<O> {
    /// Consume the query, and produce an iterator of items which satisfy the filter.
    pub fn query<'hir>(self, hir: &'hir hir::Hir) -> impl Iterator<Item = &'hir O>
    where
        O: 'hir,
    {
        let candidates = O::get_all(hir);

        candidates
            .iter()
            .filter(move |candidate| candidate.validate(&self.filter))
    }
}

/// A queryable entity.
pub trait Queryable: Sized {
    /// Representation of the filter for this entity.
    type Filter: Default;

    /// ID used to represent this entity in the [`Hir`].
    type Id;

    /// Fetch all entities.
    fn get_all(hir: &Hir) -> &IndexedVec<Self::Id, Self>;

    /// Validate this entity against the provided filter.
    fn validate(&self, filter: &Self::Filter) -> bool;
}

mod traits {
    use super::*;

    /// Helper methods for querying [`Trait`]s.
    impl Query<Trait> {
        /// Create a new query for traits.
        pub fn traits() -> Query<Trait> {
            Query {
                filter: <Trait as Queryable>::Filter::default(),
            }
        }

        /// Select traits satisfying the provided signature filter.
        pub fn methods(mut self, signatures: impl IntoIterator<Item = SignatureFilter>) -> Self {
            self.filter.signatures = Some(Vec::from_iter(signatures));
            self
        }
    }

    /// Implementation of [`Queryable`] for [`Trait`].
    impl Queryable for Trait {
        type Filter = TraitFilter;
        type Id = TraitId;

        fn get_all(hir: &Hir) -> &IndexedVec<Self::Id, Self> {
            &hir.traits
        }

        fn validate(&self, filter: &Self::Filter) -> bool {
            if let Some(filter_functions) = &filter.signatures {
                if self.methods.len() != filter_functions.len() {
                    // Number of functions differ.
                    return false;
                }

                let mut unvalidated = self.methods.iter_keys().collect::<HashSet<_>>();
                let valid = filter_functions.iter().all(|filter| {
                    // For each unvalidated method, try match a filter.
                    let Some(&validated) = unvalidated
                        .iter()
                        .find(|&&id| filter.validate(&self.methods[id]))
                    else {
                        return false;
                    };

                    // Mark the method as validated.
                    assert!(unvalidated.remove(&validated));

                    // Continue the search.
                    true
                });

                if !valid {
                    return false;
                }

                assert!(unvalidated.is_empty());
            };

            true
        }
    }

    /// Information required to filter traits.
    #[derive(Clone, Default, Debug)]
    pub struct TraitFilter {
        /// Signatures that the trait must contain.
        signatures: Option<Vec<SignatureFilter>>,
    }

    /// Information required to filter a function signature.
    #[derive(Clone, Default, Debug)]
    pub struct SignatureFilter {
        /// Parameters which the signature must match.
        parameters: Option<Vec<MaybeSelfType>>,
        /// Return type of the signature.
        return_ty: Option<MaybeSelfType>,
    }

    impl SignatureFilter {
        /// Create a new filter.
        pub fn new() -> Self {
            Self::default()
        }

        /// Only accept signatures which have the provided parameters.
        pub fn parameters(mut self, parameters: impl IntoIterator<Item = MaybeSelfType>) -> Self {
            self.parameters = Some(Vec::from_iter(parameters));
            self
        }

        /// Only accept signatures which have the provided return type.
        pub fn return_ty(mut self, return_ty: impl Into<MaybeSelfType>) -> Self {
            self.return_ty = Some(return_ty.into());
            self
        }

        /// Validate the provided [`FunctionSignature`] matches the filter.
        fn validate(&self, signature: &FunctionSignature<MaybeSelfType>) -> bool {
            if let Some(parameters) = &self.parameters {
                if parameters.len() != signature.parameters.len() {
                    // Parameter count must match.
                    return false;
                }

                // Ensure parameter types match.
                let parameters_match = parameters
                    .iter()
                    .zip(signature.parameters.iter().map(|(_, ty)| ty))
                    .all(|(parameter, signature)| parameter == signature);
                if !parameters_match {
                    return false;
                }
            }

            if let Some(return_ty) = &self.return_ty
                && return_ty != &signature.return_ty
            {
                // Return type must match.
                return false;
            }

            true
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[fixture]
    fn ctx() -> Ctx {
        Ctx::new()
    }

    #[fixture]
    fn hir() -> Hir {
        let mut hir = Hir::default();

        // Empty trait.
        hir.traits.insert(Trait {
            name: TraitBindingId::from_id(0),
            method_scope: ScopeId::from_id(0),
            method_bindings: HashMap::new(),
            methods: IndexedVec::new(),
        });

        // Single method trait.
        hir.traits.insert(Trait {
            name: TraitBindingId::from_id(1),
            method_scope: ScopeId::from_id(1),
            method_bindings: HashMap::from_iter([(
                IdentifierBindingId::from_id(0),
                TraitMethodId::from_id(0),
            )]),
            methods: indexed_vec![FunctionSignature {
                parameters: vec![],
                return_ty: MaybeSelfType::Type(TypeId::from_id(0)),
            }],
        });

        // Single method trait with parameters.
        hir.traits.insert(Trait {
            name: TraitBindingId::from_id(2),
            method_scope: ScopeId::from_id(2),
            method_bindings: HashMap::from_iter([(
                IdentifierBindingId::from_id(0),
                TraitMethodId::from_id(0),
            )]),
            methods: indexed_vec![FunctionSignature {
                parameters: vec![
                    (IdentifierBindingId::from_id(1), MaybeSelfType::SelfType),
                    (
                        IdentifierBindingId::from_id(2),
                        MaybeSelfType::Type(TypeId::from_id(0))
                    ),
                ],
                return_ty: MaybeSelfType::Type(TypeId::from_id(0)),
            }],
        });

        // Multi method trait.
        hir.traits.insert(Trait {
            name: TraitBindingId::from_id(1),
            method_scope: ScopeId::from_id(1),
            method_bindings: HashMap::from_iter([
                (IdentifierBindingId::from_id(0), TraitMethodId::from_id(0)),
                (IdentifierBindingId::from_id(1), TraitMethodId::from_id(1)),
            ]),
            methods: indexed_vec![
                FunctionSignature {
                    parameters: vec![],
                    return_ty: MaybeSelfType::Type(TypeId::from_id(0)),
                },
                FunctionSignature {
                    parameters: vec![],
                    return_ty: MaybeSelfType::Type(TypeId::from_id(0)),
                }
            ],
        });

        hir
    }

    #[rstest]
    fn all_traits(hir: Hir) {
        assert_eq!(Query::traits().query(&hir).count(), 4);
    }

    #[rstest]
    fn single_method_traits(hir: Hir) {
        assert_eq!(
            Query::traits()
                .methods([SignatureFilter::new()])
                .query(&hir)
                .count(),
            2
        );
    }

    #[rstest]
    fn single_method_traits_returning_ty(hir: Hir) {
        assert_eq!(
            Query::traits()
                .methods([SignatureFilter::new().return_ty(TypeId::from_id(0))])
                .query(&hir)
                .count(),
            2
        );
    }

    #[rstest]
    fn single_method_trait_no_parameters_returning_ty(hir: Hir) {
        assert_eq!(
            Query::traits()
                .methods([SignatureFilter::new()
                    .parameters([])
                    .return_ty(TypeId::from_id(0))])
                .query(&hir)
                .count(),
            1
        );
    }

    #[rstest]
    fn single_method_trait_with_parameters(hir: Hir) {
        assert_eq!(
            Query::traits()
                .methods([SignatureFilter::new().parameters([
                    MaybeSelfType::SelfType,
                    MaybeSelfType::Type(TypeId::from_id(0))
                ])])
                .query(&hir)
                .count(),
            1
        );
    }

    #[rstest]
    fn multiple_method_trait(hir: Hir) {
        assert_eq!(
            Query::traits()
                .methods([SignatureFilter::new(), SignatureFilter::new()])
                .query(&hir)
                .count(),
            1
        );
    }
}
