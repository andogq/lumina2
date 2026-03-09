use crate::prelude::*;

use hir::*;

pub struct Thir<'hir> {
    pub hir: &'hir Hir,
    pub identifier_tys: BTreeMap<IdentifierBindingId, TypeId>,
    pub expression_tys: IndexedVec<ExpressionId, TypeId>,
}

impl Deref for Thir<'_> {
    type Target = Hir;

    fn deref(&self) -> &Self::Target {
        self.hir
    }
}

impl<'hir> Thir<'hir> {
    pub fn new(
        hir: &'hir Hir,
        identifiers_tys: BTreeMap<IdentifierBindingId, TypeId>,
        expressions_tys: IndexedVec<ExpressionId, TypeId>,
    ) -> Self {
        Self {
            hir,
            identifier_tys: identifiers_tys,
            expression_tys: expressions_tys,
        }
    }

    pub fn type_of(&self, id: impl ThirIndex) -> TypeId {
        id.type_of(self)
    }
}

pub trait ThirIndex: Copy {
    fn type_of(self, thir: &Thir<'_>) -> TypeId;
}

impl ThirIndex for IdentifierBindingId {
    fn type_of(self, thir: &Thir<'_>) -> TypeId {
        thir.identifier_tys[&self]
    }
}

impl ThirIndex for ExpressionId {
    fn type_of(self, thir: &Thir<'_>) -> TypeId {
        thir.expression_tys[self]
    }
}
