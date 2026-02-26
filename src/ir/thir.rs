use crate::{
    prelude::*,
    ty::{TypeVarId, TypeVars},
};

use hir::*;

#[derive(Clone, Debug)]
pub struct Thir<'hir> {
    pub hir: &'hir Hir,
    pub types: HashMap<TypeVarId, TypeId>,
    pub type_vars: TypeVars,
}

impl Deref for Thir<'_> {
    type Target = Hir;

    fn deref(&self) -> &Self::Target {
        self.hir
    }
}

impl<'hir> Thir<'hir> {
    pub fn new(hir: &'hir Hir, types: HashMap<TypeVarId, TypeId>, type_vars: TypeVars) -> Self {
        Self {
            hir,
            types,
            type_vars,
        }
    }

    pub fn type_of(&self, id: impl Into<TypeVar>) -> TypeId {
        let var = self.type_vars.get(id.into());
        self.types[&var]
    }
}

pub struct Thir2<'hir> {
    pub hir: &'hir Hir,
    pub identifier_tys: BTreeMap<IdentifierBindingId, TypeId>,
    pub expression_tys: IndexedVec<ExpressionId, TypeId>,
}

impl Deref for Thir2<'_> {
    type Target = Hir;

    fn deref(&self) -> &Self::Target {
        self.hir
    }
}

impl<'hir> Thir2<'hir> {
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
    fn type_of(self, thir: &Thir2<'_>) -> TypeId;
}

impl ThirIndex for IdentifierBindingId {
    fn type_of(self, thir: &Thir2<'_>) -> TypeId {
        thir.identifier_tys[&self]
    }
}

impl ThirIndex for ExpressionId {
    fn type_of(self, thir: &Thir2<'_>) -> TypeId {
        thir.expression_tys[self]
    }
}
