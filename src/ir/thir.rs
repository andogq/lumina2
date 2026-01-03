use crate::prelude::*;

use hir::*;

#[derive(Clone, Debug)]
pub struct Thir<'hir> {
    pub hir: &'hir Hir,
    pub types: HashMap<TypeVarId, TypeId>,
}

impl Deref for Thir<'_> {
    type Target = Hir;

    fn deref(&self) -> &Self::Target {
        self.hir
    }
}

impl<'hir> Thir<'hir> {
    pub fn new(hir: &'hir Hir, types: HashMap<TypeVarId, TypeId>) -> Self {
        Self { hir, types }
    }

    pub fn type_of(&self, id: impl Into<TypeVarId>) -> TypeId {
        self.types[&id.into()]
    }
}
