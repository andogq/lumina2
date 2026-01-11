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
