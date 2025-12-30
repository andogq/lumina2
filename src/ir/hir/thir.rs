use super::*;

#[derive(Clone, Debug)]
pub struct Thir {
    hir: Hir,
    types: HashMap<TypeVarId, Type>,
}

impl Thir {
    pub fn new(hir: Hir, types: HashMap<TypeVarId, Type>) -> Self {
        Self { hir, types }
    }

    pub fn type_of(&self, id: impl Into<TypeVarId>) -> &Type {
        &self.types[&id.into()]
    }
}

impl Deref for Thir {
    type Target = Hir;

    fn deref(&self) -> &Self::Target {
        &self.hir
    }
}
