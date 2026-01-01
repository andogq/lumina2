use super::*;

#[derive(Clone, Debug)]
pub struct Thir {
    hir: Hir,
    types: HashMap<TypeVarId, Type>,
}

#[derive(Clone, Debug)]
pub struct Thir2<'hir> {
    pub hir: &'hir Hir,
    pub types: HashMap<TypeVarId, Type>,
}

impl Deref for Thir2<'_> {
    type Target = Hir;

    fn deref(&self) -> &Self::Target {
        self.hir
    }
}

impl<'hir> Thir2<'hir> {
    pub fn new(hir: &'hir Hir, types: HashMap<TypeVarId, Type>) -> Self {
        Self { hir, types }
    }

    pub fn type_of(&self, id: impl Into<TypeVarId>) -> &Type {
        &self.types[&id.into()]
    }
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
