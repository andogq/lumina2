use super::*;

#[derive(Clone, Debug)]
pub struct Thir<'hir> {
    pub hir: &'hir Hir,
    pub types: HashMap<TypeVarId, Type>,
}

impl Deref for Thir<'_> {
    type Target = Hir;

    fn deref(&self) -> &Self::Target {
        self.hir
    }
}

impl<'hir> Thir<'hir> {
    pub fn new(hir: &'hir Hir, types: HashMap<TypeVarId, Type>) -> Self {
        Self { hir, types }
    }

    pub fn type_of(&self, id: impl Into<TypeVarId>) -> &Type {
        &self.types[&id.into()]
    }
}
