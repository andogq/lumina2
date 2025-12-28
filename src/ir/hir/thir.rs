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

    pub fn binding_type(&self, function: FunctionId, binding: BindingId) -> &Type {
        match &self[function].bindings[&binding] {
            DeclarationTy::Type(ty) => ty,
            DeclarationTy::Inferred(expr) => self.type_of(*expr),
        }
    }
}

impl Deref for Thir {
    type Target = Hir;

    fn deref(&self) -> &Self::Target {
        &self.hir
    }
}
