use std::collections::HashMap;

use crate::stages::ty::TypeVarId;

use super::*;

#[derive(Clone, Debug)]
pub struct Thir {
    pub functions: Vec<Function>,
    pub binding_to_string: HashMap<BindingId, StringId>,
}

impl Thir {
    pub fn new(hir: Hir, types: HashMap<FunctionId, HashMap<TypeVarId, Type>>) -> Self {
        Self {
            functions: hir
                .functions
                .into_iter()
                .enumerate()
                .map(|(id, function)| Function::from_hir(function, &types[&FunctionId::new(id)]))
                .collect(),
            binding_to_string: hir.binding_to_string,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Function {
    pub binding: BindingId,
    pub parameters: Vec<(BindingId, Type)>,
    pub return_ty: Type,
    pub entry: BlockId,

    pub bindings: HashMap<BindingId, Type>,
    pub blocks: Vec<Block>,
    pub exprs: Vec<(Expr, Type)>,
}

impl Function {
    fn from_hir(function: super::Function, types: &HashMap<TypeVarId, Type>) -> Self {
        Self {
            binding: function.binding,
            parameters: function.parameters,
            return_ty: function.return_ty,
            entry: function.entry,

            bindings: function
                .bindings
                .into_iter()
                .map(|(binding, ty)| {
                    (
                        binding,
                        match ty {
                            DeclarationTy::Type(ty) => ty,
                            DeclarationTy::Inferred(expr_id) => types[&expr_id.into()].clone(),
                        },
                    )
                })
                .collect(),
            blocks: function.blocks,
            exprs: function
                .exprs
                .into_iter()
                .enumerate()
                .map(|(id, expr)| (expr, types[&ExprId::new(id).into()].clone()))
                .collect(),
        }
    }

    pub fn get_full_expr(&self, expr: ExprId) -> &(Expr, Type) {
        &self.exprs[expr.0]
    }

    pub fn get_expr(&self, expr: ExprId) -> &Expr {
        &self.get_full_expr(expr).0
    }

    pub fn get_expr_ty(&self, expr: ExprId) -> &Type {
        &self.get_full_expr(expr).1
    }

    pub fn get_block(&self, block: BlockId) -> &Block {
        &self.blocks[block.0]
    }
}
