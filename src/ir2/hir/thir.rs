use std::collections::HashMap;

use crate::stages::ty::TypeVarId;

use super::*;

#[derive(Clone, Debug)]
pub struct Thir {
    pub functions: Vec<Function>,
    pub bindings: HashMap<BindingId, Type>,
    pub blocks: Vec<Block>,
    pub exprs: Vec<(Expr, Type)>,
}

impl Thir {
    pub fn new(hir: Hir, types: HashMap<TypeVarId, Type>) -> Self {
        Self {
            functions: hir.functions,
            bindings: hir
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
            blocks: hir.blocks,
            exprs: hir
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
