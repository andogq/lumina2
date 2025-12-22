use super::*;

pub trait HirVisitor {
    type FunctionVisitor<'a>: HirFunctionVisitor
    where
        Self: 'a;

    fn visit_function_declaration(
        &mut self,
        id: FunctionId,
        binding: BindingId,
        params: Vec<(BindingId, Type)>,
        return_ty: Type,
        blocdk: &Block,
    ) {
    }

    fn visit_function(
        &mut self,
        id: FunctionId,
        visit: impl FnOnce(&mut Self::FunctionVisitor<'_>),
    ) {
    }
}

pub trait HirFunctionVisitor {
    fn visit_variable_declaration(&mut self, binding: BindingId, ty: DeclarationTy) {}
    fn visit_return(&mut self, value: ExprId, return_ty: Type) {}
    fn visit_assign(&mut self, id: ExprId, assign: &Assign) {}
    fn visit_binary(&mut self, id: ExprId, binary: &Binary) {}
    fn visit_unary(&mut self, id: ExprId, unary: &Unary) {}
    fn visit_switch(
        &mut self,
        id: ExprId,
        discriminator: ExprId,
        branches: Vec<(&Literal, &Block)>,
        default: Option<&Block>,
    ) {
    }
    fn visit_literal(&mut self, id: ExprId, literal: &Literal) {}
    fn visit_call(&mut self, id: ExprId, call: &Call) {}
    fn visit_block(&mut self, id: ExprId, block: &Block) {}
    fn visit_variable(&mut self, id: ExprId, variable: BindingId) {}
    fn visit_unreachable(&mut self, id: ExprId) {}
}

impl Hir {
    pub fn visit(&self, visitor: &mut impl HirVisitor) {
        // Forward-declare all functions.
        for (id, decl) in self.functions.iter().enumerate() {
            visitor.visit_function_declaration(
                FunctionId::new(id),
                decl.binding,
                decl.parameters.clone(),
                decl.return_ty.clone(),
                decl.get_block(decl.entry),
            );
        }

        // Properly visit all functions
        for (id, decl) in self.functions.iter().enumerate() {
            visitor.visit_function(FunctionId::new(id), |visitor| {
                // Visit each statement.
                decl.blocks
                    .iter()
                    .flat_map(|block| block.statements.iter())
                    .for_each(|statement| match statement {
                        Statement::Declare(declare_statement) => visitor
                            .visit_variable_declaration(
                                declare_statement.binding,
                                declare_statement.ty.clone(),
                            ),
                        Statement::Return(return_statement) => visitor.visit_return(
                            return_statement.expr,
                            // HACK: This should be the return type of each individual function. Currently
                            // not possible as blocks aren't linked back to their function.
                            Type::U8,
                        ),
                        // Exprs will be handled separately.
                        Statement::Expr(_) => {}
                    });

                decl.exprs.iter().enumerate().for_each(|(id, expr)| {
                    let id = ExprId::new(id);

                    match expr {
                        Expr::Assign(assign) => visitor.visit_assign(id, assign),
                        Expr::Binary(binary) => visitor.visit_binary(id, binary),
                        Expr::Unary(unary) => visitor.visit_unary(id, unary),
                        Expr::Switch(switch) => visitor.visit_switch(
                            id,
                            switch.discriminator,
                            switch
                                .branches
                                .iter()
                                .map(|(value, block)| (value, decl.get_block(*block)))
                                .collect(),
                            switch.default.as_ref().map(|block| decl.get_block(*block)),
                        ),
                        Expr::Literal(literal) => visitor.visit_literal(id, literal),
                        Expr::Call(call) => visitor.visit_call(id, call),
                        Expr::Block(block_id) => visitor.visit_block(id, decl.get_block(*block_id)),
                        Expr::Variable(variable) => visitor.visit_variable(id, variable.binding),
                        Expr::Unreachable => visitor.visit_unreachable(id),
                    }
                });
            });
        }
    }
}
