use super::*;

pub trait HirVisitor {
    fn visit_function_declaration(
        &mut self,
        params: Vec<(BindingId, Type)>,
        return_ty: Type,
        body: &Block,
    ) {
    }
    fn visit_variable_declaration(&mut self, binding: BindingId, ty: DeclarationTy) {}
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
}

impl Hir {
    pub fn visit(&self, visitor: &mut impl HirVisitor) {
        self.functions.iter().for_each(|decl| {
            visitor.visit_function_declaration(
                decl.parameters.clone(),
                decl.return_ty.clone(),
                self.get_block(decl.entry),
            );
        });

        self.blocks
            .iter()
            .flat_map(|block| block.statements.iter())
            .for_each(|statement| match statement {
                Statement::Declare(declare_statement) => visitor.visit_variable_declaration(
                    declare_statement.binding,
                    declare_statement.ty.clone(),
                ),
                Statement::Return(return_statement) => {}
                Statement::Expr(expr_statement) => {}
            });

        self.exprs.iter().enumerate().for_each(|(id, expr)| {
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
                        .map(|(value, block)| (value, self.get_block(*block)))
                        .collect(),
                    switch.default.as_ref().map(|block| self.get_block(*block)),
                ),
                Expr::Literal(literal) => visitor.visit_literal(id, literal),
                Expr::Call(call) => visitor.visit_call(id, call),
                Expr::Block(block_id) => visitor.visit_block(id, self.get_block(*block_id)),
                Expr::Variable(variable) => visitor.visit_variable(id, variable.binding),
            }
        });
    }
}
