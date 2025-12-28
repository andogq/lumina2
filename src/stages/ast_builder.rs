use crate::prelude::*;

use ast::*;

pub(crate) struct AstBuilder<'cst> {
    cst: &'cst cst::Program,
    ast: Ast,
}

impl<'cst> AstBuilder<'cst> {
    pub fn new(cst: &'cst cst::Program) -> Self {
        Self {
            cst,
            ast: Ast::new(),
        }
    }

    pub fn build(mut self, ctx: &mut Ctx) -> Ast {
        for item in &self.cst.items {
            self.lower_item(ctx, item);
        }

        self.ast
    }

    fn lower_item(&mut self, ctx: &mut Ctx, item: &cst::Item) {
        match item {
            cst::Item::FunctionDeclaration(function_declaration) => {
                self.lower_function_declaration(ctx, function_declaration);
            }
        }
    }

    fn lower_function_declaration(
        &mut self,
        ctx: &mut Ctx,
        function_declaration: &cst::FunctionDeclaration,
    ) -> FunctionId {
        let function_declaration = FunctionDeclaration {
            name: ctx.strings.intern(&function_declaration.name.0),
            params: function_declaration
                .params
                .iter_items()
                .map(|param| FunctionParameter {
                    name: ctx.strings.intern(&param.name.0),
                    ty: ctx.strings.intern(&param.ty.0),
                })
                .collect(),
            return_ty: function_declaration
                .return_ty
                .as_ref()
                .map(|ty| ctx.strings.intern(&ty.ty.0)),
            body: self.lower_block(ctx, &function_declaration.body),
        };
        self.ast.function_declarations.insert(function_declaration)
    }

    fn lower_block(&mut self, ctx: &mut Ctx, block: &cst::Block) -> BlockId {
        let mut statements = Vec::with_capacity(block.statements.len());
        let mut expression = None;

        for (i, statement) in block.statements.iter().enumerate() {
            let is_last = i == block.statements.len() - 1;

            match statement {
                cst::Statement::Let(let_statement) => {
                    let value = self.lower_expr(ctx, &let_statement.value);

                    statements.push(
                        self.ast.statements.insert(
                            LetStatement {
                                variable: ctx.strings.intern(&let_statement.variable.0),
                                value,
                            }
                            .into(),
                        ),
                    )
                }
                cst::Statement::Return(return_statement) => {
                    let expr = self.lower_expr(ctx, &return_statement.value);
                    statements.push(self.ast.statements.insert(ReturnStatement { expr }.into()))
                }
                cst::Statement::Expr(expr_statement) => {
                    let expr = self.lower_expr(ctx, &expr_statement.expr);

                    if is_last && expr_statement.tok_semicolon.is_none() {
                        expression = Some(expr);
                    } else {
                        statements.push(self.ast.statements.insert(ExprStatement { expr }.into()));
                    }
                }
            }
        }

        self.ast.blocks.insert(Block {
            statements,
            expression,
        })
    }

    pub fn lower_expr(&mut self, ctx: &mut Ctx, expr: &cst::Expr) -> ExprId {
        let expr = match expr {
            cst::Expr::Assign(assign) => self.lower_assign(ctx, assign).into(),
            cst::Expr::Binary(binary) => self.lower_binary(ctx, binary).into(),
            cst::Expr::Unary(unary) => self.lower_unary(ctx, unary).into(),
            cst::Expr::If(if_expr) => self.lower_if(ctx, if_expr).into(),
            cst::Expr::Literal(literal) => self.lower_literal(ctx, literal).into(),
            cst::Expr::Paren(paren) => return self.lower_expr(ctx, &paren.expr),
            cst::Expr::Call(call) => self.lower_call(ctx, call).into(),
            cst::Expr::Block(block) => self.lower_block(ctx, block).into(),
            cst::Expr::Variable(variable) => self.lower_variable(ctx, variable).into(),
        };

        self.ast.expressions.insert(expr)
    }

    fn lower_assign(&mut self, ctx: &mut Ctx, assign: &cst::Assign) -> Assign {
        Assign {
            variable: self.lower_expr(ctx, &assign.assignee),
            value: self.lower_expr(ctx, &assign.value),
        }
    }

    fn lower_binary(&mut self, ctx: &mut Ctx, binary: &cst::Binary) -> Binary {
        Binary {
            lhs: self.lower_expr(ctx, &binary.lhs),
            op: binary.op.clone(),
            rhs: self.lower_expr(ctx, &binary.rhs),
        }
    }

    fn lower_unary(&mut self, ctx: &mut Ctx, unary: &cst::Unary) -> Unary {
        Unary {
            op: unary.op.clone(),
            value: self.lower_expr(ctx, &unary.value),
        }
    }

    fn lower_if(&mut self, ctx: &mut Ctx, if_expr: &cst::If) -> If {
        let mut conditions = Vec::new();

        let otherwise = {
            let mut if_expr = if_expr;
            loop {
                conditions.push((
                    self.lower_expr(ctx, &if_expr.condition),
                    self.lower_block(ctx, &if_expr.then),
                ));

                let Some(trailer) = &if_expr.trailer else {
                    break None;
                };
                match &trailer.if_or_block {
                    cst::IfOrBlock::If(inner) => if_expr = inner,
                    cst::IfOrBlock::Block(block) => {
                        break Some(block);
                    }
                }
            }
        };

        let otherwise = otherwise.map(|block| self.lower_block(ctx, block));

        If {
            conditions,
            otherwise,
        }
    }

    fn lower_literal(&mut self, _ctx: &mut Ctx, literal: &cst::Literal) -> Literal {
        match literal {
            cst::Literal::Integer(integer_literal) => Literal::Integer(integer_literal.as_usize()),
            cst::Literal::Boolean(boolean_literal) => Literal::Boolean(boolean_literal.as_bool()),
        }
    }

    fn lower_call(&mut self, ctx: &mut Ctx, call: &cst::Call) -> Call {
        Call {
            callee: self.lower_expr(ctx, &call.callee),
            arguments: call
                .arguments
                .iter_items()
                .map(|arg| self.lower_expr(ctx, arg))
                .collect(),
        }
    }

    fn lower_variable(&mut self, ctx: &mut Ctx, variable: &cst::Variable) -> Variable {
        Variable {
            variable: ctx.strings.intern(&variable.variable.0),
        }
    }
}

pub fn build_ast(ctx: &mut Ctx, cst: &cst::Program) -> Ast {
    AstBuilder::new(cst).build(ctx)
}

#[cfg(test)]
mod test {
    use crate::stages::parse::Parse;

    use super::*;

    #[fixture]
    fn builder() -> AstBuilder<'static> {
        static CST: cst::Program = cst::Program::new();
        AstBuilder::new(&CST)
    }

    #[fixture]
    fn ctx() -> Ctx {
        Ctx::default()
    }

    fn lexer(source: &'static str) -> Lexer<'static> {
        Lexer::new(source)
    }

    fn parse<T>(source: &'static str) -> T
    where
        T: Parse,
    {
        T::parse(&mut lexer(source))
    }

    fn parse_expr<T>(source: &'static str) -> T
    where
        T: TryFrom<cst::Expr>,
        T::Error: Debug,
    {
        parse::<cst::Expr>(source).try_into().unwrap()
    }

    #[rstest]
    #[case("assign_simple", "a = 1 + 2")]
    fn lower_assign(
        #[case] name: &str,
        mut ctx: Ctx,
        mut builder: AstBuilder<'static>,
        #[case] source: &'static str,
    ) {
        assert_debug_snapshot!(
            name,
            builder.lower_assign(&mut ctx, &parse_expr(source)),
            source
        );
    }

    #[rstest]
    #[case("binary_arithmetic", "1 + 2")]
    #[case("binary_logical", "true && false")]
    #[case("binary_binary", "5 & 2")]
    fn lower_binary(
        #[case] name: &str,
        mut ctx: Ctx,
        mut builder: AstBuilder<'static>,
        #[case] source: &'static str,
    ) {
        assert_debug_snapshot!(
            name,
            builder.lower_binary(&mut ctx, &parse_expr(source)),
            source
        );
    }

    #[rstest]
    #[case("unary_minus", "-1")]
    #[case("unary_not", "!true")]
    fn lower_unary(
        #[case] name: &str,
        mut ctx: Ctx,
        mut builder: AstBuilder<'static>,
        #[case] source: &'static str,
    ) {
        assert_debug_snapshot!(
            name,
            builder.lower_unary(&mut ctx, &parse_expr(source)),
            source
        );
    }

    #[rstest]
    #[case("if_simple", "if condition { then }")]
    #[case("if_else", "if condition { then } else { otherwise }")]
    #[case("if_else_if", "if condition { then } else if thing { then_2 }")]
    #[case(
        "if_else_if_else",
        "if condition { then } else if thing { then_2 } else { otherwise }"
    )]
    fn lower_if(
        #[case] name: &str,
        mut ctx: Ctx,
        mut builder: AstBuilder<'static>,
        #[case] source: &'static str,
    ) {
        assert_debug_snapshot!(
            name,
            builder.lower_if(&mut ctx, &parse_expr(source)),
            source
        );
    }

    #[rstest]
    #[case("literal_bool", "true")]
    #[case("literal_int", "123")]
    fn lower_literal(
        #[case] name: &str,
        mut ctx: Ctx,
        mut builder: AstBuilder<'static>,
        #[case] source: &'static str,
    ) {
        assert_debug_snapshot!(
            name,
            builder.lower_literal(&mut ctx, &parse_expr(source)),
            source
        );
    }

    #[rstest]
    #[case("call_simple", "some_ident()")]
    #[case("call_args", "some_ident(1, something, true)")]
    fn lower_call(
        #[case] name: &str,
        mut ctx: Ctx,
        mut builder: AstBuilder<'static>,
        #[case] source: &'static str,
    ) {
        assert_debug_snapshot!(
            name,
            builder.lower_call(&mut ctx, &parse_expr(source)),
            source
        );
    }

    #[rstest]
    #[case("variable_simple", "some_ident")]
    fn lower_variable(
        #[case] name: &str,
        mut ctx: Ctx,
        mut builder: AstBuilder<'static>,
        #[case] source: &'static str,
    ) {
        assert_debug_snapshot!(
            name,
            builder.lower_variable(&mut ctx, &parse_expr(source)),
            source
        );
    }
}
