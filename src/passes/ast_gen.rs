use crate::prelude::*;

use ast::*;

pub struct AstGen<'ctx> {
    ctx: &'ctx mut Ctx,

    ast: Ast,
}

impl<'ctx, 'cst> Pass<'ctx, 'cst> for AstGen<'ctx> {
    type Input = cst::Program;
    type Output = Ast;

    fn run(ctx: &'ctx mut Ctx, cst: &'cst Self::Input) -> PassResult<Self::Output> {
        let mut ast_gen = Self::new(ctx);

        for item in &cst.items {
            match item {
                cst::Item::FunctionDeclaration(function_declaration) => {
                    ast_gen.lower_function(function_declaration)
                }
            }
        }

        PassResult::Ok(PassSuccess::Ok(ast_gen.ast))
    }
}

impl<'ctx> AstGen<'ctx> {
    fn new(ctx: &'ctx mut Ctx) -> Self {
        Self {
            ctx,
            ast: Ast::new(),
        }
    }

    fn lower_function(&mut self, function: &cst::FunctionDeclaration) {
        let function_declaration = FunctionDeclaration {
            name: self.ctx.strings.intern(&function.name.0),
            params: function
                .params
                .iter_items()
                .map(|param| FunctionParameter {
                    name: self.ctx.strings.intern(&param.name.0),
                    ty: self.ctx.strings.intern(&param.ty.0),
                })
                .collect(),
            return_ty: function
                .return_ty
                .as_ref()
                .map(|ty| self.ctx.strings.intern(&ty.ty.0)),
            body: self.lower_block(&function.body),
        };
        self.ast.function_declarations.insert(function_declaration);
    }

    fn lower_block(&mut self, block: &cst::Block) -> BlockId {
        let mut statements = Vec::with_capacity(block.statements.len());
        let mut expression = None;

        for (i, statement) in block.statements.iter().enumerate() {
            let is_last = i == block.statements.len() - 1;

            match statement {
                cst::Statement::Let(cst::LetStatement {
                    variable, value, ..
                }) => {
                    let value = self.lower_expr(value);

                    statements.push(
                        self.ast.statements.insert(
                            LetStatement {
                                variable: self.ctx.strings.intern(&variable.0),
                                value,
                            }
                            .into(),
                        ),
                    )
                }
                cst::Statement::Return(cst::ReturnStatement { value, .. }) => {
                    let expr = self.lower_expr(value);
                    statements.push(self.ast.statements.insert(ReturnStatement { expr }.into()))
                }
                cst::Statement::Break(cst::BreakStatement { value, .. }) => {
                    let expr = value.as_ref().map(|expr| self.lower_expr(expr));
                    statements.push(self.ast.statements.insert(BreakStatement { expr }.into()))
                }
                cst::Statement::Expr(cst::ExprStatement {
                    expr,
                    tok_semicolon,
                }) => {
                    let expr = self.lower_expr(expr);

                    if is_last && tok_semicolon.is_none() {
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

    fn lower_expr(&mut self, expr: &cst::Expr) -> ExprId {
        let expr = match expr {
            cst::Expr::Assign(cst::Assign {
                assignee, value, ..
            }) => Assign {
                variable: self.lower_expr(assignee),
                value: self.lower_expr(value),
            }
            .into(),
            cst::Expr::Binary(cst::Binary { lhs, op, rhs }) => Binary {
                lhs: self.lower_expr(lhs),
                op: op.clone(),
                rhs: self.lower_expr(rhs),
            }
            .into(),
            cst::Expr::Unary(cst::Unary { op, value }) => Unary {
                op: op.clone(),
                value: self.lower_expr(value),
            }
            .into(),
            cst::Expr::If(if_expr) => {
                let mut conditions = Vec::new();

                let otherwise = {
                    let mut if_expr = if_expr;
                    loop {
                        conditions.push((
                            self.lower_expr(&if_expr.condition),
                            self.lower_block(&if_expr.then),
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

                let otherwise = otherwise.map(|block| self.lower_block(block));

                If {
                    conditions,
                    otherwise,
                }
                .into()
            }
            cst::Expr::Loop(cst::Loop { body, .. }) => Loop {
                body: self.lower_block(body),
            }
            .into(),
            cst::Expr::Literal(literal) => match literal {
                cst::Literal::Integer(integer_literal) => {
                    Literal::Integer(integer_literal.as_usize())
                }
                cst::Literal::Boolean(boolean_literal) => {
                    Literal::Boolean(boolean_literal.as_bool())
                }
            }
            .into(),
            cst::Expr::Paren(cst::Paren { expr, .. }) => return self.lower_expr(expr),
            cst::Expr::Call(cst::Call {
                callee, arguments, ..
            }) => Call {
                callee: self.lower_expr(callee),
                arguments: arguments
                    .iter_items()
                    .map(|arg| self.lower_expr(arg))
                    .collect(),
            }
            .into(),
            cst::Expr::Block(block) => self.lower_block(block).into(),
            cst::Expr::Variable(cst::Variable { variable }) => Variable {
                variable: self.ctx.strings.intern(&variable.0),
            }
            .into(),
        };

        self.ast.expressions.insert(expr)
    }
}

#[cfg(test)]
mod test {
    use crate::stages::parse::Parse;

    use super::*;

    #[fixture]
    fn ctx() -> Ctx {
        Ctx::default()
    }

    fn parse<T>(source: &'static str) -> T
    where
        T: Parse,
    {
        T::parse(&mut Lexer::new(source))
    }

    #[rstest]
    #[case("assign_simple", "a = 1 + 2")]
    #[case("binary_arithmetic", "1 + 2")]
    #[case("binary_logical", "true && false")]
    #[case("binary_binary", "5 & 2")]
    #[case("unary_minus", "-1")]
    #[case("unary_not", "!true")]
    #[case("if_simple", "if condition { then }")]
    #[case("if_else", "if condition { then } else { otherwise }")]
    #[case("if_else_if", "if condition { then } else if thing { then_2 }")]
    #[case(
        "if_else_if_else",
        "if condition { then } else if thing { then_2 } else { otherwise }"
    )]
    #[case("literal_bool", "true")]
    #[case("literal_int", "123")]
    #[case("call_simple", "some_ident()")]
    #[case("call_args", "some_ident(1, something, true)")]
    #[case("variable_simple", "some_ident")]
    fn lower_expr(#[case] name: &str, mut ctx: Ctx, #[case] source: &'static str) {
        let mut pass = AstGen::new(&mut ctx);
        let expr_id = pass.lower_expr(&parse::<cst::Expr>(source));
        assert_debug_snapshot!(name, pass.ast[expr_id], source);
    }
}
