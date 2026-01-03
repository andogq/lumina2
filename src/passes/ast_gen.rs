use crate::prelude::*;

use ast::*;

pub struct AstGen<'ctx> {
    ctx: &'ctx mut Ctx,

    pub ast: Ast,
}

impl<'ctx, 'cst> Pass<'ctx, 'cst> for AstGen<'ctx> {
    type Input = cst::Program;
    type Output = Ast;
    type Extra = ();

    fn run(ctx: &'ctx mut Ctx, cst: &'cst Self::Input, _extra: ()) -> PassResult<Self::Output> {
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
    pub fn new(ctx: &'ctx mut Ctx) -> Self {
        Self {
            ctx,
            ast: Ast::new(),
        }
    }

    fn lower_function(&mut self, function: &cst::FunctionDeclaration) {
        let function_declaration = FunctionDeclaration {
            name: self.ctx.strings.intern(&function.name.0),
            parameters: function
                .parameters
                .iter_items()
                .map(|parameter| FunctionParameter {
                    name: self.ctx.strings.intern(&parameter.name.0),
                    ty: self.ctx.strings.intern(&parameter.ty.0),
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
        let mut block_expression = None;

        for (i, statement) in block.statements.iter().enumerate() {
            let is_last = i == block.statements.len() - 1;

            match statement {
                cst::Statement::Let(cst::LetStatement {
                    variable, value, ..
                }) => {
                    let value = self.lower_expression(value);

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
                    let expression = self.lower_expression(value);
                    statements.push(
                        self.ast
                            .statements
                            .insert(ReturnStatement { expression }.into()),
                    )
                }
                cst::Statement::Break(cst::BreakStatement { value, .. }) => {
                    let expression = value
                        .as_ref()
                        .map(|expression| self.lower_expression(expression));
                    statements.push(
                        self.ast
                            .statements
                            .insert(BreakStatement { expression }.into()),
                    )
                }
                cst::Statement::Expression(cst::ExpressionStatement {
                    expression,
                    tok_semicolon,
                }) => {
                    let expression = self.lower_expression(expression);

                    if is_last && tok_semicolon.is_none() {
                        block_expression = Some(expression);
                    } else {
                        statements.push(
                            self.ast
                                .statements
                                .insert(ExpressionStatement { expression }.into()),
                        );
                    }
                }
            }
        }

        self.ast.blocks.insert(Block {
            statements,
            expression: block_expression,
        })
    }

    pub fn lower_expression(&mut self, expression: &cst::Expression) -> ExpressionId {
        let expression = match expression {
            cst::Expression::Assign(cst::Assign {
                assignee, value, ..
            }) => Assign {
                variable: self.lower_expression(assignee),
                value: self.lower_expression(value),
            }
            .into(),
            cst::Expression::Binary(cst::Binary {
                lhs,
                operation,
                rhs,
            }) => Binary {
                lhs: self.lower_expression(lhs),
                operation: operation.into(),
                rhs: self.lower_expression(rhs),
            }
            .into(),
            cst::Expression::Unary(cst::Unary { operation, value }) => Unary {
                operation: operation.into(),
                value: self.lower_expression(value),
            }
            .into(),
            cst::Expression::If(if_expression) => {
                let mut conditions = Vec::new();

                let otherwise = {
                    let mut if_expression = if_expression;
                    loop {
                        conditions.push((
                            self.lower_expression(&if_expression.condition),
                            self.lower_block(&if_expression.then),
                        ));

                        let Some(trailer) = &if_expression.trailer else {
                            break None;
                        };
                        match &trailer.if_or_block {
                            cst::IfOrBlock::If(inner) => if_expression = inner,
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
            cst::Expression::Loop(cst::Loop { body, .. }) => Loop {
                body: self.lower_block(body),
            }
            .into(),
            cst::Expression::Literal(literal) => match literal {
                cst::Literal::Integer(integer_literal) => {
                    Literal::Integer(integer_literal.as_usize())
                }
                cst::Literal::Boolean(boolean_literal) => {
                    Literal::Boolean(boolean_literal.as_bool())
                }
                cst::Literal::Unit(_) => Literal::Unit,
            }
            .into(),
            cst::Expression::Parenthesis(cst::Parenthesis { expression, .. }) => {
                return self.lower_expression(expression);
            }
            cst::Expression::Call(cst::Call {
                callee, arguments, ..
            }) => Call {
                callee: self.lower_expression(callee),
                arguments: arguments
                    .iter_items()
                    .map(|argument| self.lower_expression(argument))
                    .collect(),
            }
            .into(),
            cst::Expression::Block(block) => self.lower_block(block).into(),
            cst::Expression::Variable(cst::Variable { variable }) => Variable {
                variable: self.ctx.strings.intern(&variable.0),
            }
            .into(),
        };

        self.ast.expressions.insert(expression)
    }
}

#[cfg(test)]
mod test {
    use crate::passes::cst_gen::Parse;

    use super::*;

    #[fixture]
    fn ctx() -> Ctx {
        Ctx::new()
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
    #[case("literal_integer", "123")]
    #[case("call_simple", "some_ident()")]
    #[case("call_arguments", "some_ident(1, something, true)")]
    #[case("variable_simple", "some_ident")]
    fn lower_expression(#[case] name: &str, mut ctx: Ctx, #[case] source: &'static str) {
        let mut pass = AstGen::new(&mut ctx);
        let expression_id = pass.lower_expression(&parse::<cst::Expression>(source));
        assert_debug_snapshot!(name, pass.ast[expression_id], source);
    }
}
