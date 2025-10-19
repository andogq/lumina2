use crate::{
    ir2::{ast::*, cst},
    lex::tok,
};

struct AstBuilder<'cst> {
    cst: &'cst cst::Program,
    ast: Ast,
}

impl<'cst> AstBuilder<'cst> {
    pub fn new(cst: &'cst cst::Program) -> Self {
        Self {
            cst,
            ast: Ast {
                function_declarations: Vec::new(),
                blocks: Vec::new(),
                expressions: Vec::new(),
                strings: StringPool::new(),
            },
        }
    }

    pub fn build(mut self) -> Ast {
        for item in &self.cst.items {
            self.lower_item(item);
        }

        self.ast
    }

    fn lower_item(&mut self, item: &cst::Item) {
        match item {
            cst::Item::FunctionDeclaration(function_declaration) => {
                self.lower_function_declaration(function_declaration);
            }
        }
    }

    fn lower_function_declaration(&mut self, function_declaration: &cst::FunctionDeclaration) {
        let function_declaration = FunctionDeclaration {
            name: self.intern(&function_declaration.name),
            params: function_declaration
                .params
                .iter_items()
                .map(|param| FunctionParameter {
                    name: self.intern(&param.name),
                    ty: self.intern(&param.ty),
                })
                .collect(),
            return_ty: function_declaration
                .return_ty
                .as_ref()
                .map(|ty| self.intern(&ty.ty)),
            body: self.lower_block(&function_declaration.body),
        };
        self.ast.function_declarations.push(function_declaration);
    }

    fn lower_block(&mut self, block: &cst::Block) -> BlockId {
        let mut statements = Vec::new();
        let mut expression = None;

        for (i, statement) in block.statements.iter().enumerate() {
            let is_last = i == block.statements.len() - 1;

            match statement {
                cst::Statement::Let(let_statement) => statements.push(
                    LetStatement {
                        variable: self.intern(&let_statement.variable),
                        value: self.lower_expr(&let_statement.value),
                    }
                    .into(),
                ),
                cst::Statement::Return(return_statement) => statements.push(
                    ReturnStatement {
                        expr: self.lower_expr(&return_statement.value),
                    }
                    .into(),
                ),
                cst::Statement::Expr(expr_statement) => {
                    let expr = self.lower_expr(&expr_statement.expr);

                    if is_last && expr_statement.tok_semicolon.is_none() {
                        expression = Some(expr);
                    } else {
                        statements.push(ExprStatement { expr }.into());
                    }
                }
            }
        }

        let id = BlockId::new(self.ast.blocks.len());
        self.ast.blocks.push(Block {
            statements,
            expression,
        });
        id
    }

    fn lower_expr(&mut self, expr: &cst::Expr) -> ExprId {
        let expr = match expr {
            cst::Expr::Assign(assign) => Expr::Assign(Assign {
                variable: self.lower_expr(&assign.assignee),
                value: self.lower_expr(&assign.value),
            }),
            cst::Expr::Binary(binary) => Expr::Binary(Binary {
                lhs: self.lower_expr(&binary.lhs),
                op: binary.op.clone(),
                rhs: self.lower_expr(&binary.rhs),
            }),
            cst::Expr::Unary(unary) => Expr::Unary(Unary {
                op: unary.op.clone(),
                value: self.lower_expr(&unary.value),
            }),
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

                Expr::If(If {
                    conditions,
                    otherwise,
                })
            }
            cst::Expr::Literal(literal) => Expr::Literal(match literal {
                cst::Literal::Integer(integer_literal) => {
                    Literal::Integer(integer_literal.as_usize())
                }
                cst::Literal::Boolean(boolean_literal) => {
                    Literal::Boolean(boolean_literal.as_bool())
                }
            }),
            cst::Expr::Paren(paren) => return self.lower_expr(&paren.expr),
            cst::Expr::Call(call) => Expr::Call(Call {
                callee: self.lower_expr(&call.callee),
                arguments: call
                    .arguments
                    .iter_items()
                    .map(|arg| self.lower_expr(arg))
                    .collect(),
            }),
            cst::Expr::Block(block) => Expr::Block(self.lower_block(block)),
            cst::Expr::Variable(variable) => Expr::Variable(Variable {
                variable: self.intern(&variable.variable),
            }),
        };

        let id = ExprId::new(self.ast.expressions.len());
        self.ast.expressions.push(expr);
        id
    }

    fn intern(&mut self, ident: &tok::Ident) -> StringId {
        self.ast.strings.intern(&ident.0)
    }
}

pub fn build_ast(cst: &cst::Program) -> Ast {
    AstBuilder::new(cst).build()
}
