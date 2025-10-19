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
            cst::Expr::Assign(assign) => self.lower_assign(assign).into(),
            cst::Expr::Binary(binary) => self.lower_binary(binary).into(),
            cst::Expr::Unary(unary) => self.lower_unary(unary).into(),
            cst::Expr::If(if_expr) => self.lower_if(if_expr).into(),
            cst::Expr::Literal(literal) => self.lower_literal(literal).into(),
            cst::Expr::Paren(paren) => return self.lower_expr(&paren.expr),
            cst::Expr::Call(call) => self.lower_call(call).into(),
            cst::Expr::Block(block) => self.lower_block(block).into(),
            cst::Expr::Variable(variable) => self.lower_variable(variable).into(),
        };

        let id = ExprId::new(self.ast.expressions.len());
        self.ast.expressions.push(expr);
        id
    }

    fn lower_assign(&mut self, assign: &cst::Assign) -> Assign {
        Assign {
            variable: self.lower_expr(&assign.assignee),
            value: self.lower_expr(&assign.value),
        }
    }

    fn lower_binary(&mut self, binary: &cst::Binary) -> Binary {
        Binary {
            lhs: self.lower_expr(&binary.lhs),
            op: binary.op.clone(),
            rhs: self.lower_expr(&binary.rhs),
        }
    }

    fn lower_unary(&mut self, unary: &cst::Unary) -> Unary {
        Unary {
            op: unary.op.clone(),
            value: self.lower_expr(&unary.value),
        }
    }

    fn lower_if(&mut self, if_expr: &cst::If) -> If {
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
    }

    fn lower_literal(&mut self, literal: &cst::Literal) -> Literal {
        match literal {
            cst::Literal::Integer(integer_literal) => Literal::Integer(integer_literal.as_usize()),
            cst::Literal::Boolean(boolean_literal) => Literal::Boolean(boolean_literal.as_bool()),
        }
    }

    fn lower_call(&mut self, call: &cst::Call) -> Call {
        Call {
            callee: self.lower_expr(&call.callee),
            arguments: call
                .arguments
                .iter_items()
                .map(|arg| self.lower_expr(arg))
                .collect(),
        }
    }

    fn lower_variable(&mut self, variable: &cst::Variable) -> Variable {
        Variable {
            variable: self.intern(&variable.variable),
        }
    }

    fn intern(&mut self, ident: &tok::Ident) -> StringId {
        self.ast.strings.intern(&ident.0)
    }
}

pub fn build_ast(cst: &cst::Program) -> Ast {
    AstBuilder::new(cst).build()
}
