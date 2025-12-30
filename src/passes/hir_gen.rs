use crate::prelude::*;

use hir::*;

/// Generator to lower the [`Ast`] into the [`Hir`].
///
/// This process will include:
///
/// - resolving [`StringId`]s into [`BindingId`]s
///
/// [`Ast`]: ast::Ast
pub struct HirGen<'ctx, 'ast> {
    /// Context used throughout this pass.
    ctx: &'ctx mut Ctx,
    /// AST that will be processed.
    ast: &'ast ast::Ast,
    /// HIR that is being generated.
    hir: Hir,
    /// Errors generated throughout this pass.
    errors: Vec<CErrorId>,
}

impl<'ctx, 'ast> Pass<'ctx, 'ast> for HirGen<'ctx, 'ast> {
    type Input = ast::Ast;
    type Output = Hir;

    fn run(ctx: &'ctx mut Ctx, ast: &'ast Self::Input) -> PassResult<Self::Output> {
        let mut hir_gen = Self::new(ctx, ast);

        // Lower each function.
        for function in ast.function_declarations.iter() {
            let _ = hir_gen.can_fail(|hir_gen| hir_gen.lower_function(function));
        }

        Ok(PassSuccess::new(hir_gen.hir, hir_gen.errors))
    }
}

impl<'ctx, 'ast> HirGen<'ctx, 'ast> {
    /// Create a new instance of the generator.
    pub fn new(ctx: &'ctx mut Ctx, ast: &'ast ast::Ast) -> Self {
        Self {
            ctx,
            ast,
            hir: Hir::default(),
            errors: Vec::new(),
        }
    }

    /// Lower the provided function.
    pub fn lower_function(&mut self, function: &ast::FunctionDeclaration) -> CResult<FunctionId> {
        // Add the function identifier to the global scope.
        let binding = self.ctx.scopes.declare_global(function.name);

        // Create a new scope for the function.
        let function_scope = self.ctx.scopes.nest_scope_global();

        // Process all of the parameters.
        let parameters = function
            .params
            .iter()
            .map(|param| {
                (
                    self.ctx.scopes.declare(function_scope, param.name),
                    self.ident_to_type(param.ty),
                )
            })
            .collect();

        // If no return type is provided, assume `()`.
        let return_ty = match function.return_ty {
            Some(return_ty) => self.ident_to_type(return_ty),
            None => Type::Unit,
        };

        // Lower the body of the function.
        let entry = self.lower_block(&self.ast[function.body], function_scope)?;

        Ok(self.hir.functions.insert(Function {
            binding,
            parameters,
            return_ty,
            entry,

            // TODO: Delete these.
            blocks: vec![],
            statements: vec![],
            expressions: vec![],
        }))
    }

    /// Lower a block, using the provided scope as the parent scope.
    pub fn lower_block(&mut self, block: &ast::Block, parent_scope: ScopeId) -> CResult<BlockId> {
        // Create a new scope for this block.
        let scope = self.ctx.scopes.nest_scope(parent_scope);

        let mut statements = Vec::new();

        for &statement_id in &block.statements {
            let statement = &self.ast[statement_id];

            match statement {
                // Statements are lowered into a declaration, followed by an assignment.
                ast::Statement::Let(ast::LetStatement { variable, value }) => {
                    // Create a new binding for the statement.
                    let binding = self.ctx.scopes.declare(scope, *variable);

                    // Lower the value.
                    let value = self.lower_expr(&self.ast[*value], scope)?;

                    // Add the declaration.
                    statements.push(self.hir.statements.insert(Statement::Declare(
                        DeclareStatement {
                            binding,
                            ty: DeclarationTy::Inferred(value),
                        },
                    )));

                    // Add the assignment.
                    statements.push({
                        let variable = self.hir.exprs.insert(Expr::Variable(Variable { binding }));
                        let assign_expr = self
                            .hir
                            .exprs
                            .insert(Expr::Assign(Assign { variable, value }));
                        self.hir
                            .statements
                            .insert(Statement::Expr(ExprStatement { expr: assign_expr }))
                    });
                }
                ast::Statement::Return(ast::ReturnStatement { expr }) => {
                    let expr = self.lower_expr(&self.ast[*expr], scope)?;
                    statements.push(
                        self.hir
                            .statements
                            .insert(Statement::Return(ReturnStatement { expr })),
                    );
                }
                ast::Statement::Break(ast::BreakStatement { expr }) => {
                    let expr = if let Some(expr) = expr {
                        self.lower_expr(&self.ast[*expr], scope)?
                    } else {
                        self.hir.exprs.insert(Expr::Literal(Literal::Unit))
                    };
                    statements.push(
                        self.hir
                            .statements
                            .insert(Statement::Break(BreakStatement { expr })),
                    )
                }
                ast::Statement::Expr(ast::ExprStatement { expr }) => {
                    let expr = self.lower_expr(&self.ast[*expr], scope)?;
                    statements.push(
                        self.hir
                            .statements
                            .insert(Statement::Expr(ExprStatement { expr })),
                    );
                }
            }
        }

        // Lower the final expression of the block, or fallback to `()` if there is no expression.
        let expr = if let Some(expr) = block.expression {
            self.lower_expr(&self.ast[expr], scope)?
        } else {
            self.hir.exprs.insert(Expr::Literal(Literal::Unit))
        };

        Ok(self.hir.blocks.insert(Block { statements, expr }))
    }

    /// Lower an expression within the provided scope.
    pub fn lower_expr(&mut self, expr: &ast::Expr, scope: ScopeId) -> CResult<ExprId> {
        let expr = match expr {
            ast::Expr::Assign(ast::Assign { variable, value }) => Assign {
                variable: self.lower_expr(&self.ast[*variable], scope)?,
                value: self.lower_expr(&self.ast[*value], scope)?,
            }
            .into(),
            ast::Expr::Binary(ast::Binary { lhs, op, rhs }) => Binary {
                lhs: self.lower_expr(&self.ast[*lhs], scope)?,
                op: op.clone(),
                rhs: self.lower_expr(&self.ast[*rhs], scope)?,
            }
            .into(),
            ast::Expr::Unary(ast::Unary { op, value }) => Unary {
                op: op.clone(),
                value: self.lower_expr(&self.ast[*value], scope)?,
            }
            .into(),
            ast::Expr::If(ast::If {
                conditions,
                otherwise,
            }) => {
                // Where the switch will be built.
                let mut switch: Option<Switch> = None;
                // Optional default expression to apply to end of switch statements.
                let mut default = otherwise
                    .map(|otherwise| {
                        Ok::<_, CError>(Expr::Block(self.lower_block(&self.ast[otherwise], scope)?))
                    })
                    .transpose()?;

                for (condition, block) in conditions.iter().rev() {
                    switch = Some(Switch {
                        discriminator: self.lower_expr(&self.ast[*condition], scope)?,
                        branches: vec![(
                            Literal::Boolean(true),
                            self.lower_block(&self.ast[*block], scope)?,
                        )],
                        // Try use the default expression.
                        default: default
                            .take()
                            // Otherwise continue building the switch statement.
                            .or_else(|| Some(switch.take()?.into()))
                            .map(|expr| {
                                let expr = self.hir.exprs.insert(expr);
                                self.hir.blocks.insert(Block {
                                    statements: Vec::new(),
                                    expr,
                                })
                            }),
                    });
                }

                switch.ok_or(HirGenError::IfMustHaveBlock)?.into()
            }
            ast::Expr::Loop(ast::Loop { body }) => Loop {
                body: self.lower_block(&self.ast[*body], scope)?,
            }
            .into(),
            ast::Expr::Literal(literal) => match literal {
                ast::Literal::Integer(value) => Literal::Integer(*value),
                ast::Literal::Boolean(value) => Literal::Boolean(*value),
                ast::Literal::Unit => Literal::Unit,
            }
            .into(),
            ast::Expr::Call(ast::Call { callee, arguments }) => Call {
                callee: self.lower_expr(&self.ast[*callee], scope)?,
                arguments: arguments
                    .iter()
                    .map(|argument| self.lower_expr(&self.ast[*argument], scope))
                    .collect::<Result<_, _>>()?,
            }
            .into(),
            ast::Expr::Block(block) => self.lower_block(&self.ast[*block], scope)?.into(),
            ast::Expr::Variable(ast::Variable { variable }) => Variable {
                binding: self.ctx.scopes.resolve(scope, *variable),
            }
            .into(),
        };

        Ok(self.hir.exprs.insert(expr))
    }

    /// Attempt to interpret an ident as a [`Type`].
    fn ident_to_type(&self, ident: StringId) -> Type {
        // HACK: This only handles built-in types.
        match self.ctx.strings.get(ident) {
            "u8" => Type::U8,
            "i8" => Type::I8,
            "bool" => Type::Boolean,
            ty => panic!("unknown type: {ty}"),
        }
    }

    /// Report the provided error, ensuring that it's tracked for later reporting.
    pub fn report(&mut self, error: impl Into<CError>) -> CErrorId {
        let id = self.ctx.errors.report(error.into());
        self.errors.push(id);
        id
    }

    /// Run the provided closure, marking and reporting any occurring errors as fatal.
    pub fn must_succeed<T>(&mut self, f: impl FnOnce(&mut Self) -> CResult<T>) -> PassResult<T> {
        match f(self) {
            Ok(value) => Ok(value.into()),
            Err(err) => Err(self.report(err.fatal())),
        }
    }

    /// Run the provided closure, reporting the error if any occurs.
    pub fn can_fail<T>(&mut self, f: impl FnOnce(&mut Self) -> CResult<T>) -> Result<T, CErrorId> {
        match f(self) {
            Ok(value) => Ok(value),
            Err(err) => Err(self.report(err)),
        }
    }
}

#[derive(Clone, Debug, thiserror::Error)]
pub enum HirGenError {
    #[error("an `if` expression must contain atleast one block.")]
    IfMustHaveBlock,
}

#[cfg(test)]
mod test {
    use super::*;

    #[fixture]
    #[once]
    fn sample_ast() -> ast::Ast {
        let mut ast = ast::Ast::new();
        ast.expressions = indexed_vec![
            ast::Expr::Variable(ast::Variable {
                variable: StringId::from_id(0),
            }),
            ast::Expr::Variable(ast::Variable {
                variable: StringId::from_id(1),
            }),
            ast::Expr::Variable(ast::Variable {
                variable: StringId::from_id(2),
            }),
        ];
        ast.statements = indexed_vec![ast::Statement::Expr(ast::ExprStatement {
            expr: ast::ExprId::from_id(0),
        })];
        ast.blocks = indexed_vec![
            ast::Block {
                statements: Vec::new(),
                expression: None
            },
            ast::Block {
                statements: Vec::new(),
                expression: None
            },
            ast::Block {
                statements: Vec::new(),
                expression: None
            }
        ];
        ast
    }

    #[fixture]
    fn ctx() -> Ctx {
        let mut ctx = Ctx::new();

        // Declare all bindings used in `sample_ast`.
        for i in 0..3 {
            ctx.scopes.declare_global(StringId::from_id(i));
        }

        ctx
    }

    #[rstest]
    #[case("block_empty", ast::Block {
        statements: vec![],
        expression: None,
    })]
    #[case("block_statement", ast::Block {
        statements: vec![ast::StatementId::from_id(0)],
        expression: None,
    })]
    #[case("block_expression", ast::Block {
        statements: vec![],
        expression: Some(ast::ExprId::from_id(0)),
    })]
    #[case("block_everything", ast::Block {
        statements: vec![ast::StatementId::from_id(0)],
        expression: Some(ast::ExprId::from_id(0)),
    })]
    fn lower_block(
        mut ctx: Ctx,
        sample_ast: &ast::Ast,
        #[case] name: &str,
        #[case] block: ast::Block,
    ) {
        let scope = ctx.scopes.nest_scope_global();
        let mut pass = HirGen::new(&mut ctx, sample_ast);
        let block_id = pass.lower_block(&block, scope).unwrap();
        assert_debug_snapshot!(name, &pass.hir[block_id], &format!("{block:?}"));
        assert!(pass.errors.is_empty());
    }

    #[rstest]
    #[case(
        "assign_simple",
        ast::Assign { variable: ast::ExprId::from_id(0), value: ast::ExprId::from_id(1) }.into()
    )]
    #[case(
        "assign_reassign",
        ast::Assign { variable: ast::ExprId::from_id(0), value: ast::ExprId::from_id(1) }.into()
    )]
    #[case(
        "binary_simple",
        ast::Binary {
            lhs: ast::ExprId::from_id(0),
            op: cst::BinaryOp::Plus(tok::Plus),
            rhs: ast::ExprId::from_id(1)
        }.into()
    )]
    #[case(
        "unary_simple",
        ast::Unary { value: ast::ExprId::from_id(0), op: cst::UnaryOp::Negative(tok::Minus) }.into()
    )]
    #[case(
        "if_simple",
        ast::If { conditions: vec![(ast::ExprId::from_id(0), ast::BlockId::from_id(0))], otherwise: None }.into()
    )]
    #[case(
        "if_else",
        ast::If {
            conditions: vec![(ast::ExprId::from_id(0), ast::BlockId::from_id(0))],
            otherwise: Some(ast::BlockId::from_id(1))
        }.into()
    )]
    #[case(
        "if_else_if",
        ast::If {
            conditions: vec![
                (ast::ExprId::from_id(0), ast::BlockId::from_id(0)),
                (ast::ExprId::from_id(1), ast::BlockId::from_id(1))
            ],
            otherwise: None
        }.into()
    )]
    #[case("literal_integer", ast::Literal::Integer(123).into())]
    #[case("literal_boolean", ast::Literal::Boolean(true).into())]
    #[case("literal_unit", ast::Literal::Unit.into())]
    #[case(
        "call_no_params",
        ast::Call { callee: ast::ExprId::from_id(0), arguments: vec![] }.into()
    )]
    #[case(
        "call_with_params",
        ast::Call {
            callee: ast::ExprId::from_id(0),
            arguments: vec![ast::ExprId::from_id(1), ast::ExprId::from_id(2)]
        }.into()
    )]
    #[case("variable_simple", ast::Variable { variable: StringId::from_id(0) }.into())]
    fn lower_expr(
        mut ctx: Ctx,
        sample_ast: &ast::Ast,
        #[case] name: &str,
        #[case] expr: ast::Expr,
    ) {
        let scope = ctx.scopes.nest_scope_global();
        let mut pass = HirGen::new(&mut ctx, sample_ast);
        let expr_id = pass.lower_expr(&expr, scope).unwrap();
        assert_debug_snapshot!(name, &pass.hir[expr_id], &format!("{expr:?}"));
        assert!(pass.errors.is_empty());
    }
}
