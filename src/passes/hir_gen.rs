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
    /// Mapping of function IDs between stages,
    function_mapping: IndexedVec<ast::FunctionId, FunctionId>,
}

impl<'ctx, 'ast> Pass<'ctx, 'ast> for HirGen<'ctx, 'ast> {
    type Input = ast::Ast;
    type Output = Hir;
    type Extra = ();

    fn run(ctx: &'ctx mut Ctx, ast: &'ast Self::Input, _extra: ()) -> PassResult<Self::Output> {
        let mut hir_gen = Self::new(ctx, ast);

        // Errors generated throughout this pass.
        let mut errors = Vec::new();

        // Register each trait declaration.
        for trait_declaration in ast.traits.iter() {
            let _ = run_and_report!(hir_gen.ctx, errors, || hir_gen
                .lower_trait_declaration(trait_declaration));
        }

        // Lower each function, saving a map from the old to new ID.
        for (function_id, function) in ast.function_declarations.iter_pairs() {
            let lowered_id =
                run_and_report!(hir_gen.ctx, errors, || hir_gen.lower_function(function));

            if let Ok(lowered_id) = lowered_id {
                // Save the new ID in the mapping, assuming that functions will be added in the
                // same order.
                assert_eq!(hir_gen.function_mapping.insert(lowered_id), function_id);
            }
        }

        // Lower each trait implementation.
        for trait_implementation in ast.trait_implementations.iter() {
            let _ = run_and_report!(hir_gen.ctx, errors, || hir_gen
                .lower_trait_implementation(trait_implementation));
        }

        Ok(PassSuccess::new(hir_gen.hir, errors))
    }
}

impl<'ctx, 'ast> HirGen<'ctx, 'ast> {
    /// Create a new instance of the generator.
    pub fn new(ctx: &'ctx mut Ctx, ast: &'ast ast::Ast) -> Self {
        Self {
            ctx,
            ast,
            hir: Hir::default(),
            function_mapping: IndexedVec::new(),
        }
    }

    /// Lower the provided trait declaration.
    pub fn lower_trait_declaration(&mut self, trait_declaration: &ast::Trait) -> CResult<TraitId> {
        let name = self.ctx.scopes.declare_global(trait_declaration.name);

        let method_scope = self.ctx.scopes.nest_scope_global();

        let mut methods = IndexedVec::new();
        let mut method_bindings = HashMap::new();

        for (method, signature) in &trait_declaration.methods {
            let binding = self.ctx.scopes.declare(method_scope, *method);

            // Create a dummy scope just to declare the parameters in.
            let parameter_scope = self.ctx.scopes.nest_scope(method_scope);
            let signature = self.lower_function_signature(signature, parameter_scope);

            let method_id = methods.insert(signature);

            // Record the method ID which corresponds with the binding.
            method_bindings.insert(binding, method_id);
        }

        Ok(self.hir.traits.insert(Trait {
            name,
            method_scope,
            method_bindings,
            methods,
        }))
    }

    pub fn lower_trait_implementation(
        &mut self,
        trait_implementation: &ast::TraitImplementation,
    ) -> CResult<()> {
        let trait_name = self
            .ctx
            .scopes
            .resolve_global(trait_implementation.trait_name);
        let ty = self.lower_ast_type(trait_implementation.target_ty);

        // Find the trait that's being implemented.
        let (trait_id, trait_declaration) = self
            .hir
            .traits
            .iter_pairs()
            .find(|(_, trait_declaration)| trait_declaration.name == trait_name)
            .unwrap();

        let key = TraitImplementationKey { trait_id, ty };

        // Ensure there's no conflicting trait implementation.
        assert!(!self.hir.trait_implementations.contains_key(&key));

        // Resolve the bindings for each method, and match them up with a `TraitMethodId`.
        let implementation_bindings = trait_implementation
            .methods
            .iter()
            .map(|(method_name, function_id)| {
                (
                    {
                        let binding = self
                            .ctx
                            .scopes
                            .resolve(trait_declaration.method_scope, *method_name);
                        trait_declaration.method_bindings[&binding]
                    },
                    function_id,
                )
            })
            .collect::<HashMap<_, _>>();

        // Record the method mapping.
        let mut methods = IndexedVec::new();
        for (method_id, _) in trait_declaration.methods.iter_pairs() {
            let original_function_id = *implementation_bindings[&method_id];
            assert_eq!(
                methods.insert(self.function_mapping[original_function_id]),
                method_id
            );
        }

        self.hir
            .trait_implementations
            .insert(key, TraitImplementation { methods });

        Ok(())
    }

    /// Lower the provided function.
    pub fn lower_function(&mut self, function: &ast::FunctionDeclaration) -> CResult<FunctionId> {
        // Add the function identifier to the global scope.
        let binding = self.ctx.scopes.declare_global(function.signature.name);

        // Create a new scope for the function.
        let function_scope = self.ctx.scopes.nest_scope_global();

        let signature = self.lower_function_signature(&function.signature, function_scope);

        // Lower the body of the function.
        let entry = self.lower_block(&self.ast[function.body], function_scope)?;

        Ok(self.hir.functions.insert(Function {
            binding,
            signature,
            entry,
        }))
    }

    /// Lower a function signature.
    pub fn lower_function_signature(
        &mut self,
        signature: &ast::FunctionSignature,
        scope: ScopeId,
    ) -> FunctionSignature {
        let parameters = signature
            .parameters
            .iter()
            .map(|parameter| {
                (
                    self.ctx.scopes.declare(scope, parameter.name),
                    self.lower_ast_type(parameter.ty),
                )
            })
            .collect();

        // If no return type is provided, assume `()`.
        let return_ty = match signature.return_ty {
            Some(return_ty) => self.lower_ast_type(return_ty),
            None => self.ctx.types.unit(),
        };

        FunctionSignature {
            parameters,
            return_ty,
        }
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
                    let value = self.lower_expression(&self.ast[*value], scope)?;

                    // Add the declaration.
                    statements.push(self.hir.statements.insert(Statement::Declare(
                        DeclareStatement {
                            binding,
                            ty: DeclarationTy::Inferred(value),
                        },
                    )));

                    // Add the assignment.
                    statements.push({
                        let variable = self
                            .hir
                            .expressions
                            .insert(Expression::Variable(Variable { binding }));
                        let assign_expression = self
                            .hir
                            .expressions
                            .insert(Expression::Assign(Assign { variable, value }));
                        self.hir
                            .statements
                            .insert(Statement::Expression(ExpressionStatement {
                                expression: assign_expression,
                            }))
                    });
                }
                ast::Statement::Return(ast::ReturnStatement { expression }) => {
                    let expression = self.lower_expression(&self.ast[*expression], scope)?;
                    statements.push(
                        self.hir
                            .statements
                            .insert(Statement::Return(ReturnStatement { expression })),
                    );
                }
                ast::Statement::Break(ast::BreakStatement { expression }) => {
                    let expression = self.lower_expression(&self.ast[*expression], scope)?;
                    statements.push(
                        self.hir
                            .statements
                            .insert(Statement::Break(BreakStatement { expression })),
                    )
                }
                ast::Statement::Expression(ast::ExpressionStatement { expression }) => {
                    let expression = self.lower_expression(&self.ast[*expression], scope)?;
                    statements.push(
                        self.hir
                            .statements
                            .insert(Statement::Expression(ExpressionStatement { expression })),
                    );
                }
            }
        }

        // Lower the final expression of the block, or fallback to `()` if there is no expression.
        let expression = match (
            block.expression,
            block
                .statements
                .last()
                .map(|statement| &self.ast[*statement]),
        ) {
            // Use the provided expression to end the block.
            (Some(expression), _) => self.lower_expression(&self.ast[expression], scope)?,
            // Otherwise, if the final statement is `return` then add an unreachable marker.
            (None, Some(ast::Statement::Return(_))) => {
                self.hir.expressions.insert(Expression::Unreachable)
            }
            // Otherwise, assume unit.
            (None, _) => self.hir.expressions.insert(Aggregate::UNIT.into()),
        };

        Ok(self.hir.blocks.insert(Block {
            statements,
            expression,
        }))
    }

    /// Lower an expression within the provided scope.
    pub fn lower_expression(
        &mut self,
        expression: &ast::Expression,
        scope: ScopeId,
    ) -> CResult<ExpressionId> {
        let expression = match expression {
            ast::Expression::Assign(ast::Assign { variable, value }) => Assign {
                variable: self.lower_expression(&self.ast[*variable], scope)?,
                value: self.lower_expression(&self.ast[*value], scope)?,
            }
            .into(),
            ast::Expression::Binary(ast::Binary {
                lhs,
                operation,
                rhs,
            }) => Binary {
                lhs: self.lower_expression(&self.ast[*lhs], scope)?,
                operation: *operation,
                rhs: self.lower_expression(&self.ast[*rhs], scope)?,
            }
            .into(),
            ast::Expression::Unary(ast::Unary { operation, value }) => Unary {
                operation: *operation,
                value: self.lower_expression(&self.ast[*value], scope)?,
            }
            .into(),
            ast::Expression::If(ast::If {
                conditions,
                otherwise,
            }) => {
                // Where the switch will be built.
                let mut switch: Option<Switch> = None;
                // Optional default expression to apply to end of switch statements.
                let mut default = otherwise
                    .map(|otherwise| {
                        Ok::<_, CError>(Expression::Block(
                            self.lower_block(&self.ast[otherwise], scope)?,
                        ))
                    })
                    .transpose()?;

                for (condition, block) in conditions.iter().rev() {
                    switch = Some(Switch {
                        discriminator: self.lower_expression(&self.ast[*condition], scope)?,
                        branches: vec![(
                            Literal::Boolean(true),
                            self.lower_block(&self.ast[*block], scope)?,
                        )],
                        // Try use the default expression.
                        default: default
                            .take()
                            // Otherwise continue building the switch statement.
                            .or_else(|| Some(switch.take()?.into()))
                            .map(|expression| {
                                let expression = self.hir.expressions.insert(expression);
                                self.hir.blocks.insert(Block {
                                    statements: Vec::new(),
                                    expression,
                                })
                            }),
                    });
                }

                switch.ok_or(HirGenError::IfMustHaveBlock)?.into()
            }
            ast::Expression::Loop(ast::Loop { body }) => Loop {
                body: self.lower_block(&self.ast[*body], scope)?,
            }
            .into(),
            ast::Expression::Literal(literal) => match literal {
                ast::Literal::Integer(value) => Literal::Integer(*value),
                ast::Literal::Boolean(value) => Literal::Boolean(*value),
            }
            .into(),
            ast::Expression::Call(ast::Call { callee, arguments }) => Call {
                callee: self.lower_expression(&self.ast[*callee], scope)?,
                arguments: arguments
                    .iter()
                    .map(|argument| self.lower_expression(&self.ast[*argument], scope))
                    .collect::<Result<_, _>>()?,
            }
            .into(),
            ast::Expression::Block(block) => self.lower_block(&self.ast[*block], scope)?.into(),
            ast::Expression::Variable(ast::Variable { variable }) => Variable {
                binding: self.ctx.scopes.resolve(scope, *variable),
            }
            .into(),
            ast::Expression::Tuple(ast::Tuple { values }) => Aggregate {
                values: values
                    .iter()
                    .map(|value| self.lower_expression(&self.ast[*value], scope))
                    .collect::<Result<_, _>>()?,
            }
            .into(),
            ast::Expression::Field(ast::Field { lhs, field }) => Field {
                lhs: self.lower_expression(&self.ast[*lhs], scope)?,
                field: match field {
                    ast::FieldKey::Unnamed(field) => *field,
                },
            }
            .into(),
            ast::Expression::QualifiedPath(ast::QualifiedPath { .. }) => {
                todo!()
            }
        };

        Ok(self.hir.expressions.insert(expression))
    }

    /// Lower an [`ast::AstType`] into a unique [`TypeId`].
    ///
    /// This will handle ensure that types are correctly equated where necessary.
    fn lower_ast_type(&mut self, ty: ast::AstTypeId) -> TypeId {
        match &self.ast[ty] {
            ast::AstType::SelfType => todo!(),
            ast::AstType::Named(string_id) => {
                // HACK: This only handles built-in types.
                match self.ctx.strings.get(*string_id) {
                    "u8" => self.ctx.types.u8(),
                    "i8" => self.ctx.types.i8(),
                    "bool" => self.ctx.types.boolean(),
                    ty => panic!("unknown type: {ty}"),
                }
            }
            ast::AstType::Tuple(ast_type_ids) => {
                let fields = ast_type_ids
                    .iter()
                    .map(|ty| self.lower_ast_type(*ty))
                    .collect::<Vec<_>>();
                self.ctx.types.tuple(fields)
            }
        }
    }
}

#[derive(Clone, Debug, thiserror::Error)]
pub enum HirGenError {
    #[error("an `if` expression must contain at least one block.")]
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
            ast::Expression::Variable(ast::Variable {
                variable: StringId::from_id(0),
            }),
            ast::Expression::Variable(ast::Variable {
                variable: StringId::from_id(1),
            }),
            ast::Expression::Variable(ast::Variable {
                variable: StringId::from_id(2),
            }),
        ];
        ast.statements = indexed_vec![ast::Statement::Expression(ast::ExpressionStatement {
            expression: ast::ExpressionId::from_id(0),
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
            let _: IdentifierBindingId = ctx.scopes.declare_global(StringId::from_id(i));
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
        expression: Some(ast::ExpressionId::from_id(0)),
    })]
    #[case("block_everything", ast::Block {
        statements: vec![ast::StatementId::from_id(0)],
        expression: Some(ast::ExpressionId::from_id(0)),
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
    }

    #[rstest]
    #[case(
        "assign_simple",
        ast::Assign { variable: ast::ExpressionId::from_id(0), value: ast::ExpressionId::from_id(1) }.into()
    )]
    #[case(
        "assign_reassign",
        ast::Assign { variable: ast::ExpressionId::from_id(0), value: ast::ExpressionId::from_id(1) }.into()
    )]
    #[case(
        "binary_simple",
        ast::Binary {
            lhs: ast::ExpressionId::from_id(0),
            operation: BinaryOperation::Plus,
            rhs: ast::ExpressionId::from_id(1)
        }.into()
    )]
    #[case(
        "unary_simple",
        ast::Unary { value: ast::ExpressionId::from_id(0), operation: UnaryOperation::Negative }.into()
    )]
    #[case(
        "if_simple",
        ast::If { conditions: vec![(ast::ExpressionId::from_id(0), ast::BlockId::from_id(0))], otherwise: None }.into()
    )]
    #[case(
        "if_else",
        ast::If {
            conditions: vec![(ast::ExpressionId::from_id(0), ast::BlockId::from_id(0))],
            otherwise: Some(ast::BlockId::from_id(1))
        }.into()
    )]
    #[case(
        "if_else_if",
        ast::If {
            conditions: vec![
                (ast::ExpressionId::from_id(0), ast::BlockId::from_id(0)),
                (ast::ExpressionId::from_id(1), ast::BlockId::from_id(1))
            ],
            otherwise: None
        }.into()
    )]
    #[case("literal_integer", ast::Literal::Integer(123).into())]
    #[case("literal_boolean", ast::Literal::Boolean(true).into())]
    #[case(
        "call_no_parameters",
        ast::Call { callee: ast::ExpressionId::from_id(0), arguments: vec![] }.into()
    )]
    #[case(
        "call_with_parameters",
        ast::Call {
            callee: ast::ExpressionId::from_id(0),
            arguments: vec![ast::ExpressionId::from_id(1), ast::ExpressionId::from_id(2)]
        }.into()
    )]
    #[case("variable_simple", ast::Variable { variable: StringId::from_id(0) }.into())]
    #[case("tuple_empty", ast::Tuple { values: vec![] }.into())]
    #[case("tuple_many", ast::Tuple { values: vec![ast::ExpressionId::from_id(1), ast::ExpressionId::from_id(2)] }.into())]
    fn lower_expression(
        mut ctx: Ctx,
        sample_ast: &ast::Ast,
        #[case] name: &str,
        #[case] expression: ast::Expression,
    ) {
        let scope = ctx.scopes.nest_scope_global();
        let mut pass = HirGen::new(&mut ctx, sample_ast);
        let expression_id = pass.lower_expression(&expression, scope).unwrap();
        assert_debug_snapshot!(name, &pass.hir[expression_id], &format!("{expression:?}"));
    }
}
