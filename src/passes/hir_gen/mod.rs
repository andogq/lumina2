mod annotations;

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

        // Lower each top-level function, saving a map from the old to new ID.
        let item_ctx = FunctionCtx::item();
        for &function_id in &ast.item_functions {
            let function = &ast[function_id];
            let _ = run_and_report!(hir_gen.ctx, errors, || hir_gen
                .lower_function(&item_ctx, function));
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
            hir: Hir::new(),
        }
    }

    /// Lower the provided trait declaration.
    fn lower_trait_declaration(&mut self, trait_declaration: &ast::Trait) -> CResult<TraitId> {
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

        Ok(self
            .hir
            .add_trait(name, method_scope, method_bindings, methods))
    }

    fn lower_trait_implementation(
        &mut self,
        trait_implementation: &ast::TraitImplementation,
    ) -> CResult<()> {
        let trait_name = self
            .ctx
            .scopes
            .resolve_global(trait_implementation.trait_name);
        let ty = self
            .lower_ast_type(trait_implementation.target_ty)
            .without_self()
            .expect("`Self` cannot be used as the implementing type of a trait.");

        // Find the trait that's being implemented.
        let (trait_id, trait_declaration) = self
            .hir
            .traits
            .iter_pairs()
            .find(|(_, trait_declaration)| trait_declaration.name == trait_name)
            .unwrap();
        // HACK: Clone here not really needed.
        let trait_declaration = trait_declaration.clone();

        let key = TraitImplementationKey { trait_id, ty };

        // Ensure there's no conflicting trait implementation.
        assert!(!self.hir.trait_implementations.contains_key(&key));

        // Lower each method, and store it against the corresponding `TraitMethodId`.
        let lowered_methods: HashMap<_, _> = trait_implementation
            .methods
            .iter()
            .map(|(method_name, function_id)| {
                // Determine which method this corresponds to.
                let trait_method = {
                    let binding = self
                        .ctx
                        .scopes
                        .resolve(trait_declaration.method_scope, *method_name);
                    *trait_declaration
                        .method_bindings
                        .get(&binding)
                        .expect("method does not exist in trait declaration")
                };

                // Lower the method.
                let method = &self.ast.function_declarations[*function_id];
                let function_id = self.lower_function(
                    &FunctionCtx::trait_method(ty, trait_id, trait_method),
                    method,
                )?;

                Ok((trait_method, function_id))
            })
            .collect::<CResult<_>>()?;

        // Order all of the lowered methods.
        let mut methods = IndexedVec::new();
        for method_id in trait_declaration.methods.iter_keys() {
            let function_id = *lowered_methods
                .get(&method_id)
                .expect("trait implementation missing method");
            assert_eq!(methods.insert(function_id), method_id);
        }

        self.hir
            .trait_implementations
            .insert(key, TraitImplementation { methods });

        Ok(())
    }

    /// Lower the provided function.
    fn lower_function(
        &mut self,
        ctx: &FunctionCtx,
        function: &ast::FunctionDeclaration,
    ) -> CResult<FunctionId> {
        // Add the function identifier to the global scope.
        let binding = self.ctx.scopes.declare_global(function.signature.name);

        // Create a new scope for the function.
        let function_scope = self.ctx.scopes.nest_scope_global();

        let signature = {
            // Lower the signature.
            let signature = self.lower_function_signature(&function.signature, function_scope);
            // Resolve `Self` depending whether it's valid in this context or not.
            match ctx.current_self() {
                Some(current_self) => signature.with_self(current_self),
                None => signature
                    .without_self()
                    .expect("`Self` cannot be used in this context."),
            }
        };

        // Lower the body of the function.
        let entry = match &function.implementation {
            ast::FunctionImplementation::Body(body) => {
                self.lower_block(ctx, &self.ast[*body], function_scope)?
            }
            ast::FunctionImplementation::None => {
                panic!("cannot generate HIR for function without implementation")
            }
        };

        Ok(self.hir.add_function(binding, signature, entry))
    }

    /// Lower a function signature.
    fn lower_function_signature(
        &mut self,
        signature: &ast::FunctionSignature,
        scope: ScopeId,
    ) -> FunctionSignature<MaybeSelfType> {
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
            None => self.ctx.types.unit().into(),
        };

        FunctionSignature {
            parameters,
            return_ty,
        }
    }

    /// Lower a block, using the provided scope as the parent scope.
    fn lower_block(
        &mut self,
        ctx: &FunctionCtx,
        block: &ast::Block,
        parent_scope: ScopeId,
    ) -> CResult<BlockId> {
        // Create a new scope for this block.
        let scope = self.ctx.scopes.nest_scope(parent_scope);

        let mut statements = Vec::new();

        for &statement_id in &block.statements {
            let statement = &self.ast[statement_id];

            match &statement.kind {
                // Statements are lowered into a declaration, followed by an assignment.
                ast::StatementKind::Let(ast::LetStatement { variable, value }) => {
                    // Create a new binding for the statement.
                    let binding = self.ctx.scopes.declare(scope, *variable);

                    // Lower the value.
                    let value = self.lower_expression(ctx, &self.ast[*value], scope)?;

                    // Add the declaration.
                    statements.push(self.hir.add_statement(DeclareStatement {
                        binding,
                        ty: DeclarationTy::Inferred(value),
                    }));

                    // Add the assignment.
                    statements.push({
                        let variable = self.hir.add_expression(Variable { binding });
                        let assign_expression = self.hir.add_expression(Assign { variable, value });
                        self.hir.add_statement(ExpressionStatement {
                            expression: assign_expression,
                        })
                    });
                }
                ast::StatementKind::Return(ast::ReturnStatement { expression }) => {
                    let expression = self.lower_expression(ctx, &self.ast[*expression], scope)?;
                    statements.push(self.hir.add_statement(ReturnStatement { expression }));
                }
                ast::StatementKind::Break(ast::BreakStatement { expression }) => {
                    let expression = self.lower_expression(ctx, &self.ast[*expression], scope)?;
                    statements.push(self.hir.add_statement(BreakStatement { expression }))
                }
                ast::StatementKind::Expression(ast::ExpressionStatement { expression }) => {
                    let expression = self.lower_expression(ctx, &self.ast[*expression], scope)?;
                    statements.push(self.hir.add_statement(ExpressionStatement { expression }));
                }
            }
        }

        // Lower the final expression of the block, or fallback to `()` if there is no expression.
        let expression = match (
            block.expression,
            block
                .statements
                .last()
                .map(|statement| &self.ast[*statement].kind),
        ) {
            // Use the provided expression to end the block.
            (Some(expression), _) => self.lower_expression(ctx, &self.ast[expression], scope)?,
            // Otherwise, if the final statement is `return` then add an unreachable marker.
            (None, Some(ast::StatementKind::Return(_))) => {
                self.hir.add_expression(ExpressionKind::Unreachable)
            }
            // Otherwise, assume unit.
            (None, _) => self.hir.add_expression(Aggregate::UNIT),
        };

        Ok(self.hir.add_block(statements, expression))
    }

    /// Lower an expression within the provided scope.
    fn lower_expression(
        &mut self,
        ctx: &FunctionCtx,
        expression: &ast::Expression,
        scope: ScopeId,
    ) -> CResult<ExpressionId> {
        Ok(match &expression.kind {
            ast::ExpressionKind::Assign(ast::Assign { variable, value }) => {
                let variable = self.lower_expression(ctx, &self.ast[*variable], scope)?;
                let value = self.lower_expression(ctx, &self.ast[*value], scope)?;

                self.hir.add_expression(Assign { variable, value })
            }
            ast::ExpressionKind::Binary(ast::Binary {
                lhs,
                operation,
                rhs,
            }) => {
                let lhs = self.lower_expression(ctx, &self.ast[*lhs], scope)?;
                let rhs = self.lower_expression(ctx, &self.ast[*rhs], scope)?;

                self.hir.add_expression(Binary {
                    lhs,
                    operation: *operation,
                    rhs,
                })
            }
            ast::ExpressionKind::Unary(ast::Unary { operation, value }) => {
                let value = self.lower_expression(ctx, &self.ast[*value], scope)?;

                self.hir.add_expression(Unary {
                    operation: *operation,
                    value,
                })
            }
            ast::ExpressionKind::If(ast::If {
                conditions,
                otherwise,
            }) => {
                // Where the switch will be built.
                let mut switch: Option<Switch> = None;
                // Optional default expression to apply to end of switch statements.
                let mut default = otherwise
                    .map(|otherwise| {
                        Ok::<_, CError>(ExpressionKind::Block(self.lower_block(
                            ctx,
                            &self.ast[otherwise],
                            scope,
                        )?))
                    })
                    .transpose()?;

                for (condition, block) in conditions.iter().rev() {
                    switch = Some(Switch {
                        discriminator: self.lower_expression(ctx, &self.ast[*condition], scope)?,
                        branches: vec![(
                            Literal::Boolean(true),
                            self.lower_block(ctx, &self.ast[*block], scope)?,
                        )],
                        // Try use the default expression.
                        default: default
                            .take()
                            // Otherwise continue building the switch statement.
                            .or_else(|| Some(switch.take()?.into()))
                            .map(|expression| {
                                let expression = self.hir.add_expression(expression);
                                self.hir.add_block(vec![], expression)
                            }),
                    });
                }

                self.hir
                    .add_expression(switch.ok_or(HirGenError::IfMustHaveBlock)?)
            }
            ast::ExpressionKind::Loop(ast::Loop { body }) => {
                let body = self.lower_block(ctx, &self.ast[*body], scope)?;

                self.hir.add_expression(Loop { body })
            }
            ast::ExpressionKind::Literal(literal) => self.hir.add_expression(match literal {
                ast::Literal::Integer(value) => Literal::Integer(*value),
                ast::Literal::Boolean(value) => Literal::Boolean(*value),
            }),
            ast::ExpressionKind::Call(ast::Call { callee, arguments }) => {
                let callee = self.lower_expression(ctx, &self.ast[*callee], scope)?;
                let arguments = arguments
                    .iter()
                    .map(|argument| self.lower_expression(ctx, &self.ast[*argument], scope))
                    .collect::<Result<_, _>>()?;

                self.hir.add_expression(Call { callee, arguments })
            }
            ast::ExpressionKind::Block(block) => {
                let block = self.lower_block(ctx, &self.ast[*block], scope)?;

                self.hir.add_expression(block)
            }
            ast::ExpressionKind::Variable(ast::Variable { variable }) => {
                self.hir.add_expression(Variable {
                    binding: self.ctx.scopes.resolve(scope, *variable),
                })
            }
            ast::ExpressionKind::Tuple(ast::Tuple { values }) => {
                let values = values
                    .iter()
                    .map(|value| self.lower_expression(ctx, &self.ast[*value], scope))
                    .collect::<Result<_, _>>()?;

                self.hir.add_expression(Aggregate { values })
            }
            ast::ExpressionKind::Field(ast::Field { lhs, field }) => {
                let lhs = self.lower_expression(ctx, &self.ast[*lhs], scope)?;

                self.hir.add_expression(Field {
                    lhs,
                    field: match field {
                        ast::FieldKey::Unnamed(field) => *field,
                    },
                })
            }
            ast::ExpressionKind::QualifiedPath(ast::QualifiedPath { ty, name, item }) => {
                let trait_name = self.ctx.scopes.resolve_global(*name);
                let (trait_id, target_trait) = self
                    .hir
                    .traits
                    .iter_pairs()
                    .find(|&(_, t)| t.name == trait_name)
                    .expect("trait must exist");
                let item_binding = self.ctx.scopes.resolve(target_trait.method_scope, *item);
                let item = *target_trait
                    .method_bindings
                    .get(&item_binding)
                    .expect("valid method on trait");
                let ty = self.lower_ast_type(*ty);

                self.hir.add_expression(Path {
                    ty: match ctx.current_self() {
                        Some(current_self) => ty.with_self(current_self),
                        None => ty
                            .without_self()
                            .expect("`Self` cannot be used in this context"),
                    },
                    target_trait: trait_id,
                    item,
                })
            }
        })
    }

    /// Lower an [`ast::AstType`] into a unique [`TypeId`].
    ///
    /// This will handle ensure that types are correctly equated where necessary.
    fn lower_ast_type(&mut self, ty: ast::AstTypeId) -> MaybeSelfType {
        match &self.ast[ty] {
            ast::AstType::SelfType => MaybeSelfType::SelfType,
            ast::AstType::Named(string_id) => MaybeSelfType::Type({
                // HACK: This only handles built-in types.
                match self.ctx.strings.get(*string_id) {
                    "u8" => self.ctx.types.u8(),
                    "i8" => self.ctx.types.i8(),
                    "bool" => self.ctx.types.boolean(),
                    ty => panic!("unknown type: {ty}"),
                }
            }),
            ast::AstType::Tuple(ast_type_ids) => MaybeSelfType::Type({
                let fields = ast_type_ids
                    .iter()
                    .map(|ty| {
                        let MaybeSelfType::Type(ty) = self.lower_ast_type(*ty) else {
                            // TODO: Allow `Self` within other types.
                            unimplemented!("`Self` within aggregate types is not supported.");
                        };

                        ty
                    })
                    .collect::<Vec<_>>();
                self.ctx.types.tuple(fields)
            }),
        }
    }
}

/// Context required when processing a function.
#[derive(Clone, Debug)]
enum FunctionCtx {
    /// An item function (top-level function).
    Item,
    /// A method within an `impl` block.
    Method {
        /// Type that the method is defined on.
        current_self: TypeId,
    },
    /// A method within a trait implementation.
    TraitMethod {
        /// Type that is implementing the trait.
        current_self: TypeId,
        /// Trait that is being implemented.
        current_trait: TraitId,
        /// Method on the trait which is being implemented.
        method: TraitMethodId,
    },
}

impl FunctionCtx {
    /// Create a new context for function item (top-level function).
    fn item() -> Self {
        Self::Item
    }

    /// Create a new context for a method (within an `impl` block).
    #[expect(
        dead_code,
        reason = "stand-alone implementations will be added in the future"
    )]
    fn method(current_self: TypeId) -> Self {
        Self::Method { current_self }
    }

    /// Create a new context for a method in a trait implementation.
    fn trait_method(current_self: TypeId, current_trait: TraitId, method: TraitMethodId) -> Self {
        Self::TraitMethod {
            current_self,
            current_trait,
            method,
        }
    }

    /// Fetch the type that represents `Self` within this context.
    fn current_self(&self) -> Option<TypeId> {
        match self {
            Self::Item => None,
            Self::Method { current_self } => Some(*current_self),
            Self::TraitMethod { current_self, .. } => Some(*current_self),
        }
    }

    /// Fetch the trait that is currently being implemented.
    #[expect(
        dead_code,
        reason = "tracking current trait may be useful for diagnostics"
    )]
    #[mutants::skip(reason = "dead code")]
    fn current_trait(&self) -> Option<TraitId> {
        match self {
            Self::TraitMethod { current_trait, .. } => Some(*current_trait),
            _ => None,
        }
    }

    /// Fetch the trait method that is currently being implemented.
    #[expect(
        dead_code,
        reason = "tracking current method may be useful for diagnostics"
    )]
    #[mutants::skip(reason = "dead code")]
    fn current_trait_method(&self) -> Option<TraitMethodId> {
        match self {
            Self::TraitMethod { method, .. } => Some(*method),
            _ => None,
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
        for i in 0..3 {
            ast.add_expression(ast::Variable {
                variable: StringId::from_id(i),
            });
        }
        ast.add_statement(ast::ExpressionStatement {
            expression: ast::ExpressionId::from_id(0),
        });
        for _ in 0..3 {
            ast.add_block(Vec::new(), None);
        }
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
        id: ast::AstId::from_id(0),
        statements: vec![],
        expression: None,
    })]
    #[case("block_statement", ast::Block {
        id: ast::AstId::from_id(0),
        statements: vec![ast::StatementId::from_id(0)],
        expression: None,
    })]
    #[case("block_expression", ast::Block {
        id: ast::AstId::from_id(0),
        statements: vec![],
        expression: Some(ast::ExpressionId::from_id(0)),
    })]
    #[case("block_everything", ast::Block {
        id: ast::AstId::from_id(0),
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
        let block_id = pass
            .lower_block(&FunctionCtx::item(), &block, scope)
            .unwrap();
        assert_debug_snapshot!(name, &pass.hir[block_id], &format!("{block:?}"));
    }

    #[rstest]
    #[case(
        "assign_simple",
        ast::Assign { variable: ast::ExpressionId::from_id(0), value: ast::ExpressionId::from_id(1) }
    )]
    #[case(
        "assign_reassign",
        ast::Assign { variable: ast::ExpressionId::from_id(0), value: ast::ExpressionId::from_id(1) }
    )]
    #[case(
        "binary_simple",
        ast::Binary {
            lhs: ast::ExpressionId::from_id(0),
            operation: BinaryOperation::Plus,
            rhs: ast::ExpressionId::from_id(1)
        }
    )]
    #[case(
        "unary_simple",
        ast::Unary { value: ast::ExpressionId::from_id(0), operation: UnaryOperation::Negative }
    )]
    #[case(
        "if_simple",
        ast::If { conditions: vec![(ast::ExpressionId::from_id(0), ast::BlockId::from_id(0))], otherwise: None }
    )]
    #[case(
        "if_else",
        ast::If {
            conditions: vec![(ast::ExpressionId::from_id(0), ast::BlockId::from_id(0))],
            otherwise: Some(ast::BlockId::from_id(1))
        }
    )]
    #[case(
        "if_else_if",
        ast::If {
            conditions: vec![
                (ast::ExpressionId::from_id(0), ast::BlockId::from_id(0)),
                (ast::ExpressionId::from_id(1), ast::BlockId::from_id(1))
            ],
            otherwise: None
        }
    )]
    #[case("literal_integer", ast::Literal::Integer(123))]
    #[case("literal_boolean", ast::Literal::Boolean(true))]
    #[case(
        "call_no_parameters",
        ast::Call { callee: ast::ExpressionId::from_id(0), arguments: vec![] }
    )]
    #[case(
        "call_with_parameters",
        ast::Call {
            callee: ast::ExpressionId::from_id(0),
            arguments: vec![ast::ExpressionId::from_id(1), ast::ExpressionId::from_id(2)]
        }
    )]
    #[case("variable_simple", ast::Variable { variable: StringId::from_id(0) })]
    #[case("tuple_empty", ast::Tuple { values: vec![] })]
    #[case("tuple_many", ast::Tuple { values: vec![ast::ExpressionId::from_id(1), ast::ExpressionId::from_id(2)] })]
    fn lower_expression(
        mut ctx: Ctx,
        sample_ast: &ast::Ast,
        #[case] name: &str,
        #[case] expression: impl Into<ast::ExpressionKind>,
    ) {
        let expression = expression.into();
        let dbg_str = format!("{expression:?}");

        let scope = ctx.scopes.nest_scope_global();
        let mut pass = HirGen::new(&mut ctx, sample_ast);
        let expression_id = pass
            .lower_expression(
                &FunctionCtx::item(),
                &ast::Expression {
                    id: ast::AstId::from_id(0),
                    kind: expression,
                },
                scope,
            )
            .unwrap();
        assert_debug_snapshot!(name, &pass.hir[expression_id], &dbg_str);
    }

    #[rstest]
    #[case("empty", [], None, None)]
    #[case("empty_with_self", [], None, Some(Type::U8))]
    #[case("self_parameter", vec![ast::AstType::SelfType], None, Some(Type::U8))]
    #[case("self_return_type", vec![], Some(ast::AstType::SelfType), Some(Type::U8))]
    fn lower_function_signature(
        mut ctx: Ctx,
        sample_ast: &ast::Ast,
        #[case] name: &str,
        #[case] parameters: impl IntoIterator<Item = ast::AstType>,
        #[case] return_ty: Option<ast::AstType>,
        #[case] current_self: Option<Type>,
    ) {
        let mut sample_ast = sample_ast.clone();

        let signature = ast::FunctionSignature {
            name: StringId::from_id(0),
            parameters: parameters
                .into_iter()
                .enumerate()
                .map(|(i, parameter)| ast::FunctionParameter {
                    name: StringId::from_id(i + 1),
                    ty: sample_ast.types.insert(parameter),
                })
                .collect(),
            return_ty: return_ty.map(|return_ty| sample_ast.types.insert(return_ty)),
        };

        let scope = ctx.scopes.nest_scope_global();
        let mut pass = HirGen::new(&mut ctx, &sample_ast);

        let lowered_signature = pass.lower_function_signature(&signature, scope);
        let lowered_signature = if let Some(current_self) = &current_self {
            lowered_signature.with_self(pass.ctx.types.get(current_self.clone()))
        } else {
            lowered_signature.without_self().unwrap()
        };
        assert_debug_snapshot!(
            name,
            lowered_signature,
            &format!("{signature:?} ({current_self:?})")
        );
    }
}
