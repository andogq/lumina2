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
            let annotations = item
                .annotations
                .iter()
                .map(|annotation| ast_gen.lower_annotation(annotation))
                .collect();

            match &item.kind {
                cst::ItemKind::FunctionDeclaration(function_declaration) => {
                    ast_gen.lower_item_function(function_declaration, annotations);
                }
                cst::ItemKind::TraitDeclaration(trait_declaration) => {
                    ast_gen.lower_trait_declaration(trait_declaration, annotations);
                }
                cst::ItemKind::TraitImplementation(trait_implementation) => {
                    ast_gen.lower_trait_implementation(trait_implementation, annotations);
                }
                cst::ItemKind::ExternalFunction(external_function) => {
                    ast_gen.lower_external_function(external_function, annotations);
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

    fn lower_annotation(&mut self, annotation: &cst::Annotation) -> AnnotationId {
        let annotation = Annotation {
            key: self.ctx.strings.intern(&annotation.key.0),
            value: match &annotation.value {
                cst::AnnotationValue::None => None,
                cst::AnnotationValue::Value { value, .. } => {
                    Some(self.ctx.strings.intern(&value.0))
                }
            },
        };
        self.ast.annotations.insert(annotation)
    }

    fn lower_function(
        &mut self,
        function: &cst::FunctionDeclaration,
        annotations: Vec<AnnotationId>,
    ) -> FunctionId {
        let function_declaration = FunctionDeclaration {
            annotations,
            signature: self.lower_function_signature(&function.signature),
            implementation: FunctionImplementation::Body(self.lower_block(&function.body)),
        };
        self.ast.function_declarations.insert(function_declaration)
    }

    fn lower_item_function(
        &mut self,
        function: &cst::FunctionDeclaration,
        annotations: Vec<AnnotationId>,
    ) -> FunctionId {
        let id = self.lower_function(function, annotations);
        self.ast.item_functions.push(id);
        id
    }

    fn lower_external_function(
        &mut self,
        external_function: &cst::ExternalFunction,
        annotations: Vec<AnnotationId>,
    ) -> FunctionId {
        let signature = self.lower_function_signature(&external_function.signature);
        let id = self.ast.function_declarations.insert(FunctionDeclaration {
            annotations,
            signature,
            implementation: FunctionImplementation::None,
        });
        self.ast.item_functions.push(id);
        id
    }

    fn lower_function_signature(
        &mut self,
        signature: &cst::FunctionSignature,
    ) -> FunctionSignature {
        FunctionSignature {
            name: self.ctx.strings.intern(&signature.name.0),
            parameters: signature
                .parameters
                .iter_items()
                .map(|parameter| FunctionParameter {
                    name: self.ctx.strings.intern(&parameter.name.0),
                    ty: self.lower_type(&parameter.ty),
                })
                .collect(),
            return_ty: signature
                .return_ty
                .as_ref()
                .map(|ty| self.lower_type(&ty.ty)),
        }
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
                    let expression = value
                        .as_ref()
                        .map(|expression| self.lower_expression(expression))
                        .unwrap_or_else(|| self.ast.expressions.insert(Tuple::UNIT.into()));
                    statements.push(
                        self.ast
                            .statements
                            .insert(ReturnStatement { expression }.into()),
                    )
                }
                cst::Statement::Break(cst::BreakStatement { value, .. }) => {
                    let expression = value
                        .as_ref()
                        .map(|expression| self.lower_expression(expression))
                        .unwrap_or_else(|| self.ast.expressions.insert(Tuple::UNIT.into()));
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
            cst::Expression::Tuple(cst::Tuple { items, .. }) => Tuple {
                values: items
                    .iter_items()
                    .map(|item| self.lower_expression(item))
                    .collect(),
            }
            .into(),
            cst::Expression::Field(field) => Field {
                lhs: self.lower_expression(&field.lhs),
                field: match &field.field {
                    cst::FieldKey::Unnamed(field) => FieldKey::Unnamed(field.0),
                    cst::FieldKey::Named(_) => unimplemented!(),
                },
            }
            .into(),
            cst::Expression::QualifiedPath(cst::QualifiedPath { ty, name, item, .. }) => {
                QualifiedPath {
                    ty: self.lower_type(ty),
                    name: self.ctx.strings.intern(&name.0),
                    item: self.ctx.strings.intern(&item.0),
                }
                .into()
            }
        };

        self.ast.expressions.insert(expression)
    }

    /// Lower a [`cst::CstType`] into an [`AstType`], returning the interned ID.
    ///
    /// Note: No de-duplication of types is done at this stage, so lowering `CstType::Named("i8")`
    /// twice will result in two different [`AstTypeId`]s.
    fn lower_type(&mut self, ty: &cst::CstType) -> AstTypeId {
        let ty = match ty {
            cst::CstType::Named(ident) => {
                if ident.0 == "Self" {
                    AstType::SelfType
                } else {
                    AstType::Named(self.ctx.strings.intern(&ident.0))
                }
            }
            cst::CstType::Tuple(tuple) => AstType::Tuple(
                tuple
                    .items
                    .iter_items()
                    .map(|ty| self.lower_type(ty))
                    .collect(),
            ),
        };
        self.ast.types.insert(ty)
    }

    /// Lower a [`cst::TraitDeclaration`] into a [`Trait`], producing a unique [`TraitId`].
    fn lower_trait_declaration(
        &mut self,
        trait_declaration: &cst::TraitDeclaration,
        annotations: Vec<AnnotationId>,
    ) -> TraitId {
        let methods = trait_declaration
            .methods
            .iter()
            .map(|(method, _)| {
                (
                    self.ctx.strings.intern(&method.name.0),
                    self.lower_function_signature(method),
                )
            })
            .collect();
        self.ast.traits.insert(Trait {
            annotations,
            name: self.ctx.strings.intern(&trait_declaration.name.0),
            methods,
        })
    }

    fn lower_trait_implementation(
        &mut self,
        trait_implementation: &cst::TraitImplementation,
        annotations: Vec<AnnotationId>,
    ) {
        let methods = trait_implementation
            .methods
            .iter()
            .map(|method| {
                let method = self.lower_function(
                    method,
                    // Currently, annotations cannot be attached to non-item functions.
                    Vec::new(),
                );

                (self.ast[method].signature.name, method)
            })
            .collect();
        let target_ty = self.lower_type(&trait_implementation.ty);
        self.ast.trait_implementations.push(TraitImplementation {
            annotations,
            trait_name: self.ctx.strings.intern(&trait_implementation.name.0),
            target_ty,
            methods,
        });
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

    fn parse<T>(source: &str) -> T
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
    #[case("tuple_empty", "()")]
    #[case("tuple_single", "(1,)")]
    #[case("tuple_many", "(1, true, 3)")]
    #[case("tuple_nested", "(1, (2, true), 4)")]
    #[case("field_unnamed", "a.1")]
    fn lower_expression(#[case] name: &str, mut ctx: Ctx, #[case] source: &'static str) {
        let mut pass = AstGen::new(&mut ctx);
        let expression_id = pass.lower_expression(&parse::<cst::Expression>(source));
        assert_debug_snapshot!(name, pass.ast[expression_id], source);
    }

    #[rstest]
    #[case("expression_statement", "{ 1 }")]
    #[case("expression_statement_semicolon", "{ 1; }")]
    fn lower_block(#[case] name: &str, mut ctx: Ctx, #[case] source: &str) {
        let mut pass = AstGen::new(&mut ctx);
        let block = parse::<cst::Block>(source);
        let block_id = pass.lower_block(&block);
        assert_debug_snapshot!(name, pass.ast[block_id], source);
    }

    #[rstest]
    #[case("trait_declaration_empty", "trait MyTrait {}")]
    #[case("trait_declaration_single", "trait MyTrait { fn something(); }")]
    #[case(
        "trait_declaration_multiple",
        "trait MyTrait { fn something(n: u8); fn another() -> bool; }"
    )]
    fn trait_declaration(#[case] name: &str, mut ctx: Ctx, #[case] source: &'static str) {
        let mut pass = AstGen::new(&mut ctx);
        let trait_id = pass.lower_trait_declaration(&parse(source), Vec::new());
        assert_debug_snapshot!(name, pass.ast[trait_id], source);
    }

    #[rstest]
    #[case("trait_implementation_empty", "impl MyTrait for MyType {}")]
    #[case(
        "trait_implementation_single",
        "impl MyTrait for MyType { fn something() {} }"
    )]
    #[case(
        "trait_implementation_multiple",
        "impl MyTrait for MyType { fn something(n: u8) {} fn another() -> bool { true } }"
    )]
    fn trait_implementation(#[case] name: &str, mut ctx: Ctx, #[case] source: &'static str) {
        let mut pass = AstGen::new(&mut ctx);
        pass.lower_trait_implementation(&parse(source), Vec::new());
        assert_debug_snapshot!(name, pass.ast.trait_implementations[0], source);
    }

    #[rstest]
    #[case("annotation_key", "@some_annotation")]
    #[case("annotation_key_value", "@some_annotation(value)")]
    fn lower_annotation(#[case] name: &str, mut ctx: Ctx, #[case] source: &str) {
        let mut pass = AstGen::new(&mut ctx);
        let annotation = pass.lower_annotation(&parse(source));
        assert_debug_snapshot!(name, pass.ast.annotations[annotation], source);
    }

    #[rstest]
    #[case("external_function_simple", "extern fn some_function();")]
    #[case(
        "external_function_parameters",
        "extern fn some_function(parameter: u8);"
    )]
    #[case("external_function_return", "extern fn some_function() -> bool;")]
    #[case(
        "external_function_full",
        "extern fn some_function(parameter: u8) -> bool;"
    )]
    fn external_function(#[case] name: &str, mut ctx: Ctx, #[case] source: &'static str) {
        let mut pass = AstGen::new(&mut ctx);
        let id = pass.lower_external_function(&parse(source), vec![]);
        assert_debug_snapshot!(name, pass.ast[id], source);
    }
}
