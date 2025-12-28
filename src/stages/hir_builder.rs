use crate::prelude::*;

use hir::*;

#[derive(Clone, Debug)]
pub struct HirBuilder<'ast> {
    /// HIR that is being built.
    hir: Hir,
    /// Reference AST.
    ast: &'ast ast::Ast,

    /// Map of bindings to corresponding functions.
    function_bindings: HashMap<BindingId, FunctionId>,
    /// Cached unit expression.
    unit_expression: Option<ExprId>,

    /// Mappings from previous expression ID, to new expression ID.
    pub expr_mapping: HashMap<ast::ExprId, ExprId>,
}

impl<'ast> HirBuilder<'ast> {
    pub fn new(ast: &'ast ast::Ast) -> Self {
        Self {
            hir: Hir {
                functions: Vec::new(),
            },
            ast,
            function_bindings: HashMap::new(),
            unit_expression: None,
            expr_mapping: HashMap::new(),
        }
    }

    pub fn lower_functions(&mut self, ctx: &mut Ctx) {
        for function in self.ast.function_declarations.iter() {
            self.lower_function(ctx, function);
        }
    }

    pub fn build(mut self, ctx: &mut Ctx) -> Hir {
        self.lower_functions(ctx);
        self.hir
    }

    fn ident_to_type(&self, ctx: &Ctx, ident: StringId) -> Type {
        // HACK: This only handles built-in types.
        match ctx.strings.get(ident) {
            "u8" => Type::U8,
            "i8" => Type::I8,
            "bool" => Type::Boolean,
            ty => panic!("unknown type: {ty}"),
        }
    }

    pub fn lower_function(
        &mut self,
        ctx: &mut Ctx,
        function: &ast::FunctionDeclaration,
    ) -> FunctionId {
        let id = FunctionId::new(self.hir.functions.len());

        let binding = ctx.scopes.declare_global(function.name);
        self.function_bindings.insert(binding, id);

        let entry_scope = ctx.scopes.nest_scope_global();

        let (parameters, entry, bindings, blocks, exprs) = {
            let mut builder = FunctionBuilder::new(self);

            let parameters = function
                .params
                .iter()
                .map(|param| {
                    (
                        ctx.scopes.declare(entry_scope, param.name),
                        builder.ident_to_type(ctx, param.ty),
                    )
                })
                .collect();

            let entry = builder.lower_block(ctx, entry_scope, function.body);

            (
                parameters,
                entry,
                builder.bindings,
                builder.blocks,
                builder.exprs,
            )
        };

        self.hir.functions.push(Function {
            binding,
            parameters,
            return_ty: function
                .return_ty
                .map(|ty| self.ident_to_type(ctx, ty))
                .unwrap_or(Type::Unit),
            entry,
            bindings,
            blocks,
            exprs,
        });

        id
    }
}

#[derive(Debug)]
struct FunctionBuilder<'hir, 'ast> {
    builder: &'hir mut HirBuilder<'ast>,
    bindings: HashMap<BindingId, DeclarationTy>,
    blocks: Vec<Block>,
    exprs: Vec<Expr>,
}

impl<'hir, 'ast> FunctionBuilder<'hir, 'ast> {
    pub fn new(builder: &'hir mut HirBuilder<'ast>) -> Self {
        Self {
            builder,
            bindings: HashMap::new(),
            blocks: Vec::new(),
            exprs: Vec::new(),
        }
    }

    pub fn lower_block(
        &mut self,
        ctx: &mut Ctx,
        parent_scope: ScopeId,
        block: ast::BlockId,
    ) -> BlockId {
        let scope = ctx.scopes.nest_scope(parent_scope);
        let block = &self.ast[block];

        let mut builder = BlockBuilder::new(self);

        for statement in &block.statements {
            builder.lower_statement(ctx, scope, &builder.ast[*statement]);
        }

        let expr = match (
            block.expression,
            block
                .statements
                .last()
                .map(|statement| &builder.ast.statements[*statement]),
        ) {
            // Use the provided expression to end the block.
            (Some(expr), _) => builder.lower_expr(ctx, scope, expr),
            // Otherwise, if the final statement is `return` then add an unreachable marker.
            (None, Some(ast::Statement::Return(_))) => builder.add_expr(Expr::Unreachable),
            // Otherwise, assume unit.
            (None, _) => builder.unit_expression(),
        };

        builder.terminate(expr)
    }

    fn unit_expression(&mut self) -> ExprId {
        if let Some(expr) = self.unit_expression {
            return expr;
        }

        let expr = self.add_expr(Expr::Literal(Literal::Unit));
        *self.unit_expression.insert(expr)
    }

    fn add_expr(&mut self, expr: Expr) -> ExprId {
        let id = ExprId::new(self.exprs.len());
        self.exprs.push(expr);
        id
    }

    fn get_expr(&self, expr: ExprId) -> &Expr {
        &self.exprs[expr.0]
    }

    fn expr_as_block(&mut self, expr: ExprId) -> BlockId {
        if let Expr::Block(block_id) = self.get_expr(expr) {
            return *block_id;
        }

        BlockBuilder::new(self).terminate(expr)
    }
}

impl<'hir, 'ast> Deref for FunctionBuilder<'hir, 'ast> {
    type Target = HirBuilder<'ast>;

    fn deref(&self) -> &Self::Target {
        self.builder
    }
}

impl<'hir, 'ast> DerefMut for FunctionBuilder<'hir, 'ast> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.builder
    }
}

#[derive(Debug)]
struct BlockBuilder<'func, 'hir, 'ast> {
    builder: &'func mut FunctionBuilder<'hir, 'ast>,
    statements: Vec<Statement>,
}

impl<'func, 'hir, 'ast> BlockBuilder<'func, 'hir, 'ast> {
    pub fn new(builder: &'func mut FunctionBuilder<'hir, 'ast>) -> Self {
        Self {
            builder,
            statements: Vec::new(),
        }
    }

    fn add_statement(&mut self, statement: Statement) {
        self.statements.push(statement);
    }

    fn terminate(self, expr: ExprId) -> BlockId {
        let id = BlockId::new(self.builder.blocks.len());
        self.builder.blocks.push(Block {
            statements: self.statements,
            expr,
        });
        id
    }

    pub fn lower_statement(&mut self, ctx: &mut Ctx, scope: ScopeId, statement: &ast::Statement) {
        match statement {
            ast::Statement::Let(let_statement) => {
                let binding = ctx.scopes.declare(scope, let_statement.variable);
                let value = self.lower_expr(ctx, scope, let_statement.value);

                // TODO: Unsure when to create this, should optionally be annotated type.
                let ty = DeclarationTy::Inferred(value);
                self.bindings.insert(binding, ty.clone());
                self.add_statement(Statement::Declare(DeclareStatement { binding, ty }));

                let variable = self.add_expr(Expr::Variable(Variable { binding }));
                let expr = self.add_expr(Expr::Assign(Assign { variable, value }));
                self.add_statement(Statement::Expr(ExprStatement { expr }));
            }
            ast::Statement::Return(return_statement) => {
                let expr = self.lower_expr(ctx, scope, return_statement.expr);
                self.add_statement(Statement::Return(ReturnStatement { expr }));
            }
            ast::Statement::Expr(expr_statement) => {
                let expr = self.lower_expr(ctx, scope, expr_statement.expr);
                self.add_statement(Statement::Expr(ExprStatement { expr }));
            }
        }
    }

    pub fn lower_expr(&mut self, ctx: &mut Ctx, scope: ScopeId, expr_id: ast::ExprId) -> ExprId {
        let expr = &self.ast[expr_id];

        let expr = match expr {
            ast::Expr::Assign(assign) => self.lower_assign(ctx, scope, assign).into(),
            ast::Expr::Binary(binary) => self.lower_binary(ctx, scope, binary).into(),
            ast::Expr::Unary(unary) => self.lower_unary(ctx, scope, unary).into(),
            ast::Expr::If(if_expr) => self.lower_if(ctx, scope, if_expr).into(),
            ast::Expr::Literal(literal) => self.lower_literal(literal).into(),
            ast::Expr::Call(call) => self.lower_call(ctx, scope, call).into(),
            ast::Expr::Block(block) => self.lower_block(ctx, scope, *block).into(),
            ast::Expr::Variable(variable) => self.lower_variable(ctx, scope, variable).into(),
        };

        let id = self.add_expr(expr);

        self.expr_mapping.insert(expr_id, id);

        id
    }

    fn lower_assign(&mut self, ctx: &mut Ctx, scope: ScopeId, assign: &ast::Assign) -> Assign {
        Assign {
            variable: self.lower_expr(ctx, scope, assign.variable),
            value: self.lower_expr(ctx, scope, assign.value),
        }
    }

    fn lower_binary(&mut self, ctx: &mut Ctx, scope: ScopeId, binary: &ast::Binary) -> Binary {
        Binary {
            lhs: self.lower_expr(ctx, scope, binary.lhs),
            op: binary.op.clone(),
            rhs: self.lower_expr(ctx, scope, binary.rhs),
        }
    }

    fn lower_unary(&mut self, ctx: &mut Ctx, scope: ScopeId, unary: &ast::Unary) -> Unary {
        Unary {
            op: unary.op.clone(),
            value: self.lower_expr(ctx, scope, unary.value),
        }
    }

    fn lower_if(&mut self, ctx: &mut Ctx, scope: ScopeId, if_expr: &ast::If) -> Switch {
        // Where the switch will be built.
        let mut switch: Option<Switch> = None;
        // Optional default expression to apply to end of switch statements.
        let mut default = if_expr
            .otherwise
            .map(|otherwise| Expr::Block(self.lower_block(ctx, scope, otherwise)));

        for (condition, block) in if_expr.conditions.iter().rev() {
            switch = Some(Switch {
                discriminator: self.lower_expr(ctx, scope, *condition),
                branches: vec![(Literal::Boolean(true), self.lower_block(ctx, scope, *block))],
                // Try use the default expression.
                default: default
                    .take()
                    // Otherwise continue building the switch statement.
                    .or_else(|| Some(switch.take()?.into()))
                    .map(|expr| {
                        let expr = self.add_expr(expr);
                        self.expr_as_block(expr)
                    }),
            });
        }

        switch.expect("if expression with at least one block")
    }

    fn lower_literal(&mut self, literal: &ast::Literal) -> Literal {
        match literal {
            ast::Literal::Integer(value) => Literal::Integer(*value),
            ast::Literal::Boolean(value) => Literal::Boolean(*value),
            ast::Literal::Unit => Literal::Unit,
        }
    }

    fn lower_call(&mut self, ctx: &mut Ctx, scope: ScopeId, call: &ast::Call) -> Call {
        Call {
            callee: self.lower_expr(ctx, scope, call.callee),
            arguments: call
                .arguments
                .iter()
                .map(|argument| self.lower_expr(ctx, scope, *argument))
                .collect(),
        }
    }

    fn lower_variable(
        &mut self,
        ctx: &mut Ctx,
        scope: ScopeId,
        variable: &ast::Variable,
    ) -> Variable {
        Variable {
            binding: ctx.scopes.resolve(scope, variable.variable),
        }
    }
}

impl<'func, 'hir, 'ast> Deref for BlockBuilder<'func, 'hir, 'ast> {
    type Target = FunctionBuilder<'hir, 'ast>;

    fn deref(&self) -> &Self::Target {
        self.builder
    }
}

impl<'func, 'hir, 'ast> DerefMut for BlockBuilder<'func, 'hir, 'ast> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.builder
    }
}

pub fn lower(ctx: &mut Ctx, ast: &ast::Ast) -> Hir {
    HirBuilder::new(ast).build(ctx)
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
            // Empty block.
            ast::Block {
                statements: vec![],
                expression: None,
            },
            // Statement block.
            ast::Block {
                statements: vec![ast::StatementId::from_id(0)],
                expression: None,
            },
            // Expression block.
            ast::Block {
                statements: vec![],
                expression: Some(ast::ExprId::from_id(0)),
            },
            // Everything block.
            ast::Block {
                statements: vec![ast::StatementId::from_id(0)],
                expression: Some(ast::ExprId::from_id(0)),
            },
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

    #[fixture]
    fn builder(sample_ast: &'static ast::Ast) -> HirBuilder<'static> {
        HirBuilder::new(sample_ast)
    }

    #[rstest]
    #[case("block_empty", ast::BlockId::from_id(0))]
    #[case("block_statement", ast::BlockId::from_id(1))]
    #[case("block_expression", ast::BlockId::from_id(2))]
    #[case("block_everything", ast::BlockId::from_id(3))]
    fn lower_block(
        mut ctx: Ctx,
        mut builder: HirBuilder<'static>,
        #[case] name: &str,
        #[case] block: ast::BlockId,
    ) {
        let scope = ctx.scopes.nest_scope_global();
        let mut builder = FunctionBuilder::new(&mut builder);
        assert_debug_snapshot!(name, builder.lower_block(&mut ctx, scope, block));
    }

    mod expr {
        use super::*;

        #[rstest]
        #[case(
            "assign_simple",
            ast::Assign { variable: ast::ExprId::from_id(0), value: ast::ExprId::from_id(1) }
        )]
        #[case(
            "assign_reassign",
            ast::Assign { variable: ast::ExprId::from_id(0), value: ast::ExprId::from_id(0) }
        )]
        fn lower_assign(
            mut ctx: Ctx,
            mut builder: HirBuilder<'static>,
            #[case] name: &str,
            #[case] assign: ast::Assign,
        ) {
            let scope = ctx.scopes.nest_scope_global();
            let mut builder = FunctionBuilder::new(&mut builder);
            let mut builder = BlockBuilder::new(&mut builder);
            assert_debug_snapshot!(name, builder.lower_assign(&mut ctx, scope, &assign));
        }

        #[rstest]
        #[case(
            "binary_simple",
            ast::Binary{ lhs: ast::ExprId::from_id(0), op: cst::BinaryOp::Plus(tok::Plus), rhs: ast::ExprId::from_id(1) }
        )]
        fn lower_binary(
            mut ctx: Ctx,
            mut builder: HirBuilder<'static>,
            #[case] name: &str,
            #[case] binary: ast::Binary,
        ) {
            let scope = ctx.scopes.nest_scope_global();
            let mut builder = FunctionBuilder::new(&mut builder);
            let mut builder = BlockBuilder::new(&mut builder);
            assert_debug_snapshot!(name, builder.lower_binary(&mut ctx, scope, &binary));
        }

        #[rstest]
        #[case(
            "unary_simple",
            ast::Unary { value: ast::ExprId::from_id(0), op: cst::UnaryOp::Negative(tok::Minus) }
        )]
        fn lower_unary(
            mut ctx: Ctx,
            mut builder: HirBuilder<'static>,
            #[case] name: &str,
            #[case] unary: ast::Unary,
        ) {
            let scope = ctx.scopes.nest_scope_global();
            let mut builder = FunctionBuilder::new(&mut builder);
            let mut builder = BlockBuilder::new(&mut builder);
            assert_debug_snapshot!(name, builder.lower_unary(&mut ctx, scope, &unary));
        }

        #[rstest]
        #[case(
            "if_simple",
            ast::If { conditions: vec![(ast::ExprId::from_id(0), ast::BlockId::from_id(0))], otherwise: None }
        )]
        #[case(
            "if_else",
            ast::If { conditions: vec![(ast::ExprId::from_id(0), ast::BlockId::from_id(0))], otherwise: Some(ast::BlockId::from_id(1)) }
        )]
        #[case(
            "if_else_if",
            ast::If { conditions: vec![(ast::ExprId::from_id(0), ast::BlockId::from_id(0)), (ast::ExprId::from_id(1), ast::BlockId::from_id(1))], otherwise: None }
        )]
        fn lower_if(
            mut ctx: Ctx,
            mut builder: HirBuilder<'static>,
            #[case] name: &str,
            #[case] if_expr: ast::If,
        ) {
            let scope = ctx.scopes.nest_scope_global();
            let mut builder = FunctionBuilder::new(&mut builder);
            let mut builder = BlockBuilder::new(&mut builder);
            assert_debug_snapshot!(name, builder.lower_if(&mut ctx, scope, &if_expr));
        }

        #[rstest]
        #[case("literal_integer", ast::Literal::Integer(123))]
        #[case("literal_boolean", ast::Literal::Boolean(true))]
        #[case("literal_unit", ast::Literal::Unit)]
        fn lower_literal(
            mut builder: HirBuilder<'static>,
            #[case] name: &str,
            #[case] literal: ast::Literal,
        ) {
            let mut builder = FunctionBuilder::new(&mut builder);
            let mut builder = BlockBuilder::new(&mut builder);
            assert_debug_snapshot!(name, builder.lower_literal(&literal));
        }

        #[rstest]
        #[case("call_no_params", ast::Call { callee: ast::ExprId::from_id(0), arguments: vec![] })]
        #[case("call_with_params", ast::Call { callee: ast::ExprId::from_id(0), arguments: vec![ast::ExprId::from_id(1), ast::ExprId::from_id(2)] })]
        fn lower_call(
            mut ctx: Ctx,
            mut builder: HirBuilder<'static>,
            #[case] name: &str,
            #[case] call: ast::Call,
        ) {
            let scope = ctx.scopes.nest_scope_global();
            let mut builder = FunctionBuilder::new(&mut builder);
            let mut builder = BlockBuilder::new(&mut builder);
            assert_debug_snapshot!(name, builder.lower_call(&mut ctx, scope, &call));
        }

        #[rstest]
        #[case("variable_simple", ast::Variable { variable: StringId::from_id(0) })]
        fn lower_variable(
            mut ctx: Ctx,
            mut builder: HirBuilder<'static>,
            #[case] name: &str,
            #[case] variable: ast::Variable,
        ) {
            let scope = ctx.scopes.nest_scope_global();
            let mut builder = FunctionBuilder::new(&mut builder);
            let mut builder = BlockBuilder::new(&mut builder);
            assert_debug_snapshot!(name, builder.lower_variable(&mut ctx, scope, &variable));
        }
    }
}
