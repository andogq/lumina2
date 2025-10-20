use std::{
    collections::HashMap,
    ops::{Deref, DerefMut},
};

use crate::ir2::{
    ast::{self, StringId},
    hir::*,
};

#[derive(Clone, Debug)]
struct HirBuilder<'ast> {
    /// HIR that is being built.
    hir: Hir,
    /// Reference AST.
    ast: &'ast ast::Ast,

    /// Map of bindings to corresponding functions.
    function_bindings: HashMap<BindingId, FunctionId>,
    /// Scope information.
    scopes: Scopes,
    /// Cached unit expression.
    unit_expression: Option<ExprId>,
}

impl<'ast> HirBuilder<'ast> {
    pub fn new(ast: &'ast ast::Ast) -> Self {
        Self {
            hir: Hir {
                functions: Vec::new(),
                blocks: Vec::new(),
                exprs: Vec::new(),
            },
            ast,
            function_bindings: HashMap::new(),
            scopes: Scopes::new(),
            unit_expression: None,
        }
    }

    pub fn build(mut self) -> Hir {
        for function in &self.ast.function_declarations {
            self.lower_function(function);
        }

        self.hir
    }

    /// Helper to push a new scope, run a callback, then pop the scope.
    pub fn with_scope<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.scopes.push();
        let value = f(self);
        self.scopes.pop();
        value
    }

    pub fn lower_function(&mut self, function: &ast::FunctionDeclaration) -> FunctionId {
        let id = FunctionId::new(self.hir.functions.len());

        let binding = self.scopes.declare_binding(function.name);
        self.function_bindings.insert(binding, id);

        let (parameters, entry) = self.with_scope(|builder| {
            let parameters = function
                .params
                .iter()
                .map(|param| {
                    (
                        builder.scopes.declare_binding(param.name),
                        // TODO: This won't resolve built-in types.
                        builder.scopes.resolve_type_ref(param.ty),
                    )
                })
                .collect();

            let entry = builder.lower_block(function.body);

            (parameters, entry)
        });

        self.hir.functions.push(Function { parameters, entry });

        id
    }

    pub fn lower_block(&mut self, block: ast::BlockId) -> BlockId {
        let block = self.ast.get_block(block);

        self.with_scope(|builder| {
            let mut builder = BlockBuilder::new(builder);

            for statement in &block.statements {
                builder.lower_statement(statement);
            }

            let expr = block
                .expression
                .map(|expr| builder.lower_expr(expr))
                .unwrap_or_else(|| builder.unit_expression());

            builder.terminate(expr)
        })
    }

    fn unit_expression(&mut self) -> ExprId {
        if let Some(expr) = self.unit_expression {
            return expr;
        }

        let expr = self.add_expr(Expr::Literal(Literal::Unit));
        *self.unit_expression.insert(expr)
    }

    fn add_expr(&mut self, expr: Expr) -> ExprId {
        let id = ExprId::new(self.hir.exprs.len());
        self.hir.exprs.push(expr);
        id
    }

    fn expr_as_block(&mut self, expr: ExprId) -> BlockId {
        if let Expr::Block(block_id) = self.hir.get_expr(expr) {
            return *block_id;
        }

        BlockBuilder::new(self).terminate(expr)
    }

    fn block_as_expr(&mut self, block: BlockId) -> ExprId {
        let hir_block = self.hir.get_block(block);

        if hir_block.statements.is_empty() {
            hir_block.expr
        } else {
            self.add_expr(Expr::Block(block))
        }
    }
}

#[derive(Debug)]
struct BlockBuilder<'hir, 'ast> {
    builder: &'hir mut HirBuilder<'ast>,
    statements: Vec<Statement>,
}

impl<'hir, 'ast> BlockBuilder<'hir, 'ast> {
    pub fn new(builder: &'hir mut HirBuilder<'ast>) -> Self {
        Self {
            builder,
            statements: Vec::new(),
        }
    }

    fn add_statement(&mut self, statement: Statement) {
        self.statements.push(statement);
    }

    fn terminate(self, expr: ExprId) -> BlockId {
        let id = BlockId::new(self.builder.hir.blocks.len());
        self.builder.hir.blocks.push(Block {
            statements: self.statements,
            expr,
        });
        id
    }

    pub fn lower_statement(&mut self, statement: &ast::Statement) {
        match statement {
            ast::Statement::Let(let_statement) => {
                let binding = self.scopes.declare_binding(let_statement.variable);
                // TODO: Unsure when to create this, should optionally be annotated type.
                let ty = self.scopes.next_type_ref_id();
                self.add_statement(Statement::Declare(DeclareStatement { binding, ty }));

                let expr = self.lower_expr(let_statement.value);
                self.add_statement(Statement::Expr(ExprStatement { expr }));
            }
            ast::Statement::Return(return_statement) => {
                let expr = self.lower_expr(return_statement.expr);
                self.add_statement(Statement::Return(ReturnStatement { expr }));
            }
            ast::Statement::Expr(expr_statement) => {
                let expr = self.lower_expr(expr_statement.expr);
                self.add_statement(Statement::Expr(ExprStatement { expr }));
            }
        }
    }

    pub fn lower_expr(&mut self, expr: ast::ExprId) -> ExprId {
        let expr = self.ast.get_expr(expr);

        let expr = match expr {
            ast::Expr::Assign(assign) => self.lower_assign(assign).into(),
            ast::Expr::Binary(binary) => self.lower_binary(binary).into(),
            ast::Expr::Unary(unary) => self.lower_unary(unary).into(),
            ast::Expr::If(if_expr) => self.lower_if(if_expr).into(),
            ast::Expr::Literal(literal) => self.lower_literal(literal).into(),
            ast::Expr::Call(call) => self.lower_call(call).into(),
            ast::Expr::Block(block) => Expr::Block(self.lower_block(*block)),
            ast::Expr::Variable(variable) => Expr::Variable(Variable {
                binding: self.scopes.resolve_binding(variable.variable),
            }),
        };

        self.add_expr(expr)
    }

    fn lower_assign(&mut self, assign: &ast::Assign) -> Assign {
        Assign {
            variable: self.lower_expr(assign.variable),
            value: self.lower_expr(assign.value),
        }
    }

    fn lower_binary(&mut self, binary: &ast::Binary) -> Binary {
        Binary {
            lhs: self.lower_expr(binary.lhs),
            op: binary.op.clone(),
            rhs: self.lower_expr(binary.rhs),
        }
    }

    fn lower_unary(&mut self, unary: &ast::Unary) -> Unary {
        Unary {
            op: unary.op.clone(),
            value: self.lower_expr(unary.value),
        }
    }

    fn lower_if(&mut self, if_expr: &ast::If) -> Switch {
        // Where the switch will be built.
        let mut switch: Option<Switch> = None;
        // Optional default expression to apply to end of switch statements.
        let mut default = if_expr
            .otherwise
            .map(|otherwise| Expr::Block(self.lower_block(otherwise)));

        for (condition, block) in if_expr.conditions.iter().rev() {
            switch = Some(Switch {
                discriminator: self.lower_expr(*condition),
                branches: vec![(Literal::Boolean(true), self.lower_block(*block))],
                default: 
                // Try use the default expression.
                default .take()
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

    fn lower_call(&mut self, call: &ast::Call) -> Call {
        Call {
            callee: self.lower_expr(call.callee),
            arguments: call
                .arguments
                .iter()
                .map(|argument| self.lower_expr(*argument))
                .collect(),
        }
    }
}

impl<'hir, 'ast> Deref for BlockBuilder<'hir, 'ast> {
    type Target = HirBuilder<'ast>;

    fn deref(&self) -> &Self::Target {
        self.builder
    }
}

impl<'hir, 'ast> DerefMut for BlockBuilder<'hir, 'ast> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.builder
    }
}

pub fn lower(ast: &ast::Ast) -> Hir {
    HirBuilder::new(ast).build()
}

#[derive(Clone, Debug)]
struct Scope {
    bindings: HashMap<StringId, BindingId>,
    types: HashMap<StringId, TypeRefId>,
}

impl Scope {
    fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            types: HashMap::new(),
        }
    }
}

/// Structure to manage layered scopes.
#[derive(Clone, Debug)]
struct Scopes {
    global: Scope,
    scopes: Vec<Scope>,

    next_binding_id: usize,
    next_type_ref_id: usize,
}

impl Scopes {
    /// Create a new set of scopes.
    fn new() -> Self {
        Self {
            global: Scope::new(),
            scopes: Vec::new(),
            next_binding_id: 0,
            next_type_ref_id: 0,
        }
    }

    /// Push a new scope.
    fn push(&mut self) {
        self.scopes.push(Scope::new());
    }

    /// Pop the current scope.
    fn pop(&mut self) {
        assert!(!self.scopes.is_empty());
        self.scopes.pop();
    }

    /// Create the next [`BindingId`].
    fn next_binding_id(&mut self) -> BindingId {
        let id = self.next_binding_id;
        self.next_binding_id += 1;
        BindingId::new(id)
    }

    /// Create the next [`TypeRefId`].
    fn next_type_ref_id(&mut self) -> TypeRefId {
        let id = self.next_type_ref_id;
        self.next_type_ref_id += 1;
        TypeRefId::new(id)
    }

    /// Produce an iterator of each scope, starting with the inner-most, and ending with the global
    /// scope.
    fn iter(&self) -> impl Iterator<Item = &Scope> {
        self.scopes.iter().rev().chain([&self.global])
    }

    /// Return a reference to the current scope.
    fn current_ref(&self) -> &Scope {
        self.scopes.last().unwrap_or(&self.global)
    }

    /// Return a mutable reference to the current scope.
    fn current_mut(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap_or(&mut self.global)
    }

    /// Resolve the provided ident into a binding, searching from the inner-most scope outwards. If
    /// the binding is not found, an error will be thrown.
    fn resolve_binding(&self, ident: StringId) -> BindingId {
        *self
            .iter()
            .find_map(|scope| scope.bindings.get(&ident))
            .expect("binding declared in a scope")
    }

    /// Declare a binding in the current scope.
    fn declare_binding(&mut self, ident: StringId) -> BindingId {
        let binding = self.next_binding_id();
        self.current_mut().bindings.insert(ident, binding);
        binding
    }

    /// Resolve the provided ident into a type ref, searching form the inner-most scope outwards.
    /// If the binding is not found, an error will be thrown.
    fn resolve_type_ref(&self, ty: StringId) -> TypeRefId {
        *self
            .iter()
            .find_map(|scope| scope.types.get(&ty))
            .expect("type declared in a scope")
    }

    /// Declare a type ref in the current scope.
    fn declare_type_ref(&mut self, ty: StringId) -> TypeRefId {
        let type_ref = self.next_type_ref_id();
        self.current_mut().types.insert(ty, type_ref);
        type_ref
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::{ir2::cst, lex::tok};

    use insta::*;
    use rstest::*;

    mod scopes {
        use super::*;

        #[fixture]
        fn scopes() -> Scopes {
            Scopes::new()
        }

        #[fixture]
        fn string() -> StringId {
            StringId::new(0)
        }

        #[rstest]
        fn declare_and_resolve_binding(mut scopes: Scopes, string: StringId) {
            assert_eq!(
                scopes.declare_binding(string),
                scopes.resolve_binding(string),
                "resolved binding must be same as declared",
            );
        }

        #[rstest]
        fn declare_shadowing(mut scopes: Scopes, string: StringId) {
            assert_ne!(
                scopes.declare_binding(string),
                scopes.declare_binding(string),
                "re-declared binding must differ",
            );
        }

        #[rstest]
        fn scope_modification(mut scopes: Scopes, string: StringId) {
            let top_binding = scopes.declare_binding(string);
            assert_eq!(
                top_binding,
                scopes.resolve_binding(string),
                "binding should resolve to top scope"
            );

            scopes.push();
            assert_eq!(
                top_binding,
                scopes.resolve_binding(string),
                "binding should bubble to top scope",
            );

            let inner_binding = scopes.declare_binding(string);
            assert_ne!(
                top_binding, inner_binding,
                "bindings in different scopes must be different"
            );
            assert_eq!(
                inner_binding,
                scopes.resolve_binding(string),
                "binding should resolve to inner scope",
            );

            scopes.pop();
            assert_eq!(
                top_binding,
                scopes.resolve_binding(string),
                "binding should bubble to top scope after popping scope",
            );
        }
    }

    mod expr {
        use super::*;

        #[fixture]
        #[once]
        fn sample_ast() -> ast::Ast {
            let mut ast = ast::Ast::new();
            ast.expressions = vec![
                ast::Expr::Variable(ast::Variable { variable: StringId::new(0) }),
                ast::Expr::Variable(ast::Variable { variable: StringId::new(1) }),
                ast::Expr::Variable(ast::Variable { variable: StringId::new(2) }),
            ];
            ast.blocks = vec![
                ast::Block { statements: Vec::new(), expression: None },
                ast::Block { statements: Vec::new(), expression: None },
                ast::Block { statements: Vec::new(), expression: None },
            ];
            ast
        }

        #[fixture]
        fn builder(sample_ast: &'static ast::Ast) -> HirBuilder<'static> {
            let mut builder = HirBuilder::new(sample_ast);
            (0..3).for_each(|i|{
                builder.scopes.declare_binding(StringId::new(i));
            });
            builder
        }

        #[rstest]
        #[case(
            "assign_simple",
            ast::Assign { variable: ast::ExprId::new(0), value: ast::ExprId::new(1) }
        )]
        #[case(
            "assign_reassign",
            ast::Assign { variable: ast::ExprId::new(0), value: ast::ExprId::new(0) }
        )]
        fn lower_assign(
            mut builder: HirBuilder<'static>,
            #[case] name: &str,
            #[case] assign: ast::Assign,
        ) {
            let mut builder = BlockBuilder::new(&mut builder);
            assert_debug_snapshot!(name, builder.lower_assign(&assign));
        }

        #[rstest]
        #[case(
            "binary_simple",
            ast::Binary{ lhs: ast::ExprId::new(0), op: cst::BinaryOp::Plus(tok::Plus), rhs: ast::ExprId::new(1) }
        )]
        fn lower_binary(
            mut builder: HirBuilder<'static>,
            #[case] name: &str,
            #[case] binary: ast::Binary,
        ) {
            let mut builder = BlockBuilder::new(&mut builder);
            assert_debug_snapshot!(name, builder.lower_binary(&binary));
        }

        #[rstest]
        #[case(
            "unary_simple",
            ast::Unary { value: ast::ExprId::new(0), op: cst::UnaryOp::Negative(tok::Minus) }
        )]
        fn lower_unary(
            mut builder: HirBuilder<'static>,
            #[case] name: &str,
            #[case] unary: ast::Unary,
        ) {
            let mut builder = BlockBuilder::new(&mut builder);
            assert_debug_snapshot!(name, builder.lower_unary(&unary));
        }

        #[rstest]
        #[case(
            "if_simple",
            ast::If { conditions: vec![(ast::ExprId::new(0), ast::BlockId::new(0))], otherwise: None }
        )]
        #[case(
            "if_else",
            ast::If { conditions: vec![(ast::ExprId::new(0), ast::BlockId::new(0))], otherwise: Some(ast::BlockId::new(1)) }
        )]
        #[case(
            "if_else_if",
            ast::If { conditions: vec![(ast::ExprId::new(0), ast::BlockId::new(0)), (ast::ExprId::new(1), ast::BlockId::new(1))], otherwise: None }
        )]
        fn lower_if(
            mut builder: HirBuilder<'static>,
            #[case] name: &str,
            #[case] if_expr: ast::If,
        ) {
            let mut builder = BlockBuilder::new(&mut builder);
            assert_debug_snapshot!(name, builder.lower_if(&if_expr));
        }

        #[rstest]
        #[case("literal_integer", ast::Literal::Integer(123))]
        #[case("literal_boolean", ast::Literal::Boolean(true))]
        #[case("literal_unit", ast::Literal::Unit)]
        fn lower_literal(mut builder: HirBuilder<'static>, #[case] name: &str, #[case] literal: ast::Literal) {
            let mut builder = BlockBuilder::new(&mut builder);
            assert_debug_snapshot!(name, builder.lower_literal(&literal));
        }

        #[rstest]
        #[case("call_no_params", ast::Call { callee: ast::ExprId::new(0), arguments: vec![] })]
        #[case("call_with_params", ast::Call { callee: ast::ExprId::new(0), arguments: vec![ast::ExprId::new(1), ast::ExprId::new(2)] })]
        fn lower_call(mut builder: HirBuilder<'static>, #[case] name: &str, #[case] call: ast::Call) {
            let mut builder = BlockBuilder::new(&mut builder);
            assert_debug_snapshot!(name, builder.lower_call(&call));
        }
    }
}
