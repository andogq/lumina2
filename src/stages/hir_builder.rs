use std::{
    collections::HashMap,
    ops::{Deref, DerefMut},
};

use crate::ir2::{
    ast::{self, StringId},
    hir::*,
};

struct HirBuilder<'ast> {
    hir: Hir,

    ast: &'ast ast::Ast,

    function_bindings: HashMap<BindingId, FunctionId>,

    global_scope: Scope,
    scopes: Vec<Scope>,

    next_binding_id: usize,
    next_type_ref_id: usize,

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
            global_scope: Scope::new(),
            scopes: Vec::new(),
            next_binding_id: 0,
            next_type_ref_id: 0,
            unit_expression: None,
        }
    }

    pub fn build(mut self) -> Hir {
        for function in &self.ast.function_declarations {
            self.lower_function(function);
        }

        self.hir
    }

    fn iter_scopes(&self) -> impl Iterator<Item = &Scope> {
        [&self.global_scope].into_iter().chain(self.scopes.iter())
    }

    fn current_scope(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap_or(&mut self.global_scope)
    }

    fn with_scope<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.scopes.push(Scope::new());

        let value = f(self);

        assert!(!self.scopes.is_empty());
        self.scopes.pop();

        value
    }

    fn resolve_binding(&self, ident: StringId) -> BindingId {
        *self
            .iter_scopes()
            .find_map(|scope| scope.bindings.get(&ident))
            .expect("binding declared in scope")
    }

    fn declare_binding(&mut self, ident: StringId) -> BindingId {
        let binding = self.new_binding_id();
        self.current_scope().bindings.insert(ident, binding);
        binding
    }

    fn new_binding_id(&mut self) -> BindingId {
        let id = BindingId::new(self.next_binding_id);
        self.next_binding_id += 1;
        id
    }

    fn resolve_type_ref(&self, id: StringId) -> TypeRefId {
        *self
            .iter_scopes()
            .find_map(|scope| scope.types.get(&id))
            .expect("type ref declared in scope")
    }

    fn declare_type_ref(&mut self, id: StringId) -> TypeRefId {
        let type_ref = self.new_type_ref_id();
        self.current_scope().types.insert(id, type_ref);
        type_ref
    }

    fn new_type_ref_id(&mut self) -> TypeRefId {
        let id = TypeRefId::new(self.next_type_ref_id);
        self.next_type_ref_id += 1;
        id
    }

    pub fn lower_function(&mut self, function: &ast::FunctionDeclaration) -> FunctionId {
        let id = FunctionId::new(self.hir.functions.len());

        let binding = self.declare_binding(function.name);
        self.function_bindings.insert(binding, id);

        let (parameters, entry) = self.with_scope(|builder| {
            let parameters = function
                .params
                .iter()
                .map(|param| {
                    (
                        builder.declare_binding(param.name),
                        // TODO: This won't resolve built-in types.
                        builder.resolve_type_ref(param.ty),
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
                let binding = self.declare_binding(let_statement.variable);
                // TODO: Unsure when to create this.
                let ty = self.new_type_ref_id();
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
            ast::Expr::Assign(assign) => Expr::Assign(Assign {
                variable: self.lower_expr(assign.variable),
                value: self.lower_expr(assign.value),
            }),
            ast::Expr::Binary(binary) => Expr::Binary(Binary {
                lhs: self.lower_expr(binary.lhs),
                op: binary.op.clone(),
                rhs: self.lower_expr(binary.rhs),
            }),
            ast::Expr::Unary(unary) => Expr::Unary(Unary {
                op: unary.op.clone(),
                value: self.lower_expr(unary.value),
            }),
            ast::Expr::If(if_expr) => {
                let mut expr = if_expr
                    .otherwise
                    .map(|otherwise| Expr::Block(self.lower_block(otherwise)));

                for (condition, block) in if_expr.conditions.iter().rev() {
                    let switch = Expr::Switch(Switch {
                        discriminator: self.lower_expr(*condition),
                        branches: vec![(Literal::Boolean(true), self.lower_block(*block))],
                        default: expr.take().map(|expr| {
                            let expr = self.add_expr(expr);
                            self.expr_as_block(expr)
                        }),
                    });
                    expr = Some(switch);
                }

                expr.expect("if expression with at least one block")
            }
            ast::Expr::Literal(literal) => Expr::Literal(match literal {
                ast::Literal::Integer(value) => Literal::Integer(*value),
                ast::Literal::Boolean(value) => Literal::Boolean(*value),
                ast::Literal::Unit => Literal::Unit,
            }),
            ast::Expr::Call(call) => Expr::Call(Call {
                callee: self.lower_expr(call.callee),
                arguments: call
                    .arguments
                    .iter()
                    .map(|argument| self.lower_expr(*argument))
                    .collect(),
            }),
            ast::Expr::Block(block) => Expr::Block(self.lower_block(*block)),
            ast::Expr::Variable(variable) => Expr::Variable(Variable {
                binding: self.resolve_binding(variable.variable),
            }),
        };

        self.add_expr(expr)
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
