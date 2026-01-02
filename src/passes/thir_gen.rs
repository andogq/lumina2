use crate::{
    ir::cst::{BinaryOp, UnaryOp},
    prelude::{thir::Thir, *},
    ty::{Constraint, IntegerKind, solver::Solver},
};

use hir::*;

/// Generator to build a collection of [`Constraint`]s, then solve them to produce a [`Thir`].
pub struct ThirGen<'ctx, 'hir> {
    /// Context used throughout this pass.
    ctx: &'ctx mut Ctx,
    /// HIR that will be processed.
    hir: &'hir Hir,
    /// Constraints collected while walking the HIR.
    constraints: Vec<(TypeVarId, Constraint)>,
    /// Errors generated throughout this pass.
    errors: Vec<CErrorId>,
}

impl<'ctx, 'hir> Pass<'ctx, 'hir> for ThirGen<'ctx, 'hir> {
    type Input = hir::Hir;
    type Output = Thir<'hir>;
    type Extra = ();

    fn run(ctx: &'ctx mut Ctx, hir: &'hir Self::Input, _extra: ()) -> PassResult<Self::Output> {
        let mut thir_gen = Self::new(ctx, hir);

        // Declare all functions up front.
        for function in thir_gen.hir.functions.iter_keys() {
            thir_gen.add_function_declaration(function);
        }

        // Lower each function.
        for function in thir_gen.hir.functions.iter_keys() {
            thir_gen.add_function_constraints(function);
        }

        // Run the solver.
        let types = Solver::run(&thir_gen.constraints);

        Ok(PassSuccess::new(Thir { hir, types }, thir_gen.errors))
    }
}

impl<'ctx, 'hir> ThirGen<'ctx, 'hir> {
    pub fn new(ctx: &'ctx mut Ctx, hir: &'hir Hir) -> Self {
        Self {
            ctx,
            hir,
            constraints: Vec::new(),
            errors: Vec::new(),
        }
    }

    fn add_function_declaration(&mut self, function_id: FunctionId) {
        let function = &self.hir[function_id];
        self.constraints.push((
            TypeVarId::Binding(function.binding),
            Constraint::Eq(
                Type::Function {
                    params: function
                        .parameters
                        .iter()
                        .map(|(_, ty)| ty.clone())
                        .collect(),
                    ret_ty: Box::new(function.return_ty.clone()),
                }
                .into(),
            ),
        ));
    }

    fn add_function_constraints(&mut self, function_id: FunctionId) {
        let function = &self.hir[function_id];

        // Add constraints for the function parameters.
        for (parameter_binding, parameter_ty) in &function.parameters {
            self.constraints.push((
                (*parameter_binding).into(),
                Constraint::Eq(parameter_ty.clone().into()),
            ));
        }

        // Add constraint for the function return type (the body of the function must result in the
        // return type).
        self.constraints.push((
            self.hir[function.entry].expr.into(),
            Constraint::Eq(function.return_ty.clone().into()),
        ));

        let ctx = ConstraintCtx::new(function_id);
        self.add_block_constraints(&ctx, function.entry);
    }

    fn add_block_constraints(&mut self, ctx: &ConstraintCtx, block_id: BlockId) {
        let block = &self.hir[block_id];

        for statement in &block.statements {
            match &self.hir[*statement] {
                Statement::Declare(DeclareStatement { binding, ty }) => self.constraints.push((
                    (*binding).into(),
                    match ty {
                        // Directly set variable type.
                        DeclarationTy::Type(ty) => Constraint::Eq(ty.clone().into()),
                        // Infer variable's type from the provided expression.
                        DeclarationTy::Inferred(expr) => Constraint::Eq((*expr).into()),
                    },
                )),
                // Expression must equal the return type of the current function.
                Statement::Return(ReturnStatement { expr }) => self.constraints.push((
                    (*expr).into(),
                    Constraint::Eq(self.hir[ctx.function].return_ty.clone().into()),
                )),
                Statement::Break(BreakStatement { expr }) => match ctx.loops.last() {
                    // Break expression must match the expression of the inner most loop.
                    Some(current_loop) => self
                        .constraints
                        .push(((*expr).into(), Constraint::Eq((*current_loop).into()))),
                    // Not currently in a loop, so report that it's invalid, and continue
                    // generating constraints.
                    None => self
                        .errors
                        .push(self.ctx.errors.report(ThirGenError::InvalidBreak)),
                },
                Statement::Expr(ExprStatement { expr }) => self.add_expr_constraints(ctx, *expr),
            }
        }

        self.add_expr_constraints(ctx, block.expr);
    }

    fn add_expr_constraints(&mut self, ctx: &ConstraintCtx, expr_id: ExprId) {
        let expr = &self.hir[expr_id];

        match expr {
            Expr::Assign(Assign { variable, value }) => {
                self.constraints.extend([
                    // Value of the assignment must match the variable it's being assigned to.
                    ((*value).into(), Constraint::Eq((*variable).into())),
                    // The actual assignment expression results in unit.
                    (expr_id.into(), Constraint::Eq(Type::Unit.into())),
                ]);

                self.add_expr_constraints(ctx, *variable);
                self.add_expr_constraints(ctx, *value);
            }
            Expr::Binary(Binary { lhs, op, rhs }) => {
                self.add_expr_constraints(ctx, *lhs);
                self.add_expr_constraints(ctx, *rhs);

                match op {
                    BinaryOp::Plus(_)
                    | BinaryOp::Minus(_)
                    | BinaryOp::Multiply(_)
                    | BinaryOp::Divide(_)
                    | BinaryOp::BinaryAnd(_)
                    | BinaryOp::BinaryOr(_) => {
                        self.constraints.extend([
                            // Operands must equal each other.
                            ((*lhs).into(), Constraint::Eq((*rhs).into())),
                            // Operands should be integers.
                            ((*lhs).into(), Constraint::Integer(IntegerKind::Any)),
                            ((*rhs).into(), Constraint::Integer(IntegerKind::Any)),
                            // Result is the same as the input.
                            (expr_id.into(), Constraint::Eq((*lhs).into())),
                        ]);
                    }
                    BinaryOp::Equal(_) | BinaryOp::NotEqual(_) => {
                        self.constraints.extend([
                            // Operands must be identical
                            ((*lhs).into(), Constraint::Eq((*rhs).into())),
                            // Results in a boolean.
                            (expr_id.into(), Constraint::Eq(Type::Boolean.into())),
                        ]);
                    }
                    BinaryOp::Greater(_)
                    | BinaryOp::GreaterEqual(_)
                    | BinaryOp::Less(_)
                    | BinaryOp::LessEqual(_) => {
                        self.constraints.extend([
                            // Operands must be identical
                            ((*lhs).into(), Constraint::Eq((*rhs).into())),
                            // Operands should be integers.
                            // TODO: Probably should check they are ordinals.
                            ((*lhs).into(), Constraint::Integer(IntegerKind::Any)),
                            ((*rhs).into(), Constraint::Integer(IntegerKind::Any)),
                            // Results in a boolean.
                            (expr_id.into(), Constraint::Eq(Type::Boolean.into())),
                        ]);
                    }
                    BinaryOp::LogicalAnd(_) | BinaryOp::LogicalOr(_) => {
                        self.constraints.extend([
                            // Operands must be booleans.
                            ((*lhs).into(), Constraint::Eq(Type::Boolean.into())),
                            ((*rhs).into(), Constraint::Eq(Type::Boolean.into())),
                            // Results in a boolean.
                            (expr_id.into(), Constraint::Eq(Type::Boolean.into())),
                        ]);
                    }
                }
            }
            Expr::Unary(Unary { op, value }) => {
                self.add_expr_constraints(ctx, *value);

                match op {
                    UnaryOp::Not(_) => {
                        self.constraints.extend([
                            // Output is same as input.
                            (expr_id.into(), Constraint::Eq((*value).into())),
                            // Operand can be any integer.
                            ((*value).into(), Constraint::Integer(IntegerKind::Any)),
                        ]);
                    }
                    UnaryOp::Negative(_) => {
                        self.constraints.extend([
                            // Output is same as input.
                            (expr_id.into(), Constraint::Eq((*value).into())),
                            // Operand can be any integer.
                            ((*value).into(), Constraint::Integer(IntegerKind::Signed)),
                        ]);
                    }
                    UnaryOp::Deref(_) => {
                        // Make sure that operand is a pointer, and output is inner type of pointer.
                        self.constraints
                            .push(((*value).into(), Constraint::Reference(expr_id.into())));
                    }
                    UnaryOp::Ref(_) => self
                        .constraints
                        .push((expr_id.into(), Constraint::Reference((*value).into()))),
                }
            }
            Expr::Switch(Switch {
                discriminator,
                branches,
                default,
            }) => {
                self.add_expr_constraints(ctx, *discriminator);
                for (_, branch) in branches {
                    self.add_block_constraints(ctx, *branch);
                }
                if let Some(default) = default {
                    self.add_block_constraints(ctx, *default);
                }

                self.constraints
                    .extend(branches.iter().flat_map(|(literal, block)| {
                        [
                            // Branch literal must match discriminator.
                            ((*discriminator).into(), constraint_from_literal(literal)),
                            // Block which is resolved must match this expression.
                            (self.hir[*block].expr.into(), Constraint::Eq(expr_id.into())),
                        ]
                    }));

                // Ensure the default branch matches the expression, or unit if there is no default branch.
                // TODO: This does not handle branches which are exhaustive.
                self.constraints.push((
                    expr_id.into(),
                    Constraint::Eq(match default {
                        Some(default) => self.hir[*default].expr.into(),
                        None => Type::Unit.into(),
                    }),
                ));
            }
            Expr::Loop(Loop { body }) => {
                // Ensure the body of the loop doesn't yield any non-unit expressions.
                self.constraints.push((
                    self.hir[*body].expr.into(),
                    Constraint::Eq(Type::Unit.into()),
                ));

                // Create a new ctx for generating constraints for the body.
                let ctx = ctx.push_loop(expr_id);
                self.add_block_constraints(&ctx, *body);
            }
            Expr::Literal(literal) => self
                .constraints
                .push((expr_id.into(), constraint_from_literal(literal))),
            Expr::Call(Call { callee, arguments }) => {
                self.add_expr_constraints(ctx, *callee);
                for argument in arguments {
                    self.add_expr_constraints(ctx, *argument);
                }

                self.constraints.push((
                    (*callee).into(),
                    Constraint::Function {
                        params: arguments.iter().map(|arg| (*arg).into()).collect(),
                        ret_ty: expr_id.into(),
                    },
                ));
            }
            Expr::Block(block_id) => {
                self.add_block_constraints(ctx, *block_id);

                // Type of this expression will be the type of the block.
                self.constraints.push((
                    expr_id.into(),
                    Constraint::Eq(self.hir[*block_id].expr.into()),
                ));
            }
            Expr::Variable(Variable { binding }) => self
                .constraints
                .push((expr_id.into(), Constraint::Eq((*binding).into()))),
            Expr::Unreachable => self
                .constraints
                .push((expr_id.into(), Constraint::Eq(Type::Never.into()))),
        }
    }
}

fn constraint_from_literal(literal: &Literal) -> Constraint {
    match literal {
        Literal::Integer(_) => Constraint::Integer(IntegerKind::Any),
        Literal::Boolean(_) => Constraint::Eq(Type::Boolean.into()),
        Literal::Unit => Constraint::Eq(Type::Unit.into()),
    }
}

/// Context required when building constraints.
#[derive(Clone, Debug)]
struct ConstraintCtx {
    /// Current function which constraints are being produced for.
    function: FunctionId,
    /// Track nested loop expressions.
    loops: Vec<ExprId>,
}

impl ConstraintCtx {
    /// Create a new context with the provided function.
    pub fn new(function: FunctionId) -> Self {
        Self {
            function,
            loops: Vec::new(),
        }
    }

    /// Push a new loop to the context, returning a new instance..
    pub fn push_loop(&self, loop_expr: ExprId) -> Self {
        let mut ctx = self.clone();
        ctx.loops.push(loop_expr);
        ctx
    }
}

#[derive(Clone, Debug, thiserror::Error)]
pub enum ThirGenError {
    #[error("`break` statement encountered outside of a `loop`")]
    InvalidBreak,
}

#[cfg(test)]
mod test {
    use super::*;

    #[fixture]
    fn hir() -> Hir {
        Hir {
            functions: indexed_vec![],
            blocks: indexed_vec![],
            statements: indexed_vec![],
            exprs: indexed_vec![Expr::Literal(Literal::Unit),],
        }
    }

    #[fixture]
    fn ctx() -> Ctx {
        Ctx::new()
    }

    #[fixture]
    fn constraint_ctx() -> ConstraintCtx {
        ConstraintCtx {
            function: FunctionId::from_id(0),
            loops: Vec::new(),
        }
    }

    #[rstest]
    #[case("simple", [], Type::Unit)]
    #[case("return int", [], Type::I8)]
    #[case("params", [(BindingId::from_id(1), Type::I8), (BindingId::from_id(2), Type::Boolean)], Type::Boolean)]
    fn function_declaration(
        mut hir: Hir,
        mut ctx: Ctx,
        #[case] name: &str,
        #[case] params: impl IntoIterator<Item = (BindingId, Type)>,
        #[case] return_ty: Type,
    ) {
        let function = Function {
            binding: BindingId::from_id(0),
            parameters: params.into_iter().collect(),
            return_ty,
            entry: BlockId::from_id(0),
            blocks: vec![],
            statements: vec![],
            expressions: vec![],
        };

        // Used for debugging.
        let signature_str = format!("{:?} => {:?}", function.parameters, function.return_ty);

        let function_id = hir.functions.insert(function);

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_function_declaration(function_id);
        assert_debug_snapshot!(name, pass.constraints, &signature_str);
        assert!(pass.errors.is_empty());
    }

    #[rstest]
    #[case("inferred", DeclarationTy::Inferred(ExprId::from_id(0)))]
    #[case("with unit", DeclarationTy::Type(Type::Unit))]
    #[case("with type", DeclarationTy::Type(Type::I8))]
    fn variable_declaration(
        mut hir: Hir,
        mut ctx: Ctx,
        constraint_ctx: ConstraintCtx,
        #[case] name: &str,
        #[case] ty: DeclarationTy,
    ) {
        let statement = hir.statements.insert(Statement::Declare(DeclareStatement {
            binding: BindingId::from_id(0),
            ty: ty.clone(),
        }));
        let block = hir.blocks.insert(Block {
            statements: vec![statement],
            expr: ExprId::from_id(0),
        });

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_block_constraints(&constraint_ctx, block);
        assert_debug_snapshot!(name, pass.constraints, &format!("{ty:?}"));
        assert!(pass.errors.is_empty());
    }

    #[rstest]
    #[case("assign", Assign { variable: ExprId::from_id(0), value: ExprId::from_id(0) })]
    #[case(
        "plus",
        Binary {
            lhs: ExprId::from_id(0),
            op: BinaryOp::Plus(tok::Plus),
            rhs: ExprId::from_id(0),
        },
    )]
    #[case(
        "logical and",
        Binary {
            lhs: ExprId::from_id(0),
            op: BinaryOp::LogicalAnd(tok::AmpAmp),
            rhs: ExprId::from_id(0),
        },
    )]
    #[case(
        "equal",
        Binary {
            lhs: ExprId::from_id(0),
            op: BinaryOp::Equal(tok::EqEq),
            rhs: ExprId::from_id(0),
        },
    )]
    #[case(
        "greater",
        Binary {
            lhs: ExprId::from_id(0),
            op: BinaryOp::Greater(tok::RAngle),
            rhs: ExprId::from_id(0),
        },
    )]
    #[case("negative", Unary { op: UnaryOp::Negative(tok::Minus), value: ExprId::from_id(0) })]
    fn expr_constraint(
        mut hir: Hir,
        mut ctx: Ctx,
        constraint_ctx: ConstraintCtx,
        #[case] name: &str,
        #[case] expr: impl Into<Expr> + Debug,
    ) {
        let dbg_str = format!("{expr:?}");
        let expr_id = hir.exprs.insert(expr.into());

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_expr_constraints(&constraint_ctx, expr_id);
        assert_debug_snapshot!(name, pass.constraints, &dbg_str);
        assert!(pass.errors.is_empty());
    }
}
