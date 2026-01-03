use crate::prelude::*;

use crate::ty::{Constraint, IntegerKind, solver::Solver};

use hir::*;
use thir::Thir;

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

        Ok(PassSuccess::new(Thir::new(hir, types), thir_gen.errors))
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
                    parameters: function
                        .parameters
                        .iter()
                        .map(|(_, ty)| ty.clone())
                        .collect(),
                    return_ty: Box::new(function.return_ty.clone()),
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
            self.hir[function.entry].expression.into(),
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
                        DeclarationTy::Inferred(expression) => Constraint::Eq((*expression).into()),
                    },
                )),
                // Expression must equal the return type of the current function.
                Statement::Return(ReturnStatement { expression }) => {
                    // Generate constraints for the return expression.
                    self.add_expression_constraints(ctx, *expression);

                    // Ensure the return expression matches the function return type.
                    self.constraints.push((
                        (*expression).into(),
                        Constraint::Eq(self.hir[ctx.function].return_ty.clone().into()),
                    ));
                }
                Statement::Break(BreakStatement { expression }) => {
                    // Generate constraints for the break expression.
                    self.add_expression_constraints(ctx, *expression);

                    match ctx.loops.last() {
                        // Break expression must match the expression of the inner most loop.
                        Some(current_loop) => self
                            .constraints
                            .push(((*expression).into(), Constraint::Eq((*current_loop).into()))),
                        // Not currently in a loop, so report that it's invalid, and continue
                        // generating constraints.
                        None => self
                            .errors
                            .push(self.ctx.errors.report(ThirGenError::InvalidBreak)),
                    }
                }
                Statement::Expression(ExpressionStatement { expression }) => {
                    self.add_expression_constraints(ctx, *expression)
                }
            }
        }

        self.add_expression_constraints(ctx, block.expression);
    }

    fn add_expression_constraints(&mut self, ctx: &ConstraintCtx, expression_id: ExpressionId) {
        let expression = &self.hir[expression_id];

        match expression {
            Expression::Assign(Assign { variable, value }) => {
                self.constraints.extend([
                    // Value of the assignment must match the variable it's being assigned to.
                    ((*value).into(), Constraint::Eq((*variable).into())),
                    // The actual assignment expression results in unit.
                    (expression_id.into(), Constraint::Eq(Type::Unit.into())),
                ]);

                self.add_expression_constraints(ctx, *variable);
                self.add_expression_constraints(ctx, *value);
            }
            Expression::Binary(Binary {
                lhs,
                operation,
                rhs,
            }) => {
                self.add_expression_constraints(ctx, *lhs);
                self.add_expression_constraints(ctx, *rhs);

                match operation {
                    BinaryOperation::Plus
                    | BinaryOperation::Minus
                    | BinaryOperation::Multiply
                    | BinaryOperation::Divide
                    | BinaryOperation::BinaryAnd
                    | BinaryOperation::BinaryOr => {
                        self.constraints.extend([
                            // Operands must equal each other.
                            ((*lhs).into(), Constraint::Eq((*rhs).into())),
                            // Operands should be integers.
                            ((*lhs).into(), Constraint::Integer(IntegerKind::Any)),
                            ((*rhs).into(), Constraint::Integer(IntegerKind::Any)),
                            // Result is the same as the input.
                            (expression_id.into(), Constraint::Eq((*lhs).into())),
                        ]);
                    }
                    BinaryOperation::Equal | BinaryOperation::NotEqual => {
                        self.constraints.extend([
                            // Operands must be identical
                            ((*lhs).into(), Constraint::Eq((*rhs).into())),
                            // Results in a boolean.
                            (expression_id.into(), Constraint::Eq(Type::Boolean.into())),
                        ]);
                    }
                    BinaryOperation::Greater
                    | BinaryOperation::GreaterEqual
                    | BinaryOperation::Less
                    | BinaryOperation::LessEqual => {
                        self.constraints.extend([
                            // Operands must be identical
                            ((*lhs).into(), Constraint::Eq((*rhs).into())),
                            // Operands should be integers.
                            // TODO: Probably should check they are ordinals.
                            ((*lhs).into(), Constraint::Integer(IntegerKind::Any)),
                            ((*rhs).into(), Constraint::Integer(IntegerKind::Any)),
                            // Results in a boolean.
                            (expression_id.into(), Constraint::Eq(Type::Boolean.into())),
                        ]);
                    }
                    BinaryOperation::LogicalAnd | BinaryOperation::LogicalOr => {
                        self.constraints.extend([
                            // Operands must be booleans.
                            ((*lhs).into(), Constraint::Eq(Type::Boolean.into())),
                            ((*rhs).into(), Constraint::Eq(Type::Boolean.into())),
                            // Results in a boolean.
                            (expression_id.into(), Constraint::Eq(Type::Boolean.into())),
                        ]);
                    }
                }
            }
            Expression::Unary(Unary { operation, value }) => {
                self.add_expression_constraints(ctx, *value);

                match operation {
                    UnaryOperation::Not => {
                        self.constraints.extend([
                            // Output is same as input.
                            (expression_id.into(), Constraint::Eq((*value).into())),
                            // Operand can be any integer.
                            ((*value).into(), Constraint::Integer(IntegerKind::Any)),
                        ]);
                    }
                    UnaryOperation::Negative => {
                        self.constraints.extend([
                            // Output is same as input.
                            (expression_id.into(), Constraint::Eq((*value).into())),
                            // Operand can be any integer.
                            ((*value).into(), Constraint::Integer(IntegerKind::Signed)),
                        ]);
                    }
                    UnaryOperation::Deref => {
                        // Make sure that operand is a pointer, and output is inner type of pointer.
                        self.constraints
                            .push(((*value).into(), Constraint::Reference(expression_id.into())));
                    }
                    UnaryOperation::Ref => self
                        .constraints
                        .push((expression_id.into(), Constraint::Reference((*value).into()))),
                }
            }
            Expression::Switch(Switch {
                discriminator,
                branches,
                default,
            }) => {
                self.add_expression_constraints(ctx, *discriminator);
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
                            (
                                self.hir[*block].expression.into(),
                                Constraint::Eq(expression_id.into()),
                            ),
                        ]
                    }));

                // Ensure the default branch matches the expression, or unit if there is no default branch.
                // TODO: This does not handle branches which are exhaustive.
                self.constraints.push((
                    expression_id.into(),
                    Constraint::Eq(match default {
                        Some(default) => self.hir[*default].expression.into(),
                        None => Type::Unit.into(),
                    }),
                ));
            }
            Expression::Loop(Loop { body }) => {
                // Ensure the body of the loop doesn't yield any non-unit expressions.
                self.constraints.push((
                    self.hir[*body].expression.into(),
                    Constraint::Eq(Type::Unit.into()),
                ));

                // Create a new ctx for generating constraints for the body.
                let ctx = ctx.push_loop(expression_id);
                self.add_block_constraints(&ctx, *body);
            }
            Expression::Literal(literal) => self
                .constraints
                .push((expression_id.into(), constraint_from_literal(literal))),
            Expression::Call(Call { callee, arguments }) => {
                self.add_expression_constraints(ctx, *callee);
                for argument in arguments {
                    self.add_expression_constraints(ctx, *argument);
                }

                self.constraints.push((
                    (*callee).into(),
                    Constraint::Function {
                        parameters: arguments
                            .iter()
                            .map(|argument| (*argument).into())
                            .collect(),
                        return_ty: expression_id.into(),
                    },
                ));
            }
            Expression::Block(block_id) => {
                self.add_block_constraints(ctx, *block_id);

                // Type of this expression will be the type of the block.
                self.constraints.push((
                    expression_id.into(),
                    Constraint::Eq(self.hir[*block_id].expression.into()),
                ));
            }
            Expression::Variable(Variable { binding }) => self
                .constraints
                .push((expression_id.into(), Constraint::Eq((*binding).into()))),
            Expression::Unreachable => self
                .constraints
                .push((expression_id.into(), Constraint::Eq(Type::Never.into()))),
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
    loops: Vec<ExpressionId>,
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
    pub fn push_loop(&self, loop_expression: ExpressionId) -> Self {
        let mut ctx = self.clone();
        ctx.loops.push(loop_expression);
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
            expressions: indexed_vec![Expression::Literal(Literal::Unit),],
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
    #[case("return integer", [], Type::I8)]
    #[case("parameters", [(BindingId::from_id(1), Type::I8), (BindingId::from_id(2), Type::Boolean)], Type::Boolean)]
    fn function_declaration(
        mut hir: Hir,
        mut ctx: Ctx,
        #[case] name: &str,
        #[case] parameters: impl IntoIterator<Item = (BindingId, Type)>,
        #[case] return_ty: Type,
    ) {
        let function = Function {
            binding: BindingId::from_id(0),
            parameters: parameters.into_iter().collect(),
            return_ty,
            entry: BlockId::from_id(0),
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
    #[case("inferred", DeclarationTy::Inferred(ExpressionId::from_id(0)))]
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
            expression: ExpressionId::from_id(0),
        });

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_block_constraints(&constraint_ctx, block);
        assert_debug_snapshot!(name, pass.constraints, &format!("{ty:?}"));
        assert!(pass.errors.is_empty());
    }

    #[rstest]
    fn return_statement(mut hir: Hir, mut ctx: Ctx, constraint_ctx: ConstraintCtx) {
        let expression = hir
            .expressions
            .insert(Expression::Literal(Literal::Integer(123)));
        let statement = hir
            .statements
            .insert(Statement::Return(ReturnStatement { expression }));
        let block = hir.blocks.insert(Block {
            statements: vec![statement],
            expression: ExpressionId::from_id(0),
        });

        // Insert a fake function to pull the return type.
        hir.functions.insert(Function {
            binding: BindingId::from_id(0),
            parameters: Vec::new(),
            return_ty: Type::U8,
            entry: block,
        });

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_block_constraints(&constraint_ctx, block);
        assert_debug_snapshot!("return_statement", pass.constraints);
        assert!(pass.errors.is_empty());
    }

    #[rstest]
    #[case("single loop", [ExpressionId::from_id(1)])]
    #[case("deep loop", [ExpressionId::from_id(1), ExpressionId::from_id(2),ExpressionId::from_id(3)])]
    fn break_statement(
        mut hir: Hir,
        mut ctx: Ctx,
        mut constraint_ctx: ConstraintCtx,
        #[case] name: &str,
        #[case] loops: impl IntoIterator<Item = ExpressionId>,
    ) {
        constraint_ctx.loops = Vec::from_iter(loops);

        // Add some dummy expressions for the loops.
        (0..3).for_each(|_| {
            hir.expressions.insert(Expression::Unreachable);
        });

        let expression = hir
            .expressions
            .insert(Expression::Literal(Literal::Integer(123)));
        let statement = hir
            .statements
            .insert(Statement::Break(BreakStatement { expression }));
        let block = hir.blocks.insert(Block {
            statements: vec![statement],
            expression: ExpressionId::from_id(0),
        });

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_block_constraints(&constraint_ctx, block);
        assert_debug_snapshot!(name, pass.constraints);
        assert!(pass.errors.is_empty());
    }

    #[rstest]
    fn break_statement_no_loop(mut hir: Hir, mut ctx: Ctx, constraint_ctx: ConstraintCtx) {
        let expression = hir
            .expressions
            .insert(Expression::Literal(Literal::Integer(123)));
        let statement = hir
            .statements
            .insert(Statement::Break(BreakStatement { expression }));
        let block = hir.blocks.insert(Block {
            statements: vec![statement],
            expression: ExpressionId::from_id(0),
        });

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_block_constraints(&constraint_ctx, block);
        assert_eq!(pass.errors.len(), 1);
        assert!(matches!(
            *pass.ctx.errors[pass.errors[0]],
            CErrorKind::ThirGen(ThirGenError::InvalidBreak)
        ));
    }

    #[rstest]
    fn expression_statement(mut hir: Hir, mut ctx: Ctx, constraint_ctx: ConstraintCtx) {
        let expression = hir
            .expressions
            .insert(Expression::Literal(Literal::Integer(123)));
        let statement = hir
            .statements
            .insert(Statement::Expression(ExpressionStatement { expression }));
        let block = hir.blocks.insert(Block {
            statements: vec![statement],
            expression: ExpressionId::from_id(0),
        });

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_block_constraints(&constraint_ctx, block);
        assert_debug_snapshot!("expression_statement", pass.constraints);
        assert!(pass.errors.is_empty());
    }

    #[rstest]
    #[case("assign", Assign { variable: ExpressionId::from_id(0), value: ExpressionId::from_id(0) })]
    #[case(
        "plus",
        Binary {
            lhs: ExpressionId::from_id(0),
            operation: BinaryOperation::Plus,
            rhs: ExpressionId::from_id(0),
        },
    )]
    #[case(
        "logical and",
        Binary {
            lhs: ExpressionId::from_id(0),
            operation: BinaryOperation::LogicalAnd,
            rhs: ExpressionId::from_id(0),
        },
    )]
    #[case(
        "equal",
        Binary {
            lhs: ExpressionId::from_id(0),
            operation: BinaryOperation::Equal,
            rhs: ExpressionId::from_id(0),
        },
    )]
    #[case(
        "greater",
        Binary {
            lhs: ExpressionId::from_id(0),
            operation: BinaryOperation::Greater,
            rhs: ExpressionId::from_id(0),
        },
    )]
    #[case("negative", Unary { operation: UnaryOperation::Negative, value: ExpressionId::from_id(0) })]
    fn expression_constraint(
        mut hir: Hir,
        mut ctx: Ctx,
        constraint_ctx: ConstraintCtx,
        #[case] name: &str,
        #[case] expression: impl Into<Expression> + Debug,
    ) {
        let dbg_str = format!("{expression:?}");
        let expression_id = hir.expressions.insert(expression.into());

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_expression_constraints(&constraint_ctx, expression_id);
        assert_debug_snapshot!(name, pass.constraints, &dbg_str);
        assert!(pass.errors.is_empty());
    }
}
