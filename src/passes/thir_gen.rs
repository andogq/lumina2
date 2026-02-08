use crate::prelude::*;

use crate::ty::{Constraints, Solver, TypeVarId, TypeVars};

use hir::*;
use thir::Thir;

/// Generator to build a collection of [`Constraint`]s, then solve them to produce a [`Thir`].
pub struct ThirGen<'ctx, 'hir> {
    /// Context used throughout this pass.
    ctx: &'ctx mut Ctx,
    /// HIR that will be processed.
    hir: &'hir Hir,
    /// Interned type variables.
    type_vars: TypeVars,
    /// Constraints collected while walking the HIR.
    constraints: Constraints,
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

        // Add constraints for each trait implementation.
        for trait_implementation in thir_gen.hir.trait_implementations.keys() {
            thir_gen.add_trait_implementation(trait_implementation);
        }

        // Collect trait implementations.
        let trait_implementations = thir_gen.hir.trait_implementations.keys().cloned().collect();

        // Run the solver.
        let types = Solver::run(
            &mut thir_gen.ctx.types,
            &mut thir_gen.type_vars,
            &trait_implementations,
            &thir_gen.constraints,
        );

        Ok(PassSuccess::new(
            Thir::new(hir, types, thir_gen.type_vars),
            thir_gen.errors,
        ))
    }
}

impl<'ctx, 'hir> ThirGen<'ctx, 'hir> {
    pub fn new(ctx: &'ctx mut Ctx, hir: &'hir Hir) -> Self {
        Self {
            ctx,
            hir,
            type_vars: TypeVars::new(),
            constraints: Constraints::new(),
            errors: Vec::new(),
        }
    }

    fn add_function_declaration(&mut self, function_id: FunctionId) {
        let function = &self.hir[function_id];

        let binding = self.type_vars.intern(function.binding);
        let signature = self.signature_as_type_var(&function.signature);

        self.constraints.equal(binding, signature);
    }

    /// Produce a [`TypeVar`] for the given [`FunctionSignature`].
    fn signature_as_type_var(&mut self, signature: &FunctionSignature) -> TypeVarId {
        self.type_vars.intern(self.ctx.types.function(
            signature.parameters.iter().map(|(_, ty)| *ty),
            signature.return_ty,
        ))
    }

    fn add_function_constraints(&mut self, function_id: FunctionId) {
        let function = &self.hir[function_id];

        if let Some(entry) = function.entry {
            // Add constraints for the function parameters.
            for (parameter_binding, parameter_ty) in &function.signature.parameters {
                self.constraints.equal(
                    self.type_vars.intern(*parameter_binding),
                    self.type_vars.intern(*parameter_ty),
                );
            }

            // Add constraint for the function return type (the body of the function must result in the
            // return type).
            self.constraints.equal(
                self.type_vars.intern(self.hir[entry].expression),
                self.type_vars.intern(function.signature.return_ty),
            );

            let ctx = ConstraintCtx::new(function_id);
            self.add_block_constraints(&ctx, entry);
        }
    }

    /// Add constraints required to check a trait implementation. Will ensure that all implemented
    /// methods match the signature of the trait, but does not verify whether all methods were
    /// implemented.
    fn add_trait_implementation(&mut self, implementation_key: &TraitImplementationKey) {
        let implementation = &self.hir[implementation_key];
        let target_trait = &self.hir[implementation_key.trait_id];

        let implementing_ty = implementation_key.ty;

        for (method_id, method) in implementation.methods.iter_pairs() {
            // Fetch the intended signature.
            let trait_method_signature = self.signature_as_type_var(
                &target_trait.methods[method_id]
                    .clone()
                    .with_self(implementing_ty),
            );

            // Fetch the method signature.
            let implemented_signature = self.signature_as_type_var(&self.hir[*method].signature);

            // Emit constraint that they're equal.
            self.constraints
                .equal(trait_method_signature, implemented_signature);
        }
    }

    fn add_block_constraints(&mut self, ctx: &ConstraintCtx, block_id: BlockId) {
        let block = &self.hir[block_id];

        for statement in &block.statements {
            match &self.hir[*statement].kind {
                StatementKind::Declare(DeclareStatement { binding, ty }) => match ty {
                    // Directly set variable type.
                    DeclarationTy::Type(ty) => self
                        .constraints
                        .equal(self.type_vars.intern(*binding), self.type_vars.intern(*ty)),
                    // Infer variable's type from the provided expression.
                    DeclarationTy::Inferred(expression) => self.constraints.equal(
                        self.type_vars.intern(*binding),
                        self.type_vars.intern(*expression),
                    ),
                },
                // Expression must equal the return type of the current function.
                StatementKind::Return(ReturnStatement { expression }) => {
                    // Generate constraints for the return expression.
                    self.add_expression_constraints(ctx, *expression);

                    // Ensure the return expression matches the function return type.
                    self.constraints.equal(
                        self.type_vars.intern(*expression),
                        self.type_vars
                            .intern(self.hir[ctx.function].signature.return_ty),
                    );
                }
                StatementKind::Break(BreakStatement { expression }) => {
                    // Generate constraints for the break expression.
                    self.add_expression_constraints(ctx, *expression);

                    match ctx.loops.last() {
                        // Break expression must match the expression of the inner most loop.
                        Some(current_loop) => self.constraints.equal(
                            self.type_vars.intern(*expression),
                            self.type_vars.intern(*current_loop),
                        ),
                        // Not currently in a loop, so report that it's invalid, and continue
                        // generating constraints.
                        None => self
                            .errors
                            .push(self.ctx.errors.report(ThirGenError::InvalidBreak)),
                    }
                }
                StatementKind::Expression(ExpressionStatement { expression }) => {
                    self.add_expression_constraints(ctx, *expression)
                }
            }
        }

        self.add_expression_constraints(ctx, block.expression);
    }

    fn add_expression_constraints(&mut self, ctx: &ConstraintCtx, expression_id: ExpressionId) {
        let expression = self.type_vars.intern(expression_id);

        // Pre-intern common types
        let ty_unit = self.type_vars.intern(self.ctx.types.unit());
        let ty_boolean = self.type_vars.intern(self.ctx.types.boolean());
        let ty_never = self.type_vars.intern(self.ctx.types.never());

        match &self.hir[expression_id].kind {
            ExpressionKind::Assign(Assign { variable, value }) => {
                // Value of the assignment must match the variable it's being assigned to.
                self.constraints.equal(
                    self.type_vars.intern(*value),
                    self.type_vars.intern(*variable),
                );
                // The actual assignment expression results in unit.
                self.constraints.equal(expression, ty_unit);

                self.add_expression_constraints(ctx, *variable);
                self.add_expression_constraints(ctx, *value);
            }
            ExpressionKind::Binary(Binary {
                lhs,
                operation,
                rhs,
            }) => {
                self.add_expression_constraints(ctx, *lhs);
                self.add_expression_constraints(ctx, *rhs);

                let lhs = self.type_vars.intern(*lhs);
                let rhs = self.type_vars.intern(*rhs);

                match operation {
                    BinaryOperation::Plus
                    | BinaryOperation::Minus
                    | BinaryOperation::Multiply
                    | BinaryOperation::Divide
                    | BinaryOperation::BinaryAnd
                    | BinaryOperation::BinaryOr => {
                        // Operands must equal each other.
                        self.constraints.equal(lhs, rhs);
                        // Operands should be integers.
                        self.constraints.integer(lhs);
                        self.constraints.integer(rhs);
                        // Result is the same as the input.
                        self.constraints.equal(expression, lhs);
                    }
                    BinaryOperation::PlusWithOverflow => {
                        // Operands must equal each other.
                        self.constraints.equal(lhs, rhs);
                        // Operands should be integers.
                        self.constraints.integer(lhs);
                        self.constraints.integer(rhs);
                        // Result is a tuple.
                        self.constraints.aggregate(expression, 2);
                        // First tuple field is the same as the input.
                        self.constraints
                            .equal(self.type_vars.intern(TypeVar::Field(expression, 0)), lhs);
                        // Second tuple field is a boolean indicating overflow.
                        self.constraints.equal(
                            self.type_vars.intern(TypeVar::Field(expression, 1)),
                            self.type_vars.intern(self.ctx.types.boolean()),
                        );
                    }
                    BinaryOperation::Equal | BinaryOperation::NotEqual => {
                        // Operands must be identical
                        self.constraints.equal(lhs, rhs);
                        // Results in a boolean.
                        self.constraints.equal(expression, ty_boolean);
                    }
                    BinaryOperation::Greater
                    | BinaryOperation::GreaterEqual
                    | BinaryOperation::Less
                    | BinaryOperation::LessEqual => {
                        // Operands must be identical
                        self.constraints.equal(lhs, rhs);
                        // Operands should be integers.
                        // TODO: Probably should check they are ordinals.
                        self.constraints.integer(lhs);
                        self.constraints.integer(rhs);
                        // Results in a boolean.
                        self.constraints.equal(expression, ty_boolean);
                    }
                    BinaryOperation::LogicalAnd | BinaryOperation::LogicalOr => {
                        // Operands must be booleans.
                        self.constraints.equal(lhs, ty_boolean);
                        self.constraints.equal(rhs, ty_boolean);
                        // Results in a boolean.
                        self.constraints.equal(expression, ty_boolean);
                    }
                }
            }
            ExpressionKind::Unary(Unary { operation, value }) => {
                self.add_expression_constraints(ctx, *value);

                let value = self.type_vars.intern(*value);

                match operation {
                    UnaryOperation::Not => {
                        // Output is same as input.
                        self.constraints.equal(expression, value);
                        // Operand can be any integer.
                        self.constraints.integer(value);
                    }
                    UnaryOperation::Negative => {
                        // Output is same as input.
                        self.constraints.equal(expression, value);
                        // Operand can be any integer.
                        self.constraints.integer_signed(value);
                    }
                    UnaryOperation::Deref => {
                        // Make sure that operand is a pointer, and output is inner type of pointer.
                        self.constraints.reference(value, expression);
                    }
                    UnaryOperation::Ref => self.constraints.reference(expression, value),
                }
            }
            ExpressionKind::Switch(Switch {
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

                branches.iter().for_each(|(literal, block)| {
                    // Branch literal must match discriminator.
                    self.add_literal_constraint(*discriminator, literal);
                    // Block which is resolved must match this expression.
                    self.constraints.equal(
                        self.type_vars.intern(self.hir[*block].expression),
                        expression,
                    );
                });

                // Ensure the default branch matches the expression, or unit if there is no default branch.
                // TODO: This does not handle branches which are exhaustive.
                match default {
                    Some(default) => self.constraints.equal(
                        expression,
                        self.type_vars.intern(self.hir[*default].expression),
                    ),
                    None => self.constraints.equal(expression, ty_unit),
                }
            }
            ExpressionKind::Loop(Loop { body }) => {
                // Ensure the body of the loop doesn't yield any non-unit expressions.
                self.constraints
                    .equal(self.type_vars.intern(self.hir[*body].expression), ty_unit);

                // Create a new ctx for generating constraints for the body.
                let ctx = ctx.push_loop(expression_id);
                self.add_block_constraints(&ctx, *body);
            }
            ExpressionKind::Literal(literal) => self.add_literal_constraint(expression_id, literal),
            ExpressionKind::Call(Call { callee, arguments }) => {
                self.add_expression_constraints(ctx, *callee);
                for argument in arguments {
                    self.add_expression_constraints(ctx, *argument);
                }

                self.constraints.function(
                    self.type_vars.intern(*callee),
                    arguments
                        .iter()
                        .map(|argument| self.type_vars.intern(*argument)),
                    expression,
                );
            }
            ExpressionKind::Block(block_id) => {
                self.add_block_constraints(ctx, *block_id);

                // Type of this expression will be the type of the block.
                self.constraints.equal(
                    expression,
                    self.type_vars.intern(self.hir[*block_id].expression),
                );
            }
            ExpressionKind::Variable(Variable { binding }) => self
                .constraints
                .equal(expression, self.type_vars.intern(*binding)),
            ExpressionKind::Unreachable => self.constraints.equal(expression, ty_never),
            ExpressionKind::Aggregate(Aggregate { values }) => {
                // Add constraints for each contained expression.
                for (i, value) in values.iter().enumerate() {
                    self.add_expression_constraints(ctx, *value);

                    self.constraints.equal(
                        self.type_vars.intern(*value),
                        self.type_vars.intern(TypeVar::Field(expression, i)),
                    );
                }

                self.constraints.aggregate(expression, values.len());
            }
            ExpressionKind::Field(Field { lhs, field }) => {
                self.add_expression_constraints(ctx, *lhs);

                let lhs = self.type_vars.intern(*lhs);
                self.constraints.equal(
                    expression,
                    self.type_vars.intern(TypeVar::Field(lhs, *field)),
                );
            }
            ExpressionKind::Path(Path {
                ty,
                target_trait,
                item,
            }) => {
                let ty_var = self.type_vars.intern(*ty);

                // Enforce the type implements the trait.
                self.constraints.implements(ty_var, *target_trait);

                // This expression results in the signature of the trait item.
                let item_signature = self.hir[*target_trait].methods[*item]
                    .clone()
                    // Since the trait method signature is used, substitute `Self` with the current
                    // type.
                    .with_self(*ty);
                let signature_var = self.signature_as_type_var(&item_signature);
                self.constraints.equal(expression, signature_var);
            }
        }
    }

    fn add_literal_constraint(&mut self, var: impl Into<TypeVar>, literal: &Literal) {
        let var = self.type_vars.intern(var);
        match literal {
            Literal::Integer(_) => self.constraints.integer(var),
            Literal::Boolean(_) => self
                .constraints
                .equal(var, self.type_vars.intern(self.ctx.types.boolean())),
        }
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

    /// Push a new loop to the context, returning a new instance.
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
        let mut hir = Hir::new();
        hir.add_expression(Aggregate::UNIT);
        hir
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
    #[case("simple", [], Type::UNIT)]
    #[case("return integer", [], Type::I8)]
    #[case("parameters", [(IdentifierBindingId::from_id(1), Type::I8), (IdentifierBindingId::from_id(2), Type::Boolean)], Type::Boolean)]
    fn function_declaration(
        mut hir: Hir,
        mut ctx: Ctx,
        #[case] name: &str,
        #[case] parameters: impl IntoIterator<Item = (IdentifierBindingId, Type)>,
        #[case] return_ty: Type,
    ) {
        let function_id = hir.add_function(
            IdentifierBindingId::from_id(0),
            FunctionSignature {
                parameters: parameters
                    .into_iter()
                    .map(|(binding, parameter)| (binding, ctx.types.get(parameter)))
                    .collect(),
                return_ty: ctx.types.get(return_ty),
            },
            Some(BlockId::from_id(0)),
        );
        let function = &hir[function_id];

        // Used for debugging.
        let signature_str = format!(
            "{:?} => {:?}",
            function.signature.parameters, function.signature.return_ty
        );

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_function_declaration(function_id);
        assert_debug_snapshot!(name, *pass.constraints, &signature_str);
        assert!(pass.errors.is_empty());
    }

    #[rstest]
    #[case("inferred", |_types: &mut Types| DeclarationTy::Inferred(ExpressionId::from_id(0)))]
    #[case("with unit", |types: &mut Types| DeclarationTy::Type(types.unit()))]
    #[case("with type", |types: &mut Types| DeclarationTy::Type(types.i8()))]
    fn variable_declaration(
        mut hir: Hir,
        mut ctx: Ctx,
        constraint_ctx: ConstraintCtx,
        #[case] name: &str,
        #[case] ty: impl Fn(&mut Types) -> DeclarationTy,
    ) {
        let ty = ty(&mut ctx.types);
        let statement = hir.add_statement(DeclareStatement {
            binding: IdentifierBindingId::from_id(0),
            ty: ty.clone(),
        });
        let block = hir.add_block(vec![statement], ExpressionId::from_id(0));

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_block_constraints(&constraint_ctx, block);
        assert_debug_snapshot!(name, *pass.constraints, &format!("{ty:?}"));
        assert!(pass.errors.is_empty());
    }

    #[rstest]
    fn return_statement(mut hir: Hir, mut ctx: Ctx, constraint_ctx: ConstraintCtx) {
        let expression = hir.add_expression(Literal::Integer(123));
        let statement = hir.add_statement(ReturnStatement { expression });
        let block = hir.add_block(vec![statement], ExpressionId::from_id(0));

        // Insert a fake function to pull the return type.
        hir.add_function(
            IdentifierBindingId::from_id(0),
            FunctionSignature {
                parameters: Vec::new(),
                return_ty: ctx.types.u8(),
            },
            Some(block),
        );

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_block_constraints(&constraint_ctx, block);
        assert_debug_snapshot!("return_statement", *pass.constraints);
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
            hir.add_expression(ExpressionKind::Unreachable);
        });

        let expression = hir.add_expression(Literal::Integer(123));
        let statement = hir.add_statement(BreakStatement { expression });
        let block = hir.add_block(vec![statement], ExpressionId::from_id(0));

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_block_constraints(&constraint_ctx, block);
        assert_debug_snapshot!(name, *pass.constraints);
        assert!(pass.errors.is_empty());
    }

    #[rstest]
    fn break_statement_no_loop(mut hir: Hir, mut ctx: Ctx, constraint_ctx: ConstraintCtx) {
        let expression = hir.add_expression(Literal::Integer(123));
        let statement = hir.add_statement(BreakStatement { expression });
        let block = hir.add_block(vec![statement], ExpressionId::from_id(0));

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
        let expression = hir.add_expression(Literal::Integer(123));
        let statement = hir.add_statement(ExpressionStatement { expression });
        let block = hir.add_block(vec![statement], ExpressionId::from_id(0));

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_block_constraints(&constraint_ctx, block);
        assert_debug_snapshot!("expression_statement", *pass.constraints);
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
        #[case] expression: impl Into<ExpressionKind> + Debug,
    ) {
        let dbg_str = format!("{expression:?}");
        let expression_id = hir.add_expression(expression);

        let mut pass = ThirGen::new(&mut ctx, &hir);
        pass.add_expression_constraints(&constraint_ctx, expression_id);
        assert_debug_snapshot!(name, *pass.constraints, &dbg_str);
        assert!(pass.errors.is_empty());
    }
}
