mod disjoint_union_set;
mod unification_table;

use crate::{ir::thir::Thir, prelude::*};

use self::unification_table::{Solution, SolutionId, UnificationTable};

use hir::*;

#[derive(Clone, Debug, thiserror::Error)]
pub enum ThirGenError {}

pub struct ThirGen<'ctx, 'hir> {
    ctx: &'ctx mut Ctx,
    hir: &'hir Hir,
}

impl<'ctx, 'hir> Pass<'ctx, 'hir> for ThirGen<'ctx, 'hir> {
    type Input = Hir;
    type Output = Thir<'hir>;
    type Extra = ();

    fn run(
        ctx: &'ctx mut Ctx,
        hir: &'hir Self::Input,
        _extra: Self::Extra,
    ) -> PassResult<Self::Output> {
        let mut thir_gen = Self::new(ctx, hir);

        // TODO: Could this be done in `hir_gen`?
        thir_gen.validate_trait_implementations();

        let globals = thir_gen.collect_globals();

        // Temporary storage for types.
        let mut identifier_tys = BTreeMap::new();
        let mut expression_tys = BTreeMap::new();

        // Perform inference for each function.
        for function in hir.functions.iter() {
            let (identifiers, expressions) = InferenceCtx::solve(
                hir,
                &mut thir_gen.ctx.types,
                globals.iter().cloned(),
                function,
            );

            // Update type storage.
            identifier_tys.extend(identifiers);
            expression_tys.extend(expressions);
        }

        // Collect all expressions into a continuous vec.
        let expression_tys = {
            let mut expressions = IndexedVec::new();
            for id in hir.expressions.iter_keys() {
                assert_eq!(expressions.insert(expression_tys[&id]), id);
            }
            expressions
        };

        PassResult::Ok(PassSuccess::Ok(Thir::new(
            hir,
            identifier_tys,
            expression_tys,
        )))
    }
}

impl<'ctx, 'hir> ThirGen<'ctx, 'hir> {
    fn new(ctx: &'ctx mut Ctx, hir: &'hir Hir) -> Self {
        Self { ctx, hir }
    }

    /// Collect a list of all global [`IdentifierBindingId`]s, and their associated [`Type`].
    fn collect_globals(&mut self) -> Vec<(IdentifierBindingId, TypeId)> {
        self.hir
            .functions
            .iter()
            .map(|function| {
                (
                    function.binding,
                    self.ctx.types.function(
                        function.signature.parameters.iter().map(|(_, ty)| *ty),
                        function.signature.return_ty,
                    ),
                )
            })
            .collect::<Vec<_>>()
    }

    /// Ensure that all trait implementations match the corresponding signature.
    fn validate_trait_implementations(&self) {
        for (key, trait_impl) in &self.hir.trait_implementations {
            let target_trait = &self.hir.traits[key.trait_id];
            for (method_id, function) in trait_impl.methods.iter_pairs() {
                let signature = &self.hir[*function].signature;
                let expected_signature = target_trait.methods[method_id].clone().with_self(key.ty);

                assert_eq!(
                    signature.parameters.len(),
                    expected_signature.parameters.len(),
                    "function signature must match trait definition"
                );

                // Ensure all parameters match.
                for ((_, parameter), (_, expected)) in signature
                    .parameters
                    .iter()
                    .zip(expected_signature.parameters)
                {
                    assert_eq!(*parameter, expected);
                }

                assert_eq!(signature.return_ty, expected_signature.return_ty);
            }
        }
    }
}

/// An unfulfilled condition that must be satisfied before a type can be solved.
#[derive(Clone, Debug)]
enum Obligation {
    /// `base.field == projection`
    Projection {
        base: SolutionId,
        field: usize,
        result: SolutionId,
    },
}

#[derive(Debug)]
pub struct InferenceCtx<'hir, 'ty> {
    hir: &'hir Hir,
    types: &'ty mut Types,
    table: UnificationTable,
    /// [`SolutionId`]s corresponding to each [`IdentifierBindingId`].
    environment: BTreeMap<IdentifierBindingId, SolutionId>,
    /// [`SolutionId`]s corresponding to each [`ExpressionId`].
    expressions: BTreeMap<ExpressionId, SolutionId>,
    /// Pending obligations.
    obligations: Vec<Obligation>,
    /// Return type of this function.
    return_ty: SolutionId,
    /// Stack of [`SolutionId`] corresponding with loop expressions.
    loop_expressions: Vec<SolutionId>,
}

impl<'hir, 'ty> InferenceCtx<'hir, 'ty> {
    /// Create a new instance.
    fn new(hir: &'hir Hir, types: &'ty mut Types, return_ty: TypeId) -> Self {
        let mut table = UnificationTable::new();

        let return_ty = table.concrete(return_ty);

        Self {
            hir,
            types,
            table,
            return_ty,
            environment: BTreeMap::new(),
            expressions: BTreeMap::new(),
            obligations: Vec::new(),
            loop_expressions: Vec::new(),
        }
    }

    /// Solve types for the provided function.
    fn solve(
        hir: &'hir Hir,
        types: &'ty mut Types,
        globals: impl Iterator<Item = (IdentifierBindingId, TypeId)>,
        function: &Function,
    ) -> (
        BTreeMap<IdentifierBindingId, TypeId>,
        BTreeMap<ExpressionId, TypeId>,
    ) {
        let mut ctx = Self::new(hir, types, function.signature.return_ty);

        // Fill out the environment with globals.
        for (identifier, ty) in globals {
            let ty = ctx.table.concrete(ty);
            assert!(ctx.environment.insert(identifier, ty).is_none());
        }

        if let Some(entry) = function.entry {
            let block = &hir[entry];

            // Check each statement.
            for statement in &block.statements {
                ctx.check_statement(*statement);
            }

            // Ensure the return expression matches.
            let return_ty = ctx.table.concrete(function.signature.return_ty);
            ctx.check(block.expression, return_ty);
        }

        ctx.process_obligations();

        (
            ctx.environment
                // HACK: Buffer for borrow checker
                .clone()
                .into_iter()
                .map(|(binding, solver_ty)| (binding, ctx.reify(solver_ty).expect("valid type")))
                .collect(),
            ctx.expressions
                // HACK: Buffer for borrow checker
                .clone()
                .into_iter()
                .map(|(expression_id, solver_ty)| {
                    (expression_id, ctx.reify(solver_ty).expect("valid type"))
                })
                .collect(),
        )
    }

    /// Process all obligations.
    fn process_obligations(&mut self) {
        while !self.obligations.is_empty() {
            let mut processed = false;

            for obligation in std::mem::take(&mut self.obligations) {
                if self.process_obligation(&obligation) {
                    processed = true;
                } else {
                    self.obligations.push(obligation);
                }
            }

            if !processed {
                panic!("couldn't advance obligation processing");
            }
        }
    }

    fn process_obligation(&mut self, obligation: &Obligation) -> bool {
        match obligation {
            Obligation::Projection {
                base,
                field,
                result,
            } => {
                let base = *base;
                let field = *field;
                let result = *result;

                match self.table.get(base) {
                    Solution::Concrete(ty) => {
                        let Type::Composite(CompositeType::Tuple(fields)) = &self.types[*ty] else {
                            panic!("cannot have projection on non-tuple type");
                        };

                        if field >= fields.len() {
                            panic!("field out of bounds");
                        }

                        let field_ty = self.table.concrete(fields[field]);
                        self.table.unify(self.types, result, field_ty);

                        true
                    }
                    Solution::Inferred(CompositeType::Tuple(fields)) => {
                        if field >= fields.len() {
                            panic!("field out of bounds");
                        }

                        let field_ty = fields[field];
                        self.table.unify(self.types, result, field_ty);

                        true
                    }
                    Solution::Unknown => {
                        // Try again later.
                        false
                    }
                    _ => panic!("invalid type for projection obligation"),
                }
            }
        }
    }

    /// Check that the given expression results in an expected type.
    ///
    /// This is used to propagate a type inwards.
    fn check(&mut self, expression_id: ExpressionId, expected: SolutionId) {
        let inferred = self.infer(expression_id);
        self.table.unify(self.types, inferred, expected);
    }

    /// Infer the type of an expression.
    ///
    /// This is used to propagate a type upwards.
    fn infer(&mut self, expression_id: ExpressionId) -> SolutionId {
        let expression = &self.hir[expression_id];
        let expression_ty = self.get_solution(expression_id);

        let resulting_ty = match &expression.kind {
            ExpressionKind::Assign(Assign { variable, value }) => {
                // Infer the variable type.
                let variable_ty = self.infer(*variable);

                // Check that the value matches the type.
                self.check(*value, variable_ty);

                // This expression resolves to unit.
                self.table.concrete(self.types.unit())
            }
            ExpressionKind::Binary(Binary {
                lhs,
                operation,
                rhs,
            }) => {
                match operation {
                    BinaryOperation::Plus
                    | BinaryOperation::Minus
                    | BinaryOperation::Multiply
                    | BinaryOperation::Divide
                    | BinaryOperation::BinaryAnd
                    | BinaryOperation::BinaryOr => {
                        // Arguments must be an integer.
                        let any_integer_ty = self.table.any_integer();
                        self.check(*lhs, any_integer_ty);
                        self.check(*rhs, any_integer_ty);

                        any_integer_ty
                    }
                    BinaryOperation::PlusWithOverflow => {
                        // Arguments must be an integer.
                        let any_integer_ty = self.table.any_integer();
                        self.check(*lhs, any_integer_ty);
                        self.check(*rhs, any_integer_ty);

                        let boolean_ty = self.table.concrete(self.types.boolean());

                        // Outcome is a tuple of `(result, overflow)`
                        self.table
                            .inferred(CompositeType::Tuple(vec![any_integer_ty, boolean_ty]))
                    }
                    BinaryOperation::Equal | BinaryOperation::NotEqual => {
                        // Infer arguments
                        let lhs_ty = self.infer(*lhs);
                        let rhs_ty = self.infer(*rhs);

                        // LHS and RHS are equal.
                        self.table.unify(self.types, lhs_ty, rhs_ty);

                        self.table.concrete(self.types.boolean())
                    }
                    BinaryOperation::Greater
                    | BinaryOperation::GreaterEqual
                    | BinaryOperation::Less
                    | BinaryOperation::LessEqual => {
                        // Arguments must be an integer.
                        let any_integer_ty = self.table.any_integer();
                        self.check(*lhs, any_integer_ty);
                        self.check(*rhs, any_integer_ty);

                        self.table.concrete(self.types.boolean())
                    }
                    BinaryOperation::LogicalAnd | BinaryOperation::LogicalOr => {
                        // Arguments must be a boolean.
                        let boolean_ty = self.table.concrete(self.types.boolean());
                        self.check(*lhs, boolean_ty);
                        self.check(*rhs, boolean_ty);

                        boolean_ty
                    }
                }
            }
            ExpressionKind::Unary(Unary { operation, value }) => {
                match operation {
                    UnaryOperation::Not => {
                        // HACK: Make this support booleans.
                        let any_integer = self.table.any_integer();

                        // Value must be any integer.
                        self.check(*value, any_integer);

                        any_integer
                    }
                    UnaryOperation::Negative => {
                        let any_signed_integer = self.table.any_integer();

                        // Value must be a signed integer.
                        self.check(*value, any_signed_integer);

                        any_signed_integer
                    }
                    UnaryOperation::Deref => {
                        let inner_ty = self.table.unknown();
                        let ref_ty = self.table.inferred(CompositeType::Ref(inner_ty));

                        // Value must be a reference
                        self.check(*value, ref_ty);

                        inner_ty
                    }
                    UnaryOperation::Ref => {
                        // Infer the value.
                        let inner_ty = self.infer(*value);

                        // Result is a reference to the value.
                        self.table.inferred(CompositeType::Ref(inner_ty))
                    }
                }
            }
            ExpressionKind::Switch(Switch {
                discriminator,
                branches,
                default,
            }) => {
                let discriminator = self.infer(*discriminator);

                let expression_ty = if let Some(default) = default {
                    // Default block, switch statement will result in that type.
                    let expression = self.check_block(*default);
                    self.infer(expression)
                } else {
                    // No default block, expression must be unit.
                    self.table.concrete(self.types.unit())
                };

                for (literal, block) in branches {
                    // Ensure literal matches discriminator.
                    let literal = self.get_solution(literal);
                    self.table.unify(self.types, discriminator, literal);

                    let expression = self.check_block(*block);

                    // Ensure the block expression matches the expression type.
                    self.check(expression, expression_ty);
                }

                expression_ty
            }
            ExpressionKind::Loop(Loop { body }) => {
                let unit = self.table.concrete(self.types.unit());
                let result = self.table.unknown();

                // Record the resulting type.
                self.loop_expressions.push(result);

                // Infer the body.
                let expression = self.check_block(*body);
                // Expression must result in unit.
                self.check(expression, unit);

                // Pop back off.
                assert_eq!(self.loop_expressions.pop().unwrap(), result);

                result
            }
            ExpressionKind::Literal(literal) => self.get_solution(literal),
            ExpressionKind::Call(call) => {
                let return_ty = self.table.unknown();
                self.infer_call(call, return_ty);
                return_ty
            }
            ExpressionKind::Block(block_id) => {
                let block_expression = self.check_block(*block_id);
                self.infer(block_expression)
            }
            ExpressionKind::Variable(Variable { binding }) => self.get_solution(*binding),
            ExpressionKind::Unreachable => self.table.concrete(self.types.never()),
            ExpressionKind::Aggregate(Aggregate { values }) => {
                // Infer all values.
                let values = values
                    .clone()
                    .into_iter()
                    .map(|value| self.infer(value))
                    .collect::<Vec<_>>();
                self.table.inferred(CompositeType::Tuple(values))
            }
            ExpressionKind::Field(Field { lhs, field }) => {
                let base = self.infer(*lhs);
                let result = self.table.unknown();
                self.obligations.push(Obligation::Projection {
                    base,
                    field: *field,
                    result,
                });
                result
            }
            ExpressionKind::Path(Path {
                ty,
                target_trait,
                item,
            }) => {
                if !self
                    .hir
                    .trait_implementations
                    .contains_key(&TraitImplementationKey {
                        trait_id: *target_trait,
                        ty: *ty,
                    })
                {
                    panic!("type must implement trait");
                }

                let signature = self.hir.traits[*target_trait].methods[*item]
                    .clone()
                    .with_self(*ty);
                let signature_ty = self.types.function(
                    signature.parameters.into_iter().map(|(_, ty)| ty),
                    signature.return_ty,
                );
                self.table.concrete(signature_ty)
            }
        };

        self.table.unify(self.types, expression_ty, resulting_ty)
    }

    /// Infer a function call, using the provided return type.
    fn infer_call(&mut self, call: &Call, return_ty: SolutionId) {
        let callee = self.infer(call.callee);

        // Generate placeholders for arguments and return type.
        let parameters = call
            .arguments
            .iter()
            .map(|_| self.table.unknown())
            .collect::<Vec<_>>();

        // Use the placeholders to create an inferred function signature.
        let signature_ty = self.table.inferred(CompositeType::Function {
            parameters: parameters.clone(),
            return_ty,
        });

        // Unify the callee with the inferred signature.
        self.table.unify(self.types, callee, signature_ty);

        // Check arguments.
        for (argument, parameter_ty) in call.arguments.iter().cloned().zip(parameters) {
            self.check(argument, parameter_ty);
        }
    }

    /// Check each [`Statement`] within a [`Block`], then return the block's [`Expression`].
    fn check_block(&mut self, block: BlockId) -> ExpressionId {
        let block = &self.hir[block];

        // Check all statements in block.
        for statement in &block.statements {
            self.check_statement(*statement);
        }

        block.expression
    }

    /// Check a [`Statement`], inferring [`Expression`]s where necessary.
    fn check_statement(&mut self, statement_id: StatementId) {
        match &self.hir[statement_id].kind {
            StatementKind::Declare(DeclareStatement { binding, ty }) => {
                let binding_ty = self.get_solution(*binding);

                match ty {
                    DeclarationTy::Type(type_id) => {
                        // Make sure the declaration type matches the variable.
                        let expected_ty = self.table.concrete(*type_id);
                        self.table.unify(self.types, binding_ty, expected_ty);
                    }
                    DeclarationTy::Inferred(expression_id) => {
                        // Variable type is determined from the corresponding variable.
                        let expression_ty = self.get_solution(*expression_id);
                        self.table.unify(self.types, binding_ty, expression_ty);
                    }
                }
            }
            StatementKind::Return(ReturnStatement { expression }) => {
                self.check(*expression, self.return_ty);
            }
            StatementKind::Break(BreakStatement { expression }) => {
                self.check(
                    *expression,
                    *self
                        .loop_expressions
                        .last()
                        .expect("used break outside of loop"),
                );
            }
            StatementKind::Expression(ExpressionStatement { expression }) => {
                // Expression statements can be any type, as they're ignored.
                self.infer(*expression);
            }
        }
    }

    /// Attempt to solve a [`Solution`] into a concrete [`Type`]. If a solution cannot be reached,
    /// [`None`] will be returned.
    fn reify(&mut self, solver_ty: SolutionId) -> Option<TypeId> {
        match self.table.get(solver_ty) {
            Solution::Concrete(type_id) => Some(*type_id),
            Solution::Inferred(composite_type) => match composite_type {
                CompositeType::Ref(inner) => {
                    let inner = *inner;
                    let inner = self.reify(inner)?;
                    Some(self.types.ref_of(inner))
                }
                CompositeType::Function {
                    parameters,
                    return_ty,
                } => {
                    let return_ty = *return_ty;
                    let parameters = parameters
                        // HACK: Buffer for borrow checker.
                        .clone()
                        .into_iter()
                        .map(|parameter| self.reify(parameter))
                        .collect::<Option<Vec<_>>>()?;
                    let return_ty = self.reify(return_ty)?;
                    Some(self.types.function(parameters, return_ty))
                }
                CompositeType::Tuple(items) => {
                    let items = items
                        .clone()
                        .into_iter()
                        .map(|field| self.reify(field))
                        .collect::<Option<Vec<_>>>()?;
                    Some(self.types.tuple(items))
                }
            },
            Solution::AnyInteger | Solution::SignedInteger => Some(self.types.i8()),
            Solution::UnsignedInteger => Some(self.types.u8()),
            Solution::Error => None,
            Solution::Unknown => None,
        }
    }
}

/// Helper trait to fetch the [`SolutionId`] of some type `T`.
trait GetSolution<T> {
    /// Get the [`SolutionId`].
    fn get_solution(&mut self, value: T) -> SolutionId;
}

impl GetSolution<&'_ Literal> for InferenceCtx<'_, '_> {
    fn get_solution(&mut self, literal: &'_ Literal) -> SolutionId {
        match literal {
            Literal::Integer(_) => self.table.any_integer(),
            Literal::Boolean(_) => self.table.concrete(self.types.boolean()),
        }
    }
}

impl GetSolution<ExpressionId> for InferenceCtx<'_, '_> {
    fn get_solution(&mut self, expression_id: ExpressionId) -> SolutionId {
        *self
            .expressions
            .entry(expression_id)
            .or_insert_with(|| self.table.unknown())
    }
}

impl GetSolution<IdentifierBindingId> for InferenceCtx<'_, '_> {
    fn get_solution(&mut self, identifier: IdentifierBindingId) -> SolutionId {
        *self
            .environment
            .entry(identifier)
            .or_insert_with(|| self.table.unknown())
    }
}

#[cfg(test)]
mod test {
    use crate::passes::{
        ast_gen::AstGen,
        cst_gen::Parse,
        hir_gen::{FunctionCtx, HirGen},
    };

    use super::*;

    #[fixture]
    fn ctx() -> Ctx {
        Ctx::new()
    }

    #[fixture]
    fn hir() -> Hir {
        Hir::new()
    }

    fn get_ty(expression: &str) -> Type {
        let mut ctx = Ctx::new();

        // Tokenise and parse the source.
        let mut lexer = Lexer::new(expression);
        let expression = cst::Expression::parse(&mut lexer);
        lexer.expect::<tok::Eof>().unwrap();

        // Lower into AST.
        let mut ast_pass = AstGen::new(&mut ctx);
        let expression_id = ast_pass.lower_expression(&expression);
        let ast = ast_pass.ast;

        let scope = ctx.scopes.nest_scope_global();
        let mut hir_gen = HirGen::new(&mut ctx, &ast);
        let expression_id = hir_gen
            .lower_expression(&FunctionCtx::Item, &ast[expression_id], scope)
            .unwrap();
        let hir = hir_gen.hir;

        let unit_ty = ctx.types.unit();
        let mut inference = InferenceCtx::new(&hir, &mut ctx.types, unit_ty);
        let solver_ty = inference.infer(expression_id);
        let ty = inference.reify(solver_ty).expect("valid type");

        ctx.types[ty].clone()
    }

    #[rstest]
    fn unify_u8() {
        let types = Types::new();

        let u8_ty = types.u8();

        let mut table = UnificationTable::new();

        let u8 = table.concrete(u8_ty);
        let unknown = table.unknown();

        table.unify(&types, u8, unknown);

        assert_eq!(table.get(unknown), &Solution::Concrete(u8_ty));
    }

    #[rstest]
    #[case("1", Type::I8)]
    #[case("1 + 2", Type::I8)]
    #[case("1 - 2", Type::I8)]
    #[case("1 & 2", Type::I8)]
    #[case("true && true", Type::Boolean)]
    #[case("1 < 2", Type::Boolean)]
    #[case("{ 1 }", Type::I8)]
    #[case("{ 1; }", Type::UNIT)]
    #[case("{ let a = 1; }", Type::UNIT)]
    #[case("{ let a = 1; 1 }", Type::I8)]
    #[case("{ let a = 1; a }", Type::I8)]
    fn assert_expression_ty(#[case] expression: &str, #[case] ty: Type) {
        assert_eq!(get_ty(expression), ty);
    }

    mod process_obligations {
        use super::*;

        mod projection {
            use super::*;

            #[rstest]
            fn base_unknown() {
                let hir = Hir::new();
                let mut types = Types::new();
                let return_ty = types.unit();

                let mut ctx = InferenceCtx::new(&hir, &mut types, return_ty);

                let base = ctx.table.unknown();
                let result = ctx.table.unknown();
                let processed = ctx.process_obligation(&Obligation::Projection {
                    base,
                    field: 0,
                    result,
                });

                assert!(!processed);
            }
        }
    }
}
