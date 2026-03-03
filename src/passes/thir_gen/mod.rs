use crate::{ir::thir::Thir, prelude::*, ty::DisjointUnionSet};

use hir::*;

create_id!(SolverTypeId);

#[derive(Clone, Debug, thiserror::Error)]
pub enum ThirGenError {}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SolverType {
    Unknown,
    Concrete(TypeId),
    Inferred(CompositeType<SolverTypeId>),
    AnyInteger,
    #[expect(dead_code, reason = "unsigned integer may be used in the future")]
    UnsignedInteger,
    #[expect(dead_code, reason = "signed integer may be used in the future")]
    SignedInteger,
    #[expect(dead_code, reason = "error may be used in the future")]
    Error,
}

pub struct ThirGen;

impl<'ctx, 'hir> Pass<'ctx, 'hir> for ThirGen {
    type Input = Hir;
    type Output = Thir<'hir>;
    type Extra = ();

    fn run(
        ctx: &'ctx mut Ctx,
        hir: &'hir Self::Input,
        _extra: Self::Extra,
    ) -> PassResult<Self::Output> {
        let mut globals = Vec::new();

        // Collect all functions.
        for function in hir.functions.iter() {
            globals.push((
                function.binding,
                ctx.types.function(
                    function.signature.parameters.iter().map(|(_, ty)| *ty),
                    function.signature.return_ty,
                ),
            ));
        }

        // Temporary storage for types.
        let mut identifier_tys = BTreeMap::new();
        let mut expression_tys = BTreeMap::new();

        // Ensure all trait implementations match required signature.
        for (key, trait_impl) in &hir.trait_implementations {
            let target_trait = &hir.traits[key.trait_id];
            for (method_id, function) in trait_impl.methods.iter_pairs() {
                let signature = &hir[*function].signature;
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

        // Perform inference for each function.
        for function in hir.functions.iter() {
            let mut inference_ctx = InferenceCtx::new(
                hir,
                &mut ctx.types,
                globals
                    .iter()
                    .cloned()
                    .chain(function.signature.parameters.iter().cloned()),
                function.signature.return_ty,
            );

            if let Some(entry) = function.entry {
                let block = &hir[entry];

                // Check each statement.
                for statement in &block.statements {
                    inference_ctx.check_statement(*statement);
                }

                // Ensure the return expression matches.
                let return_ty = inference_ctx.get_type(function.signature.return_ty);
                inference_ctx.check(block.expression, return_ty);
            }

            inference_ctx.process_obligations();

            // Update type storage.
            identifier_tys.extend(
                inference_ctx
                    .environment
                    // HACK: Buffer for borrow checker
                    .clone()
                    .into_iter()
                    .map(|(binding, solver_ty)| {
                        (binding, inference_ctx.reify(solver_ty).expect("valid type"))
                    }),
            );
            expression_tys.extend(
                inference_ctx
                    .expressions
                    // HACK: Buffer for borrow checker
                    .clone()
                    .into_iter()
                    .map(|(expression_id, solver_ty)| {
                        (
                            expression_id,
                            inference_ctx.reify(solver_ty).expect("valid type"),
                        )
                    }),
            );
        }

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

#[derive(Clone, Debug)]
struct UnificationTable {
    set: DisjointUnionSet<SolverTypeId, SolverType>,
}

impl UnificationTable {
    /// Create a new unification.
    pub fn new() -> Self {
        Self {
            set: DisjointUnionSet::new(),
        }
    }

    /// Create a new [`SolverType::Concrete`] type variable.
    fn new_unknown(&mut self) -> SolverTypeId {
        self.set.insert(SolverType::Unknown)
    }

    /// Create a new [`SolverType::Concrete`] type variable.
    fn new_concrete(&mut self, ty: TypeId) -> SolverTypeId {
        self.set.insert(SolverType::Concrete(ty))
    }

    /// Create a new [`SolverType::AnyInteger`] type variable.
    fn new_any_integer(&mut self) -> SolverTypeId {
        self.set.insert(SolverType::AnyInteger)
    }

    /// Create a new [`SolverType::Inferred`] type variable.
    fn new_inferred(&mut self, inferred: CompositeType<SolverTypeId>) -> SolverTypeId {
        self.set.insert(SolverType::Inferred(inferred))
    }

    /// Unify the given types. The resulting root type will be returned.
    fn unify(&mut self, types: &Types, lhs: SolverTypeId, rhs: SolverTypeId) -> SolverTypeId {
        let lhs = self.set.find_root(lhs);
        let rhs = self.set.find_root(rhs);

        if lhs == rhs {
            return lhs;
        }

        let [lhs_node, rhs_node] = self.set.get_multiple([lhs, rhs]);

        match ((lhs, lhs_node), (rhs, rhs_node)) {
            // One is unknown, point at other root.
            ((unknown, SolverType::Unknown), (root, _))
            | ((root, _), (unknown, SolverType::Unknown)) => {
                assert_eq!(
                    self.set.redirect(unknown, root).expect("nodes must differ"),
                    SolverType::Unknown,
                    "should replace unknown node"
                );
                root
            }
            // One of the types is concrete, it always takes precedence.
            ((concrete, SolverType::Concrete(concrete_ty)), (other, other_ty))
            | ((other, other_ty), (concrete, SolverType::Concrete(concrete_ty))) => {
                if *concrete_ty == types.never() {
                    // Concrete type is `never`, so return the other type.
                    return other;
                }

                match other_ty {
                    SolverType::Concrete(other_ty) => {
                        if concrete_ty != other_ty {
                            if *other_ty == types.never() {
                                // Other type is `never`, so return the concrete type.
                                return concrete;
                            }

                            panic!("cannot unify different concrete types");
                        }
                    }
                    SolverType::Inferred(inferred_ty) => {
                        let Type::Composite(composite_ty) = &types[*concrete_ty] else {
                            panic!("cannot infer with primitive");
                        };

                        // Collect the fields from the composite type.
                        let (concrete_fields, inferred_fields) = match (composite_ty, inferred_ty) {
                            (
                                CompositeType::Ref(composite_inner_ty),
                                CompositeType::Ref(inferred_inner_ty),
                            ) => (vec![*composite_inner_ty], vec![*inferred_inner_ty]),
                            (
                                CompositeType::Function {
                                    parameters: composite_parameters,
                                    return_ty: composite_return_ty,
                                },
                                CompositeType::Function {
                                    parameters: inferred_parameters,
                                    return_ty: inferred_return_ty,
                                },
                            ) => (
                                composite_parameters
                                    .iter()
                                    .cloned()
                                    .chain([*composite_return_ty])
                                    .collect(),
                                inferred_parameters
                                    .iter()
                                    .cloned()
                                    .chain([*inferred_return_ty])
                                    .collect(),
                            ),
                            (
                                CompositeType::Tuple(composite_fields),
                                CompositeType::Tuple(inferred_fields),
                            ) => (composite_fields.clone(), inferred_fields.clone()),
                            _ => panic!("cannot unify"),
                        };

                        assert_eq!(concrete_fields.len(), inferred_fields.len());
                        for (concrete, inferred) in concrete_fields.into_iter().zip(inferred_fields)
                        {
                            // Generate a solver type for the concrete type.
                            let parameter_concrete = self.new_concrete(concrete);

                            // Unify the types.
                            self.unify(types, parameter_concrete, inferred);
                        }
                    }
                    SolverType::AnyInteger => {
                        if !matches!(&types[*concrete_ty], Type::I8 | Type::U8) {
                            panic!("type is not any integer");
                        }
                    }
                    SolverType::UnsignedInteger => {
                        if !matches!(&types[*concrete_ty], Type::U8) {
                            panic!("type is not unsigned integer");
                        }
                    }
                    SolverType::SignedInteger => {
                        if !matches!(&types[*concrete_ty], Type::I8) {
                            panic!("type is not signed integer");
                        }
                    }
                    SolverType::Error => todo!(),
                    SolverType::Unknown => unreachable!("covered in other branch"),
                }

                // Always redirect to concrete type.
                self.set.redirect(other, concrete).expect("different nodes");
                concrete
            }
            // Both are inferred.
            ((_, SolverType::Inferred(inferred_lhs)), (_, SolverType::Inferred(inferred_rhs))) => {
                // Collect fields for inferred composite types.
                let (lhs_fields, rhs_fields) = match (inferred_lhs, inferred_rhs) {
                    // Structured types, recursively unify children.
                    (CompositeType::Ref(inner_lhs), CompositeType::Ref(inner_rhs)) => {
                        (vec![*inner_lhs], vec![*inner_rhs])
                    }
                    (
                        CompositeType::Function {
                            parameters: lhs_parameters,
                            return_ty: lhs_return_ty,
                        },
                        CompositeType::Function {
                            parameters: rhs_parameters,
                            return_ty: rhs_return_ty,
                        },
                    ) => (
                        lhs_parameters
                            .iter()
                            .cloned()
                            .chain([*lhs_return_ty])
                            .collect(),
                        rhs_parameters
                            .iter()
                            .cloned()
                            .chain([*rhs_return_ty])
                            .collect(),
                    ),
                    (CompositeType::Tuple(lhs_fields), CompositeType::Tuple(rhs_fields)) => {
                        (lhs_fields.clone(), rhs_fields.clone())
                    }

                    // Type mismatches.
                    _ => todo!(),
                };

                // Used later for assertion.
                let inferred_lhs = inferred_lhs.clone();

                // Merge the fields together.
                assert_eq!(lhs_fields.len(), rhs_fields.len());
                for (lhs, rhs) in lhs_fields.into_iter().zip(rhs_fields.into_iter()) {
                    self.unify(types, lhs, rhs);
                }

                assert_eq!(
                    self.set.redirect(lhs, rhs).expect("different nodes"),
                    SolverType::Inferred(inferred_lhs),
                );
                rhs
            }
            // Both sides are some kind of integer.
            ((lhs, kind @ SolverType::AnyInteger), (rhs, SolverType::AnyInteger))
            | ((lhs, kind @ SolverType::UnsignedInteger), (rhs, SolverType::UnsignedInteger)) => {
                let kind = kind.clone();
                assert_eq!(self.set.redirect(lhs, rhs).expect("different nodes"), kind);
                rhs
            }
            _ => {
                todo!()
            }
        }
    }
}

#[derive(Clone, Debug)]
enum Obligation {
    /// `base.field == projection`
    Projection {
        base: SolverTypeId,
        field: usize,
        result: SolverTypeId,
    },
}

#[derive(Debug)]
pub struct InferenceCtx<'hir, 'ty> {
    hir: &'hir Hir,
    types: &'ty mut Types,
    table: UnificationTable,
    environment: BTreeMap<IdentifierBindingId, SolverTypeId>,
    expressions: BTreeMap<ExpressionId, SolverTypeId>,
    concrete_type_cache: BTreeMap<TypeId, SolverTypeId>,
    obligations: Vec<Obligation>,
    return_ty: SolverTypeId,
    loop_expressions: Vec<SolverTypeId>,
}

impl<'hir, 'ty> InferenceCtx<'hir, 'ty> {
    pub fn new(
        hir: &'hir Hir,
        types: &'ty mut Types,
        environment: impl IntoIterator<Item = (IdentifierBindingId, TypeId)>,
        return_ty: TypeId,
    ) -> Self {
        let mut ctx = Self {
            hir,
            types,
            environment: BTreeMap::new(),
            table: UnificationTable::new(),
            expressions: BTreeMap::new(),
            concrete_type_cache: BTreeMap::new(),
            obligations: Vec::new(),
            // HACK: Actual return type filled below.
            return_ty: SolverTypeId::from_id(0),
            loop_expressions: Vec::new(),
        };

        ctx.return_ty = ctx.get_type(return_ty);

        for (identifier, ty) in environment {
            let ty = ctx.get_type(ty);
            assert!(ctx.environment.insert(identifier, ty).is_none());
        }

        ctx
    }

    fn process_obligations(&mut self) {
        while !self.obligations.is_empty() {
            let mut processed = false;

            for obligation in std::mem::take(&mut self.obligations) {
                match obligation {
                    Obligation::Projection {
                        base,
                        field,
                        result,
                    } => {
                        match self.table.set.get(base) {
                            SolverType::Concrete(ty) => {
                                let Type::Composite(CompositeType::Tuple(fields)) =
                                    &self.types[*ty]
                                else {
                                    panic!("cannot have projection on non-tuple type");
                                };

                                if field >= fields.len() {
                                    panic!("field out of bounds");
                                }

                                let field_ty = self.get_type(fields[field]);
                                self.table.unify(self.types, result, field_ty);

                                processed = true;
                            }
                            SolverType::Inferred(CompositeType::Tuple(fields)) => {
                                if field >= fields.len() {
                                    panic!("field out of bounds");
                                }

                                let field_ty = fields[field];
                                self.table.unify(self.types, result, field_ty);

                                processed = true;
                            }
                            SolverType::Unknown => {
                                // Try again later.
                                self.obligations.push(obligation);
                                continue;
                            }
                            _ => panic!("invalid type for projection obligation"),
                        }
                    }
                }
            }

            if !processed {
                panic!("couldn't advance obligation processing");
            }
        }
    }

    fn get_type(&mut self, ty: TypeId) -> SolverTypeId {
        *self
            .concrete_type_cache
            .entry(ty)
            .or_insert_with(|| self.table.new_concrete(ty))
    }

    fn get_boolean_type(&mut self) -> SolverTypeId {
        let boolean_type = self.types.boolean();
        self.get_type(boolean_type)
    }

    fn get_unit_type(&mut self) -> SolverTypeId {
        let boolean_type = self.types.unit();
        self.get_type(boolean_type)
    }

    fn check(&mut self, expression_id: ExpressionId, expected: SolverTypeId) {
        let expression = &self.hir[expression_id];

        match &expression.kind {
            ExpressionKind::Call(call) => {
                // Infer the call using the expected return type.
                self.infer_call(call, expected);
                let expression_ty = self.expression_solver_type(expression_id);
                self.table.unify(self.types, expression_ty, expected);
            }
            _ => {
                let inferred = self.infer(expression_id);
                self.table.unify(self.types, inferred, expected);
            }
        }
    }

    fn literal_to_solver_type(&mut self, literal: &Literal) -> SolverTypeId {
        match literal {
            Literal::Integer(_) => self.table.new_any_integer(),
            Literal::Boolean(_) => self.get_boolean_type(),
        }
    }

    fn expression_solver_type(&mut self, expression_id: ExpressionId) -> SolverTypeId {
        *self
            .expressions
            .entry(expression_id)
            .or_insert_with(|| self.table.new_unknown())
    }

    fn identifier_to_solver_type(&mut self, identifier: IdentifierBindingId) -> SolverTypeId {
        *self
            .environment
            .entry(identifier)
            .or_insert_with(|| self.table.new_unknown())
    }

    fn infer(&mut self, expression_id: ExpressionId) -> SolverTypeId {
        let expression = &self.hir[expression_id];
        let expression_ty = self.expression_solver_type(expression_id);

        let resulting_ty = match &expression.kind {
            ExpressionKind::Assign(Assign { variable, value }) => {
                // Infer the variable type.
                let variable_ty = self.infer(*variable);

                // Check that the value matches the type.
                self.check(*value, variable_ty);

                // This expression resolves to unit.
                self.get_unit_type()
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
                        let any_integer_ty = self.table.new_any_integer();
                        self.check(*lhs, any_integer_ty);
                        self.check(*rhs, any_integer_ty);

                        any_integer_ty
                    }
                    BinaryOperation::PlusWithOverflow => {
                        // Arguments must be an integer.
                        let any_integer_ty = self.table.new_any_integer();
                        self.check(*lhs, any_integer_ty);
                        self.check(*rhs, any_integer_ty);

                        let result = self.table.set.find_root(any_integer_ty);
                        let boolean_ty = self.get_boolean_type();

                        // Outcome is a tuple of `(result, overflow)`
                        self.table
                            .new_inferred(CompositeType::Tuple(vec![result, boolean_ty]))
                    }
                    BinaryOperation::Equal | BinaryOperation::NotEqual => {
                        // Infer arguments
                        let lhs_ty = self.infer(*lhs);
                        let rhs_ty = self.infer(*rhs);

                        // LHS and RHS are equal.
                        self.table.unify(self.types, lhs_ty, rhs_ty);

                        self.get_boolean_type()
                    }
                    BinaryOperation::Greater
                    | BinaryOperation::GreaterEqual
                    | BinaryOperation::Less
                    | BinaryOperation::LessEqual => {
                        // Arguments must be an integer.
                        let any_integer_ty = self.table.new_any_integer();
                        self.check(*lhs, any_integer_ty);
                        self.check(*rhs, any_integer_ty);

                        self.get_boolean_type()
                    }
                    BinaryOperation::LogicalAnd | BinaryOperation::LogicalOr => {
                        // Arguments must be a boolean.
                        let boolean_ty = self.get_boolean_type();
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
                        let any_integer = self.table.new_any_integer();

                        // Value must be any integer.
                        self.check(*value, any_integer);

                        any_integer
                    }
                    UnaryOperation::Negative => {
                        let any_signed_integer = self.table.new_any_integer();

                        // Value must be a signed integer.
                        self.check(*value, any_signed_integer);

                        any_signed_integer
                    }
                    UnaryOperation::Deref => {
                        let inner_ty = self.table.new_unknown();
                        let ref_ty = self.table.new_inferred(CompositeType::Ref(inner_ty));

                        // Value must be a reference
                        self.check(*value, ref_ty);

                        inner_ty
                    }
                    UnaryOperation::Ref => {
                        // Infer the value.
                        let inner_ty = self.infer(*value);

                        // Result is a reference to the value.
                        self.table.new_inferred(CompositeType::Ref(inner_ty))
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
                    self.get_unit_type()
                };

                for (literal, block) in branches {
                    // Ensure literal matches discriminator.
                    let literal = self.literal_to_solver_type(literal);
                    self.table.unify(self.types, discriminator, literal);

                    let expression = self.check_block(*block);

                    // Ensure the block expression matches the expression type.
                    self.check(expression, expression_ty);
                }

                expression_ty
            }
            ExpressionKind::Loop(Loop { body }) => {
                let unit = self.get_unit_type();
                let result = self.table.new_unknown();

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
            ExpressionKind::Literal(literal) => self.literal_to_solver_type(literal),
            ExpressionKind::Call(call) => {
                let return_ty = self.table.new_unknown();
                self.infer_call(call, return_ty);
                return_ty
            }
            ExpressionKind::Block(block_id) => {
                let block_expression = self.check_block(*block_id);
                self.infer(block_expression)
            }
            ExpressionKind::Variable(Variable { binding }) => {
                self.identifier_to_solver_type(*binding)
            }
            ExpressionKind::Unreachable => self.get_type(self.types.never()),
            ExpressionKind::Aggregate(Aggregate { values }) => {
                // Infer all values.
                let values = values
                    .clone()
                    .into_iter()
                    .map(|value| self.infer(value))
                    .collect::<Vec<_>>();
                self.table.new_inferred(CompositeType::Tuple(values))
            }
            ExpressionKind::Field(Field { lhs, field }) => {
                let base = self.infer(*lhs);
                let result = self.table.new_unknown();
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
                self.get_type(signature_ty)
            }
        };

        self.table.unify(self.types, expression_ty, resulting_ty)
    }

    /// Infer a function call, using the provided return type.
    fn infer_call(&mut self, call: &Call, return_ty: SolverTypeId) {
        let callee = self.infer(call.callee);

        // Generate placeholders for arguments and return type.
        let parameters = call
            .arguments
            .iter()
            .map(|_| self.table.new_unknown())
            .collect::<Vec<_>>();

        // Use the placeholders to create an inferred function signature.
        let signature_ty = self.table.new_inferred(CompositeType::Function {
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

    fn check_block(&mut self, block: BlockId) -> ExpressionId {
        let block = &self.hir[block];

        // Check all statements in block.
        for statement in &block.statements {
            self.check_statement(*statement);
        }

        block.expression
    }

    fn check_statement(&mut self, statement_id: StatementId) {
        match &self.hir[statement_id].kind {
            StatementKind::Declare(DeclareStatement { binding, ty }) => {
                let binding_ty = self.identifier_to_solver_type(*binding);

                match ty {
                    DeclarationTy::Type(type_id) => {
                        // Make sure the declaration type matches the variable.
                        let expected_ty = self.get_type(*type_id);
                        self.table.unify(self.types, binding_ty, expected_ty);
                    }
                    DeclarationTy::Inferred(expression_id) => {
                        // Variable type is determined from the corresponding variable.
                        let expression_ty = self.expression_solver_type(*expression_id);
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

    fn reify(&mut self, solver_ty: SolverTypeId) -> Option<TypeId> {
        match self.table.set.get(solver_ty) {
            SolverType::Concrete(type_id) => Some(*type_id),
            SolverType::Inferred(composite_type) => match composite_type {
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
            SolverType::AnyInteger | SolverType::SignedInteger => Some(self.types.i8()),
            SolverType::UnsignedInteger => Some(self.types.u8()),
            SolverType::Error => None,
            SolverType::Unknown => None,
        }
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
        let mut inference = InferenceCtx::new(&hir, &mut ctx.types, BTreeMap::new(), unit_ty);
        let solver_ty = inference.infer(expression_id);
        let ty = inference.reify(solver_ty).expect("valid type");

        ctx.types[ty].clone()
    }

    #[rstest]
    fn unify_u8() {
        let types = Types::new();

        let u8_ty = types.u8();

        let mut table = UnificationTable::new();

        let u8 = table.set.insert(SolverType::Concrete(u8_ty));
        let unknown = table.new_unknown();

        table.unify(&types, u8, unknown);

        assert_eq!(table.set.get(unknown), &SolverType::Concrete(u8_ty));
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
}
