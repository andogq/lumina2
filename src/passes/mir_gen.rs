use crate::prelude::*;

use mir::{UnaryOperation, *};
use thir::Thir;

pub struct MirGen<'ctx, 'hir, 'thir> {
    ctx: &'ctx mut Ctx,
    thir: &'thir Thir<'hir>,

    mir: Mir,

    bindings: HashMap<BindingId, Binding>,
    locals: FunctionLocals,

    function_ids: IndexedVec<FunctionId, hir::FunctionId>,
}

impl<'ctx, 'hir, 'thir> Pass<'ctx, 'thir> for MirGen<'ctx, 'hir, 'thir> {
    type Input = Thir<'hir>;
    type Output = Mir;
    type Extra = ();

    fn run(ctx: &'ctx mut Ctx, thir: &'thir Self::Input, _extra: ()) -> PassResult<Self::Output> {
        let mut mir_gen = Self::new(ctx, thir);

        let mut errors = Vec::new();

        // Declare all functions.
        for function in mir_gen.thir.functions.iter_keys() {
            mir_gen.declare_function(function);
        }

        // Lower each function.
        for function in mir_gen.thir.functions.iter_keys() {
            let _ = run_and_report!(mir_gen.ctx, errors, || mir_gen
                .lower_function(function)
                .map_err(|err| CError::from(err)
                    .fatal()
                    .with_message("failed to lower function to MIR")));
        }

        Ok(PassSuccess::new(mir_gen.mir, errors))
    }
}

impl<'ctx, 'hir, 'thir> MirGen<'ctx, 'hir, 'thir> {
    /// Create a new instance.
    pub fn new(ctx: &'ctx mut Ctx, thir: &'thir Thir<'hir>) -> Self {
        Self {
            ctx,
            thir,
            mir: Mir::new(),
            bindings: HashMap::new(),
            locals: FunctionLocals::new(),
            function_ids: IndexedVec::new(),
        }
    }

    /// Declare a function by creating a new binding.
    fn declare_function(&mut self, hir_function_id: hir::FunctionId) {
        assert!(!self.function_ids.contains(&hir_function_id));

        let function_binding = self.thir[hir_function_id].binding;
        let function_id = self.function_ids.insert(hir_function_id);
        self.bindings
            .insert(function_binding, Binding::Function(function_id));
    }

    /// Lower a function.
    fn lower_function(&mut self, hir_function_id: hir::FunctionId) -> Result<(), MirGenError> {
        let function = &self.thir[hir_function_id];
        let (function_id, _) = self
            .function_ids
            .iter_pairs()
            .find(|(_, id)| **id == hir_function_id)
            .ok_or(MirGenError::FunctionNotFound(hir_function_id))?;

        // Create local for return value, as it must be the first.
        // TODO: Store this local in some context somewhere, to use it as the return local.
        let return_local = self.locals.create(function_id, function.return_ty);

        // Following locals are all for the parameters.
        for (binding, ty) in &function.parameters {
            let local = self.locals.create_with_binding(function_id, *ty, *binding);
            self.bindings.insert(*binding, Binding::Local(local));
        }

        // Lower the entry block.
        let ctx = FunctionCtx::new(function_id);
        let block = self.lower_block(&ctx, function.entry);

        // If the block resolves to a value of the same type as the return value, then it's an
        // implicit return.
        let body = &self.thir[function.entry];
        if let Some(result) = block.operand
            && self.thir.type_of(body.expression) == function.return_ty
        {
            let place = self.mir.places.insert(return_local.into());
            self.mir.add_statement(
                block.exit,
                Assign {
                    place,
                    rvalue: RValue::Use(result),
                },
            );
        }

        // Function block must always terminate with a return.
        self.mir
            .terminate_if_unterminated(block.exit, Terminator::Return);

        self.mir.functions.insert(Function {
            return_ty: function.return_ty,
            parameters: function.parameters.iter().map(|(_, ty)| *ty).collect(),
            binding: function.binding,
            locals: self.locals.generate_locals(function_id),
            entry: block.entry,
        });

        Ok(())
    }

    /// Lower a block within a function.
    fn lower_block(&mut self, ctx: &FunctionCtx, block_id: hir::BlockId) -> LoweredBlock {
        let block = &self.thir[block_id];

        // Create a new (empty) basic block to lower into.
        let entry = self.mir.add_basic_block();

        // Track the ending basic block.
        let mut current_basic_block = entry;

        for statement in &block.statements {
            match &self.thir[*statement] {
                hir::Statement::Declare(hir::DeclareStatement { binding, .. }) => {
                    // Fetch the type of the binding.
                    let ty = self.thir.type_of(*binding);

                    // Create a local for the binding.
                    let local = self.locals.create_with_binding(ctx.function, ty, *binding);

                    // Register the local against the binding.
                    self.bindings.insert(*binding, Binding::Local(local));
                }
                hir::Statement::Return(hir::ReturnStatement { expression }) => {
                    // If a value is present, store it within the return local.
                    if let Some(value) =
                        self.lower_expression(ctx, &mut current_basic_block, *expression)
                    {
                        let place = self
                            .mir
                            .places
                            .insert(self.locals.return_local(ctx.function).into());
                        self.mir.add_statement(
                            entry,
                            Assign {
                                place,
                                rvalue: RValue::Use(value),
                            },
                        );
                    }

                    self.mir.terminate(entry, Terminator::Return);
                }
                hir::Statement::Break(hir::BreakStatement { expression }) => {
                    let (loop_place, loop_exit) =
                        ctx.current_loop().expect("currently within a loop");

                    if let Some(value) =
                        self.lower_expression(ctx, &mut current_basic_block, *expression)
                        // HACK: This check shouldn't be required, as `Constant::Unit` shouldn't exist
                        // in MIR
                        && self.thir.type_of(*expression) != self.ctx.types.unit()
                    {
                        self.mir.add_statement(
                            current_basic_block,
                            Assign {
                                place: loop_place,
                                rvalue: RValue::Use(value),
                            },
                        );
                    }

                    self.mir.terminate(
                        entry,
                        Goto {
                            basic_block: loop_exit,
                        },
                    );
                }
                hir::Statement::Expression(hir::ExpressionStatement { expression }) => {
                    self.lower_expression(ctx, &mut current_basic_block, *expression);
                }
            }
        }

        let value = self.lower_expression(ctx, &mut current_basic_block, block.expression);

        LoweredBlock {
            entry,
            exit: current_basic_block,
            operand: value,
        }
    }

    /// Lower an expression into a basic block. Accepts a cursor to the current basic block, so it
    /// may be updated as new blocks are created for sub-expressions.
    fn lower_expression(
        &mut self,
        ctx: &FunctionCtx,
        basic_block: &mut BasicBlockId,
        expression_id: hir::ExpressionId,
    ) -> Option<OperandId> {
        Some(match &self.thir[expression_id] {
            hir::Expression::Assign(hir::Assign { variable, value }) => {
                let value = self.lower_expression(ctx, basic_block, *value)?;
                let place = self.expression_to_place(*variable);
                let place = self.mir.places.insert(place);

                self.mir.add_statement(
                    *basic_block,
                    Assign {
                        place,
                        rvalue: RValue::Use(value),
                    },
                );

                self.mir.operands.insert(Operand::Constant(Constant::Unit))
            }
            hir::Expression::Binary(hir::Binary {
                lhs,
                operation,
                rhs,
            }) => {
                let lhs = self.lower_expression(ctx, basic_block, *lhs)?;
                let rhs = self.lower_expression(ctx, basic_block, *rhs)?;

                let result = self
                    .locals
                    .create(ctx.function, self.thir.type_of(expression_id));
                let result_place = self.mir.places.insert(result.into());

                self.mir.add_statement(
                    *basic_block,
                    Assign {
                        place: result_place,
                        rvalue: RValue::Binary(Binary {
                            lhs,
                            operation: *operation,
                            rhs,
                        }),
                    },
                );

                self.mir.operands.insert(Operand::Place(result_place))
            }
            hir::Expression::Unary(hir::Unary { operation, value }) => {
                let value = self.lower_expression(ctx, basic_block, *value)?;

                /// Helper to create a new place to store the result of the unary operation.
                #[inline]
                fn create_result_place(
                    mir_gen: &mut MirGen,
                    function: FunctionId,
                    expression_id: hir::ExpressionId,
                ) -> PlaceId {
                    let result = mir_gen
                        .locals
                        .create(function, mir_gen.thir.type_of(expression_id));
                    mir_gen.mir.places.insert(result.into())
                }

                /// Perform a unary operation, by creating a new [`Place`] for the result, adding a
                /// [`Statement`] with the operation, and returning an [`OperandId`] to the result.
                #[inline]
                fn create_unary_operation(
                    mir_gen: &mut MirGen,
                    function: FunctionId,
                    basic_block: &BasicBlockId,
                    expression_id: hir::ExpressionId,
                    value: OperandId,
                    operation: UnaryOperation,
                ) -> OperandId {
                    // Create a place for the result to be inserted.
                    let result_place = create_result_place(mir_gen, function, expression_id);

                    // Perform the operation.
                    mir_gen.mir.add_statement(
                        *basic_block,
                        Assign {
                            place: result_place,
                            rvalue: RValue::Unary(Unary { operation, value }),
                        },
                    );

                    // Produce the operation result.
                    mir_gen.mir.operands.insert(Operand::Place(result_place))
                }

                match operation {
                    // Standard `!` operation.
                    crate::ir::UnaryOperation::Not => create_unary_operation(
                        self,
                        ctx.function,
                        basic_block,
                        expression_id,
                        value,
                        UnaryOperation::Not,
                    ),
                    // Standard `-` operation.
                    crate::ir::UnaryOperation::Negative => create_unary_operation(
                        self,
                        ctx.function,
                        basic_block,
                        expression_id,
                        value,
                        UnaryOperation::Negative,
                    ),
                    // Modifies a `Place` by adding the `Deref` projection.
                    crate::ir::UnaryOperation::Deref => {
                        let target_place = self.operand_as_place(ctx.function, basic_block, value);

                        // TODO: Make sure that `target_place` is only used in one place, otherwise
                        // clone it.
                        let mut place = self.mir[target_place].clone();
                        place.projection.push(Projection::Deref);

                        self.mir
                            .operands
                            .insert(Operand::Place(self.mir.places.insert(place)))
                    }
                    // Uses `RValue::Ref`.
                    crate::ir::UnaryOperation::Ref => {
                        let result_place = create_result_place(self, ctx.function, expression_id);

                        let target_place = self.operand_as_place(ctx.function, basic_block, value);
                        self.mir.add_statement(
                            *basic_block,
                            Assign {
                                place: result_place,
                                rvalue: RValue::Ref(target_place),
                            },
                        );

                        self.mir.operands.insert(Operand::Place(result_place))
                    }
                }
            }
            hir::Expression::Switch(hir::Switch {
                discriminator,
                branches,
                default,
            }) => {
                let discriminator_ty = self.thir.type_of(*discriminator);
                let discriminator = self.lower_expression(ctx, basic_block, *discriminator)?;

                let switch_ty = self.thir.type_of(expression_id);
                let switch_value = self.locals.create(ctx.function, switch_ty);
                let switch_place = self.mir.places.insert(switch_value.into());

                let end_block = self.mir.add_basic_block();

                // Lower all of the branches.
                let targets = branches
                    .iter()
                    .map(|(target, block)| {
                        // Lower the block.
                        let lowered_block = self.lower_block(ctx, *block);

                        // Store the resulting block value.
                        if let Some(result) = lowered_block.operand
                            && !matches!(&self.ctx.types[switch_ty], Type::Unit | Type::Never)
                        {
                            self.mir.add_statement(
                                lowered_block.exit,
                                Assign {
                                    place: switch_place,
                                    rvalue: RValue::Use(result),
                                },
                            );
                        }

                        // If required, jump to the ending basic block.
                        self.mir.terminate_if_unterminated(
                            lowered_block.exit,
                            Goto {
                                basic_block: end_block,
                            },
                        );

                        (
                            literal_to_constant(&self.ctx.types, target, discriminator_ty),
                            lowered_block.entry,
                        )
                    })
                    .collect();

                // Generate the otherwise branch.
                let otherwise = if let Some(default) = default {
                    // Lower the block.
                    let lowered_block = self.lower_block(ctx, *default);

                    // Store the resulting block value.
                    if let Some(result) = lowered_block.operand
                        && !matches!(&self.ctx.types[switch_ty], Type::Unit | Type::Never)
                    {
                        self.mir.add_statement(
                            lowered_block.exit,
                            Assign {
                                place: switch_place,
                                rvalue: RValue::Use(result),
                            },
                        );
                    }

                    // If required, jump to the ending basic block.
                    self.mir.terminate_if_unterminated(
                        lowered_block.exit,
                        Goto {
                            basic_block: end_block,
                        },
                    );

                    lowered_block.entry
                } else {
                    end_block
                };

                // Terminate the current block.
                self.mir.terminate(
                    *basic_block,
                    SwitchInteger {
                        discriminator,
                        targets,
                        otherwise,
                    },
                );

                // Update the current basic block to be pointing to the new end block.
                *basic_block = end_block;

                self.mir.operands.insert(Operand::Place(switch_place))
            }
            hir::Expression::Loop(hir::Loop { body }) => {
                // Create a new local for the loop break value.
                let loop_local = self
                    .locals
                    .create(ctx.function, self.thir.type_of(expression_id));
                let loop_place = self.mir.places.insert(loop_local.into());

                // Create exit basic block.
                let exit = self.mir.add_basic_block();

                // Lower the loop body.
                let loop_ctx = ctx.push_loop(loop_place, exit);
                let lowered_block = self.lower_block(&loop_ctx, *body);

                // If the loop exits unterminated, loop back to the entry.
                self.mir.terminate_if_unterminated(
                    lowered_block.exit,
                    Goto {
                        basic_block: lowered_block.entry,
                    },
                );

                // Jump to the loop entry.
                self.mir.terminate(
                    *basic_block,
                    Goto {
                        basic_block: lowered_block.entry,
                    },
                );

                // Continue lowering into exit basic block.
                *basic_block = exit;

                // Produce the local for the break value.
                self.mir.operands.insert(Operand::Place(loop_place))
            }
            hir::Expression::Literal(literal) => {
                self.mir
                    .operands
                    .insert(Operand::Constant(literal_to_constant(
                        &self.ctx.types,
                        literal,
                        self.thir.type_of(expression_id),
                    )))
            }
            hir::Expression::Call(hir::Call { callee, arguments }) => {
                // Create a local to store the resulting value.
                let result = self.mir.places.insert(
                    self.locals
                        .create(ctx.function, self.thir.type_of(expression_id))
                        .into(),
                );
                // Create a basic block to return to after the function returns.
                let target = self.mir.add_basic_block();

                // Lower function expression and arguments.
                let callee = self.lower_expression(ctx, basic_block, *callee).unwrap();
                let arguments = arguments
                    .iter()
                    .map(|expression| {
                        self.lower_expression(ctx, basic_block, *expression)
                            .unwrap()
                    })
                    .collect();

                // Terminate the current block.
                self.mir.terminate(
                    *basic_block,
                    Call {
                        function: callee,
                        arguments,
                        destination: result,
                        target,
                    },
                );

                // Update the cursor to point at the returning block.
                *basic_block = target;

                // Produce the value of this function.
                self.mir.operands.insert(Operand::Place(result))
            }
            hir::Expression::Block(block_id) => {
                // Lower the block
                let lowered_block = self.lower_block(ctx, *block_id);

                // Jump to the block's entry.
                self.mir.terminate(
                    *basic_block,
                    Goto {
                        basic_block: lowered_block.entry,
                    },
                );

                // Update cursor to basic block's exit.
                *basic_block = lowered_block.exit;

                // Yield the block's value.
                lowered_block.operand?
            }
            hir::Expression::Variable(hir::Variable { binding }) => match self.bindings[binding] {
                Binding::Local(local) => {
                    let place = self.mir.places.insert(local.into());
                    self.mir.operands.insert(Operand::Place(place))
                }
                Binding::Function(function_id) => self
                    .mir
                    .operands
                    .insert(Operand::Constant(Constant::Function(function_id))),
            },
            hir::Expression::Unreachable => return None,
            hir::Expression::Aggregate(hir::Aggregate { values }) => {
                let ty = self.thir.type_of(expression_id);

                // Create a local to store the resulting value in.
                let result = self.locals.create(ctx.function, ty);
                let result_place = self.mir.places.insert(result.into());

                // Create the RValue.
                let aggregate = Aggregate {
                    values: values
                        .iter()
                        .map(|value| self.lower_expression(ctx, basic_block, *value).unwrap())
                        .collect(),
                    ty,
                };
                self.mir.add_statement(
                    *basic_block,
                    Assign {
                        place: result_place,
                        rvalue: RValue::Aggregate(aggregate),
                    },
                );

                // Produce the resulting place.
                self.mir.operands.insert(Operand::Place(result_place))
            }
        })
    }

    fn expression_to_place(&mut self, expression_id: hir::ExpressionId) -> Place {
        match &self.thir[expression_id] {
            hir::Expression::Variable(hir::Variable { binding }) => {
                self.bindings[binding].clone().into_local().into()
            }
            hir::Expression::Unary(hir::Unary {
                operation: crate::ir::UnaryOperation::Deref,
                value,
            }) => {
                let mut value = self.expression_to_place(*value);
                // TODO: Not sure if this is append or prepend.
                value.projection.push(Projection::Deref);
                value
            }
            expression => panic!("invalid lhs: {expression:?}"),
        }
    }

    /// Produce a [`Place`] for an [`Operand`]. If [`Operand::Constant`] is encountered, it will
    /// be loaded into a local.
    fn operand_as_place(
        &mut self,
        function: FunctionId,
        basic_block: &BasicBlockId,
        operand: OperandId,
    ) -> PlaceId {
        match &self.mir[operand] {
            // Operand is already a place, so use that directly.
            Operand::Place(place_id) => *place_id,
            // Put the constant into a local.
            Operand::Constant(constant) => {
                let constant_ty = match constant {
                    Constant::U8(_) => self.ctx.types.u8(),
                    Constant::I8(_) => self.ctx.types.i8(),
                    Constant::Boolean(_) => self.ctx.types.boolean(),
                    Constant::Unit => self.ctx.types.unit(),
                    Constant::Function(function_id) => {
                        let function = &self.mir[*function_id];
                        self.ctx
                            .types
                            .function(function.parameters.iter().cloned(), function.return_ty)
                    }
                };
                let constant_local = self.locals.create(function, constant_ty);
                let constant_place = self.mir.places.insert(constant_local.into());
                self.mir.add_statement(
                    *basic_block,
                    Assign {
                        place: constant_place,
                        rvalue: RValue::Use(operand),
                    },
                );
                constant_place
            }
        }
    }
}

/// The result of lowering a block.
#[derive(Clone, Debug)]
struct LoweredBlock {
    /// Entry basic block.
    entry: BasicBlockId,
    /// Exit basic block.
    exit: BasicBlockId,
    /// Operand yielded from block (if it exists).
    operand: Option<OperandId>,
}

#[derive(Clone, Debug)]
enum Binding {
    Local(LocalId),
    Function(FunctionId),
}

impl Binding {
    pub fn into_local(self) -> LocalId {
        match self {
            Self::Local(local) => local,
            _ => panic!("expected local"),
        }
    }
}

/// Track available locals within a function.
#[derive(Clone, Debug, Default)]
struct FunctionLocals(HashMap<FunctionId, IndexedVec<LocalId, (TypeId, Option<BindingId>)>>);
impl FunctionLocals {
    /// Create a new instance.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new local in the provided function, with the provided type.
    pub fn create(&mut self, function: FunctionId, ty: TypeId) -> LocalId {
        self.0.entry(function).or_default().insert((ty, None))
    }

    pub fn create_with_binding(
        &mut self,
        function: FunctionId,
        ty: TypeId,
        binding: BindingId,
    ) -> LocalId {
        self.0
            .entry(function)
            .or_default()
            .insert((ty, Some(binding)))
    }

    pub fn generate_locals(
        &self,
        function: FunctionId,
    ) -> IndexedVec<LocalId, (Option<BindingId>, TypeId)> {
        let mut locals = IndexedVec::new();

        if let Some(function_locals) = self.0.get(&function) {
            for (ty, binding) in function_locals.iter() {
                locals.insert((*binding, *ty));
            }
        }

        locals
    }

    /// Fetch the local corresponding with the return value for a given function.
    pub fn return_local(&self, _function: FunctionId) -> LocalId {
        // HACK: Not ideal to be manually creating this.
        LocalId::from_id(0)
    }
}

/// Context used when lowering things within a [`Function`].
#[derive(Clone, Debug)]
struct FunctionCtx {
    /// Current function.
    function: FunctionId,
    /// [`PlaceId`] for result, and [`BasicBlockId`] for exit, each corresponding to enclosing loops.
    loops: Vec<(PlaceId, BasicBlockId)>,
}

impl FunctionCtx {
    /// Create a new context within the provided function.
    pub fn new(function: FunctionId) -> Self {
        Self {
            function,
            loops: Vec::new(),
        }
    }

    /// Enter a new loop, with the provided [`PlaceId`] and exit [`BasicBlockId`].
    pub fn push_loop(&self, place: PlaceId, exit: BasicBlockId) -> Self {
        let mut ctx = self.clone();
        ctx.loops.push((place, exit));
        ctx
    }

    /// Produce the [`PlaceId`] and exit [`BasicBlockId`] corresponding to the inner-most loop.
    pub fn current_loop(&self) -> Option<(PlaceId, BasicBlockId)> {
        self.loops.last().cloned()
    }
}

fn literal_to_constant(types: &Types, literal: &hir::Literal, ty: TypeId) -> Constant {
    match (literal, &types[ty]) {
        (hir::Literal::Integer(value), Type::I8) => Constant::I8(*value as i8),
        (hir::Literal::Integer(value), Type::U8) => Constant::U8(*value as u8),
        (hir::Literal::Boolean(value), Type::Boolean) => Constant::Boolean(*value),
        (hir::Literal::Unit, Type::Unit) => Constant::Unit,
        (literal, ty) => panic!("invalid literal {literal:?} for type {ty:?}"),
    }
}

#[derive(Clone, Debug, thiserror::Error)]
pub enum MirGenError {
    #[error("could not find function {0:?}")]
    FunctionNotFound(hir::FunctionId),
}
