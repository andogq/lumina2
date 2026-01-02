use crate::prelude::*;

use hir::Type;
use mir::*;
use thir::Thir;

pub struct MirGen<'hir, 'thir> {
    thir: &'thir Thir<'hir>,

    mir: Mir,

    bindings: HashMap<BindingId, Binding>,
    locals: FunctionLocals,

    function_ids: IndexedVec<FunctionId, hir::FunctionId>,
}

impl<'ctx, 'hir, 'thir> Pass<'ctx, 'thir> for MirGen<'hir, 'thir> {
    type Input = Thir<'hir>;
    type Output = Mir;
    type Extra = ();

    fn run(_ctx: &'ctx mut Ctx, thir: &'thir Self::Input, _extra: ()) -> PassResult<Self::Output> {
        let mut mir_gen = Self::new(thir);

        // Declare all functions.
        for function in mir_gen.thir.functions.iter_keys() {
            mir_gen.declare_function(function);
        }

        // Lower each function.
        for function in mir_gen.thir.functions.iter_keys() {
            mir_gen.lower_function(function);
        }

        Ok(PassSuccess::Ok(mir_gen.mir))
    }
}

impl<'hir, 'thir> MirGen<'hir, 'thir> {
    /// Create a new instance.
    pub fn new(thir: &'thir Thir<'hir>) -> Self {
        Self {
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
    fn lower_function(&mut self, hir_function_id: hir::FunctionId) {
        let function = &self.thir[hir_function_id];
        let (function_id, _) = self
            .function_ids
            .iter_pairs()
            .find(|(_, id)| **id == hir_function_id)
            .unwrap();

        // Create local for return value, as it must be the first.
        // TODO: Store this local in some context somewhere, to use it as the return local.
        let return_local = self.locals.create(function_id, function.return_ty.clone());

        // Following locals are all for the parameters.
        for (binding, ty) in &function.parameters {
            let local = self.locals.create(function_id, ty.clone());
            self.bindings.insert(*binding, Binding::Local(local));
        }

        // Lower the entry block.
        let block = self.lower_block(function_id, function.entry);

        // If the block resolves to a value of the same type as the return value, then it's an
        // implicit return.
        let body = &self.thir[function.entry];
        if let Some(result) = block.operand
            && self.thir.type_of(body.expression) == &function.return_ty
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
            return_ty: function.return_ty.clone(),
            parameters: function
                .parameters
                .iter()
                .map(|(_, ty)| ty.clone())
                .collect(),
            binding: function.binding,
            locals: self.locals.generate_locals(function_id),
            entry: block.entry,
        });
    }

    /// Lower a block within a function.
    fn lower_block(&mut self, function: FunctionId, block_id: hir::BlockId) -> LoweredBlock {
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
                    let local = self.locals.create(function, ty.clone());

                    // Register the local against the binding.
                    self.bindings.insert(*binding, Binding::Local(local));
                }
                hir::Statement::Return(hir::ReturnStatement { expression }) => {
                    // If a value is present, store it within the return local.
                    if let Some(value) =
                        self.lower_expression(function, &mut current_basic_block, *expression)
                    {
                        let place = self
                            .mir
                            .places
                            .insert(self.locals.return_local(function).into());
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
                    if let Some(value) =
                        self.lower_expression(function, &mut current_basic_block, *expression)
                    {
                        // TODO: Store resulting expression in the local for the current loop.
                        unimplemented!();
                    }

                    self.mir.terminate(
                        entry,
                        Terminator::Goto(todo!("work out which block to jump to")),
                    );
                }
                hir::Statement::Expression(hir::ExpressionStatement { expression }) => {
                    self.lower_expression(function, &mut current_basic_block, *expression);
                }
            }
        }

        let value = self.lower_expression(function, &mut current_basic_block, block.expression);

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
        function: FunctionId,
        basic_block: &mut BasicBlockId,
        expression_id: hir::ExpressionId,
    ) -> Option<OperandId> {
        Some(match &self.thir[expression_id] {
            hir::Expression::Assign(hir::Assign { variable, value }) => {
                let value = self.lower_expression(function, basic_block, *value)?;
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
                let lhs = self.lower_expression(function, basic_block, *lhs)?;
                let rhs = self.lower_expression(function, basic_block, *rhs)?;

                let result = self
                    .locals
                    .create(function, self.thir.type_of(expression_id).clone());
                let result_place = self.mir.places.insert(result.into());

                self.mir.add_statement(
                    *basic_block,
                    Assign {
                        place: result_place,
                        rvalue: RValue::Binary(Binary {
                            lhs,
                            operation: operation.clone(),
                            rhs,
                        }),
                    },
                );

                self.mir.operands.insert(Operand::Place(result_place))
            }
            hir::Expression::Unary(hir::Unary { operation, value }) => {
                let value = self.lower_expression(function, basic_block, *value)?;

                let result = self
                    .locals
                    .create(function, self.thir.type_of(expression_id).clone());
                let result_place = self.mir.places.insert(result.into());

                self.mir.add_statement(
                    *basic_block,
                    Assign {
                        place: result_place,
                        rvalue: RValue::Unary(Unary {
                            operation: operation.clone(),
                            value,
                        }),
                    },
                );

                self.mir.operands.insert(Operand::Place(result_place))
            }
            hir::Expression::Switch(hir::Switch {
                discriminator,
                branches,
                default,
            }) => {
                let discriminator_ty = self.thir.type_of(*discriminator);
                let discriminator = self.lower_expression(function, basic_block, *discriminator)?;

                let switch_ty = self.thir.type_of(expression_id);
                let switch_value = self.locals.create(function, switch_ty.clone());
                let switch_place = self.mir.places.insert(switch_value.into());

                let end_block = self.mir.add_basic_block();

                // Lower all of the branches.
                let targets = branches
                    .iter()
                    .map(|(target, block)| {
                        // Lower the block.
                        let lowered_block = self.lower_block(function, *block);

                        // Store the resulting block value.
                        if let Some(result) = lowered_block.operand
                            && !matches!(switch_ty, Type::Unit | Type::Never)
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
                            literal_to_constant(target, discriminator_ty),
                            lowered_block.entry,
                        )
                    })
                    .collect();

                // Generate the otherwise branch.
                let otherwise = if let Some(default) = default {
                    // Lower the block.
                    let lowered_block = self.lower_block(function, *default);

                    // Store the resulting block value.
                    if let Some(result) = lowered_block.operand
                        && !matches!(switch_ty, Type::Unit | Type::Never)
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
                // TODO: Create a new local for the loop break value, and register it somewhere.

                // Lower the loop body.
                let lowered_block = self.lower_block(function, *body);
                assert!(lowered_block.operand.is_none());

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

                // TODO: When break expressions are supported, produce the local here.
                self.mir.operands.insert(Operand::Constant(Constant::Unit))
            }
            hir::Expression::Literal(literal) => {
                self.mir
                    .operands
                    .insert(Operand::Constant(literal_to_constant(
                        literal,
                        self.thir.type_of(expression_id),
                    )))
            }
            hir::Expression::Call(hir::Call { callee, arguments }) => {
                // Create a local to store the resulting value.
                let result = self.mir.places.insert(
                    self.locals
                        .create(function, self.thir.type_of(expression_id).clone())
                        .into(),
                );
                // Create a basic block to return to after the function returns.
                let target = self.mir.add_basic_block();

                // Lower function expression and arguments.
                let callee = self
                    .lower_expression(function, basic_block, *callee)
                    .unwrap();
                let arguments = arguments
                    .iter()
                    .map(|expression| {
                        self.lower_expression(function, basic_block, *expression)
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
                let lowered_block = self.lower_block(function, *block_id);

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
        })
    }

    fn expression_to_place(&mut self, expression_id: hir::ExpressionId) -> Place {
        match &self.thir[expression_id] {
            hir::Expression::Variable(hir::Variable { binding }) => {
                self.bindings[binding].clone().as_local().into()
            }
            hir::Expression::Unary(hir::Unary {
                operation: cst::UnaryOperation::Deref(_),
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
    pub fn as_local(self) -> LocalId {
        match self {
            Self::Local(local) => local,
            _ => panic!("expected local"),
        }
    }
}

/// Track available locals within a function.
#[derive(Clone, Debug, Default)]
struct FunctionLocals(HashMap<FunctionId, IndexedVec<LocalId, (Type, Option<BindingId>)>>);
impl FunctionLocals {
    /// Create a new instance.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new local in the provided function, with the provided type.
    pub fn create(&mut self, function: FunctionId, ty: Type) -> LocalId {
        self.0.entry(function).or_default().insert((ty, None))
    }

    pub fn create_with_binding(
        &mut self,
        function: FunctionId,
        ty: Type,
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
    ) -> IndexedVec<LocalId, (Option<BindingId>, Type)> {
        let mut locals = IndexedVec::new();

        if let Some(function_locals) = self.0.get(&function) {
            for (ty, binding) in function_locals.iter() {
                locals.insert((*binding, ty.clone()));
            }
        }

        locals
    }

    /// Fetch the local corresponding with the return value for a given function.
    pub fn return_local(&self, function: FunctionId) -> LocalId {
        // HACK: Not ideal to be manually creating this.
        LocalId::from_id(0)
    }
}

fn literal_to_constant(literal: &hir::Literal, ty: &Type) -> Constant {
    match (literal, ty) {
        (hir::Literal::Integer(value), Type::I8) => Constant::I8(*value as i8),
        (hir::Literal::Integer(value), Type::U8) => Constant::U8(*value as u8),
        (hir::Literal::Boolean(value), Type::Boolean) => Constant::Boolean(*value),
        (hir::Literal::Unit, Type::Unit) => Constant::Unit,
        (literal, ty) => panic!("invalid literal {literal:?} for type {ty:?}"),
    }
}
