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
        let ret_local = self.locals.create(function_id, function.return_ty.clone());

        // Following locals are all for the parameters.
        for (binding, ty) in &function.parameters {
            let local = self.locals.create(function_id, ty.clone());
            self.bindings.insert(*binding, Binding::Local(local));
        }

        // Lower the entry block.
        let (entry, exit, result) = self.lower_block(function_id, function.entry);

        // If the block resolves to a value of the same type as the return value, then it's an
        // implicit return.
        let body = &self.thir[function.entry];
        if let Some(result) = result
            && self.thir.type_of(body.expr) == &function.return_ty
        {
            let place = self.mir.places.insert(ret_local.into());
            self.mir.add_statement(
                exit,
                Assign {
                    place,
                    rvalue: RValue::Use(result),
                },
            );
        }

        // Function block must always terminate with a return.
        self.mir.terminate_if_unterminated(exit, Terminator::Return);

        self.mir.functions.insert(Function {
            ret_ty: function.return_ty.clone(),
            params: function
                .parameters
                .iter()
                .map(|(_, ty)| ty.clone())
                .collect(),
            binding: function.binding,
            locals: self.locals.generate_locals(function_id),
            entry,
        });
    }

    fn lower_block(
        &mut self,
        function: FunctionId,
        block_id: hir::BlockId,
    ) -> (BasicBlockId, BasicBlockId, Option<OperandId>) {
        let block = &self.thir[block_id];

        // Create a new (empty) basic block to lower into.
        let basic_block = self.mir.add_basic_block();

        // Track the ending basic block.
        let mut current_basic_block = basic_block;

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
                hir::Statement::Return(hir::ReturnStatement { expr }) => {
                    // If a value is present, store it within the return local.
                    if let Some(value) = self.lower_expr(function, &mut current_basic_block, *expr)
                    {
                        let place = self
                            .mir
                            .places
                            .insert(self.locals.return_local(function).into());
                        self.mir.add_statement(
                            basic_block,
                            Assign {
                                place,
                                rvalue: RValue::Use(value),
                            },
                        );
                    }

                    self.mir.terminate(basic_block, Terminator::Return);
                }
                hir::Statement::Break(hir::BreakStatement { expr }) => {
                    if let Some(value) = self.lower_expr(function, &mut current_basic_block, *expr)
                    {
                        // TODO: Store resulting expression in the local for the current loop.
                        unimplemented!();
                    }

                    self.mir.terminate(
                        basic_block,
                        Terminator::Goto(todo!("work out which block to jump to")),
                    );
                }
                hir::Statement::Expr(hir::ExprStatement { expr }) => {
                    self.lower_expr(function, &mut current_basic_block, *expr);
                }
            }
        }

        let value = self.lower_expr(function, &mut current_basic_block, block.expr);

        (basic_block, current_basic_block, value)
    }

    fn lower_expr(
        &mut self,
        function: FunctionId,
        basic_block: &mut BasicBlockId,
        expr_id: hir::ExprId,
    ) -> Option<OperandId> {
        Some(match &self.thir[expr_id] {
            hir::Expr::Assign(hir::Assign { variable, value }) => {
                let value = self.lower_expr(function, basic_block, *value)?;
                let place = self.expr_to_place(*variable);
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
            hir::Expr::Binary(hir::Binary { lhs, op, rhs }) => {
                let lhs = self.lower_expr(function, basic_block, *lhs)?;
                let rhs = self.lower_expr(function, basic_block, *rhs)?;

                let result = self
                    .locals
                    .create(function, self.thir.type_of(expr_id).clone());
                let result_place = self.mir.places.insert(result.into());

                self.mir.add_statement(
                    *basic_block,
                    Assign {
                        place: result_place,
                        rvalue: RValue::Binary(Binary {
                            lhs,
                            op: op.clone(),
                            rhs,
                        }),
                    },
                );

                self.mir.operands.insert(Operand::Place(result_place))
            }
            hir::Expr::Unary(hir::Unary { op, value }) => {
                let value = self.lower_expr(function, basic_block, *value)?;

                let result = self
                    .locals
                    .create(function, self.thir.type_of(expr_id).clone());
                let result_place = self.mir.places.insert(result.into());

                self.mir.add_statement(
                    *basic_block,
                    Assign {
                        place: result_place,
                        rvalue: RValue::Unary(Unary {
                            op: op.clone(),
                            value,
                        }),
                    },
                );

                self.mir.operands.insert(Operand::Place(result_place))
            }
            hir::Expr::Switch(hir::Switch {
                discriminator,
                branches,
                default,
            }) => {
                let discriminator_ty = self.thir.type_of(*discriminator);
                let discriminator = self.lower_expr(function, basic_block, *discriminator)?;

                let switch_ty = self.thir.type_of(expr_id);
                let switch_value = self.locals.create(function, switch_ty.clone());
                let switch_place = self.mir.places.insert(switch_value.into());

                let end_block = self.mir.add_basic_block();

                // Lower all of the branches.
                let targets = branches
                    .iter()
                    .map(|(target, block)| {
                        // Lower the block.
                        let (basic_block_entry, basic_block_exit, result) =
                            self.lower_block(function, *block);

                        // Store the resulting block value.
                        if let Some(result) = result
                            && !matches!(switch_ty, Type::Unit | Type::Never)
                        {
                            self.mir.add_statement(
                                basic_block_exit,
                                Assign {
                                    place: switch_place,
                                    rvalue: RValue::Use(result),
                                },
                            );
                        }

                        // If required, jump to the ending basic block.
                        self.mir.terminate_if_unterminated(
                            basic_block_exit,
                            Goto {
                                basic_block: end_block,
                            },
                        );

                        (
                            literal_to_constant(target, discriminator_ty),
                            basic_block_entry,
                        )
                    })
                    .collect();

                // Generate the otherwise branch.
                let otherwise = if let Some(default) = default {
                    // Lower the block.
                    let (basic_block_entry, basic_block_exit, result) =
                        self.lower_block(function, *default);

                    // Store the resulting block value.
                    if let Some(result) = result
                        && !matches!(switch_ty, Type::Unit | Type::Never)
                    {
                        self.mir.add_statement(
                            basic_block_exit,
                            Assign {
                                place: switch_place,
                                rvalue: RValue::Use(result),
                            },
                        );
                    }

                    // If required, jump to the ending basic block.
                    self.mir.terminate_if_unterminated(
                        basic_block_exit,
                        Goto {
                            basic_block: end_block,
                        },
                    );

                    basic_block_entry
                } else {
                    end_block
                };

                // Terminate the current block.
                self.mir.terminate(
                    *basic_block,
                    SwitchInt {
                        discriminator,
                        targets,
                        otherwise,
                    },
                );

                // Update the current basic block to be pointing to the new end block.
                *basic_block = end_block;

                self.mir.operands.insert(Operand::Place(switch_place))
            }
            hir::Expr::Loop(hir::Loop { body }) => {
                // TODO: Create a new local for the loop break value, and register it somewhere.

                // Lower the loop body.
                let (loop_entry, loop_exit, loop_value) = self.lower_block(function, *body);
                assert!(loop_value.is_none());

                // If the loop exits unterminated, loop back to the entry.
                self.mir.terminate_if_unterminated(
                    loop_exit,
                    Goto {
                        basic_block: loop_entry,
                    },
                );

                // Jump to the loop entry.
                self.mir.terminate(
                    *basic_block,
                    Goto {
                        basic_block: loop_entry,
                    },
                );

                // TODO: When break expressions are supported, produce the local here.
                self.mir.operands.insert(Operand::Constant(Constant::Unit))
            }
            hir::Expr::Literal(literal) => {
                self.mir
                    .operands
                    .insert(Operand::Constant(literal_to_constant(
                        literal,
                        self.thir.type_of(expr_id),
                    )))
            }
            hir::Expr::Call(hir::Call { callee, arguments }) => {
                // Create a local to store the resulting value.
                let result = self.mir.places.insert(
                    self.locals
                        .create(function, self.thir.type_of(expr_id).clone())
                        .into(),
                );
                // Create a basic block to return to after the function returns.
                let target = self.mir.add_basic_block();

                // Lower function expression and arguments.
                let func = self.lower_expr(function, basic_block, *callee).unwrap();
                let args = arguments
                    .iter()
                    .map(|expr| self.lower_expr(function, basic_block, *expr).unwrap())
                    .collect();

                // Terminate the current block.
                self.mir.terminate(
                    *basic_block,
                    Call {
                        func,
                        args,
                        destination: result,
                        target,
                    },
                );

                // Update the cursor to point at the returning block.
                *basic_block = target;

                // Produce the value of this function.
                self.mir.operands.insert(Operand::Place(result))
            }
            hir::Expr::Block(block_id) => {
                // Lower the block
                let (entry, exit, value) = self.lower_block(function, *block_id);

                // Jump to the block's entry.
                let terminator_id = self.mir[*basic_block].terminator;
                self.mir[terminator_id] = Terminator::Goto(Goto { basic_block: entry });

                // Update cursor to basic block's exit.
                *basic_block = exit;

                // Yield the block's value.
                value?
            }
            hir::Expr::Variable(hir::Variable { binding }) => match self.bindings[binding] {
                Binding::Local(local) => {
                    let place = self.mir.places.insert(local.into());
                    self.mir.operands.insert(Operand::Place(place))
                }
                Binding::Function(function_id) => self
                    .mir
                    .operands
                    .insert(Operand::Constant(Constant::Function(function_id))),
            },
            hir::Expr::Unreachable => return None,
        })
    }

    fn expr_to_place(&mut self, expr_id: hir::ExprId) -> Place {
        match &self.thir[expr_id] {
            hir::Expr::Variable(hir::Variable { binding }) => {
                self.bindings[binding].clone().as_local().into()
            }
            hir::Expr::Unary(hir::Unary {
                op: cst::UnaryOp::Deref(_),
                value,
            }) => {
                let mut value = self.expr_to_place(*value);
                // TODO: Not sure if this is append or prepend.
                value.projection.push(Projection::Deref);
                value
            }
            expr => panic!("invalid lhs: {expr:?}"),
        }
    }
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
