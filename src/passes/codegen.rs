// spell-checker:ignore IntPredicate, into_int_value, get_param_iter, build_int, const_int
use inkwell::{
    AddressSpace, IntPredicate,
    basic_block::BasicBlock as IBasicBlock,
    builder::Builder,
    context::Context,
    module::Module,
    types::{BasicType, BasicTypeEnum, FunctionType},
    values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue},
};

use crate::prelude::*;

use hir::Type;
use mir::*;

pub struct Codegen<'ctx, 'mir, 'ink> {
    ctx: &'ctx mut Ctx,
    mir: &'mir Mir,

    ink: &'ink Context,
    module: Module<'ink>,

    functions: IndexedVec<FunctionId, FunctionValue<'ink>>,
    locals: IndexedVec<FunctionId, IndexedVec<LocalId, (PointerValue<'ink>, Type)>>,
    basic_blocks: HashMap<BasicBlockId, IBasicBlock<'ink>>,
}

impl<'ctx, 'mir, 'ink> Pass<'ctx, 'mir> for Codegen<'ctx, 'mir, 'ink> {
    type Input = Mir;
    type Output = Module<'ink>;
    type Extra = &'ink Context;

    fn run(
        ctx: &'ctx mut Ctx,
        mir: &'mir Self::Input,
        ink: Self::Extra,
    ) -> PassResult<Self::Output> {
        let mut pass = Self::new(ctx, mir, ink);

        // Declare each function.
        for function_id in pass.mir.functions.iter_keys() {
            pass.declare_function(function_id);
        }

        // Lower each function.
        for function_id in pass.mir.functions.iter_keys() {
            pass.lower_function(function_id);
        }

        // Verify all functions.
        for function_id in pass.mir.functions.iter_keys() {
            assert!(pass.verify(function_id));
        }

        Ok(PassSuccess::Ok(pass.module))
    }
}

impl<'ctx, 'mir, 'ink> Codegen<'ctx, 'mir, 'ink> {
    fn new(ctx: &'ctx mut Ctx, mir: &'mir Mir, ink: &'ink Context) -> Self {
        Self {
            ctx,
            mir,
            ink,
            module: ink.create_module("module"),
            functions: IndexedVec::new(),
            locals: IndexedVec::new(),
            basic_blocks: HashMap::new(),
        }
    }

    /// Declare a function in the LLVM module.
    ///
    /// This must be called in order of ascending [`FunctionId`].
    fn declare_function(&mut self, function_id: FunctionId) {
        let function = &self.mir[function_id];

        let value = self.module.add_function(
            self.ctx
                .strings
                .get(self.ctx.scopes.to_string(function.binding)),
            self.function_ty(&function.return_ty, &function.parameters),
            None,
        );

        assert_eq!(
            self.functions.insert(value),
            function_id,
            "expect `declare_function` to be called in order"
        );

        assert_eq!(
            self.locals.insert(IndexedVec::new()),
            function_id,
            "expect `declare_function` to be called in order"
        );
    }

    /// Verify that a function is well-formed.
    fn verify(&self, function_id: FunctionId) -> bool {
        self.functions[function_id].verify(true)
    }

    fn lower_function(&mut self, function_id: FunctionId) {
        let function = &self.mir[function_id];
        let value = self.functions[function_id];

        assert_eq!(
            value.count_basic_blocks(),
            0,
            "function must not have any basic blocks"
        );

        // Create entry basic block for the function.
        let entry = self.ink.append_basic_block(value, "entry");

        let builder = self.ink.create_builder();
        builder.position_at_end(entry);

        // Declare all locals.
        for (i, (binding, ty)) in function.locals.iter().enumerate() {
            let alloca = match binding {
                Some(binding) => builder.build_alloca(
                    self.basic_ty(ty),
                    self.ctx.strings.get(self.ctx.scopes.to_string(*binding)),
                ),
                None => builder.build_alloca(self.basic_ty(ty), format!("local_{i}").as_str()),
            }
            .unwrap();

            // TODO: Find better way to collect all locals against their `LocalId`.
            assert_eq!(
                self.locals[function_id].insert((alloca, ty.clone())),
                LocalId::from_id(i)
            );
        }

        // HACK: Load all parameters (first local is the return value, so skip it).
        for ((ptr, _), parameter) in self.locals[function_id]
            .iter()
            .skip(1)
            .zip(value.get_param_iter())
        {
            builder.build_store(*ptr, parameter).unwrap();
        }

        // Lower the function body.
        let entry = self.lower_block(function_id, function.entry);

        // Unconditionally jump to the user entry block.
        builder.build_unconditional_branch(entry).unwrap();
    }

    fn lower_block(
        &mut self,
        function_id: FunctionId,
        block_id: BasicBlockId,
    ) -> IBasicBlock<'ink> {
        // If present, the block has already been lowered.
        if let Some(entry) = self.basic_blocks.get(&block_id) {
            return *entry;
        }

        let block = &self.mir[block_id];

        // Create the basic block and the builder.
        let function = self.functions[function_id];
        let bb = self
            .ink
            .append_basic_block(function, format!("{block_id:?}").as_str());
        let builder = self.ink.create_builder();
        builder.position_at_end(bb);

        // Save the basic block.
        self.basic_blocks.insert(block_id, bb);

        // Lower each statement.
        for statement in &block.statements {
            match &self.mir[*statement] {
                Statement::Assign(Assign { place, rvalue }) => {
                    let (ptr, ptr_ty) = self.resolve_place(&builder, function_id, *place);
                    let (value, ty) = self.resolve_rvalue(&builder, function_id, rvalue);

                    assert_eq!(ptr_ty, ty);

                    builder.build_store(ptr, value).unwrap();
                }
                Statement::StorageLive(_) => todo!(),
                Statement::StorageDead(_) => todo!(),
            }
        }

        // Lower the terminator.
        match &self.mir[block.terminator] {
            Terminator::Call(Call {
                function,
                arguments,
                destination,
                target,
            }) => {
                // Lower arguments.
                let arguments = arguments
                    .iter()
                    .map(|argument| {
                        self.resolve_operand(&builder, function_id, *argument)
                            .0
                            .into()
                    })
                    .collect::<Vec<_>>();

                // Lower function call.
                let return_value = match &self.mir[*function] {
                    // If possible. use a direct call.
                    Operand::Constant(Constant::Function(function_id)) => {
                        let function = self.functions[*function_id];
                        builder
                            .build_direct_call(
                                function,
                                arguments.as_slice(),
                                self.ctx
                                    .strings
                                    .get(self.ctx.scopes.to_string(self.mir[*function_id].binding)),
                            )
                            .unwrap()
                            .try_as_basic_value()
                            .left()
                            .unwrap()
                    }
                    // Otherwise fall back to an indirect call.
                    _ => {
                        let (function_ptr, function_ty) =
                            self.resolve_operand(&builder, function_id, *function);
                        let Type::Function {
                            parameters,
                            return_ty,
                        } = function_ty
                        else {
                            panic!();
                        };
                        let function_ty = self.function_ty(&return_ty, &parameters);

                        builder
                            .build_indirect_call(
                                function_ty,
                                function_ptr.into_pointer_value(),
                                arguments.as_slice(),
                                "function_indirect",
                            )
                            .unwrap()
                            .try_as_basic_value()
                            .left()
                            .unwrap()
                    }
                };

                // Save the return value to the relevant local.
                let (return_value_ptr, _) = self.resolve_place(&builder, function_id, *destination);
                builder.build_store(return_value_ptr, return_value).unwrap();

                // Since function calls aren't a terminator in LLVM, manually terminate this block.
                let target_bb = self.lower_block(function_id, *target);
                builder.build_unconditional_branch(target_bb).unwrap();
            }
            Terminator::Goto(Goto { basic_block }) => {
                let bb = self.lower_block(function_id, *basic_block);
                builder.build_unconditional_branch(bb).unwrap();
            }
            Terminator::Return => {
                // TODO: Don't just create return value local.
                let (ptr, ptr_ty) = &self.locals[function_id][LocalId::from_id(0)];
                let return_value = builder
                    .build_load(self.basic_ty(ptr_ty), *ptr, "load-return")
                    .unwrap();
                builder.build_return(Some(&return_value)).unwrap();
            }
            Terminator::SwitchInteger(SwitchInteger {
                discriminator,
                targets,
                otherwise,
            }) => {
                let (discriminator, discriminator_ty) =
                    self.resolve_operand(&builder, function_id, *discriminator);
                assert!(matches!(
                    discriminator_ty,
                    Type::I8 | Type::U8 | Type::Boolean
                ));

                let targets = targets
                    .iter()
                    .map(|(value, block)| {
                        (
                            self.constant(value).0.into_int_value(),
                            self.lower_block(function_id, *block),
                        )
                    })
                    .collect::<Vec<_>>();

                let otherwise = self.lower_block(function_id, *otherwise);

                builder
                    .build_switch(discriminator.into_int_value(), otherwise, &targets)
                    .unwrap();
            }
            Terminator::Unterminated => todo!(),
        }

        bb
    }

    fn resolve_operand(
        &mut self,
        builder: &Builder<'ink>,
        function_id: FunctionId,
        operand: OperandId,
    ) -> (BasicValueEnum<'ink>, Type) {
        match &self.mir[operand] {
            Operand::Place(place) => {
                let (ptr, ty) = self.resolve_place(builder, function_id, *place);
                (
                    builder.build_load(self.basic_ty(&ty), ptr, "load").unwrap(),
                    ty,
                )
            }
            Operand::Constant(constant) => self.constant(constant),
        }
    }

    fn resolve_place(
        &mut self,
        builder: &Builder<'ink>,
        function_id: FunctionId,
        place: PlaceId,
    ) -> (PointerValue<'ink>, Type) {
        let place = &self.mir[place];

        let (mut ptr, mut ty) = self.locals[function_id][place.local].clone();

        for projection in &place.projection {
            (ptr, ty) = match (projection, ty) {
                (Projection::Deref, ref ty @ Type::Ref(ref inner_ty)) => (
                    builder
                        .build_load(self.basic_ty(ty), ptr, "deref")
                        .unwrap()
                        .into_pointer_value(),
                    (**inner_ty).clone(),
                ),
                (Projection::Deref, ty) => panic!("cannot dereference {ty:?}"),
            }
        }

        (ptr, ty)
    }

    fn resolve_rvalue(
        &mut self,
        builder: &Builder<'ink>,
        function_id: FunctionId,
        rvalue: &RValue,
    ) -> (BasicValueEnum<'ink>, Type) {
        match rvalue {
            RValue::Use(operand) => self.resolve_operand(builder, function_id, *operand),
            RValue::Ref(place) => {
                // Resolve the place.
                let (ptr, ty) = self.resolve_place(builder, function_id, *place);
                // Produce a pointer value.
                (ptr.as_basic_value_enum(), Type::Ref(Box::new(ty)))
            }
            RValue::Binary(binary) => {
                let (lhs, lhs_ty) = self.resolve_operand(builder, function_id, binary.lhs);
                let (rhs, rhs_ty) = self.resolve_operand(builder, function_id, binary.rhs);

                match (lhs_ty, &binary.operation, rhs_ty) {
                    (
                        lhs_ty @ (Type::U8 | Type::I8),
                        BinaryOperation::Plus,
                        rhs_ty @ (Type::U8 | Type::I8),
                    ) if lhs_ty == rhs_ty => (
                        builder
                            .build_int_add(lhs.into_int_value(), rhs.into_int_value(), "add")
                            .unwrap()
                            .as_basic_value_enum(),
                        lhs_ty,
                    ),
                    (
                        lhs_ty @ (Type::U8 | Type::I8),
                        BinaryOperation::Minus,
                        rhs_ty @ (Type::U8 | Type::I8),
                    ) if lhs_ty == rhs_ty => (
                        builder
                            .build_int_sub(lhs.into_int_value(), rhs.into_int_value(), "add")
                            .unwrap()
                            .as_basic_value_enum(),
                        lhs_ty,
                    ),
                    (
                        lhs_ty @ (Type::U8 | Type::I8),
                        BinaryOperation::Multiply,
                        rhs_ty @ (Type::U8 | Type::I8),
                    ) if lhs_ty == rhs_ty => (
                        builder
                            .build_int_mul(lhs.into_int_value(), rhs.into_int_value(), "add")
                            .unwrap()
                            .as_basic_value_enum(),
                        lhs_ty,
                    ),
                    (Type::U8, BinaryOperation::Divide, Type::U8) => (
                        builder
                            .build_int_unsigned_div(
                                lhs.into_int_value(),
                                rhs.into_int_value(),
                                "add",
                            )
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::U8,
                    ),
                    (Type::I8, BinaryOperation::Divide, Type::I8) => (
                        builder
                            .build_int_signed_div(lhs.into_int_value(), rhs.into_int_value(), "add")
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::I8,
                    ),
                    (Type::Boolean, BinaryOperation::LogicalAnd, Type::Boolean) => (
                        builder
                            .build_and(lhs.into_int_value(), rhs.into_int_value(), "logical_and")
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::Boolean,
                    ),
                    (Type::Boolean, BinaryOperation::LogicalOr, Type::Boolean) => (
                        builder
                            .build_or(lhs.into_int_value(), rhs.into_int_value(), "logical_or")
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::Boolean,
                    ),
                    (
                        lhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                        BinaryOperation::BinaryAnd,
                        rhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                    ) if lhs_ty == rhs_ty => (
                        builder
                            .build_and(lhs.into_int_value(), rhs.into_int_value(), "binary_and")
                            .unwrap()
                            .as_basic_value_enum(),
                        lhs_ty,
                    ),
                    (
                        lhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                        BinaryOperation::BinaryOr,
                        rhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                    ) if lhs_ty == rhs_ty => (
                        builder
                            .build_or(lhs.into_int_value(), rhs.into_int_value(), "binary_or")
                            .unwrap()
                            .as_basic_value_enum(),
                        lhs_ty,
                    ),
                    (
                        lhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                        BinaryOperation::Equal,
                        rhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                    ) if lhs_ty == rhs_ty => (
                        builder
                            .build_int_compare(
                                IntPredicate::EQ,
                                lhs.into_int_value(),
                                rhs.into_int_value(),
                                "equal",
                            )
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::Boolean,
                    ),
                    (
                        lhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                        BinaryOperation::NotEqual,
                        rhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                    ) if lhs_ty == rhs_ty => (
                        builder
                            .build_int_compare(
                                IntPredicate::NE,
                                lhs.into_int_value(),
                                rhs.into_int_value(),
                                "not_equal",
                            )
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::Boolean,
                    ),
                    (Type::U8, BinaryOperation::Less, Type::U8) => (
                        builder
                            .build_int_compare(
                                IntPredicate::ULT,
                                lhs.into_int_value(),
                                rhs.into_int_value(),
                                "unsigned_less",
                            )
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::Boolean,
                    ),
                    (Type::I8, BinaryOperation::Less, Type::I8) => (
                        builder
                            .build_int_compare(
                                IntPredicate::SLT,
                                lhs.into_int_value(),
                                rhs.into_int_value(),
                                "signed_less",
                            )
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::Boolean,
                    ),
                    (Type::U8, BinaryOperation::LessEqual, Type::U8) => (
                        builder
                            .build_int_compare(
                                IntPredicate::ULE,
                                lhs.into_int_value(),
                                rhs.into_int_value(),
                                "unsigned_less_equal",
                            )
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::Boolean,
                    ),
                    (Type::I8, BinaryOperation::LessEqual, Type::I8) => (
                        builder
                            .build_int_compare(
                                IntPredicate::SLE,
                                lhs.into_int_value(),
                                rhs.into_int_value(),
                                "signed_less_equal",
                            )
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::Boolean,
                    ),
                    (Type::U8, BinaryOperation::Greater, Type::U8) => (
                        builder
                            .build_int_compare(
                                IntPredicate::UGT,
                                lhs.into_int_value(),
                                rhs.into_int_value(),
                                "unsigned_greater",
                            )
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::Boolean,
                    ),
                    (Type::I8, BinaryOperation::Greater, Type::I8) => (
                        builder
                            .build_int_compare(
                                IntPredicate::SGT,
                                lhs.into_int_value(),
                                rhs.into_int_value(),
                                "signed_greater",
                            )
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::Boolean,
                    ),
                    (Type::U8, BinaryOperation::GreaterEqual, Type::U8) => (
                        builder
                            .build_int_compare(
                                IntPredicate::UGE,
                                lhs.into_int_value(),
                                rhs.into_int_value(),
                                "unsigned_greater_equal",
                            )
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::Boolean,
                    ),
                    (Type::I8, BinaryOperation::GreaterEqual, Type::I8) => (
                        builder
                            .build_int_compare(
                                IntPredicate::SGE,
                                lhs.into_int_value(),
                                rhs.into_int_value(),
                                "signed_greater_equal",
                            )
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::Boolean,
                    ),
                    _ => todo!(),
                }
            }
            RValue::Unary(unary) => match unary.operation {
                UnaryOperation::Not => {
                    let (value, value_ty) = self.resolve_operand(builder, function_id, unary.value);

                    if !matches!(value_ty, Type::U8 | Type::I8 | Type::Boolean) {
                        panic!("cannot apply unary operation NOT on {value_ty:?}");
                    }

                    (
                        builder
                            .build_not(value.into_int_value(), "not")
                            .unwrap()
                            .as_basic_value_enum(),
                        value_ty,
                    )
                }
                UnaryOperation::Negative => {
                    let (value, value_ty) = self.resolve_operand(builder, function_id, unary.value);

                    if !matches!(value_ty, Type::I8) {
                        panic!("cannot apply unary operation NEG on {value_ty:?}");
                    }

                    (
                        builder
                            .build_int_neg(value.into_int_value(), "neg")
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::I8,
                    )
                }
                UnaryOperation::Deref => {
                    let (value, value_ty) = self.resolve_operand(builder, function_id, unary.value);

                    let Type::Ref(inner_ty) = value_ty else {
                        panic!("cannot dereference value of type: {value_ty:?}");
                    };

                    (
                        builder
                            .build_load(
                                self.basic_ty(&inner_ty),
                                value.into_pointer_value(),
                                "deref",
                            )
                            .unwrap()
                            .as_basic_value_enum(),
                        *inner_ty,
                    )
                }
                UnaryOperation::Ref => {
                    let Operand::Place(place) = &self.mir[unary.value] else {
                        panic!("can only take reference of place");
                    };

                    let (ptr, ty) = self.resolve_place(builder, function_id, *place);

                    (ptr.as_basic_value_enum(), Type::Ref(Box::new(ty)))
                }
            },
        }
    }

    /// Fetch the [`FunctionType`] for a given function signature.
    fn function_ty(&self, return_ty: &Type, parameters: &[Type]) -> FunctionType<'ink> {
        let parameters = parameters
            .iter()
            .map(|parameter| self.basic_ty(parameter).into())
            .collect::<Vec<_>>();

        match return_ty {
            Type::Unit => self.ink.void_type().fn_type(&parameters, false),
            return_ty => self.basic_ty(return_ty).fn_type(&parameters, false),
        }
    }

    /// Fetch [`BasicTypeEnum`] for a given [`Type`].
    fn basic_ty(&self, ty: &Type) -> BasicTypeEnum<'ink> {
        match ty {
            Type::Unit => self.ink.struct_type(&[], true).into(),
            Type::I8 => self.ink.i8_type().into(),
            Type::U8 => self.ink.i8_type().into(),
            Type::Boolean => self.ink.bool_type().into(),
            Type::Ref(_) => self.ink.ptr_type(AddressSpace::default()).into(),
            Type::Never => unreachable!(),
            Type::Function { .. } => self.ink.ptr_type(AddressSpace::default()).into(),
        }
    }

    fn constant(&self, constant: &Constant) -> (BasicValueEnum<'ink>, Type) {
        match constant {
            Constant::U8(value) => (
                self.ink
                    .i8_type()
                    .const_int(*value as u64, false)
                    .as_basic_value_enum(),
                Type::U8,
            ),
            Constant::I8(value) => (
                self.ink
                    .i8_type()
                    // NOTE: Extra cast here to preserve sign.
                    .const_int(*value as i64 as u64, true)
                    .as_basic_value_enum(),
                Type::I8,
            ),
            Constant::Boolean(value) => (
                self.ink
                    .bool_type()
                    .const_int(if *value { 1 } else { 0 }, false)
                    .as_basic_value_enum(),
                Type::Boolean,
            ),
            Constant::Unit => unreachable!(),
            Constant::Function(id) => {
                let function_value = self.functions[*id];
                (
                    function_value.as_global_value().as_pointer_value().into(),
                    Type::Function {
                        parameters: self.mir.functions[*id].parameters.clone(),
                        return_ty: Box::new(self.mir.functions[*id].return_ty.clone()),
                    },
                )
            }
        }
    }
}
