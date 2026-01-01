use crate::prelude::*;

use cst::{BinaryOp, UnaryOp};
use hir::Type;
use mir::*;

use inkwell::{
    AddressSpace, IntPredicate,
    basic_block::BasicBlock as IBasicBlock,
    builder::Builder,
    context::Context,
    module::Module,
    types::{BasicType, BasicTypeEnum, FunctionType},
    values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue},
};

pub fn codegen<'ink>(ctx: &Ctx, ink: &'ink Context, mir: &Mir2) -> Module<'ink> {
    let mut codegen = Codegen::new(ink);

    // Forward declare all functions.
    for (id, function) in mir.functions.iter_pairs() {
        codegen.declare_fn(
            id,
            function,
            ctx.strings.get(ctx.scopes.to_string(function.binding)),
        );
    }

    // Lower each function.
    for (function_id, function) in mir.functions.iter_pairs() {
        let mut codegen = codegen.function(function_id);

        // Declare each local.
        for (i, (binding, ty)) in function.locals.iter().enumerate() {
            match binding {
                Some(binding) => codegen.declare_local(
                    LocalId::from_id(i),
                    ty,
                    ctx.strings.get(ctx.scopes.to_string(*binding)),
                ),
                None => {
                    codegen.declare_local(LocalId::from_id(i), ty, format!("local_{i}").as_str())
                }
            }
        }

        // HACK: Store all of the parameter values into appropriate locals.
        for (param, local_id) in codegen.function.get_param_iter().zip(1..) {
            let local_id = LocalId::from_id(local_id);

            let (_, ptr) = &codegen.locals[&local_id];

            codegen.builder.build_store(*ptr, param).unwrap();
        }

        lower_block(ctx, &mut codegen, mir, function.entry);

        // Unconditional jump to the first block.
        let user_entry = codegen.get_basic_block(function.entry);
        codegen.builder.position_at_end(codegen.entry_bb);
        codegen
            .builder
            .build_unconditional_branch(user_entry)
            .unwrap();

        // Ensure the module is well-formed.
        codegen.verify();
    }

    codegen.complete()
}

fn lower_block<'ink, 'codegen>(
    ctx: &Ctx,
    codegen: &mut FunctionCodegen<'ink, 'codegen>,
    mir: &Mir2,
    block_id: BasicBlockId,
) -> IBasicBlock<'ink> {
    let block = &mir.basic_blocks[block_id];
    let bb = codegen.get_basic_block(block_id);

    if bb.get_terminator().is_some() {
        // Block has already been lowered
        return bb;
    }

    let restore_bb = codegen.builder.get_insert_block();
    codegen.builder.position_at_end(bb);

    for statement in &block.statements {
        match statement {
            Statement::Assign(Assign { place, rvalue }) => {
                let (ptr, ptr_ty) = codegen.resolve_place(place);
                let (value, ty) = codegen.resolve_rvalue(rvalue);

                assert_eq!(ptr_ty, ty);

                codegen.builder.build_store(ptr, value).unwrap();
            }
            Statement::StorageLive(storage_live) => todo!(),
            Statement::StorageDead(storage_dead) => todo!(),
        }
    }

    match &block.terminator {
        Terminator::Call(call) => {
            let args = call
                .args
                .iter()
                .map(|arg| codegen.resolve_operand(arg).0.into())
                .collect::<Vec<_>>();

            let ret_value = match &call.func {
                Operand::Constant(Constant::Function(function_id)) => {
                    let function = codegen.functions[function_id].0;
                    codegen
                        .builder
                        .build_direct_call(
                            function,
                            args.as_slice(),
                            ctx.strings
                                .get(ctx.scopes.to_string(mir[*function_id].binding)),
                        )
                        .unwrap()
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                }
                func => {
                    let (func_ptr, func_ty) = codegen.resolve_operand(func);
                    let Type::Function { params, ret_ty } = func_ty else {
                        panic!()
                    };
                    let func_ty = codegen.fn_ty(&ret_ty, &params);

                    codegen
                        .builder
                        .build_indirect_call(
                            func_ty,
                            func_ptr.into_pointer_value(),
                            args.as_slice(),
                            "function_indirect",
                        )
                        .unwrap()
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                }
            };

            let ret_value_address = codegen.resolve_place(&call.destination).0;
            codegen
                .builder
                .build_store(ret_value_address, ret_value)
                .unwrap();

            let basic_block = lower_block(ctx, codegen, mir, call.target);
            codegen
                .builder
                .build_unconditional_branch(basic_block)
                .unwrap();
        }
        Terminator::Goto(Goto { basic_block }) => {
            let basic_block = lower_block(ctx, codegen, mir, *basic_block);

            codegen
                .builder
                .build_unconditional_branch(basic_block)
                .unwrap();
        }
        Terminator::Return => {
            let (ptr_ty, ptr) = &codegen.locals[&LocalId::from_id(0)];
            let return_value = codegen
                .builder
                .build_load(codegen.basic_ty(ptr_ty), *ptr, "load-return")
                .unwrap();
            codegen.builder.build_return(Some(&return_value)).unwrap();
        }
        Terminator::SwitchInt(SwitchInt {
            discriminator,
            targets,
            otherwise,
        }) => {
            let (discriminator, discriminator_ty) = codegen.resolve_operand(discriminator);

            assert!(matches!(
                discriminator_ty,
                Type::I8 | Type::U8 | Type::Boolean
            ));

            let targets = targets
                .iter()
                .map(|(value, block)| {
                    (
                        codegen.constant(value).0.into_int_value(),
                        lower_block(ctx, codegen, mir, *block),
                    )
                })
                .collect::<Vec<_>>();

            let otherwise = lower_block(ctx, codegen, mir, *otherwise);

            codegen
                .builder
                .build_switch(discriminator.into_int_value(), otherwise, &targets)
                .unwrap();
        }
        Terminator::Unterminated => todo!(),
    }

    if let Some(restore_bb) = restore_bb {
        codegen.builder.position_at_end(restore_bb);
    }

    bb
}

struct Codegen<'ink> {
    ink: &'ink Context,
    module: Module<'ink>,

    functions: HashMap<FunctionId, (FunctionValue<'ink>, Type)>,
}

impl<'ink> Codegen<'ink> {
    pub fn new(ink: &'ink Context) -> Self {
        Self {
            module: ink.create_module("module"),
            ink,
            functions: HashMap::new(),
        }
    }

    pub fn complete(self) -> Module<'ink> {
        self.module
    }

    pub fn declare_fn(&mut self, id: FunctionId, function: &Function2, name: &str) {
        let fn_value =
            self.module
                .add_function(name, self.fn_ty(&function.ret_ty, &function.params), None);
        self.functions.insert(
            id,
            (
                fn_value,
                Type::Function {
                    params: function.params.clone(),
                    ret_ty: Box::new(function.ret_ty.clone()),
                },
            ),
        );
    }

    pub fn function<'codegen>(
        &'codegen mut self,
        function: FunctionId,
    ) -> FunctionCodegen<'ink, 'codegen> {
        FunctionCodegen::new(self, function)
    }

    fn fn_ty(&self, ret_ty: &Type, params: &[Type]) -> FunctionType<'ink> {
        let params = params
            .iter()
            .map(|param| self.basic_ty(param).into())
            .collect::<Vec<_>>();

        match ret_ty {
            Type::Unit => self.ink.void_type().fn_type(&params, false),
            ret_ty => self.basic_ty(ret_ty).fn_type(&params, false),
        }
    }

    fn basic_ty(&self, ty: &Type) -> BasicTypeEnum<'ink> {
        match ty {
            Type::Unit => self.ink.struct_type(&[], true).into(),
            Type::I8 => self.ink.i8_type().into(),
            Type::U8 => self.ink.i8_type().into(),
            Type::Boolean => self.ink.bool_type().into(),
            Type::Ref(_) => self.ink.ptr_type(AddressSpace::default()).into(),
            Type::Never => unreachable!(),
            Type::Function { params, ret_ty } => self.ink.ptr_type(AddressSpace::default()).into(),
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
                let (function_value, ty) = &self.functions[id];
                (
                    function_value.as_global_value().as_pointer_value().into(),
                    ty.clone(),
                )
            }
        }
    }
}

struct FunctionCodegen<'ink, 'codegen> {
    codegen: &'codegen Codegen<'ink>,
    builder: Builder<'ink>,

    function: FunctionValue<'ink>,
    entry_bb: IBasicBlock<'ink>,

    locals: HashMap<LocalId, (Type, PointerValue<'ink>)>,
    basic_blocks: HashMap<BasicBlockId, IBasicBlock<'ink>>,
}

impl<'ink, 'codegen> FunctionCodegen<'ink, 'codegen> {
    pub fn new(codegen: &'codegen mut Codegen<'ink>, function: FunctionId) -> Self {
        let (function, _) = codegen.functions[&function];

        let entry_bb = function
            .get_first_basic_block()
            .unwrap_or_else(|| codegen.ink.append_basic_block(function, "entry"));

        let builder = codegen.ink.create_builder();
        builder.position_at_end(entry_bb);

        Self {
            codegen,
            builder,
            function,
            entry_bb,
            locals: HashMap::new(),
            basic_blocks: HashMap::new(),
        }
    }

    pub fn verify(&self) {
        assert!(self.function.verify(true));
    }

    pub fn declare_local(&mut self, local: LocalId, ty: &Type, label: &str) {
        // Move to the entry block.
        let current_block = self.builder.get_insert_block();
        self.builder.position_at_end(self.entry_bb);

        // Create the allocation.
        let alloca = self.builder.build_alloca(self.basic_ty(ty), label).unwrap();

        // Save the allocation against the local.
        self.locals.insert(local, (ty.clone(), alloca));

        if let Some(current_block) = current_block {
            // Reset builder back to end of original block.
            self.builder.position_at_end(current_block);
        }
    }

    pub fn get_basic_block(&mut self, basic_block_id: BasicBlockId) -> IBasicBlock<'ink> {
        match self.basic_blocks.get(&basic_block_id) {
            Some(bb) => *bb,
            None => {
                let bb = self
                    .ink
                    .append_basic_block(self.function, format!("{basic_block_id:?}").as_str());
                self.basic_blocks.insert(basic_block_id, bb);
                bb
            }
        }
    }

    /// Produce a pointer to a [`Place`].
    pub fn resolve_place(&mut self, place: &Place) -> (PointerValue<'ink>, Type) {
        let (mut ty, mut ptr) = self.locals[&place.local].clone();

        for projection in &place.projection {
            (ptr, ty) = match (projection, ty) {
                (Projection::Deref, ref ty @ Type::Ref(ref inner_ty)) => (
                    self.builder
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

    pub fn load_place(&mut self, place: &Place) -> (BasicValueEnum<'ink>, Type) {
        let (ptr, ty) = self.resolve_place(place);
        (
            self.builder
                .build_load(self.basic_ty(&ty), ptr, "load")
                .unwrap(),
            ty,
        )
    }

    pub fn resolve_rvalue(&mut self, rvalue: &RValue) -> (BasicValueEnum<'ink>, Type) {
        match rvalue {
            RValue::Use(operand) => self.resolve_operand(operand),
            RValue::Ref(place) => {
                // Resolve the place.
                let (ptr, ty) = self.resolve_place(place);
                // Produce a pointer value.
                (ptr.as_basic_value_enum(), Type::Ref(Box::new(ty)))
            }
            RValue::Binary(binary) => {
                let (lhs, lhs_ty) = self.resolve_operand(&binary.lhs);
                let (rhs, rhs_ty) = self.resolve_operand(&binary.rhs);

                match (lhs_ty, &binary.op, rhs_ty) {
                    (
                        lhs_ty @ (Type::U8 | Type::I8),
                        BinaryOp::Plus(_),
                        rhs_ty @ (Type::U8 | Type::I8),
                    ) if lhs_ty == rhs_ty => (
                        self.builder
                            .build_int_add(lhs.into_int_value(), rhs.into_int_value(), "add")
                            .unwrap()
                            .as_basic_value_enum(),
                        lhs_ty,
                    ),
                    (
                        lhs_ty @ (Type::U8 | Type::I8),
                        BinaryOp::Minus(_),
                        rhs_ty @ (Type::U8 | Type::I8),
                    ) if lhs_ty == rhs_ty => (
                        self.builder
                            .build_int_sub(lhs.into_int_value(), rhs.into_int_value(), "add")
                            .unwrap()
                            .as_basic_value_enum(),
                        lhs_ty,
                    ),
                    (
                        lhs_ty @ (Type::U8 | Type::I8),
                        BinaryOp::Multiply(_),
                        rhs_ty @ (Type::U8 | Type::I8),
                    ) if lhs_ty == rhs_ty => (
                        self.builder
                            .build_int_mul(lhs.into_int_value(), rhs.into_int_value(), "add")
                            .unwrap()
                            .as_basic_value_enum(),
                        lhs_ty,
                    ),
                    (Type::U8, BinaryOp::Divide(_), Type::U8) => (
                        self.builder
                            .build_int_unsigned_div(
                                lhs.into_int_value(),
                                rhs.into_int_value(),
                                "add",
                            )
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::U8,
                    ),
                    (Type::I8, BinaryOp::Divide(_), Type::I8) => (
                        self.builder
                            .build_int_signed_div(lhs.into_int_value(), rhs.into_int_value(), "add")
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::I8,
                    ),
                    (Type::Boolean, BinaryOp::LogicalAnd(_), Type::Boolean) => (
                        self.builder
                            .build_and(lhs.into_int_value(), rhs.into_int_value(), "logical_and")
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::Boolean,
                    ),
                    (Type::Boolean, BinaryOp::LogicalOr(_), Type::Boolean) => (
                        self.builder
                            .build_or(lhs.into_int_value(), rhs.into_int_value(), "logical_or")
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::Boolean,
                    ),
                    (
                        lhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                        BinaryOp::BinaryAnd(_),
                        rhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                    ) if lhs_ty == rhs_ty => (
                        self.builder
                            .build_and(lhs.into_int_value(), rhs.into_int_value(), "binary_and")
                            .unwrap()
                            .as_basic_value_enum(),
                        lhs_ty,
                    ),
                    (
                        lhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                        BinaryOp::BinaryOr(_),
                        rhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                    ) if lhs_ty == rhs_ty => (
                        self.builder
                            .build_or(lhs.into_int_value(), rhs.into_int_value(), "binary_or")
                            .unwrap()
                            .as_basic_value_enum(),
                        lhs_ty,
                    ),
                    (
                        lhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                        BinaryOp::Equal(_),
                        rhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                    ) if lhs_ty == rhs_ty => (
                        self.builder
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
                        BinaryOp::NotEqual(_),
                        rhs_ty @ (Type::U8 | Type::I8 | Type::Boolean),
                    ) if lhs_ty == rhs_ty => (
                        self.builder
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
                    (Type::U8, BinaryOp::Less(_), Type::U8) => (
                        self.builder
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
                    (Type::I8, BinaryOp::Less(_), Type::I8) => (
                        self.builder
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
                    (Type::U8, BinaryOp::LessEqual(_), Type::U8) => (
                        self.builder
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
                    (Type::I8, BinaryOp::LessEqual(_), Type::I8) => (
                        self.builder
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
                    (Type::U8, BinaryOp::Greater(_), Type::U8) => (
                        self.builder
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
                    (Type::I8, BinaryOp::Greater(_), Type::I8) => (
                        self.builder
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
                    (Type::U8, BinaryOp::GreaterEqual(_), Type::U8) => (
                        self.builder
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
                    (Type::I8, BinaryOp::GreaterEqual(_), Type::I8) => (
                        self.builder
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
            RValue::Unary(unary) => match unary.op {
                UnaryOp::Not(_) => {
                    let (value, value_ty) = self.resolve_operand(&unary.value);

                    if !matches!(value_ty, Type::U8 | Type::I8 | Type::Boolean) {
                        panic!("cannot apply unary op NOT on {value_ty:?}");
                    }

                    (
                        self.builder
                            .build_not(value.into_int_value(), "not")
                            .unwrap()
                            .as_basic_value_enum(),
                        value_ty,
                    )
                }
                UnaryOp::Negative(_) => {
                    let (value, value_ty) = self.resolve_operand(&unary.value);

                    if !matches!(value_ty, Type::I8) {
                        panic!("cannot apply unary op NEG on {value_ty:?}");
                    }

                    (
                        self.builder
                            .build_int_neg(value.into_int_value(), "neg")
                            .unwrap()
                            .as_basic_value_enum(),
                        Type::I8,
                    )
                }
                UnaryOp::Deref(_) => {
                    let (value, value_ty) = self.resolve_operand(&unary.value);

                    let Type::Ref(inner_ty) = value_ty else {
                        panic!("cannot dereference value of type: {value_ty:?}");
                    };

                    (
                        self.builder
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
                UnaryOp::Ref(_) => {
                    let Operand::Place(place) = &unary.value else {
                        panic!("can only take reference of place");
                    };

                    let (ptr, ty) = self.resolve_place(place);

                    (ptr.as_basic_value_enum(), Type::Ref(Box::new(ty)))
                }
            },
        }
    }

    pub fn resolve_operand(&mut self, operand: &Operand) -> (BasicValueEnum<'ink>, Type) {
        match operand {
            Operand::Place(place) => self.load_place(place),
            Operand::Constant(constant) => self.constant(constant),
        }
    }
}

impl<'ink, 'codegen> Deref for FunctionCodegen<'ink, 'codegen> {
    type Target = Codegen<'ink>;

    fn deref(&self) -> &Self::Target {
        self.codegen
    }
}
