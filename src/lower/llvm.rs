use std::{marker::PhantomData, ops::Deref, rc::Rc};

use inkwell::{
    AddressSpace,
    builder::Builder,
    context::Context,
    execution_engine::JitFunction,
    intrinsics::Intrinsic,
    module::Module,
    types::{BasicType, BasicTypeEnum},
    values::{
        AnyValue as _, ArrayValue, BasicValue, BasicValueEnum, FunctionValue, IntValue,
        PointerValue,
    },
};

use crate::{
    ir::{
        Ty, TyInfo, Tys,
        value::{Any, AnyValue, Constant, Integer, IntegerValue, Loadable, Storable, ValueBackend},
    },
    lower,
};

pub struct Llvm<'ctx> {
    ctx: &'ctx Context,
    module: Rc<Module<'ctx>>,
}
impl<'ctx> Llvm<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        Self {
            ctx,
            module: Rc::new(ctx.create_module("some_module")),
        }
    }

    pub fn run(&self, name: &str) -> u8 {
        println!(
            "{}",
            self.module
                .get_first_function()
                .unwrap()
                .print_to_string()
                .to_string()
        );

        let engine = self
            .module
            .create_jit_execution_engine(inkwell::OptimizationLevel::None)
            .unwrap();
        let f: JitFunction<'ctx, unsafe extern "C" fn() -> u8> =
            unsafe { engine.get_function(name).unwrap() };

        unsafe { f.call() }
    }
}
impl<'ctx> lower::Backend<'ctx> for Llvm<'ctx> {
    type Value = Value<'ctx>;
    type Function = Function<'ctx>;

    fn add_function(
        &self,
        name: &str,
        ret_ty: <Self::Value as ValueBackend>::Ty,
    ) -> Self::Function {
        Function::new(self.ctx, Rc::clone(&self.module), name, ret_ty)
    }

    fn get_ty(&self, tys: &Tys, ty: Ty) -> <Self::Value as ValueBackend>::Ty {
        match tys.get(ty) {
            TyInfo::U8 => self.ctx.i8_type().into(),
            TyInfo::I8 => self.ctx.i8_type().into(),
            TyInfo::Ref(inner_ty) => match tys.get(inner_ty) {
                // Fat pointer
                TyInfo::Slice(_) => self
                    .ctx
                    .ptr_type(AddressSpace::default())
                    .array_type(2)
                    .into(),
                // Normal pointer
                _ => self.ctx.ptr_type(AddressSpace::default()).into(),
            },
            TyInfo::Slice(_) => panic!("unsized type, cannot convert to LLVM"),
            TyInfo::Array { ty, length } => self.get_ty(tys, ty).array_type(length as u32).into(),
        }
    }
}

pub struct Function<'ctx> {
    ctx: &'ctx Context,
    module: Rc<Module<'ctx>>,
    builder: Builder<'ctx>,
    function: FunctionValue<'ctx>,
    entry_bb: inkwell::basic_block::BasicBlock<'ctx>,
}
impl<'ctx> Function<'ctx> {
    pub fn new(
        ctx: &'ctx Context,
        module: Rc<Module<'ctx>>,
        name: &str,
        ret_ty: BasicTypeEnum<'ctx>,
    ) -> Self {
        let function = module.add_function(
            name,
            ret_ty.fn_type(
                // TODO: Params
                &[],
                false,
            ),
            None,
        );

        Function {
            builder: ctx.create_builder(),
            function,
            entry_bb: ctx.append_basic_block(function, "entry"),

            ctx,
            module,
        }
    }
}
impl<'ctx> lower::Function<'ctx> for Function<'ctx> {
    type Value = Value<'ctx>;

    fn declare_local(
        &mut self,
        ty: <Self::Value as ValueBackend>::Ty,
        name: &str,
    ) -> <Value<'ctx> as ValueBackend>::Pointer {
        // Find the last non-terminator instruction.
        let mut last_non_terminator = self.entry_bb.get_last_instruction();
        while let Some(instr) = last_non_terminator
            && instr.is_terminator()
        {
            last_non_terminator = instr.get_previous_instruction();
        }

        match last_non_terminator {
            // Non-terminator instruction found, position after it.
            Some(instr) => self.builder.position_at(self.entry_bb, &instr),
            // No instruction found, position at end of basic block.
            None => self.builder.position_at_end(self.entry_bb),
        }

        Pointer(self.builder.build_alloca(ty, name).unwrap())
    }

    fn add_basic_block(&mut self, name: &str) -> <Value<'ctx> as ValueBackend>::BasicBlock {
        let bb = self.ctx.append_basic_block(self.function, name);

        // If this is the first basic block added after the entry, ensure the entry jumps to it.
        if self.function.count_basic_blocks() == 2 {
            // Put builder at the end of the basic block.
            match self.entry_bb.get_terminator() {
                Some(terminator) => {
                    self.builder.position_before(&terminator);
                    terminator.remove_from_basic_block();
                }
                None => self.builder.position_at_end(self.entry_bb),
            }

            // Jump to this basic block.
            self.builder.build_unconditional_branch(bb).unwrap();
        }

        BasicBlock {
            ctx: self.ctx,
            module: Rc::clone(&self.module),
            builder: {
                let builder = self.ctx.create_builder();
                builder.position_at_end(bb);
                builder
            },
            bb,
        }
    }
}

pub struct BasicBlock<'ctx> {
    ctx: &'ctx Context,
    module: Rc<Module<'ctx>>,
    builder: Builder<'ctx>,
    bb: inkwell::basic_block::BasicBlock<'ctx>,
}
impl<'ctx> lower::BasicBlock for BasicBlock<'ctx> {
    type Value = Value<'ctx>;

    fn term_return(&self, value: IntegerValue<Self::Value>) {
        self.builder
            .build_return(Some(&value.as_basic_value_enum()))
            .unwrap();
    }

    fn storage_live(&self, ptr: Pointer<'ctx>) {
        let intrinsic = Intrinsic::find("llvm.lifetime.start").unwrap();
        let intrinsic_fn = intrinsic
            .get_declaration(&self.module, &[BasicTypeEnum::PointerType(ptr.get_type())])
            .unwrap();
        self.builder
            .build_call(intrinsic_fn, &[(*ptr).into()], "lifetime.start")
            .unwrap();
    }

    fn storage_dead(&self, ptr: Pointer<'ctx>) {
        let intrinsic = Intrinsic::find("llvm.lifetime.end").unwrap();
        let intrinsic_fn = intrinsic
            .get_declaration(&self.module, &[BasicTypeEnum::PointerType(ptr.get_type())])
            .unwrap();
        self.builder
            .build_call(intrinsic_fn, &[(*ptr).into()], "lifetime.end")
            .unwrap();
    }

    fn term_goto(&self, target: &BasicBlock<'ctx>) {
        self.builder.build_unconditional_branch(target.bb).unwrap();
    }

    fn term_switch<I: Integer<Self::Value>>(
        &self,
        discriminator: I,
        default: &BasicBlock<'ctx>,
        targets: Vec<(I::Value, &BasicBlock<'ctx>)>,
    ) {
        self.builder
            .build_switch(
                // HACK: Also mega hacky
                discriminator
                    .into_integer_value()
                    .as_basic_value_enum()
                    .into_int_value(),
                default.bb,
                targets
                    .into_iter()
                    .map(|(value, target)| {
                        (
                            // HACK: Mega hacky
                            I::create(self, value)
                                .into_integer_value()
                                .as_basic_value_enum()
                                .into_int_value(),
                            target.bb,
                        )
                    })
                    .collect::<Vec<_>>()
                    .as_slice(),
            )
            .unwrap();
    }
}

pub struct Value<'ctx>(PhantomData<&'ctx ()>);
impl<'ctx> lower::ValueBackend for Value<'ctx> {
    type BasicBlock = BasicBlock<'ctx>;

    type Ty = BasicTypeEnum<'ctx>;

    type Pointer = Pointer<'ctx>;
    type FatPointer = FatPointer<'ctx>;

    type Array = Array<'ctx>;

    type I8 = I8<'ctx>;
    type U8 = U8<'ctx>;
}

#[derive(Clone, Debug)]
pub struct Pointer<'ctx>(PointerValue<'ctx>);
impl<'ctx> crate::ir::value::Pointer<Value<'ctx>> for Pointer<'ctx> {
    fn element_ptr<I: Integer<Value<'ctx>>>(
        self,
        bb: &BasicBlock<'ctx>,
        i: I,
        ty: BasicTypeEnum<'ctx>,
    ) -> Self {
        let ordered_indexes = [
            // HACK: Mega hacky
            i.into_integer_value()
                .as_basic_value_enum()
                .into_int_value(),
        ];
        let name = "el_pointer";

        Self(
            unsafe {
                bb.builder
                    .build_in_bounds_gep(ty, *self, &ordered_indexes, name)
            }
            .unwrap(),
        )
    }

    fn deref(self, bb: &BasicBlock<'ctx>) -> Self {
        Self(
            bb.builder
                .build_load(bb.ctx.ptr_type(AddressSpace::default()), *self, "deref")
                .unwrap()
                .into_pointer_value(),
        )
    }
}
impl<'ctx> Loadable<Value<'ctx>> for Pointer<'ctx> {
    fn load(bb: &BasicBlock<'ctx>, ptr: Pointer<'ctx>) -> Self {
        Self(
            bb.builder
                .build_load(bb.ctx.ptr_type(AddressSpace::default()), *ptr, "load_ptr")
                .unwrap()
                .into_pointer_value(),
        )
    }
}
impl<'ctx> Storable<Value<'ctx>> for Pointer<'ctx> {
    fn store(self, bb: &BasicBlock<'ctx>, ptr: Pointer<'ctx>) {
        bb.builder.build_store(*ptr, self.0).unwrap();
    }
}
impl<'ctx> Any<Value<'ctx>> for Pointer<'ctx> {
    fn into_any_value(self) -> AnyValue<Value<'ctx>> {
        AnyValue::Pointer(self)
    }
}
impl<'ctx> Deref for Pointer<'ctx> {
    type Target = PointerValue<'ctx>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Debug)]
pub struct FatPointer<'ctx> {
    pointer: Pointer<'ctx>,
    data: U8<'ctx>,
}
impl<'ctx> crate::ir::value::FatPointer<Value<'ctx>> for FatPointer<'ctx> {
    fn from_ptr(ptr: Pointer<'ctx>, data: U8<'ctx>) -> Self {
        Self { pointer: ptr, data }
    }

    fn get_metadata(&self) -> <Value<'ctx> as ValueBackend>::U8 {
        self.data.clone()
    }
}
impl<'ctx> crate::ir::value::Pointer<Value<'ctx>> for FatPointer<'ctx> {
    fn element_ptr<I: Integer<Value<'ctx>>>(
        self,
        bb: &<Value<'ctx> as ValueBackend>::BasicBlock,
        i: I,
        ty: <Value<'ctx> as ValueBackend>::Ty,
    ) -> Pointer<'ctx> {
        self.pointer.element_ptr(bb, i, ty)
    }

    fn deref(self, bb: &<Value<'ctx> as ValueBackend>::BasicBlock) -> Pointer<'ctx> {
        self.pointer.deref(bb)
    }
}
impl<'ctx> Loadable<Value<'ctx>> for FatPointer<'ctx> {
    fn load(
        bb: &<Value<'ctx> as ValueBackend>::BasicBlock,
        ptr: <Value<'ctx> as ValueBackend>::Pointer,
    ) -> Self {
        let ptr_ty = bb.ctx.ptr_type(AddressSpace::default());
        let pointer = bb
            .builder
            .build_load(ptr_ty, *ptr, "load_ptr")
            .unwrap()
            .into_pointer_value();

        // HACK: Skip the `ptr` by pretending it's an array of pointers
        let data_ptr = unsafe {
            bb.builder.build_in_bounds_gep(
                ptr_ty,
                *ptr,
                &[bb.ctx.i8_type().const_int(1, false)],
                "data_ptr",
            )
        }
        .unwrap();

        let data = bb
            .builder
            .build_load(bb.ctx.i8_type(), data_ptr, "load_data")
            .unwrap()
            .into_int_value();

        Self {
            pointer: Pointer(pointer),
            data: U8(data),
        }
    }
}
impl<'ctx> Storable<Value<'ctx>> for FatPointer<'ctx> {
    fn store(
        self,
        bb: &<Value<'ctx> as ValueBackend>::BasicBlock,
        ptr: <Value<'ctx> as ValueBackend>::Pointer,
    ) {
        // Store pointer.
        bb.builder.build_store(*ptr, *self.pointer).unwrap();

        // HACK: Skip the `ptr` by pretending it's an array of pointers
        let ptr_ty = bb.ctx.ptr_type(AddressSpace::default());
        let data_ptr = unsafe {
            bb.builder.build_in_bounds_gep(
                ptr_ty,
                *ptr,
                &[bb.ctx.i8_type().const_int(1, false)],
                "data_ptr",
            )
        }
        .unwrap();

        // Store data.
        bb.builder.build_store(data_ptr, *self.data).unwrap();
    }
}
impl<'ctx> Any<Value<'ctx>> for FatPointer<'ctx> {
    fn into_any_value(self) -> AnyValue<Value<'ctx>> {
        AnyValue::FatPointer(self)
    }
}

#[derive(Clone, Debug)]
pub struct I8<'ctx>(IntValue<'ctx>);
impl<'ctx> Any<Value<'ctx>> for I8<'ctx> {
    fn into_any_value(self) -> AnyValue<Value<'ctx>> {
        self.into_integer_value().into_any_value()
    }
}
impl<'ctx> Integer<Value<'ctx>> for I8<'ctx> {
    fn into_integer_value(self) -> IntegerValue<Value<'ctx>> {
        IntegerValue::I8(self)
    }

    fn add(bb: &BasicBlock<'ctx>, lhs: Self, rhs: Self) -> Self {
        Self(bb.builder.build_int_add(lhs.0, rhs.0, "add_i8").unwrap())
    }
}
impl<'ctx> Constant<Value<'ctx>> for I8<'ctx> {
    type Value = i8;

    fn create(bb: &BasicBlock<'ctx>, value: Self::Value) -> Self {
        Self(bb.ctx.i8_type().const_int(value as u64, false))
    }
}
impl<'ctx> Loadable<Value<'ctx>> for I8<'ctx> {
    fn load(bb: &BasicBlock<'ctx>, ptr: Pointer<'ctx>) -> Self {
        Self(
            bb.builder
                .build_load(bb.ctx.i8_type(), *ptr, "load_i8")
                .unwrap()
                .into_int_value(),
        )
    }
}
impl<'ctx> Storable<Value<'ctx>> for I8<'ctx> {
    fn store(self, bb: &BasicBlock<'ctx>, ptr: Pointer<'ctx>) {
        bb.builder.build_store(*ptr, self.0).unwrap();
    }
}
impl<'ctx> Deref for I8<'ctx> {
    type Target = IntValue<'ctx>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Debug)]
pub struct U8<'ctx>(IntValue<'ctx>);
impl<'ctx> Any<Value<'ctx>> for U8<'ctx> {
    fn into_any_value(self) -> AnyValue<Value<'ctx>> {
        self.into_integer_value().into_any_value()
    }
}
impl<'ctx> Integer<Value<'ctx>> for U8<'ctx> {
    fn into_integer_value(self) -> IntegerValue<Value<'ctx>> {
        IntegerValue::U8(self)
    }

    fn add(bb: &BasicBlock<'ctx>, lhs: Self, rhs: Self) -> Self {
        Self(bb.builder.build_int_add(lhs.0, rhs.0, "add_u8").unwrap())
    }
}
impl<'ctx> Constant<Value<'ctx>> for U8<'ctx> {
    type Value = u8;

    fn create(bb: &BasicBlock<'ctx>, value: Self::Value) -> Self {
        Self(bb.ctx.i8_type().const_int(value as u64, false))
    }
}
impl<'ctx> Loadable<Value<'ctx>> for U8<'ctx> {
    fn load(bb: &BasicBlock<'ctx>, ptr: Pointer<'ctx>) -> Self {
        Self(
            bb.builder
                .build_load(bb.ctx.i8_type(), *ptr, "load_u8")
                .unwrap()
                .into_int_value(),
        )
    }
}

impl<'ctx> Storable<Value<'ctx>> for U8<'ctx> {
    fn store(self, bb: &BasicBlock<'ctx>, ptr: Pointer<'ctx>) {
        bb.builder.build_store(*ptr, self.0).unwrap();
    }
}
impl<'ctx> Deref for U8<'ctx> {
    type Target = IntValue<'ctx>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

trait IntegerValueExt<'ctx> {
    fn as_basic_value_enum(&self) -> BasicValueEnum<'ctx>;
}
impl<'ctx> IntegerValueExt<'ctx> for IntegerValue<Value<'ctx>> {
    fn as_basic_value_enum(&self) -> BasicValueEnum<'ctx> {
        match self {
            IntegerValue::I8(i8) => i8.0.as_basic_value_enum(),
            IntegerValue::U8(u8) => u8.0.as_basic_value_enum(),
        }
    }
}

pub struct Array<'ctx>(ArrayValue<'ctx>);
impl<'ctx> crate::ir::value::Array<Value<'ctx>> for Array<'ctx> {
    fn load_count(
        bb: &BasicBlock<'ctx>,
        ptr: Pointer<'ctx>,
        ty: BasicTypeEnum<'ctx>,
        count: usize,
    ) -> Self {
        let out = bb
            .builder
            .build_load(ty.array_type(count as u32), *ptr, "load_array")
            .unwrap()
            .into_array_value();

        todo!()
    }
}
impl<'ctx> Storable<Value<'ctx>> for Array<'ctx> {
    fn store(
        self,
        bb: &<Value<'ctx> as ValueBackend>::BasicBlock,
        ptr: <Value<'ctx> as ValueBackend>::Pointer,
    ) {
        todo!()
    }
}
impl<'ctx> Any<Value<'ctx>> for Array<'ctx> {
    fn into_any_value(self) -> AnyValue<Value<'ctx>> {
        AnyValue::Array(todo!())
    }
}
