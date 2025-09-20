use std::{marker::PhantomData, ops::Deref, rc::Rc};

use inkwell::{
    AddressSpace,
    builder::Builder,
    context::Context,
    execution_engine::JitFunction,
    intrinsics::Intrinsic,
    module::Module,
    types::{BasicType, BasicTypeEnum},
    values::{AnyValue as _, BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue},
};

use crate::{
    ir::{
        Ty, TyInfo, Tys,
        any_value::{Any, AnyValue},
        integer::{Constant, Integer, IntegerValue, ValueBackend},
    },
    lower,
};

pub struct Llvm<'ctx, 'ir> {
    ctx: &'ctx Context,
    module: Rc<Module<'ctx>>,
    tys: &'ir Tys,
}
impl<'ctx, 'ir> Llvm<'ctx, 'ir> {
    pub fn new(ctx: &'ctx Context, tys: &'ir Tys) -> Self {
        Self {
            ctx,
            module: Rc::new(ctx.create_module("some_module")),
            tys,
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
impl<'ctx, 'ir> lower::Backend<'ctx> for Llvm<'ctx, 'ir> {
    type Value
        = Value<'ctx>
    where
        Self:;
    type Function
        = Function<'ctx, 'ir>
    where
        Self:;

    fn add_function(&self, name: &str, ret_ty: Ty) -> Self::Function {
        Function::new(self.ctx, Rc::clone(&self.module), self.tys, name, ret_ty)
    }

    fn get_ty(&self, ty: Ty) -> <Self::Value as ValueBackend>::Ty {
        to_llvm_ty(ty, self.tys, self.ctx)
    }
}

pub struct Function<'ctx, 'ir> {
    ctx: &'ctx Context,
    module: Rc<Module<'ctx>>,
    tys: &'ir Tys,
    builder: Builder<'ctx>,
    function: FunctionValue<'ctx>,
    entry_bb: inkwell::basic_block::BasicBlock<'ctx>,
}
impl<'ctx, 'ir> Function<'ctx, 'ir> {
    pub fn new(
        ctx: &'ctx Context,
        module: Rc<Module<'ctx>>,
        tys: &'ir Tys,
        name: &str,
        ret_ty: Ty,
    ) -> Self {
        let function = module.add_function(
            name,
            to_llvm_ty(ret_ty, tys, ctx).fn_type(
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
            tys,
        }
    }
}
impl<'ctx, 'ir> lower::Function<'ctx> for Function<'ctx, 'ir> {
    type Value = Value<'ctx>;

    fn declare_local(&mut self, ty: Ty, name: &str) -> <Value<'ctx> as ValueBackend>::Pointer {
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

        Pointer(
            self.builder
                .build_alloca(to_llvm_ty(ty, self.tys, self.ctx), name)
                .unwrap(),
        )
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

    fn term_return(&mut self, value: IntegerValue<Self::Value>) {
        self.builder
            .build_return(Some(&value.as_basic_value_enum()))
            .unwrap();
    }

    fn storage_live(&mut self, ptr: <Value<'ctx> as ValueBackend>::Pointer) {
        let intrinsic = Intrinsic::find("llvm.lifetime.start").unwrap();
        let intrinsic_fn = intrinsic
            .get_declaration(&self.module, &[BasicTypeEnum::PointerType(ptr.get_type())])
            .unwrap();
        self.builder
            .build_call(intrinsic_fn, &[(*ptr).into()], "lifetime.start")
            .unwrap();
    }

    fn storage_dead(&mut self, ptr: <Value<'ctx> as ValueBackend>::Pointer) {
        let intrinsic = Intrinsic::find("llvm.lifetime.end").unwrap();
        let intrinsic_fn = intrinsic
            .get_declaration(&self.module, &[BasicTypeEnum::PointerType(ptr.get_type())])
            .unwrap();
        self.builder
            .build_call(intrinsic_fn, &[(*ptr).into()], "lifetime.end")
            .unwrap();
    }
}

pub struct Value<'ctx>(PhantomData<&'ctx ()>);
impl<'ctx> lower::ValueBackend for Value<'ctx> {
    type BasicBlock = BasicBlock<'ctx>;

    type Ty = BasicTypeEnum<'ctx>;

    type Pointer = Pointer<'ctx>;

    type I8 = I8<'ctx>;
    type U8 = U8<'ctx>;
}

#[derive(Clone, Debug)]
pub struct Pointer<'ctx>(PointerValue<'ctx>);
impl<'ctx> crate::ir::integer::Pointer<Value<'ctx>> for Pointer<'ctx> {
    fn element_ptr<I: Integer<Value<'ctx>>>(
        self,
        bb: &mut BasicBlock<'ctx>,
        i: I,
        ty: BasicTypeEnum<'ctx>,
    ) -> Self {
        let ordered_indexes = [
            // WARN: Mega hacky
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

    fn deref(self, bb: &mut BasicBlock<'ctx>) -> Self {
        Self(
            bb.builder
                .build_load(bb.ctx.ptr_type(AddressSpace::default()), *self, "deref")
                .unwrap()
                .into_pointer_value(),
        )
    }
}
impl<'ctx> Any<Value<'ctx>> for Pointer<'ctx> {
    fn into_any_value(self) -> AnyValue<Value<'ctx>> {
        AnyValue::Pointer(self)
    }

    fn load(
        bb: &mut <Value<'ctx> as ValueBackend>::BasicBlock,
        ptr: <Value<'ctx> as ValueBackend>::Pointer,
    ) -> Self {
        Self(
            bb.builder
                .build_load(bb.ctx.ptr_type(AddressSpace::default()), *ptr, "load_ptr")
                .unwrap()
                .into_pointer_value(),
        )
    }

    fn store(
        self,
        bb: &mut <Value<'ctx> as ValueBackend>::BasicBlock,
        ptr: <Value<'ctx> as ValueBackend>::Pointer,
    ) {
        bb.builder.build_store(*ptr, self.0).unwrap();
    }
}
impl<'ctx> Deref for Pointer<'ctx> {
    type Target = PointerValue<'ctx>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Debug)]
pub struct I8<'ctx>(IntValue<'ctx>);
impl<'ctx> Any<Value<'ctx>> for I8<'ctx> {
    fn into_any_value(self) -> AnyValue<Value<'ctx>> {
        self.into_integer_value().into_any_value()
    }

    fn load(bb: &mut BasicBlock<'ctx>, ptr: <Value<'ctx> as ValueBackend>::Pointer) -> Self {
        Self(
            bb.builder
                .build_load(bb.ctx.i8_type(), *ptr, "load_i8")
                .unwrap()
                .into_int_value(),
        )
    }

    fn store(self, bb: &mut BasicBlock<'ctx>, ptr: <Value<'ctx> as ValueBackend>::Pointer) {
        bb.builder.build_store(*ptr, self.0).unwrap();
    }
}
impl<'ctx> Integer<Value<'ctx>> for I8<'ctx> {
    fn into_integer_value(self) -> IntegerValue<Value<'ctx>> {
        IntegerValue::I8(self)
    }

    fn add(bb: &mut BasicBlock<'ctx>, lhs: Self, rhs: Self) -> Self {
        Self(bb.builder.build_int_add(lhs.0, rhs.0, "add_i8").unwrap())
    }
}
impl<'ctx> Constant<Value<'ctx>> for I8<'ctx> {
    type Value = i8;

    fn create(bb: &mut <Value<'ctx> as ValueBackend>::BasicBlock, value: Self::Value) -> Self {
        Self(bb.ctx.i8_type().const_int(value as u64, false))
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

    fn load(bb: &mut BasicBlock<'ctx>, ptr: <Value<'ctx> as ValueBackend>::Pointer) -> Self {
        Self(
            bb.builder
                .build_load(bb.ctx.i8_type(), *ptr, "load_u8")
                .unwrap()
                .into_int_value(),
        )
    }

    fn store(self, bb: &mut BasicBlock<'ctx>, ptr: <Value<'ctx> as ValueBackend>::Pointer) {
        bb.builder.build_store(*ptr, self.0).unwrap();
    }
}
impl<'ctx> Integer<Value<'ctx>> for U8<'ctx> {
    fn into_integer_value(self) -> IntegerValue<Value<'ctx>> {
        IntegerValue::U8(self)
    }

    fn add(bb: &mut BasicBlock<'ctx>, lhs: Self, rhs: Self) -> Self {
        Self(bb.builder.build_int_add(lhs.0, rhs.0, "add_u8").unwrap())
    }
}
impl<'ctx> Constant<Value<'ctx>> for U8<'ctx> {
    type Value = u8;

    fn create(bb: &mut <Value<'ctx> as ValueBackend>::BasicBlock, value: Self::Value) -> Self {
        Self(bb.ctx.i8_type().const_int(value as u64, false))
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

fn to_llvm_ty<'ctx>(ty: Ty, tys: &Tys, ctx: &'ctx Context) -> BasicTypeEnum<'ctx> {
    match tys.get(ty) {
        TyInfo::U8 => ctx.i8_type().into(),
        TyInfo::I8 => ctx.i8_type().into(),
        TyInfo::Ref(inner_ty) => match tys.get(inner_ty) {
            // Fat pointer
            TyInfo::Slice(_) => ctx.ptr_type(AddressSpace::default()).array_type(2).into(),
            // Normal pointer
            _ => ctx.ptr_type(AddressSpace::default()).into(),
        },
        TyInfo::Slice(_) => panic!("unsized type, cannot convert to LLVM"),
        TyInfo::Array { ty, length } => to_llvm_ty(ty, tys, ctx).array_type(length as u32).into(),
    }
}
