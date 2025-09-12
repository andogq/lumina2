use std::marker::PhantomData;

use inkwell::{
    AddressSpace,
    builder::Builder,
    context::Context,
    execution_engine::JitFunction,
    intrinsics::Intrinsic,
    module::Module,
    types::{BasicType, BasicTypeEnum},
    values::{BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue},
};

use crate::{
    ir::{
        Ty, TyInfo, Tys,
        integer::{I8, Integer, IntegerValue, U8},
    },
    lower,
};

pub struct Llvm<'ctx, 'ir> {
    ctx: &'ctx Context,
    module: Module<'ctx>,
    tys: &'ir Tys,
}
impl<'ctx, 'ir> Llvm<'ctx, 'ir> {
    pub fn new(ctx: &'ctx Context, tys: &'ir Tys) -> Self {
        Self {
            ctx,
            module: ctx.create_module("some_module"),
            tys,
        }
    }

    pub fn run(&self, name: &str) -> u8 {
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
    type Function<'backend>
        = Function<'ctx, 'ir, 'backend>
    where
        Self: 'backend;

    fn add_function<'backend>(&'backend self, name: &str, ret_ty: Ty) -> Self::Function<'backend> {
        Function::new(self.ctx, &self.module, self.tys, name, ret_ty)
    }
}

pub struct Function<'ctx, 'ir, 'backend> {
    ctx: &'ctx Context,
    module: &'backend Module<'ctx>,
    tys: &'ir Tys,
    builder: Builder<'ctx>,
    function: FunctionValue<'ctx>,
    entry_bb: inkwell::basic_block::BasicBlock<'ctx>,
}
impl<'ctx, 'ir, 'backend> Function<'ctx, 'ir, 'backend> {
    pub fn new(
        ctx: &'ctx Context,
        module: &'backend Module<'ctx>,
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
impl<'ctx, 'ir, 'backend> lower::Function<'ctx> for Function<'ctx, 'ir, 'backend> {
    type BasicBlock = BasicBlock<'ctx, 'backend>;
    type Pointer = PointerValue<'ctx>;

    fn declare_local(&mut self, ty: Ty, name: &str) -> Self::Pointer {
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

        self.builder
            .build_alloca(to_llvm_ty(ty, self.tys, self.ctx), name)
            .unwrap()
    }

    fn add_basic_block(&mut self, name: &str) -> Self::BasicBlock {
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
            module: self.module,
            builder: {
                let builder = self.ctx.create_builder();
                builder.position_at_end(bb);
                builder
            },
            bb,
        }
    }
}

pub struct BasicBlock<'ctx, 'backend> {
    ctx: &'ctx Context,
    module: &'backend Module<'ctx>,
    builder: Builder<'ctx>,
    bb: inkwell::basic_block::BasicBlock<'ctx>,
}
impl<'ctx, 'backend> lower::BasicBlock for BasicBlock<'ctx, 'backend> {
    type Pointer = PointerValue<'ctx>;
    type Value = Value<'ctx>;

    fn integer_add<I: Integer<Self::Value>>(&mut self, lhs: I, rhs: I) {
        todo!()
    }

    fn term_return(&mut self, value: IntegerValue<Self::Value>) {
        self.builder
            .build_return(Some(&value.as_basic_value_enum()))
            .unwrap();
    }

    fn storage_live(&mut self, ptr: Self::Pointer) {
        let intrinsic = Intrinsic::find("llvm.lifetime.start").unwrap();
        let intrinsic_fn = intrinsic
            .get_declaration(&self.module, &[BasicTypeEnum::PointerType(ptr.get_type())])
            .unwrap();
        self.builder
            .build_call(intrinsic_fn, &[ptr.into()], "lifetime.start")
            .unwrap();
    }

    fn storage_dead(&mut self, ptr: Self::Pointer) {
        let intrinsic = Intrinsic::find("llvm.lifetime.end").unwrap();
        let intrinsic_fn = intrinsic
            .get_declaration(&self.module, &[BasicTypeEnum::PointerType(ptr.get_type())])
            .unwrap();
        self.builder
            .build_call(intrinsic_fn, &[ptr.into()], "lifetime.end")
            .unwrap();
    }

    fn p_deref(&mut self, ptr: Self::Pointer) -> Self::Pointer {
        self.builder
            .build_load(self.ctx.ptr_type(AddressSpace::default()), ptr, "deref")
            .unwrap()
            .into_pointer_value()
    }

    fn c_i8(&mut self, value: i8) -> I8<Self::Value> {
        I8(self.ctx.i8_type().const_int(value as u64, true))
    }
    fn c_u8(&mut self, value: u8) -> U8<Self::Value> {
        U8(self.ctx.i8_type().const_int(value as u64, false))
    }

    fn l_u8(&mut self, ptr: Self::Pointer) -> U8<Self::Value> {
        U8(self
            .builder
            .build_load(self.ctx.i8_type(), ptr, "l_u8")
            .unwrap()
            .into_int_value())
    }
    fn l_i8(&mut self, ptr: Self::Pointer) -> I8<Self::Value> {
        I8(self
            .builder
            .build_load(self.ctx.i8_type(), ptr, "l_i8")
            .unwrap()
            .into_int_value())
    }

    fn s_u8(&mut self, ptr: Self::Pointer, value: U8<Self::Value>) {
        self.builder.build_store(ptr, value.0).unwrap();
    }
    fn s_i8(&mut self, ptr: Self::Pointer, value: I8<Self::Value>) {
        self.builder.build_store(ptr, value.0).unwrap();
    }
}

pub struct Value<'ctx>(PhantomData<&'ctx ()>);
impl<'ctx> lower::ValueBackend for Value<'ctx> {
    type I8 = IntValue<'ctx>;
    type U8 = IntValue<'ctx>;
}

trait IntegerValueExt<'ctx> {
    fn as_basic_value_enum(self) -> BasicValueEnum<'ctx>;
}
impl<'ctx> IntegerValueExt<'ctx> for IntegerValue<Value<'ctx>> {
    fn as_basic_value_enum(self) -> BasicValueEnum<'ctx> {
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
