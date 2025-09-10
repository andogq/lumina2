use std::marker::PhantomData;

use inkwell::{
    AddressSpace,
    builder::Builder,
    context::Context,
    module::Module,
    types::{BasicType, BasicTypeEnum},
    values::{BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue},
};

use crate::{
    ir::{
        Ty, TyInfo, Tys,
        integer::{Constant, I8, Integer, IntegerValue, U8, ValueBackend},
    },
    lower,
};

pub struct Llvm<'ir> {
    ctx: Context,
    tys: &'ir Tys,
}
impl<'ir> Llvm<'ir> {
    pub fn new(tys: &'ir Tys) -> Self {
        Self {
            ctx: Context::create(),
            tys,
        }
    }
}
impl<'ir> lower::Backend for Llvm<'ir> {
    type Function<'ctx>
        = Function<'ctx>
    where
        'ir: 'ctx;

    fn add_function<'ctx>(&'ctx self, name: &str, ret_ty: Ty) -> Self::Function<'ctx> {
        Function::new(&self.ctx, &self.tys, name, ret_ty)
    }
}

pub struct Function<'ctx> {
    ctx: &'ctx Context,
    tys: &'ctx Tys,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    function: FunctionValue<'ctx>,
    entry_bb: inkwell::basic_block::BasicBlock<'ctx>,
}
impl<'ctx> Function<'ctx> {
    pub fn new(ctx: &'ctx Context, tys: &'ctx Tys, name: &str, ret_ty: Ty) -> Self {
        // TODO: Module name
        let module = ctx.create_module("some_module");
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
            tys,
            module,
        }
    }
}
impl<'ctx> lower::Function<'ctx> for Function<'ctx> {
    type BasicBlock = BasicBlock<'ctx>;
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
    builder: Builder<'ctx>,
    bb: inkwell::basic_block::BasicBlock<'ctx>,
}
impl<'ctx> lower::BasicBlock for BasicBlock<'ctx> {
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

    fn p_deref(&mut self, ptr: Self::Pointer) -> Self::Pointer {
        self.builder
            .build_load(self.ctx.ptr_type(AddressSpace::default()), ptr, "deref")
            .unwrap()
            .into_pointer_value()
    }

    fn c<C: Constant<Self::Value>>(&mut self, value: C) -> C::Value {
        C::create(self, value)
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

    fn l<T: Integer<Self::Value>>(&mut self, ptr: Self::Pointer) -> T {
        todo!()
    }
}

pub struct Value<'ctx>(PhantomData<&'ctx ()>);
impl<'ctx> lower::ValueBackend for Value<'ctx> {
    type Ctx = BasicBlock<'ctx>;

    type I8 = IntValue<'ctx>;
    type U8 = IntValue<'ctx>;

    fn create_i8(bb: &Self::Ctx, value: i8) -> <Value<'ctx> as ValueBackend>::I8 {
        bb.ctx.i8_type().const_int(value as u64, true)
    }

    fn create_u8(bb: &Self::Ctx, value: u8) -> <Value<'ctx> as ValueBackend>::U8 {
        bb.ctx.i8_type().const_int(value as u64, false)
    }
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
