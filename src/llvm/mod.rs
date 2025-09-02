use std::{cell::RefCell, collections::HashMap};

use inkwell::{
    AddressSpace,
    basic_block::BasicBlock as IBasicBlock,
    builder::Builder,
    context::Context as IContext,
    execution_engine::JitFunction,
    intrinsics::Intrinsic,
    module::Module as IModule,
    types::{BasicType, BasicTypeEnum},
    values::{AnyValue, BasicValueEnum, PointerValue},
};

use crate::{
    ir::{
        BasicBlock, BinOp, Body, Local, Operand, Place, Projection, RValue, Statement, Terminator,
        Ty, TyInfo, Value,
        ctx::{Function, IrCtx},
    },
    util::indexed_vec::IndexedVec,
};

pub struct Llvm<'ir> {
    ctx: IContext,
    ir: &'ir IrCtx,
}
impl<'ir> Llvm<'ir> {
    pub fn new(ir: &'ir IrCtx) -> Self {
        Self {
            ctx: IContext::create(),
            ir,
        }
    }

    pub fn new_module(&self, name: &str) -> Module<'ir, '_> {
        Module::new(self, name)
    }
}

pub struct Module<'ir, 'ctx> {
    llvm: &'ctx Llvm<'ir>,
    module: IModule<'ctx>,
    tys: LlvmTys<'ir, 'ctx>,
}
impl<'ir, 'ctx> Module<'ir, 'ctx> {
    pub fn new(llvm: &'ctx Llvm<'ir>, name: &str) -> Self {
        Self {
            llvm,
            module: llvm.ctx.create_module(name),
            tys: LlvmTys::new(llvm),
        }
    }

    pub fn compile(&self, function: Function, name: &str) {
        FunctionBuilder::compile(self, function, name);
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

pub struct FunctionBuilder<'m, 'ir, 'ctx> {
    module: &'m Module<'ir, 'ctx>,
    builder: Builder<'ctx>,

    body: &'m Body,

    locals: IndexedVec<Local, (PointerValue<'ctx>, Ty)>,
    basic_blocks: IndexedVec<BasicBlock, IBasicBlock<'ctx>>,
}
impl<'m, 'ir, 'ctx> FunctionBuilder<'m, 'ir, 'ctx> {
    fn compile(module: &'m Module<'ir, 'ctx>, function: Function, name: &str) {
        let builder = module.llvm.ctx.create_builder();
        let body = &module.llvm.ir.functions[function];
        let function = module.module.add_function(
            name,
            {
                let ret_ty = module.tys.get(body.local_decls[Local::zero()].ty);
                ret_ty.fn_type(&[], false)
            },
            None,
        );

        // Create the entry basic block, and position the builder so that local allocations will be
        // added to it.
        let entry_bb = module.llvm.ctx.append_basic_block(function, "entry");
        builder.position_at_end(entry_bb);

        // Allocate all of the locals.
        let locals = body
            .local_decls
            .iter()
            .fold(IndexedVec::new(), |mut locals, decl| {
                locals.insert((
                    builder
                        .build_alloca(module.tys.get(decl.ty), "some_local")
                        .unwrap(),
                    decl.ty,
                ));

                locals
            });

        // Create all the basic blocks.
        let basic_blocks = body.basic_blocks.iter_keys().fold(
            IndexedVec::new(),
            |mut basic_blocks, (bb, _basic_block)| {
                basic_blocks.insert(
                    module
                        .llvm
                        .ctx
                        .append_basic_block(function, &bb.to_string()),
                );

                basic_blocks
            },
        );

        // Ensure entry bb jumps to first basic block.
        builder
            .build_unconditional_branch(basic_blocks[BasicBlock::zero()])
            .unwrap();

        // Gather all state into single object to share.
        let f = Self {
            locals,
            basic_blocks,

            module,
            builder,
            body,
        };

        // Compile each of the basic blocks.
        for (bb, _) in f.basic_blocks.iter_keys() {
            f.compile_basic_block(bb);
        }

        println!("{}", function.print_to_string().to_string());
    }

    fn compile_basic_block(&self, basic_block: BasicBlock) {
        self.builder.position_at_end(self.basic_blocks[basic_block]);

        let bb = &self.body.basic_blocks[basic_block];

        for statement in &bb.statements {
            match statement {
                Statement::Assign { place, rvalue } => {
                    let (place_ptr, place_ty) = self.get_place_ptr(place);
                    self.store_rvalue(rvalue, place_ptr, place_ty);
                }
                Statement::StorageDead(local) => {
                    let ptr = self.locals[*local].0;

                    let intrinsic = Intrinsic::find("llvm.lifetime.end").unwrap();
                    let intrinsic_fn = intrinsic
                        .get_declaration(
                            &self.module.module,
                            &[BasicTypeEnum::PointerType(ptr.get_type())],
                        )
                        .unwrap();
                    self.builder
                        .build_call(intrinsic_fn, &[ptr.into()], "lifetime.end")
                        .unwrap();
                }
                Statement::StorageLive(local) => {
                    let ptr = self.locals[*local].0;

                    let intrinsic = Intrinsic::find("llvm.lifetime.start").unwrap();
                    let intrinsic_fn = intrinsic
                        .get_declaration(
                            &self.module.module,
                            &[BasicTypeEnum::PointerType(ptr.get_type())],
                        )
                        .unwrap();
                    self.builder
                        .build_call(intrinsic_fn, &[ptr.into()], "lifetime.start")
                        .unwrap();
                }
            }
        }

        match &bb.terminator {
            Terminator::Call {
                func,
                args,
                destination,
                target,
            } => todo!(),
            Terminator::Goto(basic_block) => todo!(),
            Terminator::Return => {
                let ret_local = Local::zero();

                let (ret_ptr, ret_ty) = self.locals[ret_local];

                let out = self
                    .builder
                    .build_load(self.module.tys.get(ret_ty), ret_ptr, "idk")
                    .unwrap();
                self.builder.build_return(Some(&out)).unwrap();
            }
            Terminator::SwitchInt {
                discriminator,
                targets,
                otherwise,
            } => todo!(),
        }
    }

    fn get_place_ptr(&self, place: &Place) -> (PointerValue<'ctx>, TyInfo) {
        let (mut ptr, ty) = self.locals[place.local];
        let mut ty = self.module.llvm.ir.tys.get(ty);

        for projection in &place.projection {
            match projection {
                Projection::Deref => {
                    let TyInfo::Ref(inner_ty) = ty else {
                        panic!("can only deref a reference");
                    };

                    ptr = self
                        .builder
                        .build_load(
                            self.module
                                .tys
                                .get(self.module.llvm.ir.tys.find_or_insert(ty)),
                            ptr,
                            "deref",
                        )
                        .unwrap()
                        .into_pointer_value();
                    ty = self.module.llvm.ir.tys.get(inner_ty);
                }
                Projection::Field(_) => todo!(),
                Projection::Index(local) => {
                    let array_ty = self.module.llvm.ir.tys.find_or_insert(ty.clone());
                    let TyInfo::Array {
                        ty: inner_ty,
                        length: _,
                    } = ty
                    else {
                        panic!("can only index an array");
                    };

                    let (local_ptr, local_ty) = self.locals[*local];
                    let index = self
                        .builder
                        .build_load(self.module.tys.get(local_ty), local_ptr, "load index")
                        .unwrap()
                        .into_int_value();

                    ptr = unsafe {
                        self.builder
                            .build_in_bounds_gep(
                                self.module.tys.get(inner_ty),
                                ptr,
                                &[index],
                                "index something",
                            )
                            .unwrap()
                    };
                    ty = self.module.llvm.ir.tys.get(inner_ty);
                }
            }
        }

        (ptr, ty)
    }

    fn store_rvalue(&self, rvalue: &RValue, place_ptr: PointerValue<'ctx>, place_ty: TyInfo) {
        match rvalue {
            RValue::Use(operand) => {
                let (value, ty) = self.get_operand(operand);
                assert_eq!(place_ty, ty,);
                self.builder.build_store(place_ptr, value).unwrap();
            }
            RValue::Ref(place) => {
                let (ptr, inner_ty) = self.get_place_ptr(place);
                let ty = TyInfo::Ref(self.module.llvm.ir.tys.find_or_insert(inner_ty));
                assert_eq!(place_ty, ty);
                self.builder.build_store(place_ptr, ptr).unwrap();
            }
            RValue::BinaryOp { op, lhs, rhs } => {
                let (BasicValueEnum::IntValue(lhs), lhs_ty) = self.get_operand(lhs) else {
                    panic!("not good");
                };
                let (BasicValueEnum::IntValue(rhs), rhs_ty) = self.get_operand(rhs) else {
                    panic!("not good");
                };
                assert_eq!(lhs_ty, rhs_ty);

                assert_eq!(place_ty, lhs_ty);

                let value = match op {
                    BinOp::Add => self.builder.build_int_add(lhs, rhs, "add shit").unwrap(),
                    BinOp::Sub => self.builder.build_int_sub(lhs, rhs, "sub shit").unwrap(),
                    BinOp::Mul => self.builder.build_int_mul(lhs, rhs, "mul shit").unwrap(),
                    BinOp::Div => match lhs_ty {
                        TyInfo::U8 => self
                            .builder
                            .build_int_unsigned_div(lhs, rhs, "div shit")
                            .unwrap(),
                        TyInfo::I8 => self
                            .builder
                            .build_int_signed_div(lhs, rhs, "div shit (but signed)")
                            .unwrap(),
                        _ => panic!("can't div this type"),
                    },
                };
                self.builder.build_store(place_ptr, value).unwrap();
            }
            RValue::UnaryOp { op, rhs } => todo!(),
            RValue::Aggregate { values } => {
                let values = values
                    .iter()
                    .map(|value| self.get_operand(value))
                    .collect::<Vec<_>>();

                let pointee_ty = self.module.llvm.ir.tys.find_or_insert(values[0].1.clone());
                let ty = TyInfo::Array {
                    ty: pointee_ty,
                    length: values.len(),
                };
                assert_eq!(place_ty, ty);

                let pointee_ty = self.module.tys.get(pointee_ty);

                for (i, (value, _)) in values.into_iter().enumerate() {
                    let ptr = unsafe {
                        self.builder.build_in_bounds_gep(
                            pointee_ty,
                            place_ptr,
                            &[self
                                .module
                                .tys
                                .get(self.module.llvm.ir.tys.find_or_insert(TyInfo::U8))
                                .into_int_type()
                                .const_int(i as u64, false)],
                            "something",
                        )
                    }
                    .unwrap();

                    self.builder.build_store(ptr, value).unwrap();
                }
            }
        }
    }

    fn get_operand(&self, operand: &Operand) -> (BasicValueEnum<'ctx>, TyInfo) {
        match operand {
            Operand::Place(place) => {
                let (ptr, ty) = self.get_place_ptr(place);
                (
                    self.builder
                        .build_load(
                            self.module
                                .tys
                                .get(self.module.llvm.ir.tys.find_or_insert(ty.clone())),
                            ptr,
                            "asdfasdf",
                        )
                        .unwrap(),
                    ty,
                )
            }
            Operand::Constant(value) => match value {
                Value::U8(value) => (
                    self.module
                        .tys
                        .get(self.module.llvm.ir.tys.find_or_insert(TyInfo::U8))
                        .into_int_type()
                        .const_int(*value as u64, false)
                        .into(),
                    TyInfo::U8,
                ),
                Value::I8(value) => (
                    self.module
                        .tys
                        .get(self.module.llvm.ir.tys.find_or_insert(TyInfo::I8))
                        .into_int_type()
                        .const_int(*value as u64, false)
                        .into(),
                    TyInfo::I8,
                ),
                Value::Ref(pointer) => todo!(),
                Value::Array(values) => todo!(),
            },
        }
    }
}

struct LlvmTys<'ir, 'ctx> {
    cache: RefCell<HashMap<Ty, BasicTypeEnum<'ctx>>>,
    llvm: &'ctx Llvm<'ir>,
}
impl<'ir, 'ctx> LlvmTys<'ir, 'ctx> {
    pub fn new(llvm: &'ctx Llvm<'ir>) -> Self {
        Self {
            cache: RefCell::new(HashMap::new()),
            llvm,
        }
    }

    pub fn get(&self, ty: Ty) -> BasicTypeEnum<'ctx> {
        let cache = self.cache.borrow().get(&ty).cloned();
        match cache {
            Some(ty) => ty,
            None => {
                let mut cache = self.cache.borrow_mut();
                cache.insert(ty, self.of_ty(ty));
                cache[&ty]
            }
        }
    }

    fn of_ty(&self, ty: Ty) -> BasicTypeEnum<'ctx> {
        match self.llvm.ir.tys.get(ty) {
            TyInfo::U8 => self.llvm.ctx.i8_type().as_basic_type_enum(),
            TyInfo::I8 => self.llvm.ctx.i8_type().as_basic_type_enum(),
            TyInfo::Ref(_) => self
                .llvm
                .ctx
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum(),
            TyInfo::Array { ty, length } => self
                .of_ty(ty)
                .array_type(length as u32)
                .as_basic_type_enum(),
        }
    }
}
