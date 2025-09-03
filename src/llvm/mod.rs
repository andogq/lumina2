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
        BasicBlock, BinOp, Body, CastKind, Local, Operand, Place, PointerCoercion, Projection,
        RValue, Statement, Terminator, Ty, TyInfo, UnOp, Value,
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
            Terminator::Goto(basic_block) => {
                self.builder
                    .build_unconditional_branch(self.basic_blocks[*basic_block])
                    .unwrap();
            }
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
            } => {
                self.builder
                    .build_switch(
                        self.get_operand(discriminator).0.into_int_value(),
                        self.basic_blocks[*otherwise],
                        &targets
                            .iter()
                            .map(|(value, bb)| {
                                (
                                    self.module
                                        .tys
                                        .get(value.get_const_ty(&self.module.llvm.ir.tys))
                                        .into_int_type()
                                        .const_int(
                                            // HACK: Only supports u8
                                            value.clone().into_u8().unwrap() as u64,
                                            false,
                                        ),
                                    self.basic_blocks[*bb],
                                )
                            })
                            .collect::<Vec<_>>(),
                    )
                    .unwrap();
            }
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

                    match self.module.llvm.ir.tys.get(inner_ty) {
                        TyInfo::Slice(_) => {
                            // Load pointer component of fat pointer
                            ptr = self
                                .builder
                                .build_load(
                                    // HACK: Directly pulling out the pointer type, assuming that
                                    // the fat pointer ptr is at the start.
                                    self.module.llvm.ctx.ptr_type(AddressSpace::default()),
                                    ptr,
                                    "deref",
                                )
                                .unwrap()
                                .into_pointer_value();
                        }
                        _ => {
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
                        }
                    }

                    ty = self.module.llvm.ir.tys.get(inner_ty);
                }
                Projection::Field(_) => todo!(),
                Projection::Index(local) => {
                    let inner_ty = match ty {
                        TyInfo::Array { ty, .. } => ty,
                        TyInfo::Slice(ty) => ty,
                        _ => {
                            panic!("can only index an array or slice");
                        }
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
            RValue::UnaryOp { op, rhs } => {
                let (rhs, rhs_ty) = self.get_operand(rhs);

                match op {
                    UnOp::Not => {
                        todo!()
                    }
                    UnOp::Neg => {
                        todo!()
                    }
                    UnOp::PtrMetadata => {
                        let TyInfo::Ref(inner_ty) = rhs_ty else {
                            panic!("can only get ptr metadata of reference")
                        };
                        let TyInfo::Slice(_) = self.module.llvm.ir.tys.get(inner_ty) else {
                            panic!("can only get ptr metadata of slice reference");
                        };

                        // HACK: Assuming rhs is an array value
                        let data = self
                            .builder
                            .build_extract_value(rhs.into_array_value(), 1, "extract data")
                            .unwrap();
                        self.builder.build_store(place_ptr, data).unwrap();
                    }
                }
            }
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
            RValue::Cast {
                kind,
                op,
                ty: cast_ty,
            } => {
                let (op, op_ty) = self.get_operand(op);

                match kind {
                    CastKind::PointerCoercion(PointerCoercion::Unsize) => {
                        let TyInfo::Ref(_place_inner) = place_ty else {
                            panic!("can only store coercion in reference");
                        };

                        let TyInfo::Ref(ref_ty) = self.module.llvm.ir.tys.get(*cast_ty) else {
                            panic!("can only unsize coerce to reference");
                        };
                        let TyInfo::Ref(op_ty) = op_ty else {
                            panic!("can only unsize coerce if operand is a reference");
                        };

                        let op_ty = self.module.llvm.ir.tys.get(op_ty);
                        let ref_ty = self.module.llvm.ir.tys.get(ref_ty);

                        match (op_ty, ref_ty) {
                            (
                                TyInfo::Array {
                                    ty: inner_ty,
                                    length,
                                },
                                TyInfo::Slice(slice_ty),
                            ) if inner_ty == slice_ty => {
                                let ptr = op.into_pointer_value();

                                let data_ptr = {
                                    // HACK: Assumes that fat pointers are allocated as an array of
                                    // two pointers. This will access the second item (the data).
                                    let pointee_ty =
                                        self.module.llvm.ctx.ptr_type(AddressSpace::default());
                                    let ordered_indexes =
                                        &[self.module.llvm.ctx.i8_type().const_int(1, false)];
                                    unsafe {
                                        self.builder.build_in_bounds_gep(
                                            pointee_ty,
                                            place_ptr,
                                            ordered_indexes,
                                            "fat pointer data index",
                                        )
                                    }
                                    .unwrap()
                                };

                                // Write the pointer to the start.
                                self.builder.build_store(place_ptr, ptr).unwrap();

                                // Write the data to the end.
                                self.builder
                                    .build_store(
                                        data_ptr,
                                        // HACK: Directly creating int for the length.
                                        self.module
                                            .llvm
                                            .ctx
                                            .i64_type()
                                            .const_int(length as u64, false),
                                    )
                                    .unwrap();
                            }
                            (op_ty, ref_ty) => panic!(
                                "cannot coerce pointer to {op_ty:?} into pointer of {ref_ty:?}"
                            ),
                        }
                    }
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
                Value::FatPointer { .. } => todo!(),
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
            TyInfo::Ref(inner) => match self.llvm.ir.tys.get(inner) {
                // References to slices are fat pointers, so are 2 pointers wide.
                TyInfo::Slice(_) => self
                    .llvm
                    .ctx
                    .ptr_type(AddressSpace::default())
                    .array_type(2)
                    .as_basic_type_enum(),
                _ => self
                    .llvm
                    .ctx
                    .ptr_type(AddressSpace::default())
                    .as_basic_type_enum(),
            },
            TyInfo::Slice(_) => unimplemented!(),
            TyInfo::Array { ty, length } => self
                .of_ty(ty)
                .array_type(length as u32)
                .as_basic_type_enum(),
        }
    }
}
