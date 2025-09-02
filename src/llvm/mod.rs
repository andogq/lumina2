use std::{cell::RefCell, collections::HashMap};

use inkwell::{
    builder::Builder,
    context::Context as IContext,
    execution_engine::JitFunction,
    module::Module as IModule,
    types::{BasicType, BasicTypeEnum},
    values::{BasicValueEnum, PointerValue},
};

use crate::ir::{
    BasicBlock, BinOp, Body, Local, Operand, Place, Projection, RValue, Statement, Terminator, Ty,
    TyInfo, Value,
    ctx::{Function, IrCtx},
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
        let builder = self.llvm.ctx.create_builder();

        // Capture function body.
        let body = &self.llvm.ir.functions[function];

        // Set up function signature.
        let ret_ty = self.tys.get(body.local_decls[Local::zero()].ty);
        let function = self
            .module
            .add_function(name, ret_ty.fn_type(&[], false), None);

        // Entry basic block sets up allocations.
        let entry_bb = self.llvm.ctx.append_basic_block(function, "entry");
        builder.position_at_end(entry_bb);
        let locals = body
            .local_decls
            .iter_keys()
            .map(|(local, alloc)| {
                let alloc = builder.build_alloca(self.tys.get(alloc.ty), name).unwrap();

                (local, alloc)
            })
            .collect::<HashMap<_, _>>();

        // Prepare all other basic blocks.
        let basic_blocks = body
            .basic_blocks
            .iter_keys()
            .map(|(bb, _)| {
                let llvm_bb = self
                    .llvm
                    .ctx
                    .append_basic_block(function, bb.to_string().as_str());
                (bb, llvm_bb)
            })
            .collect::<HashMap<_, _>>();

        // Jump to function entry, and compile user basic blocks.
        builder
            .build_unconditional_branch(basic_blocks[&BasicBlock::zero()])
            .unwrap();

        for (bb, block) in body.basic_blocks.iter_keys() {
            builder.position_at_end(basic_blocks[&bb]);

            for statement in &block.statements {
                match statement {
                    Statement::Assign { place, rvalue } => {
                        let (place, ty) =
                            self.get_place_ptr(place.clone(), &builder, body, &locals);

                        let rvalue = match rvalue {
                            RValue::Use(operand) => {
                                self.get_operand(operand, &builder, body, &locals)
                            }
                            RValue::Ref(place) => todo!(),
                            RValue::BinaryOp { op, lhs, rhs } => {
                                let BasicValueEnum::IntValue(lhs) =
                                    self.get_operand(lhs, &builder, body, &locals)
                                else {
                                    panic!("not good");
                                };
                                let BasicValueEnum::IntValue(rhs) =
                                    self.get_operand(rhs, &builder, body, &locals)
                                else {
                                    panic!("not good");
                                };

                                match op {
                                    BinOp::Add => {
                                        builder.build_int_add(lhs, rhs, "add shit").unwrap().into()
                                    }
                                    BinOp::Sub => todo!(),
                                    BinOp::Mul => todo!(),
                                    BinOp::Div => todo!(),
                                }
                            }
                            RValue::UnaryOp { op, rhs } => todo!(),
                            RValue::Aggregate { values } => todo!(),
                        };

                        builder.build_store(place, rvalue).unwrap();
                    }
                    Statement::StorageDead(local) => {}
                    Statement::StorageLive(local) => {}
                }
            }

            match &block.terminator {
                Terminator::Call {
                    func,
                    args,
                    destination,
                    target,
                } => todo!(),
                Terminator::Goto(basic_block) => todo!(),
                Terminator::Return => {
                    let ret_local = Local::zero();

                    let out = builder
                        .build_load(
                            self.tys.get(body.local_decls[ret_local].ty),
                            locals[&ret_local],
                            "idk",
                        )
                        .unwrap();
                    builder.build_return(Some(&out)).unwrap();
                }
                Terminator::SwitchInt {
                    discriminator,
                    targets,
                    otherwise,
                } => todo!(),
            }
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

    fn get_place_ptr(
        &self,
        place: Place,
        builder: &Builder<'ctx>,
        body: &Body,
        locals: &HashMap<Local, PointerValue<'ctx>>,
    ) -> (PointerValue<'ctx>, TyInfo) {
        let mut ptr = locals[&place.local];
        let mut ty = self.llvm.ir.tys.get(body.local_decls[place.local].ty);

        for projection in place.projection {
            match projection {
                Projection::Deref => {
                    let TyInfo::Ref(inner_ty) = ty else {
                        panic!("can only deref a reference");
                    };

                    ptr = builder
                        .build_load(self.tys.get(inner_ty), ptr, "deref")
                        .unwrap()
                        .into_pointer_value();
                    ty = self.llvm.ir.tys.get(inner_ty);
                }
                Projection::Field(_) => todo!(),
                Projection::Index(local) => {
                    let array_ty = self.llvm.ir.tys.find_or_insert(ty.clone());
                    let TyInfo::Array {
                        ty: inner_ty,
                        length: _,
                    } = ty
                    else {
                        panic!("can only index an array");
                    };

                    let index = builder
                        .build_load(
                            self.tys.get(body.local_decls[place.local].ty),
                            locals[&local],
                            "load index",
                        )
                        .unwrap()
                        .into_int_value();

                    ptr = unsafe {
                        builder
                            .build_gep(self.tys.get(array_ty), ptr, &[index], "index somethign")
                            .unwrap()
                    };
                    ty = self.llvm.ir.tys.get(inner_ty);
                }
            }
        }

        (ptr, ty)
    }

    fn get_operand(
        &self,
        operand: &Operand,
        builder: &Builder<'ctx>,
        body: &Body,
        locals: &HashMap<Local, PointerValue<'ctx>>,
    ) -> BasicValueEnum<'ctx> {
        match operand {
            Operand::Place(place) => {
                let (ptr, ty) = self.get_place_ptr(place.clone(), &builder, body, &locals);
                builder
                    .build_load(
                        self.tys.get(self.llvm.ir.tys.find_or_insert(ty)),
                        ptr,
                        "asdfasdf",
                    )
                    .unwrap()
            }
            Operand::Constant(value) => match value {
                Value::U8(value) => self
                    .tys
                    .get(self.llvm.ir.tys.find_or_insert(TyInfo::U8))
                    .into_int_type()
                    .const_int(*value as u64, false)
                    .into(),
                Value::I8(value) => self
                    .tys
                    .get(self.llvm.ir.tys.find_or_insert(TyInfo::I8))
                    .into_int_type()
                    .const_int(*value as u64, false)
                    .into(),
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
            TyInfo::Ref(ty) => todo!(),
            TyInfo::Array { ty, length } => todo!(),
        }
    }
}
