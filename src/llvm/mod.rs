use std::collections::HashMap;

use inkwell::{
    AddressSpace,
    context::Context as IContext,
    execution_engine::JitFunction,
    module::Module as IModule,
    values::{BasicValueEnum, IntValue},
};

use crate::ir::{
    BasicBlock, BinOp, Local, Operand, Projection, RValue, Statement, Terminator, Ty, TyInfo,
    Value,
    ctx::{Function, IrCtx},
};

pub struct Llvm(IContext);
impl Llvm {
    pub fn new() -> Self {
        Self(IContext::create())
    }

    pub fn new_module(&self, name: &str) -> Module {
        Module::new(&self.0, name)
    }
}

pub struct Module<'ctx> {
    context: &'ctx IContext,
    module: IModule<'ctx>,
}
impl<'ctx> Module<'ctx> {
    pub fn new(context: &'ctx IContext, name: &str) -> Self {
        Self {
            context,
            module: context.create_module(name),
        }
    }

    pub fn compile(&self, ctx: IrCtx, function: Function, name: &str) {
        let builder = self.context.create_builder();

        // Capture function body.
        let body = &ctx.functions[function];

        let i8_type = self.context.i8_type();
        let ptr_type = self.context.ptr_type(AddressSpace::default());

        // Set up function signature.
        let function = self
            .module
            .add_function(name, i8_type.fn_type(&[], false), None);

        // Entry basic block sets up allocations.
        let entry_bb = self.context.append_basic_block(function, "entry");
        builder.position_at_end(entry_bb);
        let locals = body
            .local_decls
            .iter_keys()
            .map(|(local, alloc)| {
                let alloc = builder
                    .build_alloca(
                        match &ctx.tys[alloc.ty] {
                            TyInfo::U8 | TyInfo::I8 => i8_type,
                            _ => unimplemented!(),
                        },
                        name,
                    )
                    .unwrap();

                (local, alloc)
            })
            .collect::<HashMap<_, _>>();

        // Prepare all other basic blocks.
        let basic_blocks = body
            .basic_blocks
            .iter_keys()
            .map(|(bb, _)| {
                let llvm_bb = self
                    .context
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
                        let place = {
                            let mut ptr = locals[&place.local];

                            for proj in &place.projection {
                                match proj {
                                    Projection::Deref => todo!(),
                                    Projection::Field(_) => todo!(),
                                    Projection::Index(local) => todo!(),
                                }
                            }

                            ptr
                        };

                        let rvalue = match rvalue {
                            RValue::Use(operand) => match operand {
                                Operand::Place(place) => {
                                    let ptr = locals[&place.local];
                                    assert!(place.projection.is_empty());
                                    builder.build_load(i8_type, ptr, "asdfasdf").unwrap()
                                }
                                Operand::Constant(value) => match value {
                                    Value::U8(value) => {
                                        i8_type.const_int(*value as u64, false).into()
                                    }
                                    Value::I8(value) => {
                                        i8_type.const_int(*value as u64, false).into()
                                    }
                                    Value::Ref(pointer) => todo!(),
                                    Value::Array(values) => todo!(),
                                },
                            },
                            RValue::Ref(place) => todo!(),
                            RValue::BinaryOp { op, lhs, rhs } => {
                                let BasicValueEnum::IntValue(lhs) = (match lhs {
                                    Operand::Place(place) => {
                                        let ptr = locals[&place.local];
                                        assert!(place.projection.is_empty());
                                        builder.build_load(i8_type, ptr, "asdfasdf").unwrap()
                                    }
                                    Operand::Constant(value) => match value {
                                        Value::U8(value) => {
                                            i8_type.const_int(*value as u64, false).into()
                                        }
                                        Value::I8(value) => {
                                            i8_type.const_int(*value as u64, false).into()
                                        }
                                        Value::Ref(pointer) => todo!(),
                                        Value::Array(values) => todo!(),
                                    },
                                }) else {
                                    panic!("not good");
                                };
                                let BasicValueEnum::IntValue(rhs) = (match rhs {
                                    Operand::Place(place) => {
                                        let ptr = locals[&place.local];
                                        assert!(place.projection.is_empty());
                                        builder.build_load(i8_type, ptr, "asdfasdf").unwrap()
                                    }
                                    Operand::Constant(value) => match value {
                                        Value::U8(value) => {
                                            i8_type.const_int(*value as u64, false).into()
                                        }
                                        Value::I8(value) => {
                                            i8_type.const_int(*value as u64, false).into()
                                        }
                                        Value::Ref(pointer) => todo!(),
                                        Value::Array(values) => todo!(),
                                    },
                                }) else {
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
                    Statement::StorageDead(local) => todo!(),
                    Statement::StorageLive(local) => todo!(),
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
                    let out = builder
                        .build_load(i8_type, locals[&Local::zero()], "idk")
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

        println!("{}", self.module.print_to_string().to_string());
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
