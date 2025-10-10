use core::net;
use std::{cell::RefCell, collections::HashMap};

use inkwell::{
    AddressSpace,
    builder::Builder,
    context::Context as InkContext,
    execution_engine::JitFunction,
    intrinsics::Intrinsic,
    module::Module,
    types::{BasicType, BasicTypeEnum},
    values::{BasicMetadataValueEnum, BasicValueEnum, PointerValue},
};

use crate::ir::{
    Ty, TyInfo,
    ctx::IrCtx,
    repr::{
        BasicBlock, BinOp, CastKind, Constant, Local, Locals, Operand, Place, PointerCoercion,
        Projection, RValue, Statement, Terminator, UnOp,
    },
};

pub struct Llvm<'ink, 'ir> {
    ctx: &'ink InkContext,
    ir: &'ir IrCtx,
    module: Module<'ink>,

    tys: RefCell<HashMap<Ty, BasicTypeEnum<'ink>>>,
}

impl<'ink, 'ir> Llvm<'ink, 'ir> {
    pub fn new(ctx: &'ink InkContext, ir: &'ir IrCtx) -> Self {
        let mut llvm = Self {
            ctx,
            ir,
            module: ctx.create_module("module"),
            tys: RefCell::new(HashMap::new()),
        };

        llvm.lower();

        llvm
    }

    pub fn run(&self, name: &str) -> u8 {
        let engine = self
            .module
            .create_jit_execution_engine(inkwell::OptimizationLevel::None)
            .unwrap();
        let f: JitFunction<'ink, unsafe extern "C" fn() -> u8> =
            unsafe { engine.get_function(name).unwrap() };

        unsafe { f.call() }
    }

    fn lower(&mut self) {
        // Forward declare all functions.
        let functions = self
            .ir
            .functions
            .iter_keys()
            .map(|(id, function)| {
                let ret = self
                    .get_ty(function.local_decls[Local::zero()].ty)
                    .fn_type(&[], false);

                (
                    id,
                    (
                        self.module
                            .add_function(format!("func_{id:?}").as_str(), ret, None),
                        function,
                    ),
                )
            })
            .collect::<HashMap<_, _>>();

        for (function_id, (function, ir)) in &functions {
            let entry_bb = self.ctx.append_basic_block(*function, "entry");
            let builder = self.ctx.create_builder();
            builder.position_at_end(entry_bb);

            // Build all locals.
            let local_ptrs = ir
                .local_decls
                .iter_keys()
                .map(|(id, local)| {
                    (
                        id,
                        builder
                            .build_alloca(self.get_ty(local.ty), id.to_string().as_str())
                            .unwrap(),
                    )
                })
                .collect::<HashMap<_, _>>();

            // Forward declare all basic blocks.
            let basic_blocks = ir
                .basic_blocks
                .iter_keys()
                .map(|(bb_id, _)| {
                    (
                        bb_id,
                        self.ctx
                            .append_basic_block(*function, bb_id.to_string().as_str()),
                    )
                })
                .collect::<HashMap<_, _>>();

            // Terminate the entry basic block by jumping to the first user basic block.
            builder
                .build_unconditional_branch(basic_blocks[&BasicBlock::zero()])
                .unwrap();

            // Lower each of the blocks.
            for (bb_id, block) in ir.basic_blocks.iter_keys() {
                let bb = basic_blocks[&bb_id];
                builder.position_at_end(bb);

                for statement in &block.statements {
                    match statement {
                        Statement::Assign { place, rvalue } => {
                            let (place_ptr, place_ty) =
                                self.resolve_place(&builder, place, &ir.local_decls, &local_ptrs);
                            self.store_rvalue(
                                &builder,
                                rvalue,
                                place_ptr,
                                place_ty,
                                &ir.local_decls,
                                &local_ptrs,
                            );
                        }
                        Statement::StorageDead(local) => {
                            let ptr = local_ptrs[local];
                            self.build_intrinsic(
                                &builder,
                                "llvm.lifetime.end",
                                &[ptr.get_type().into()],
                                &[ptr.into()],
                            );
                        }
                        Statement::StorageLive(local) => {
                            let ptr = local_ptrs[local];
                            self.build_intrinsic(
                                &builder,
                                "llvm.lifetime.start",
                                &[ptr.get_type().into()],
                                &[ptr.into()],
                            );
                        }
                    }
                }

                match &block.terminator {
                    Terminator::Call {
                        func,
                        args,
                        destination,
                        target,
                    } => todo!(),
                    Terminator::Goto(basic_block) => {
                        builder
                            .build_unconditional_branch(basic_blocks[basic_block])
                            .unwrap();
                    }
                    Terminator::Return => {
                        let ret_local = Local::zero();
                        let ret_ty = ir.local_decls[ret_local].ty;
                        let ret_ptr = local_ptrs[&ret_local];

                        let out = builder
                            .build_load(self.get_ty(ret_ty), ret_ptr, "load ret")
                            .unwrap();
                        builder.build_return(Some(&out)).unwrap();
                    }
                    Terminator::SwitchInt {
                        discriminator,
                        targets,
                        otherwise,
                    } => {
                        builder
                            .build_switch(
                                self.get_operand(
                                    &builder,
                                    discriminator,
                                    &ir.local_decls,
                                    &local_ptrs,
                                )
                                .0
                                .into_int_value(),
                                basic_blocks[otherwise],
                                &targets
                                    .iter()
                                    .map(|(value, bb)| {
                                        (
                                            match value {
                                                Constant::I8(value) => self
                                                    .get_ty(self.ir.tys.find_or_insert(TyInfo::I8))
                                                    .into_int_type()
                                                    .const_int(*value as u64, true),
                                                Constant::U8(value) => self
                                                    .get_ty(self.ir.tys.find_or_insert(TyInfo::U8))
                                                    .into_int_type()
                                                    .const_int(*value as u64, false),
                                            },
                                            basic_blocks[bb],
                                        )
                                    })
                                    .collect::<Vec<_>>(),
                            )
                            .unwrap();
                    }
                }
            }
        }
    }

    fn get_ty(&self, ty: Ty) -> BasicTypeEnum<'ink> {
        if let Some(ty) = self.tys.borrow().get(&ty) {
            return *ty;
        }

        let ty_info = match self.ir.tys.get(ty) {
            TyInfo::U8 => self.ctx.i8_type().into(),
            TyInfo::I8 => self.ctx.i8_type().into(),
            TyInfo::Ref(ty) => match self.ir.tys.get(ty) {
                // Ref to slice is a fat pointer.
                TyInfo::Slice(_) => self
                    .ctx
                    .ptr_type(AddressSpace::default())
                    .array_type(2)
                    .into(),
                _ => self.ctx.ptr_type(AddressSpace::default()).into(),
            },
            TyInfo::Array { ty, length } => self.get_ty(ty).array_type(length as u32).into(),
            TyInfo::Slice(ty) => panic!("cannot have type for slice, as it's unsized"),
            TyInfo::Unit => todo!("unit type"),
        };

        self.tys.borrow_mut().insert(ty, ty_info);

        ty_info
    }

    fn resolve_place(
        &self,
        builder: &Builder<'ink>,
        place: &Place,
        locals: &Locals,
        local_ptrs: &HashMap<Local, PointerValue<'ink>>,
    ) -> (PointerValue<'ink>, Ty) {
        let mut ptr = local_ptrs[&place.local];
        let mut ty = locals[place.local].ty;

        for projection in &place.projection {
            match projection {
                Projection::Deref => {
                    let TyInfo::Ref(inner_ty) = self.ir.tys.get(ty) else {
                        panic!("Can only dereference a reference");
                    };

                    match self.ir.tys.get(inner_ty) {
                        TyInfo::Slice(_) => {
                            // Load pointer component of fat pointer.
                            ptr = builder
                                .build_load(
                                    // HACK: Assuming pointer is stored at the start of the address.
                                    self.ctx.ptr_type(AddressSpace::default()),
                                    ptr,
                                    "deref",
                                )
                                .unwrap()
                                .into_pointer_value();
                        }
                        _ => {
                            ptr = builder
                                .build_load(self.get_ty(ty), ptr, "deref")
                                .unwrap()
                                .into_pointer_value()
                        }
                    }

                    ty = inner_ty;
                }
                Projection::Field(_) => todo!(),
                Projection::Index(local) => {
                    let inner_ty = match self.ir.tys.get(ty) {
                        TyInfo::Array { ty, .. } => ty,
                        TyInfo::Slice(ty) => ty,
                        _ => {
                            panic!("can only index an array or slice");
                        }
                    };

                    let local_ty = locals[*local].ty;
                    let TyInfo::U8 = self.ir.tys.get(local_ty) else {
                        panic!("can only index using u8");
                    };
                    let index = builder
                        .build_load(self.get_ty(local_ty), local_ptrs[local], "load index")
                        .unwrap()
                        .into_int_value();

                    ptr = unsafe {
                        builder.build_in_bounds_gep(self.get_ty(inner_ty), ptr, &[index], "index")
                    }
                    .unwrap();
                    ty = inner_ty;
                }
            }
        }

        (ptr, ty)
    }

    fn store_rvalue(
        &self,
        builder: &Builder<'ink>,
        rvalue: &RValue,
        place_ptr: PointerValue<'ink>,
        place_ty: Ty,
        locals: &Locals,
        local_ptrs: &HashMap<Local, PointerValue<'ink>>,
    ) {
        match rvalue {
            RValue::Use(operand) => {
                let (value, ty) = self.get_operand(builder, operand, locals, local_ptrs);
                assert_eq!(place_ty, ty);
                builder.build_store(place_ptr, value).unwrap();
            }
            RValue::Ref(place) => {
                let (ptr, inner_ty) = self.resolve_place(builder, place, locals, local_ptrs);
                let ty = self.ir.tys.find_or_insert(TyInfo::Ref(inner_ty));
                assert_eq!(place_ty, ty);
                builder.build_store(place_ptr, ptr).unwrap();
            }
            RValue::BinaryOp { op, lhs, rhs } => {
                let (BasicValueEnum::IntValue(lhs), lhs_ty) =
                    self.get_operand(builder, lhs, locals, local_ptrs)
                else {
                    panic!("expected integer lhs");
                };

                let (BasicValueEnum::IntValue(rhs), rhs_ty) =
                    self.get_operand(builder, rhs, locals, local_ptrs)
                else {
                    panic!("expected integer rhs");
                };

                // Operands must be of the same type.
                assert_eq!(lhs_ty, rhs_ty);

                let ty = lhs_ty;
                assert_eq!(place_ty, ty);

                let value = match op {
                    BinOp::Add => builder.build_int_add(lhs, rhs, "add").unwrap(),
                    BinOp::Sub => builder.build_int_sub(lhs, rhs, "sub").unwrap(),
                    BinOp::Mul => builder.build_int_mul(lhs, rhs, "mul").unwrap(),
                    BinOp::Div => match self.ir.tys.get(ty) {
                        TyInfo::U8 => builder
                            .build_int_unsigned_div(lhs, rhs, "unsigned div")
                            .unwrap(),
                        TyInfo::I8 => builder
                            .build_int_signed_div(lhs, rhs, "signed div")
                            .unwrap(),
                        _ => panic!("invalid div type"),
                    },
                };

                builder.build_store(place_ptr, value).unwrap();
            }
            RValue::UnaryOp { op, rhs } => {
                let (rhs, rhs_ty) = self.get_operand(builder, rhs, locals, local_ptrs);

                match op {
                    UnOp::Not => {
                        let (TyInfo::U8 | TyInfo::I8) = self.ir.tys.get(rhs_ty) else {
                            panic!("cannot unary not a non-primitive");
                        };

                        assert_eq!(place_ty, rhs_ty);

                        let result = builder.build_not(rhs.into_int_value(), "not").unwrap();
                        builder.build_store(place_ptr, result).unwrap();
                    }
                    UnOp::Neg => {
                        let TyInfo::I8 = self.ir.tys.get(rhs_ty) else {
                            panic!("cannot unary neg a non-signed integer");
                        };

                        assert_eq!(place_ty, rhs_ty);

                        let result = builder.build_not(rhs.into_int_value(), "not").unwrap();
                        builder.build_store(place_ptr, result).unwrap();
                    }
                    UnOp::PtrMetadata => {
                        let TyInfo::Ref(inner_ty) = self.ir.tys.get(rhs_ty) else {
                            panic!("can only get ptr metadata of reference");
                        };
                        let TyInfo::Slice(_) = self.ir.tys.get(inner_ty) else {
                            panic!("can only get ptr metadata of slice reference");
                        };

                        // HACK: Hard-coding pointer metadata as u8
                        assert_eq!(place_ty, self.ir.tys.find_or_insert(TyInfo::U8));

                        // HACK: Assuming fat pointer is two pointers wide.
                        let data = builder
                            .build_extract_value(rhs.into_array_value(), 1, "ptr metadata")
                            .unwrap();
                        builder.build_store(place_ptr, data).unwrap();
                    }
                }
            }
            RValue::Aggregate { values } => {
                // If there's no values, there's nothing that needs to be stored.
                if values.is_empty() {
                    return;
                }

                let values = values
                    .iter()
                    .map(|value| self.get_operand(builder, value, locals, local_ptrs))
                    .collect::<Vec<_>>();

                let pointee_ty = values[0].1;
                let index_ty = self
                    .get_ty(self.ir.tys.find_or_insert(TyInfo::U8))
                    .into_int_type();

                for (i, (value, ty)) in values.into_iter().enumerate() {
                    assert_eq!(pointee_ty, ty);

                    let ptr = unsafe {
                        builder.build_in_bounds_gep(
                            self.get_ty(pointee_ty),
                            place_ptr,
                            &[index_ty.const_int(i as u64, false)],
                            format!("gep agg {i}").as_str(),
                        )
                    }
                    .unwrap();
                    builder.build_store(ptr, value).unwrap();
                }
            }
            RValue::Cast { kind, op, ty } => {
                let (op, op_ty) = self.get_operand(builder, op, locals, local_ptrs);
                match kind {
                    CastKind::PointerCoercion(PointerCoercion::Unsize) => {
                        let TyInfo::Ref(place_inner_ty) = self.ir.tys.get(place_ty) else {
                            panic!("can only store pointer coercion in reference");
                        };
                        let TyInfo::Ref(to_ty) = self.ir.tys.get(*ty) else {
                            panic!("can only unsize coerce to a reference");
                        };
                        let TyInfo::Ref(from_ty) = self.ir.tys.get(op_ty) else {
                            panic!("can only unsize coerce from a reference");
                        };

                        assert_eq!(place_inner_ty, to_ty);

                        match (self.ir.tys.get(from_ty), self.ir.tys.get(to_ty)) {
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
                                    // two pointers.
                                    let pointee_ty = self.ctx.ptr_type(AddressSpace::default());
                                    let ordered_indexes = &[self.ctx.i8_type().const_int(1, false)];
                                    unsafe {
                                        builder.build_in_bounds_gep(
                                            pointee_ty,
                                            place_ptr,
                                            ordered_indexes,
                                            "fat pointer data index",
                                        )
                                    }
                                    .unwrap()
                                };

                                // Write the pointer.
                                builder.build_store(place_ptr, ptr).unwrap();

                                // Write the data after the pointer.
                                builder
                                    .build_store(
                                        data_ptr,
                                        // HACK: Directly creating the length.
                                        self.ctx.i64_type().const_int(length as u64, false),
                                    )
                                    .unwrap();
                            }
                            (from_ty, to_ty) => {
                                panic!("cannot coerce pointer from {from_ty:?} to {to_ty:?}")
                            }
                        }
                    }
                }
            }
        }
    }

    fn get_operand(
        &self,
        builder: &Builder<'ink>,
        operand: &Operand,
        locals: &Locals,
        local_ptrs: &HashMap<Local, PointerValue<'ink>>,
    ) -> (BasicValueEnum<'ink>, Ty) {
        match operand {
            Operand::Place(place) => {
                let (ptr, ty) = self.resolve_place(builder, place, locals, local_ptrs);
                (
                    builder
                        .build_load(self.get_ty(ty), ptr, "load place operand")
                        .unwrap(),
                    ty,
                )
            }
            Operand::Constant(constant) => match constant {
                Constant::U8(value) => {
                    let ty = self.ir.tys.find_or_insert(TyInfo::U8);
                    (
                        self.get_ty(ty)
                            .into_int_type()
                            .const_int(*value as u64, false)
                            .into(),
                        ty,
                    )
                }
                Constant::I8(value) => {
                    let ty = self.ir.tys.find_or_insert(TyInfo::I8);
                    (
                        self.get_ty(ty)
                            .into_int_type()
                            .const_int(*value as u64, true)
                            .into(),
                        ty,
                    )
                }
            },
        }
    }

    // Call an intrinsic function.
    fn build_intrinsic(
        &self,
        builder: &Builder<'ink>,
        name: &str,
        tys: &[BasicTypeEnum],
        values: &[BasicMetadataValueEnum],
    ) {
        let intrinsic = Intrinsic::find(name).unwrap();
        let intrinsic_fn = intrinsic.get_declaration(&self.module, tys).unwrap();
        builder.build_call(intrinsic_fn, values, name).unwrap();
    }
}
