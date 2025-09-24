mod interpreter;
pub mod llvm;

use std::collections::HashMap;

use crate::ir::{
    self, BinOp, CastKind, Local, Operand, Place, PointerCoercion, Projection, RValue, Statement,
    Terminator, Ty, TyInfo, Tys, UnOp,
    any_value::{Any, AnyValue, Loadable, Storable},
    ctx::IrCtx,
    integer::{
        Array, Constant, ConstantValue, FatPointer, Integer, IntegerValue, Pointer, ValueBackend,
    },
};

pub fn lower<'ctx, B: Backend<'ctx>>(ir: &IrCtx, backend: &mut B) {
    // Forward declare all the functions.
    let mut functions = ir
        .functions
        .iter_keys()
        .map(|(id, body)| {
            (
                id,
                backend.add_function(
                    // TODO: Function name
                    "function_name",
                    // `_0` holds the return value.
                    backend.get_ty(&ir.tys, body.local_decls[Local::zero()].ty),
                ),
            )
        })
        .collect::<HashMap<_, _>>();

    // Lower each function.
    for (&f_id, f) in &mut functions {
        // Declare all locals.
        let locals = ir.functions[f_id]
            .local_decls
            .iter_keys()
            .map(|(local, decl)| {
                (
                    local,
                    (
                        f.declare_local(
                            backend.get_ty(&ir.tys, decl.ty),
                            local.to_string().as_str(),
                        ),
                        decl.ty,
                    ),
                )
            })
            .collect::<HashMap<_, _>>();

        let bbs = &ir.functions[f_id].basic_blocks;

        // Forward declare all the basic blocks.
        let basic_blocks: HashMap<ir::BasicBlock, <B::Value as ValueBackend>::BasicBlock> = bbs
            .iter_keys()
            .map(|(bb_id, _bb)| (bb_id, f.add_basic_block(bb_id.to_string().as_str())))
            .collect();

        // Lower each basic block
        for (bb_id, bb) in bbs.iter_keys() {
            let block = basic_blocks.get(&bb_id).unwrap();

            for statement in &bb.statements {
                match statement {
                    Statement::Assign { place, rvalue } => {
                        let (ptr, place_ty) =
                            resolve_place(place, block, &locals, &ir.tys, backend);

                        match rvalue {
                            RValue::Use(operand) => {
                                let (value, value_ty) =
                                    resolve_operand(operand, block, &locals, &ir.tys, backend);

                                assert_eq!(place_ty, value_ty);
                                value.store(block, ptr);
                            }
                            RValue::Ref(place) => {
                                let (value, ty) =
                                    resolve_place(place, block, &locals, &ir.tys, backend);

                                let value_ty = ir.tys.find_or_insert(TyInfo::Ref(ty));

                                assert_eq!(place_ty, value_ty);
                                value.store(block, ptr);
                            }
                            RValue::BinaryOp { op, lhs, rhs } => {
                                let (lhs, lhs_ty) =
                                    resolve_operand(lhs, block, &locals, &ir.tys, backend);
                                let (rhs, rhs_ty) =
                                    resolve_operand(rhs, block, &locals, &ir.tys, backend);

                                let value = match op {
                                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                                        assert_eq!(
                                            lhs_ty, rhs_ty,
                                            "lhs and rhs operands must match for {op:?}"
                                        );

                                        // TODO: Find reusable way to convert between `Value` enum, and
                                        // the underlying types.
                                        match (lhs, rhs) {
                                            (
                                                AnyValue::Integer(IntegerValue::I8(lhs)),
                                                AnyValue::Integer(IntegerValue::I8(rhs)),
                                            ) => {
                                                <B::Value as ValueBackend>::I8::add(block, lhs, rhs)
                                                    .into_integer_value()
                                            }
                                            (
                                                AnyValue::Integer(IntegerValue::U8(lhs)),
                                                AnyValue::Integer(IntegerValue::U8(rhs)),
                                            ) => {
                                                <B::Value as ValueBackend>::U8::add(block, lhs, rhs)
                                                    .into_integer_value()
                                            }
                                            _ => panic!("lhs and rhs are mis-matched"),
                                        }
                                    }
                                    _ => unimplemented!(),
                                };

                                // Can re-use lhs type since it's the same as the result
                                assert_eq!(place_ty, lhs_ty);
                                value.store(block, ptr);
                            }
                            RValue::UnaryOp { op, rhs } => {
                                let (rhs, rhs_ty) =
                                    resolve_operand(rhs, block, &locals, &ir.tys, backend);

                                match op {
                                    UnOp::Not => todo!(),
                                    UnOp::Neg => todo!(),
                                    UnOp::PtrMetadata => {
                                        let AnyValue::FatPointer(fat_ptr) = rhs else {
                                            panic!(
                                                "cannot get pointer metadata of non-fat pointer"
                                            );
                                        };

                                        // TODO: Replace once something other than U8 is used for
                                        // ptr info
                                        assert_eq!(place_ty, ir.tys.find_or_insert(TyInfo::U8));

                                        let metadata = fat_ptr.get_metadata();

                                        metadata.store(block, ptr);
                                    }
                                }
                            }
                            RValue::Aggregate { values } => {
                                let TyInfo::Array { ty, length } = ir.tys.get(place_ty) else {
                                    panic!("cannot assign aggregate to non-array");
                                };

                                let ty_info = backend.get_ty(&ir.tys, ty);

                                assert_eq!(values.len(), length);

                                for (i, value) in values.iter().enumerate() {
                                    let i = <B::Value as ValueBackend>::U8::create(block, i as u8);
                                    let ptr = ptr.clone().element_ptr(block, i, ty_info.clone());
                                    let (value, value_ty) =
                                        resolve_operand(value, block, &locals, &ir.tys, backend);
                                    assert_eq!(ty, value_ty);
                                    value.store(block, ptr);
                                }
                            }
                            RValue::Cast {
                                kind,
                                op,
                                ty: target_ty,
                            } => {
                                let (op, op_ty) =
                                    resolve_operand(op, block, &locals, &ir.tys, backend);

                                match kind {
                                    CastKind::PointerCoercion(PointerCoercion::Unsize) => {
                                        // Ensure that the resulting type can be correctly stored.
                                        assert_eq!(place_ty, *target_ty);

                                        // Ensure the target type is correct
                                        let TyInfo::Ref(inner_ty) = ir.tys.get(*target_ty) else {
                                            panic!("cannot unsize coerce into non-ref");
                                        };
                                        let TyInfo::Slice(item_ty) = ir.tys.get(inner_ty) else {
                                            panic!("cannot unsize coerce non-slice");
                                        };

                                        // Ensure the operand is of the correct type.
                                        let TyInfo::Ref(inner_ty) = ir.tys.get(op_ty) else {
                                            panic!("expected reference to pointer coerce");
                                        };
                                        let TyInfo::Array {
                                            ty: array_item_ty,
                                            length,
                                        } = ir.tys.get(inner_ty)
                                        else {
                                            panic!("expected reference to array");
                                        };

                                        // Ensure the end type is compatible with this type.
                                        assert_eq!(item_ty, array_item_ty);

                                        let length = <B::Value as ValueBackend>::U8::create(
                                            block,
                                            length as u8,
                                        );

                                        let unsize_ptr =
                                            <B::Value as ValueBackend>::FatPointer::from_ptr(
                                                op.into_pointer_value(),
                                                length,
                                            );

                                        unsize_ptr.store(block, ptr);
                                    }
                                }
                            }
                        };
                    }
                    Statement::StorageDead(local) => {
                        let (ptr, _) = &locals[local];
                        block.storage_dead(ptr.clone());
                    }
                    Statement::StorageLive(local) => {
                        let (ptr, _) = &locals[local];
                        block.storage_live(ptr.clone());
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
                Terminator::Goto(basic_block) => block.term_goto(&basic_blocks[basic_block]),
                Terminator::Return => {
                    let (value_ptr, value_ty) = &locals[&Local::zero()];

                    // TODO: Add type overloads for `block.l` to load specific values.
                    let value = match ir.tys.get(*value_ty) {
                        TyInfo::U8 => {
                            <B::Value as ValueBackend>::U8::load(block, value_ptr.clone())
                                .into_integer_value()
                        }
                        TyInfo::I8 => {
                            <B::Value as ValueBackend>::I8::load(block, value_ptr.clone())
                                .into_integer_value()
                        }
                        _ => unimplemented!(),
                    };

                    block.term_return(value)
                }
                Terminator::SwitchInt {
                    discriminator,
                    targets,
                    otherwise,
                } => {
                    let (discriminator, _) =
                        resolve_operand(discriminator, block, &locals, &ir.tys, backend);
                    let discriminator = discriminator.into_integer_value();

                    // TODO: Temporary until `Value` is completely replaced
                    let targets = targets
                        .iter()
                        .map(|(value, bb)| {
                            let value = match value {
                                crate::Constant::U8(u8) => ConstantValue::<B::Value>::U8(*u8),
                                crate::Constant::I8(i8) => ConstantValue::I8(*i8),
                            };

                            (value, bb)
                        })
                        .collect::<Vec<_>>();

                    let otherwise = &basic_blocks[otherwise];

                    match discriminator {
                        IntegerValue::I8(discriminator) => {
                            let targets = targets
                                .into_iter()
                                .map(|(value, bb)| {
                                    let ConstantValue::I8(value) = value else {
                                        panic!("invalid constant");
                                    };

                                    (value, &basic_blocks[bb])
                                })
                                .collect();

                            block.term_switch(discriminator, otherwise, targets);
                        }
                        IntegerValue::U8(discriminator) => {
                            let targets = targets
                                .into_iter()
                                .map(|(value, bb)| {
                                    let ConstantValue::U8(value) = value else {
                                        panic!("invalid constant");
                                    };

                                    (value, &basic_blocks[bb])
                                })
                                .collect();

                            block.term_switch(discriminator, otherwise, targets);
                        }
                    }
                }
            }
        }
    }
}

fn resolve_place<'ctx, B: BasicBlock>(
    place: &Place,
    block: &B,
    locals: &HashMap<Local, (<B::Value as ValueBackend>::Pointer, Ty)>,
    tys: &Tys,
    backend: &impl Backend<'ctx, Value = B::Value>,
) -> (<B::Value as ValueBackend>::Pointer, Ty) {
    let (mut ptr, mut ty) = locals[&place.local].clone();

    for proj in &place.projection {
        (ptr, ty) = match proj {
            Projection::Deref => {
                let ty_info = tys.get(ty);
                let TyInfo::Ref(inner_ty) = ty_info else {
                    panic!("expected ref to dereference, but found {ty_info:?}");
                };

                (ptr.deref(block), inner_ty)
            }
            Projection::Field(_) => todo!(),
            Projection::Index(local) => {
                let (TyInfo::Array { ty: item_ty, .. } | TyInfo::Slice(item_ty)) = tys.get(ty)
                else {
                    panic!("can only index on an array or slice");
                };

                let (index_ptr, index_ty) = locals[local].clone();

                // HACK: Can only index U8
                assert!(matches!(tys.get(index_ty), TyInfo::U8));

                let index = <B::Value as ValueBackend>::U8::load(block, index_ptr);
                let item_ptr = ptr.element_ptr(block, index, backend.get_ty(&tys, item_ty));

                (item_ptr, item_ty)
            }
        };
    }

    (ptr, ty)
}

fn resolve_operand<'ctx, B: BasicBlock>(
    operand: &Operand,
    block: &B,
    locals: &HashMap<Local, (<B::Value as ValueBackend>::Pointer, Ty)>,
    tys: &Tys,
    backend: &impl Backend<'ctx, Value = B::Value>,
) -> (AnyValue<B::Value>, Ty) {
    match operand {
        Operand::Place(place) => {
            let (ptr, ty) = resolve_place(place, block, locals, tys, backend);

            (
                match tys.get(ty) {
                    TyInfo::U8 => <B::Value as ValueBackend>::U8::load(block, ptr)
                        .into_integer_value()
                        .into_any_value(),
                    TyInfo::I8 => <B::Value as ValueBackend>::I8::load(block, ptr)
                        .into_integer_value()
                        .into_any_value(),
                    TyInfo::Ref(ty) => match tys.get(ty) {
                        TyInfo::Slice(ty) => {
                            <B::Value as ValueBackend>::FatPointer::load(block, ptr)
                                .into_any_value()
                        }
                        _ => <B::Value as ValueBackend>::Pointer::load(block, ptr).into_any_value(),
                    },
                    TyInfo::Slice(ty) => panic!("not possible, slice is unsized"),
                    TyInfo::Array { ty, length } => <B::Value as ValueBackend>::Array::load_count(
                        block,
                        ptr,
                        backend.get_ty(tys, ty),
                        length,
                    )
                    .into_any_value(),
                },
                ty,
            )
        }
        Operand::Constant(value) => {
            // TODO: Use something other than `Value` which doesn't have non-constant variants.
            match value {
                crate::Constant::U8(value) => (
                    <B::Value as ValueBackend>::U8::create(block, *value)
                        .into_integer_value()
                        .into_any_value(),
                    tys.find_or_insert(TyInfo::U8),
                ),
                crate::Constant::I8(value) => (
                    <B::Value as ValueBackend>::I8::create(block, *value)
                        .into_integer_value()
                        .into_any_value(),
                    tys.find_or_insert(TyInfo::I8),
                ),
                _ => panic!("invalid constant value"),
            }
        }
    }
}

pub trait Backend<'ctx>: Sized {
    type Value: ValueBackend;
    type Function: Function<'ctx, Value = Self::Value>;

    fn add_function(&self, name: &str, ret_ty: <Self::Value as ValueBackend>::Ty)
    -> Self::Function;
    fn get_ty(&self, tys: &Tys, ty: Ty) -> <Self::Value as ValueBackend>::Ty;
}

pub trait Function<'ctx> {
    type Value: ValueBackend;

    fn declare_local(
        &mut self,
        ty: <Self::Value as ValueBackend>::Ty,
        name: &str,
    ) -> <Self::Value as ValueBackend>::Pointer;

    fn add_basic_block(&mut self, name: &str) -> <Self::Value as ValueBackend>::BasicBlock;
}

pub trait BasicBlock {
    type Value: ValueBackend<BasicBlock = Self>;

    fn term_return(&self, value: IntegerValue<Self::Value>);
    fn term_goto(&self, bb: &<Self::Value as ValueBackend>::BasicBlock);
    fn term_switch<I: Integer<Self::Value>>(
        &self,
        discriminator: I,
        default: &<Self::Value as ValueBackend>::BasicBlock,
        targets: Vec<(I::Value, &<Self::Value as ValueBackend>::BasicBlock)>,
    );

    fn storage_live(&self, ptr: <Self::Value as ValueBackend>::Pointer);
    fn storage_dead(&self, ptr: <Self::Value as ValueBackend>::Pointer);
}
