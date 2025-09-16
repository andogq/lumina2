mod interpreter;
pub mod llvm;

use std::collections::HashMap;

use crate::ir::{
    self, BinOp, Local, Operand, Place, Projection, RValue, Statement, Terminator, Ty, TyInfo, Tys,
    Value,
    ctx::IrCtx,
    integer::{Constant, Integer, IntegerValue, ValueBackend},
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
                    body.local_decls[Local::zero()].ty,
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
                        f.declare_local(decl.ty, local.to_string().as_str()),
                        decl.ty,
                    ),
                )
            })
            .collect::<HashMap<_, _>>();

        let bbs = &ir.functions[f_id].basic_blocks;

        // Forward declare all the basic blocks.
        let mut basic_blocks: HashMap<ir::BasicBlock, <B::Value as ValueBackend>::BasicBlock> = bbs
            .iter_keys()
            .map(|(bb_id, _bb)| (bb_id, f.add_basic_block(bb_id.to_string().as_str())))
            .collect();

        // Lower each basic block
        for (bb_id, bb) in bbs.iter_keys() {
            let block = basic_blocks.get_mut(&bb_id).unwrap();

            for statement in &bb.statements {
                match statement {
                    Statement::Assign { place, rvalue } => {
                        let (ptr, place_ty) = resolve_place(place, block, &locals, &ir.tys);

                        let (value, value_ty) = match rvalue {
                            RValue::Use(operand) => {
                                resolve_operand(operand, block, &locals, &ir.tys)
                            }
                            RValue::Ref(place) => todo!(),
                            RValue::BinaryOp { op, lhs, rhs } => match op {
                                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                                    let (lhs, lhs_ty) =
                                        resolve_operand(lhs, block, &locals, &ir.tys);
                                    let (rhs, rhs_ty) =
                                        resolve_operand(rhs, block, &locals, &ir.tys);

                                    assert_eq!(
                                        lhs_ty, rhs_ty,
                                        "lhs and rhs operands must match for {op:?}"
                                    );

                                    // TODO: Find reusable way to convert between `Value` enum, and
                                    // the underlying types.
                                    let result = match (lhs, rhs) {
                                        (IntegerValue::I8(lhs), IntegerValue::I8(rhs)) => {
                                            <B::Value as ValueBackend>::I8::add(block, lhs, rhs)
                                                .into_integer_value()
                                        }
                                        (IntegerValue::U8(lhs), IntegerValue::U8(rhs)) => {
                                            <B::Value as ValueBackend>::U8::add(block, lhs, rhs)
                                                .into_integer_value()
                                        }
                                        _ => panic!("lhs and rhs are mis-matched"),
                                    };

                                    // lhs ty can be reused, since the result will be the same.
                                    (result, lhs_ty)
                                }
                                _ => unimplemented!(),
                            },
                            RValue::UnaryOp { op, rhs } => todo!(),
                            RValue::Aggregate { values } => todo!(),
                            RValue::Cast { kind, op, ty } => todo!(),
                        };

                        assert_eq!(place_ty, value_ty);

                        value.store(block, ptr);
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
                Terminator::Goto(basic_block) => todo!(),
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
                } => todo!(),
            }
        }
    }
}

fn resolve_place<B: BasicBlock>(
    place: &Place,
    block: &mut B,
    locals: &HashMap<Local, (<B::Value as ValueBackend>::Pointer, Ty)>,
    tys: &Tys,
) -> (<B::Value as ValueBackend>::Pointer, Ty) {
    let (mut ptr, mut ty) = locals[&place.local].clone();

    for proj in &place.projection {
        (ptr, ty) = match proj {
            Projection::Deref => {
                let ty_info = tys.get(ty);
                let TyInfo::Ref(inner_ty) = ty_info else {
                    panic!("expected ref to dereference, but found {ty_info:?}");
                };

                (block.p_deref(ptr), inner_ty)
            }
            Projection::Field(_) => todo!(),
            Projection::Index(local) => todo!(),
        };
    }

    (ptr, ty)
}

fn resolve_operand<B: BasicBlock>(
    operand: &Operand,
    block: &mut B,
    locals: &HashMap<Local, (<B::Value as ValueBackend>::Pointer, Ty)>,
    tys: &Tys,
) -> (IntegerValue<B::Value>, Ty) {
    match operand {
        Operand::Place(place) => {
            let (ptr, ty) = resolve_place(place, block, locals, tys);

            (
                match tys.get(ty) {
                    TyInfo::U8 => {
                        <B::Value as ValueBackend>::U8::load(block, ptr).into_integer_value()
                    }
                    TyInfo::I8 => {
                        <B::Value as ValueBackend>::I8::load(block, ptr).into_integer_value()
                    }
                    TyInfo::Ref(ty) => todo!(),
                    TyInfo::Slice(ty) => todo!(),
                    TyInfo::Array { ty, length } => todo!(),
                },
                ty,
            )
        }
        Operand::Constant(value) => {
            // TODO: Use something other than `Value` which doesn't have non-constant variants.
            match value {
                Value::U8(value) => (
                    <B::Value as ValueBackend>::U8::create(block, *value).into_integer_value(),
                    tys.find_or_insert(TyInfo::U8),
                ),
                Value::I8(value) => (
                    <B::Value as ValueBackend>::I8::create(block, *value).into_integer_value(),
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

    fn add_function(&self, name: &str, ret_ty: Ty) -> Self::Function;
}

pub trait Function<'ctx> {
    type Value: ValueBackend;

    fn declare_local(&mut self, ty: Ty, name: &str) -> <Self::Value as ValueBackend>::Pointer;

    fn add_basic_block(&mut self, name: &str) -> <Self::Value as ValueBackend>::BasicBlock;
}

pub trait BasicBlock {
    type Value: ValueBackend<BasicBlock = Self>;

    fn term_return(&mut self, value: IntegerValue<Self::Value>);

    fn storage_live(&mut self, ptr: <Self::Value as ValueBackend>::Pointer);
    fn storage_dead(&mut self, ptr: <Self::Value as ValueBackend>::Pointer);

    fn p_deref(
        &mut self,
        ptr: <Self::Value as ValueBackend>::Pointer,
    ) -> <Self::Value as ValueBackend>::Pointer;
}
