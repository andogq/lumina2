mod interpreter;
pub mod llvm;

use std::collections::HashMap;

use crate::ir::{
    BinOp, Local, Operand, Place, Projection, RValue, Statement, Terminator, Ty, TyInfo, Tys,
    Value,
    ctx::IrCtx,
    integer::{I8, Integer, IntegerValue, U8, ValueBackend},
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
        let mut basic_blocks = bbs
            .iter_keys()
            .map(|(bb_id, _bb)| (bb_id, f.add_basic_block(bb_id.to_string().as_str())))
            .collect::<HashMap<_, _>>();

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
                                            block.integer_add(lhs, rhs).into_integer_value()
                                        }
                                        (IntegerValue::U8(lhs), IntegerValue::U8(rhs)) => {
                                            block.integer_add(lhs, rhs).into_integer_value()
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
                        TyInfo::U8 => block.l_u8(value_ptr.clone()).into_integer_value(),
                        TyInfo::I8 => block.l_i8(value_ptr.clone()).into_integer_value(),
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
    locals: &HashMap<Local, (B::Pointer, Ty)>,
    tys: &Tys,
) -> (B::Pointer, Ty) {
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
    locals: &HashMap<Local, (B::Pointer, Ty)>,
    tys: &Tys,
) -> (IntegerValue<B::Value>, Ty) {
    match operand {
        Operand::Place(place) => {
            let (ptr, ty) = resolve_place(place, block, locals, tys);

            (
                match tys.get(ty) {
                    TyInfo::U8 => block.l_u8(ptr).into_integer_value(),
                    TyInfo::I8 => block.l_i8(ptr).into_integer_value(),
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
                    block.c(*value).into_integer_value(),
                    tys.find_or_insert(TyInfo::U8),
                ),
                Value::I8(value) => (
                    block.c(*value).into_integer_value(),
                    tys.find_or_insert(TyInfo::I8),
                ),
                _ => panic!("invalid constant value"),
            }
        }
    }
}

pub trait Backend<'ctx>: Sized {
    type Function<'backend>: Function<'ctx>
    where
        Self: 'backend;

    fn add_function<'backend>(&'backend self, name: &str, ret_ty: Ty) -> Self::Function<'backend>;
}

pub trait Function<'ctx> {
    type Pointer: Clone;
    type BasicBlock: BasicBlock<Pointer = Self::Pointer>;

    fn declare_local(&mut self, ty: Ty, name: &str) -> Self::Pointer;

    fn add_basic_block(&mut self, name: &str) -> Self::BasicBlock;
}

pub trait BasicBlock {
    type Pointer: Clone;
    type Value: ValueBackend;

    fn integer_add<I: Integer<Self::Value>>(&mut self, lhs: I, rhs: I) -> I;

    fn term_return(&mut self, value: IntegerValue<Self::Value>);

    fn storage_live(&mut self, ptr: Self::Pointer);
    fn storage_dead(&mut self, ptr: Self::Pointer);

    fn p_deref(&mut self, ptr: Self::Pointer) -> Self::Pointer;

    fn c<C: Constant<Self>>(&mut self, value: C) -> C::Value {
        C::create(self, value)
    }
    fn c_u8(&mut self, value: u8) -> U8<Self::Value>;
    fn c_i8(&mut self, value: i8) -> I8<Self::Value>;

    fn l<T: BbPrim<Self>>(&mut self, ptr: Self::Pointer) -> T {
        T::load(self, ptr)
    }
    fn l_u8(&mut self, ptr: Self::Pointer) -> U8<Self::Value>;
    fn l_i8(&mut self, ptr: Self::Pointer) -> I8<Self::Value>;

    fn s<T: BbPrim<Self>>(&mut self, ptr: Self::Pointer, value: T) {
        T::store(self, ptr, value);
    }
    fn s_u8(&mut self, ptr: Self::Pointer, value: U8<Self::Value>);
    fn s_i8(&mut self, ptr: Self::Pointer, value: I8<Self::Value>);
}

pub trait BbPrim<B: BasicBlock + ?Sized> {
    fn load(bb: &mut B, ptr: B::Pointer) -> Self;
    fn store(bb: &mut B, ptr: B::Pointer, value: Self);
}

impl<B: BasicBlock> BbPrim<B> for U8<B::Value> {
    fn load(bb: &mut B, ptr: <B as BasicBlock>::Pointer) -> Self {
        bb.l_u8(ptr)
    }

    fn store(bb: &mut B, ptr: <B as BasicBlock>::Pointer, value: Self) {
        bb.s_u8(ptr, value);
    }
}

impl<B: BasicBlock> BbPrim<B> for I8<B::Value> {
    fn load(bb: &mut B, ptr: <B as BasicBlock>::Pointer) -> Self {
        bb.l_i8(ptr)
    }

    fn store(bb: &mut B, ptr: <B as BasicBlock>::Pointer, value: Self) {
        bb.s_i8(ptr, value);
    }
}

pub trait Constant<B: BasicBlock + ?Sized> {
    type Value;

    fn create(bb: &mut B, value: Self) -> Self::Value;
}

impl<B: BasicBlock> Constant<B> for u8 {
    type Value = U8<B::Value>;

    fn create(bb: &mut B, value: Self) -> Self::Value {
        bb.c_u8(value)
    }
}

impl<B: BasicBlock> Constant<B> for i8 {
    type Value = I8<B::Value>;

    fn create(bb: &mut B, value: Self) -> Self::Value {
        bb.c_i8(value)
    }
}
