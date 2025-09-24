#[macro_export(local_inner_macros)]
macro_rules! ir_rvalue {
    // Handle unary operation (single argument).
    (cb_op($op:ident) [$($rhs:tt)*]) => {
        $crate::ir::RValue::UnaryOp {
            op: $crate::ir::UnOp::$op,
            rhs: $crate::ir_operand!($($rhs)*),
        }
    };

    // Handle binary operation (two arguments).
    (cb_op($op:ident) [$($lhs:tt)*] [$($rhs:tt)*]) => {
        $crate::ir::RValue::BinaryOp {
            op: $crate::ir::BinOp::$op,
            lhs: $crate::ir_operand!($($lhs)*),
            rhs: $crate::ir_operand!($($rhs)*),
        }
    };

    // Operation with unknown amount of arguments.
    (cb_op($op:ident) $([$($args:tt)*])*) => {
        ::std::compile_error!(::std::concat!("Unknown arguments: ", ::std::stringify!($($($args)*)*)));
    };

    // Parse an operation in the form of `Op(args, ...)`.
    //
    // This branch will extract the operation name (`Op`), and split the args within the parens at
    // the comma. The `cb_op` branches will be caled with the split parameters, which will
    // determine whether it's a binary or unary operation.
    ([$tys:expr] $op:ident($($operands:tt)*)) => {
        $crate::split_token!([,] [ir_rvalue(cb_op($op))] $($operands)*)
    };

    // Reference of a place.
    ([$tys:expr] & $($place:tt)*) => {
        $crate::ir::RValue::Ref(ir_place!($($place)*))
    };

    // Array aggregate.
    ([$tys:expr] [$($operands:tt)*]) => {
        $crate::split_token!([,] [ir_rvalue(@cb_aggregate)] $($operands)*)
    };

    (@cb_aggregate $([$($operand:tt)*])*) => {
        $crate::ir::RValue::Aggregate {
            values: ::std::vec![$(ir_operand!($($operand)*),)*],
        }
    };

    // Assume something with an operand (operand or cast).
    (@cb_operand_or_cast[$tys:expr] [$($operand:tt)*]) => {
        $crate::ir::RValue::Use(ir_operand!($($operand)*))
    };
    (@cb_operand_or_cast[$tys:expr] [$($operand:tt)*] [$($cast_info:tt)*]) => {{
        let (kind, ty) = $crate::ir_rvalue!(@extract_cast_info[$tys] ty=[] $($cast_info)*);

        $crate::ir::RValue::Cast {
            op: $crate::ir_operand!($($operand)*),
            kind,
            ty
        }
    }};
    // If the last group of tokens is wrapped in parens, it's the cast kind.
    (@extract_cast_info[$tys:expr] ty=[$($ty:tt)*] ($cast_kind:ident $(($($args:tt)*))?)) => {
        (
            $crate::ir::CastKind::$cast_kind $(({
                // NOTE: Import all enums used as args.
                use $crate::ir::PointerCoercion::*;

                $($args)*
            }))?,
            $crate::ir_ty!([$tys] $($ty)*),
        )
    };
    // Otherwise it's part of the type.
    (@extract_cast_info[$tys:expr] ty=[$($ty:tt)*] $tok:tt $($rest:tt)*) => {
        $crate::ir_rvalue!(@extract_cast_info[$tys] ty=[$($ty)* $tok] $($rest)*)
    };
    ([$tys:expr] $($toks:tt)*) => {
        $crate::split_token!([as] without_trailing [ir_rvalue(@cb_operand_or_cast[$tys])] $($toks)*)
    };
}

#[cfg(test)]
mod test {
    #![allow(clippy::just_underscores_and_digits)]

    use crate::ir::{
        BinOp, CastKind, Constant, Local, Operand, Place, PointerCoercion, Projection, RValue,
        TyInfo, Tys, UnOp,
    };

    #[test]
    fn unary_operation() {
        assert_eq!(
            ir_rvalue!([_] Neg(const 1_u8)),
            RValue::UnaryOp {
                op: UnOp::Neg,
                rhs: Operand::Constant(Constant::U8(1))
            },
        );
    }

    #[test]
    fn binary_operation() {
        assert_eq!(
            ir_rvalue!([_] Add(const 1_u8, const 2_u8)),
            RValue::BinaryOp {
                op: BinOp::Add,
                lhs: Operand::Constant(Constant::U8(1)),
                rhs: Operand::Constant(Constant::U8(2)),
            },
        );
    }

    #[test]
    fn reference() {
        let _0 = Local::zero();

        assert_eq!(
            ir_rvalue!([_] & _0),
            RValue::Ref(Place {
                local: _0,
                projection: vec![]
            }),
        );
    }

    #[test]
    fn use_constant() {
        assert_eq!(
            ir_rvalue!([_] const 1_u8),
            RValue::Use(Operand::Constant(Constant::U8(1))),
        );
    }

    #[test]
    fn use_place() {
        let _0 = Local::zero();
        let _1 = Local::of(1);

        assert_eq!(
            ir_rvalue!([_] _0[_1]),
            RValue::Use(Operand::Place(Place {
                local: _0,
                projection: vec![Projection::Index(_1)]
            })),
        );
    }

    #[test]
    fn cast() {
        let _0 = Local::zero();

        let mut tys = Tys::new();
        let u8_ty = tys.find_or_insert(TyInfo::U8);
        let u8_slice_ty = tys.find_or_insert(TyInfo::Slice(u8_ty));
        let ty = tys.find_or_insert(TyInfo::Ref(u8_slice_ty));

        assert_eq!(
            ir_rvalue!([&mut tys] _0 as &[u8] (PointerCoercion(Unsize))),
            RValue::Cast {
                kind: CastKind::PointerCoercion(PointerCoercion::Unsize),
                op: Operand::Place(Place {
                    local: _0,
                    projection: vec![]
                }),
                ty
            }
        );
    }
}
