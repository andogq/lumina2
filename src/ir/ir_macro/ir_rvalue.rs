#[macro_export(local_inner_macros)]
macro_rules! ir_rvalue {
    // Handle unary operation (single argument).
    (cb_op($op:ident) [$($rhs:tt)*]) => {
        $crate::ir::repr::RValue::UnaryOp {
            op: $crate::ir::repr::UnOp::$op,
            rhs: $crate::ir_operand!($($rhs)*),
        }
    };

    // Handle binary operation (two arguments).
    (cb_op($op:ident) [$($lhs:tt)*] [$($rhs:tt)*]) => {
        $crate::ir::repr::RValue::BinaryOp {
            op: $crate::ir::repr::BinOp::$op,
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
    // the comma. The `cb_op` branches will be called with the split parameters, which will
    // determine whether it's a binary or unary operation.
    ($op:ident($($operands:tt)*)) => {
        $crate::split_token!([,] [ir_rvalue(cb_op($op))] $($operands)*)
    };

    // Reference of a place.
    (& $($place:tt)*) => {
        $crate::ir::repr::RValue::Ref(ir_place!($($place)*))
    };

    // Array aggregate.
    ([$($operands:tt)*]) => {
        $crate::split_token!([,] [ir_rvalue(@cb_aggregate)] $($operands)*)
    };

    (@cb_aggregate $([$($operand:tt)*])*) => {
        $crate::ir::repr::RValue::Aggregate {
            values: ::std::vec![$(ir_operand!($($operand)*),)*],
        }
    };

    // Assume something with an operand (operand or cast).
    (@cb_operand_or_cast [$($operand:tt)*]) => {
        $crate::ir::repr::RValue::Use(ir_operand!($($operand)*))
    };
    (@cb_operand_or_cast [$($operand:tt)*] [$($cast_info:tt)*]) => {{
        let (kind, ty) = $crate::ir_rvalue!(@extract_cast_info ty=[] $($cast_info)*);

        $crate::ir::repr::RValue::Cast {
            op: $crate::ir_operand!($($operand)*),
            kind,
            ty
        }
    }};
    // If the last group of tokens is wrapped in parens, it's the cast kind.
    (@extract_cast_info ty=[$($ty:tt)*] ($cast_kind:ident $(($($args:tt)*))?)) => {
        (
            $crate::ir::repr::CastKind::$cast_kind $(({
                // NOTE: Import all enums used as args.
                use $crate::ir::repr::PointerCoercion::*;

                $($args)*
            }))?,
            $crate::ir_ty!($($ty)*),
        )
    };
    // Otherwise it's part of the type.
    (@extract_cast_info ty=[$($ty:tt)*] $tok:tt $($rest:tt)*) => {
        $crate::ir_rvalue!(@extract_cast_info ty=[$($ty)* $tok] $($rest)*)
    };
    ($($toks:tt)*) => {
        $crate::split_token!([as] without_trailing [ir_rvalue(@cb_operand_or_cast)] $($toks)*)
    };
}

#[cfg(test)]
mod test {
    #![allow(clippy::just_underscores_and_digits)]

    use crate::{
        ir::repr::{
            BinOp, CastKind, Constant, Local, Operand, Place, PointerCoercion, Projection, RValue,
            UnOp,
        },
        tir::Ty,
    };

    #[test]
    fn unary_operation() {
        assert_eq!(
            ir_rvalue!(Neg(const 1_u8)),
            RValue::UnaryOp {
                op: UnOp::Neg,
                rhs: Operand::Constant(Constant::U8(1))
            },
        );
    }

    #[test]
    fn binary_operation() {
        assert_eq!(
            ir_rvalue!(Add(const 1_u8, const 2_u8)),
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
            ir_rvalue!(&_0),
            RValue::Ref(Place {
                local: _0,
                projection: vec![]
            }),
        );
    }

    #[test]
    fn use_constant() {
        assert_eq!(
            ir_rvalue!(const 1_u8),
            RValue::Use(Operand::Constant(Constant::U8(1))),
        );
    }

    #[test]
    fn use_place() {
        let _0 = Local::zero();
        let _1 = Local::of(1);

        assert_eq!(
            ir_rvalue!(_0[_1]),
            RValue::Use(Operand::Place(Place {
                local: _0,
                projection: vec![Projection::Index(_1)]
            })),
        );
    }

    #[test]
    fn cast() {
        let _0 = Local::zero();

        assert_eq!(
            ir_rvalue!(_0 as &[u8] (PointerCoercion(Unsize))),
            RValue::Cast {
                kind: CastKind::PointerCoercion(PointerCoercion::Unsize),
                op: Operand::Place(Place {
                    local: _0,
                    projection: vec![]
                }),
                ty: Ty::Ref(Box::new(Ty::Slice(Box::new(Ty::U8))))
            }
        );
    }
}
