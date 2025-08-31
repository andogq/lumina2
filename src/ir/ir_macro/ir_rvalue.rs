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
    ($op:ident($($operands:tt)*)) => {
        $crate::split_token!([,] [ir_rvalue(cb_op($op))] $($operands)*)
    };

    // Reference of a place.
    (& $($place:tt)*) => {
        $crate::ir::RValue::Ref(ir_place!($($place)*))
    };

    // Array aggregate.
    ([$($operands:tt)*]) => {
        $crate::split_token!([,] [ir_rvalue(@cb_aggregate)] $($operands)*)
    };

    (@cb_aggregate $([$($operand:tt)*])*) => {
        $crate::ir::RValue::Aggregate {
            values: ::std::vec![$(ir_operand!($($operand)*),)*],
        }
    };

    // Assume an operand.
    ($($operand:tt)*) => {
        $crate::ir::RValue::Use(ir_operand!($($operand)*))
    };
}

#[cfg(test)]
mod test {
    #![allow(clippy::just_underscores_and_digits)]

    use crate::ir::{BinOp, Local, Operand, Place, Projection, RValue, UnOp, Value};

    #[test]
    fn unary_operation() {
        assert_eq!(
            ir_rvalue!(Neg(const 1_u8)),
            RValue::UnaryOp {
                op: UnOp::Neg,
                rhs: Operand::Constant(Value::U8(1))
            },
        );
    }

    #[test]
    fn binary_operation() {
        assert_eq!(
            ir_rvalue!(Add(const 1_u8, const 2_u8)),
            RValue::BinaryOp {
                op: BinOp::Add,
                lhs: Operand::Constant(Value::U8(1)),
                rhs: Operand::Constant(Value::U8(2)),
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
            RValue::Use(Operand::Constant(Value::U8(1))),
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
}
