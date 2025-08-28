mod ir_ty;
mod util;

#[macro_export(local_inner_macros)]
macro_rules! ir_impl {
    (local($program:ident) $local:ident: $($ty:tt)*) => {
        #[allow(unused)]
        let $local = $program.local_decls.insert($crate::ir::LocalDecl {
            ty: ir_impl!(parse_ty [$program.ctx.tys] $($ty)*),
        });
    };

    (parse_ty [$tys:expr] & $($ty:tt)*) => {{
        let ref_ty = ir_impl!(parse_ty [$tys] $($ty)*);

        $tys.find_or_insert(
            $crate::ir::TyInfo::Ref(ref_ty)
        )
    }};
    (parse_ty [$tys:expr] u8) => {
        $tys.find_or_insert(
            $crate::ir::TyInfo::U8
        )
    };
    (parse_ty [$tys:expr] i8) => {
        $tys.find_or_insert(
            $crate::ir::ctx::ty::TyInfo::I8
        )
    };
    (parse_ty [$tys:expr] [$inner:tt; $length:expr]) => {{
        let inner_ty = ir_impl!(parse_ty [$tys] $inner);

        $tys.find_or_insert(
            $crate::ir::TyInfo::Array { ty: inner_ty, length: $length }
        )
    }};

    (basic_block($program:ident) $bb:ident: { $($body:tt)* }) => {
        #[allow(unused)]
        let $bb = $program.basic_blocks.insert(ir_impl!(split(build_basic_block) [] [] [$($body)*]));
    };

    (build_basic_block [$([$($statements:tt)*])*] [$($terminator:tt)*]) => {
        $crate::ir::BasicBlockData {
            statements: ::std::vec![
                $(ir_impl!(statement [$($statements)*])),*
            ],
            terminator: ir_impl!(terminator [$($terminator)*]),
        }
    };

    // StorageLive(_0)
    (statement [$statement:ident($($params:ident),* $(,)?)]) => {
        $crate::ir::Statement::$statement($($params,)*)
    };

    // Assume assignment
    (statement [$($tt:tt)*]) => {
        ir_impl!(split_assign(assign_statement) [] [$($tt)*])
    };

    (assign_statement [$($lhs:tt)*] [$($rhs:tt)*]) => {
        $crate::ir::Statement::Assign {
            place: ir_impl!(parse_place [$($lhs)*]),
            rvalue: ir_impl!(parse_rvalue [$($rhs)*]),
        }
    };

    (parse_place [$local:ident]) => {
        $crate::ir::Place {
            local: $local,
            projection: ::std::vec![],
        }
    };

    (parse_place [* $local:ident]) => {
        $crate::ir::Place {
            local: $local,
            projection: ::std::vec![$crate::ir::Projection::Deref],
        }
    };

    (parse_place [$local:ident [$index:ident]]) => {
        $crate::ir::Place {
            local: $local,
            projection: ::std::vec![$crate::ir::Projection::Index($index)],
        }
    };

    (parse_rvalue [$op:ident($($params:tt)*)]) => {
        ir_impl!(split_params(rvalue_op_with_params($op)) [] [] [$($params)*])
    };
    (rvalue_op_with_params($op:ident) [$($rhs:tt)*]) => {
        $crate::ir::RValue::UnaryOp {
            op: $crate::ir::UnOp::$op,
            rhs: ir_impl!(parse_operand [$($rhs)*]),
        }
    };
    (rvalue_op_with_params($op:ident) [$($lhs:tt)*] [$($rhs:tt)*]) => {
        $crate::ir::RValue::BinaryOp {
            op: $crate::ir::BinOp::$op,
            lhs: ir_impl!(parse_operand [$($lhs)*]),
            rhs: ir_impl!(parse_operand [$($rhs)*]),
        }
    };

    (parse_rvalue [&$($place:tt)*]) => {
        $crate::ir::RValue::Ref(ir_impl!(parse_place [$($place)*]))
    };

    (parse_rvalue [$($operand:tt)*]) => {
        $crate::ir::RValue::Use(ir_impl!(parse_operand [$($operand)*]))
    };

    (parse_operand [const $value:literal]) => {
        $crate::ir::Operand::Constant($value.into())
    };
    // HACK: Only parses constant operands
    (parse_operand [[$(const $val:tt),* $(,)?]]) => {{
        $crate::ir::Operand::Constant($crate::ir::Value::Array(::std::vec![$($val.into()),*]))
    }};
    (parse_operand [$($place:tt)*]) => {
        $crate::ir::Operand::Place(ir_impl!(parse_place [$($place)*]))
    };

    (terminator [return]) => {
        $crate::ir::Terminator::Return
    };

    (split_params($($callback:tt)*) [$($params:tt)*] [] []) => {
        ir_impl!($($callback)* $($params)*)
    };
    (split_params($($callback:tt)*) [$($params:tt)*] [$($current:tt)*] [$(, $($rest:tt)*)?]) => {
        ir_impl!(split_params($($callback)*) [$($params)* [$($current)*]] [] [$($($rest)*)?])
    };
    (split_params($($callback:tt)*) [$($params:tt)*] [$($current:tt)*] [$tok:tt $($rest:tt)*]) => {
        ir_impl!(split_params($($callback)*) [$($params)*] [$($current)* $tok] [$($rest)*])
    };

    (split_assign($callback:ident) [$($lhs:tt)*] [= $($rest:tt)*]) => {
        ir_impl!($callback [$($lhs)*] [$($rest)*])
    };

    (split_assign($callback:ident) [$($lhs:tt)*] [$tok:tt $($rest:tt)*]) => {
        ir_impl!(split_assign($callback) [$($lhs)* $tok] [$($rest)*])
    };

    (split($callback:ident) [$($statements:tt)*] [$($current:tt)*] [;]) => {
        ir_impl!($callback [$($statements)*] [$($current)*])
    };
    (split($callback:ident) [$($statements:tt)*] [$($current:tt)*] [; $($rest:tt)+]) => {
        ir_impl!(split($callback) [$($statements)* [$($current)*]] [] [$($rest)+])
    };
    (split($callback:ident) [$($statements:tt)*] [$($current:tt)*] [$tok:tt $($rest:tt)+]) => {
        ir_impl!(split($callback) [$($statements)*] [$($current)* $tok] [$($rest)+])
    };

    // HACK: Properly split statements by `;`, instead of repeating rule for `&`
    (munch($program:ident)[let $local:ident: &$ty:tt; $($rest:tt)*]) => {
        ir_impl!(local($program) $local: &$ty);
        ir_impl!(munch($program)[$($rest)*]);
    };
    (munch($program:ident)[let $local:ident: $ty:tt; $($rest:tt)*]) => {
        ir_impl!(local($program) $local: $ty);
        ir_impl!(munch($program)[$($rest)*]);
    };
    (munch($program:ident)[$bb:ident: { $($body:tt)* } $($rest:tt)*]) => {
        ir_impl!(basic_block($program) $bb: { $($body)* });
        ir_impl!(munch($program)[$($rest)*]);
    };
    (munch($program:ident)[]) => { };
}

#[macro_export(local_inner_macros)]
macro_rules! ir {
    ($($tt:tt)*) => {{
        let mut program = $crate::ir::Body::default();

        ir_impl!(munch(program) [$($tt)*]);

        program
    }};
}

#[cfg(test)]
mod test {
    use insta::assert_debug_snapshot;

    #[test]
    fn locals() {
        assert_debug_snapshot!(ir! {
            let _0: u8;
            let _1: u8;
            let _2: u8;

            bb0: {
                return;
            }
        });
    }

    #[test]
    fn basic_blocks() {
        assert_debug_snapshot!(ir! {
            bb0: {
                return;
            }

            bb1: {
                return;
            }
        });
    }

    #[test]
    fn mul_numbers() {
        assert_debug_snapshot!(ir! {
            let _0: u8;
            let _1: u8;
            let _2: u8;

            bb0: {
                _1 = const 2_u8;
                _2 = const 3_u8;
                _0 = Mul(_1, _2);
                return;
            }
        });
    }

    #[test]
    fn reference() {
        assert_debug_snapshot!(ir! {
            let _0: u8;
            let _1: &u8;

            bb0: {
                _0 = const 1_u8;
                _1 = &_0;
                return;
            }
        });
    }
}
