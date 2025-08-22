#[macro_export(local_inner_macros)]
macro_rules! ir_impl {
    (local($program:ident) $local:ident) => {
        let $local = $program.local_decls.insert(LocalDecl {});
    };

    (basic_block($program:ident) $bb:ident: { $($body:tt)* }) => {
        let $bb = $program.basic_blocks.insert(ir_impl!(split(build_basic_block) [] [] [$($body)*]));
    };

    (build_basic_block [$([$($statements:tt)*])*] [$($terminator:tt)*]) => {
        BasicBlockData {
            statements: ::std::vec![
                $(ir_impl!(statement [$($statements)*])),*
            ],
            terminator: ir_impl!(terminator [$($terminator)*]),
        }
    };

    // StorageLive(_0)
    (statement [$statement:ident($($params:ident),* $(,)?)]) => {
        Statement::$statement($($params,)*)
    };

    // Assume assignment
    (statement [$($tt:tt)*]) => {
        ir_impl!(split_assign(assign_statement) [] [$($tt)*])
    };

    (assign_statement [$($lhs:tt)*] [$($rhs:tt)*]) => {
        Statement::Assign {
            place: ir_impl!(parse_place [$($lhs)*]),
            rvalue: ir_impl!(parse_rvalue [$($rhs)*]),
        }
    };

    (parse_place [$local:ident]) => {
        Place {
            local: $local,
            projection: ::std::vec![],
        }
    };

    (parse_rvalue [$op:ident($($params:tt)*)]) => {
        ir_impl!(split_params(rvalue_op_with_params($op)) [] [] [$($params)*])
    };
    (rvalue_op_with_params($op:ident) [$($rhs:tt)*]) => {
        RValue::UnaryOp {
            op: UnOp::$op,
            rhs: ir_impl!(parse_operand [$($rhs)*]),
        }
    };
    (rvalue_op_with_params($op:ident) [$($lhs:tt)*] [$($rhs:tt)*]) => {
        RValue::BinaryOp {
            op: BinOp::$op,
            lhs: ir_impl!(parse_operand [$($lhs)*]),
            rhs: ir_impl!(parse_operand [$($rhs)*]),
        }
    };

    (parse_rvalue [$($operand:tt)*]) => {
        RValue::Use(ir_impl!(parse_operand [$($operand)*]))
    };

    (parse_operand [const $value:literal]) => {
        Operand::Constant($value)
    };
    (parse_operand [copy $($place:tt)*]) => {
        Operand::Copy(ir_impl!(parse_place [$($place)*]))
    };
    (parse_operand [move $($place:tt)*]) => {
        Operand::Move(ir_impl!(parse_place [$($place)*]))
    };

    (terminator [return]) => {
        Terminator::Return
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

    (munch($program:ident)[let $local:ident; $($rest:tt)*]) => {
        ir_impl!(local($program) $local);
        ir_impl!(munch($program)[$($rest)*]);
    };

    (munch($program:ident)[$bb:ident: { $($body:tt)* } $($rest:tt)*]) => {
        ir_impl!(basic_block($program) $bb: { $($body)* });
    };
}

#[macro_export(local_inner_macros)]
macro_rules! ir {
    ($($tt:tt)*) => {{
        let mut program = Body::default();

        ir_impl!(munch(program) [$($tt)*]);

        program
    }};
}
