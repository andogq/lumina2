#[macro_export(local_inner_macros)]
macro_rules! ir_function {
    // Basic block statement, with further trailing statements.
    (@basic_block($($statements:tt)*) [$($statement:tt)*] $($rest:tt)+) => {
        ir_function!(@basic_block($($statements)* ir_statement!($($statement)*),) $($rest)*)
    };

    // Terminator, which can only occur as the last statement of a basic block.
    (@basic_block($($statements:tt)*) [$($terminator:tt)+]) => {
        BasicBlockData {
            statements: ::std::vec![
                $($statements)*
            ],
            terminator: ir_terminator!($($terminator)+)
        }
    };

    // Section option 1: local declaration.
    (@section($ctx:ident, $body:ident) let $local:ident: $($ty:tt)*) => {
        let $local = $body.local_decls.insert($crate::ir::LocalDecl {
            ty: ir_ty!([$ctx.tys] $($ty)*),
        });
    };

    // Section option 2: basic block section.
    (@section($ctx:ident, $body:ident) $($bb_name:ident: { $($bb:tt)* })*) => {
        $(
            #[allow(unused_variables)]
            let $bb_name = $body.basic_blocks.insert(
                $crate::split_token!([;] [ir_function(@basic_block())] $($bb)*)
            );
        )*
    };

    // Unknown section.
    (@section($ctx:ident, $body:ident) $($toks:tt)*) => {
        ::std::compile_error!(::std::concat!("Unknown section: ", ::std::stringify!($($toks)*)));
    };

    // Instantiate the body, and pass each item separated by semicolon to `@section`.
    (@cb_sections($ctx:expr) $([$($section:tt)*])*) => {{
        let ctx = $ctx;

        #[allow(unused_mut)]
        let mut body = $crate::ir::Body::default();

        $(ir_function!(@section(ctx, body) $($section)*);)*

        ctx.functions.insert(body)
    }};

    // Macro entry point. Split input at semicolon, and pass result to `@cb_sections`.
    ([$ctx:expr] $($toks:tt)*) => {
        $crate::split_token!([;] [ir_function(@cb_sections($ctx))] $($toks)*)
    };
}

#[cfg(test)]
mod test {
    #![allow(clippy::just_underscores_and_digits)]

    use crate::ir::{
        BasicBlockData, BinOp, Body, Local, LocalDecl, Operand, Place, Projection, RValue,
        Statement, Terminator, TyInfo, Value, ctx::IrCtx,
    };

    fn assert_body(body: &Body, locals: &[LocalDecl], basic_blocks: &[BasicBlockData]) {
        assert_eq!(body.local_decls.iter().cloned().collect::<Vec<_>>(), locals);
        assert_eq!(
            body.basic_blocks.iter().cloned().collect::<Vec<_>>(),
            basic_blocks
        );
    }

    #[test]
    fn it_works() {
        let mut ctx = IrCtx::default();
        let program = ir_function! {[&mut ctx]};
        assert_body(&ctx.functions[program], &[], &[]);
    }

    #[test]
    fn local_decls() {
        let mut ctx = IrCtx::default();
        let program = ir_function! {
            [&mut ctx]
            let _0: u8;
            let _1: &u8;
        };

        let u8_ty = ctx.tys.find_or_insert(TyInfo::U8);
        let ref_u8_ty = ctx.tys.find_or_insert(TyInfo::Ref(u8_ty));

        assert_body(
            &ctx.functions[program],
            &[LocalDecl { ty: u8_ty }, LocalDecl { ty: ref_u8_ty }],
            &[],
        );
    }

    #[test]
    fn basic_blocks() {
        let mut ctx = IrCtx::default();
        let program = ir_function! {
            [&mut ctx]
            bb0: {
                return;
            }

            bb1: {
                return;
            }
        };

        assert_body(
            &ctx.functions[program],
            &[],
            &[
                BasicBlockData {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
                BasicBlockData {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
        );
    }

    #[test]
    fn everything() {
        let mut ctx = IrCtx::default();

        let program = ir_function! {
            [&mut ctx]
            let _0: u8;
            let _1: &u8;

            bb0: {
                _0 = const 1_u8;
                _1 = &_0;
                return;
            }

            bb0: {
                _0 = Add(_0, *_1);
                return;
            }
        };

        let _0 = Local::zero();
        let _1 = Local::of(1);
        let u8_ty = ctx.tys.find_or_insert(TyInfo::U8);
        let ref_u8_ty = ctx.tys.find_or_insert(TyInfo::Ref(u8_ty));

        assert_body(
            &ctx.functions[program],
            &[LocalDecl { ty: u8_ty }, LocalDecl { ty: ref_u8_ty }],
            &[
                BasicBlockData {
                    statements: vec![
                        Statement::Assign {
                            place: Place {
                                local: _0,
                                projection: vec![],
                            },
                            rvalue: RValue::Use(Operand::Constant(Value::U8(1))),
                        },
                        Statement::Assign {
                            place: Place {
                                local: _1,
                                projection: vec![],
                            },
                            rvalue: RValue::Ref(Place {
                                local: _0,
                                projection: vec![],
                            }),
                        },
                    ],
                    terminator: Terminator::Return,
                },
                BasicBlockData {
                    statements: vec![Statement::Assign {
                        place: Place {
                            local: _0,
                            projection: vec![],
                        },
                        rvalue: RValue::BinaryOp {
                            op: BinOp::Add,
                            lhs: Operand::Place(Place {
                                local: _0,
                                projection: vec![],
                            }),
                            rhs: Operand::Place(Place {
                                local: _1,
                                projection: vec![Projection::Deref],
                            }),
                        },
                    }],
                    terminator: Terminator::Return,
                },
            ],
        );
    }
}
