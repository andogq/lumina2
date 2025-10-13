#[macro_export(local_inner_macros)]
macro_rules! ir_function {
    // Basic block statement, with further trailing statements.
    (@basic_block($ctx:ident) [$($statements:tt)*] [$($statement:tt)*] $($rest:tt)+) => {
        ir_function!(@basic_block($ctx) [$($statements)* ir_statement!($($statement)*),] $($rest)*)
    };

    // Terminator, which can only occur as the last statement of a basic block.
    (@basic_block($ctx:ident) [$($statements:tt)*] [$($terminator:tt)+]) => {
        $crate::ir::repr::BasicBlockData {
            statements: ::std::vec![
                $($statements)*
            ],
            terminator: ir_terminator!($($terminator)+)
        }
    };

    // Section option 1: local declaration.
    (@section($ctx:ident, $body:ident) let $local:ident: $($ty:tt)*) => {
        let $local = $body.local_decls.insert($crate::ir::repr::LocalDecl {
            ty: ir_ty!($($ty)*),
        });
    };

    // Section option 2: basic block section.
    (@section($ctx:ident, $body:ident) $($bb_name:ident: { $($bb:tt)* })*) => {
        // HACK: Pre-declare all basic blocks.
        $(
            let $bb_name = $body.basic_blocks.insert($crate::ir::repr::BasicBlockData {
                statements: ::std::vec![],
                terminator: $crate::ir::repr::Terminator::Return,
            });
        )*

        // Overwrite all basic blocks with their actual definition.
        $(
            $body.basic_blocks[$bb_name] = $crate::split_token!([;] [ir_function(@basic_block ($ctx) [])] $($bb)*);
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
        let mut body = $crate::ir::repr::Function::default();

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

    use crate::{
        Idents,
        ir::{
            ctx::IrCtx,
            repr::{
                BasicBlockData, BinOp, Constant, Function, Local, LocalDecl, Operand, Place,
                Projection, RValue, Statement, Terminator,
            },
        },
        tir::Ty,
    };

    fn assert_body(body: &Function, locals: &[LocalDecl], basic_blocks: &[BasicBlockData]) {
        assert_eq!(body.local_decls.iter().cloned().collect::<Vec<_>>(), locals);
        assert_eq!(
            body.basic_blocks.iter().cloned().collect::<Vec<_>>(),
            basic_blocks
        );
    }

    fn create_ctx() -> IrCtx {
        IrCtx::new({
            let idents = Idents::default();
            idents.intern("main".to_string());
            idents
        })
    }

    #[test]
    fn it_works() {
        let mut ctx = create_ctx();
        let program = ir_function! {[&mut ctx]};
        assert_body(&ctx.functions[program], &[], &[]);
    }

    #[test]
    fn local_decls() {
        let mut ctx = create_ctx();
        let program = ir_function! {
            [&mut ctx]
            let _0: u8;
            let _1: &u8;
        };

        assert_body(
            &ctx.functions[program],
            &[
                LocalDecl { ty: Ty::U8 },
                LocalDecl {
                    ty: Ty::Ref(Box::new(Ty::U8)),
                },
            ],
            &[],
        );
    }

    #[test]
    fn basic_blocks() {
        let mut ctx = create_ctx();
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
        let mut ctx = create_ctx();

        let program = ir_function! {
            [&mut ctx]
            let _0: u8;
            let _1: &u8;

            bb0: {
                _0 = const 1_u8;
                _1 = &_0;
                return;
            }

            bb1: {
                _0 = Add(_0, *_1);
                return;
            }
        };

        let _0 = Local::zero();
        let _1 = Local::of(1);

        assert_body(
            &ctx.functions[program],
            &[
                LocalDecl { ty: Ty::U8 },
                LocalDecl {
                    ty: Ty::Ref(Box::new(Ty::U8)),
                },
            ],
            &[
                BasicBlockData {
                    statements: vec![
                        Statement::Assign {
                            place: Place {
                                local: _0,
                                projection: vec![],
                            },
                            rvalue: RValue::Use(Operand::Constant(Constant::U8(1))),
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
