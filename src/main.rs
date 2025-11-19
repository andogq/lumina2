#![recursion_limit = "256"]

mod ast;
mod ctx;
mod ir;
mod ir2;
mod lex;
mod llvm;
mod stages;
mod tir;
mod util;

use crate::stages::parse::Parse;

pub use self::{ctx::*, lex::Tok};

fn run(source: &str) -> u8 {
    let ctx = Ctx::new();

    let toks = lex::Lexer::new(&ctx, source);
    let program = ast::parse(toks);
    let tir = tir::lower(&ctx, &program);
    let ir = ir::lower(&ctx, &tir);

    let ink_ctx = inkwell::context::Context::create();
    let llvm = llvm::Llvm::new(&ink_ctx, &ir);
    llvm.run("main")
}

fn main() {
    let source = "fn main() -> u8 { if true { 1 } else { 2 } }";

    let mut toks = lex::lex2::Lexer::new(source);
    let cst = ir2::cst::Program::parse(&mut toks);
    let ast = stages::ast_builder::build_ast(&cst);
    let hir = stages::hir_builder::lower(&ast);
    stages::ty::solve(&hir);
}

#[cfg(test)]
mod test {
    use super::*;

    mod full {
        use super::*;

        #[test]
        fn implicit_return_u8() {
            assert_eq!(run("fn main() -> u8 { 42 }"), 42);
        }

        #[test]
        fn basic_expression() {
            assert_eq!(run("fn main() -> u8 { 1 + 2 }"), 3);
        }

        #[test]
        fn variables() {
            assert_eq!(
                run("fn main() -> u8 { let a = 1; let b = 123; a + b }"),
                124
            );
        }

        #[test]
        fn booleans() {
            assert_eq!(
                run("fn main() -> bool { let my_bool = true; let other_bool = false; my_bool }"),
                1
            );
        }

        #[test]
        fn if_statement() {
            assert_eq!(run("fn main() -> u8 { if true { 123 } else { 99 } }"), 123);
        }

        #[test]
        fn if_variable() {
            assert_eq!(
                run("fn main() -> u8 { let a = if true { 123 } else { 44 }; let b = a + 10; b }"),
                133
            );
        }

        #[test]
        fn reassignment() {
            assert_eq!(run("fn main() -> u8 { let a = 1; a = 2; a }"), 2);
        }

        #[test]
        fn conditional_reassignment() {
            assert_eq!(
                run("fn main() -> u8 { let a = 1; if a == 1 { a = 2; } a }"),
                2
            );
        }

        #[test]
        fn explicit_return() {
            assert_eq!(run("fn main() -> u8 { return 1; }"), 1);
        }

        #[test]
        fn conditional_return() {
            assert_eq!(run("fn main() -> u8 { if true { return 2; } 1 }"), 2);
        }

        #[test]
        fn reference() {
            assert_eq!(run("fn main() -> u8 { let a = 123; let b = &a; *b }"), 123);
        }

        #[test]
        fn assign_to_reference() {
            assert_eq!(
                run("fn main() -> u8 { let a = 123; let b = &a; *b = 44; a }"),
                44
            );
        }

        #[test]
        fn so_many_refs() {
            assert_eq!(
                run(
                    "fn main() -> u8 { let a = 123; let b = 111; let a_ref = &a; let b_ref = &b; *a_ref = *b_ref; a }"
                ),
                111
            );
        }

        #[test]
        fn fns() {
            assert_eq!(
                run("fn cool_fn() -> u8 { return 123; } fn main() -> u8 { cool_fn() }"),
                123
            );
        }
    }

    mod ir {
        use super::*;
        use crate::ir::ctx::IrCtx;

        macro_rules! run_test {
            ($name:ident => [$expected:expr] $($program:tt)*) => {
                #[test]
                fn $name() {
                    let mut ctx = IrCtx::new({
                        let idents = Idents::default();
                        idents.intern("main".to_string());
                        idents
                    });
                    ir_function! {
                        [&mut ctx]
                        $($program)*
                    };

                    let expected = $expected;

                    let llvm_output = {
                        let llvm_ctx = inkwell::context::Context::create();
                        let backend = llvm::Llvm::new(&llvm_ctx, &ctx);
                        backend.run("main")
                    };
                    assert_eq!(expected, llvm_output);
                }
            };
        }

        run_test! {
            add_constant => [123u8]

            let _0: u8;
            bb0: {
                _0 = Add(const 100u8, const 23_u8);
                return;
            }
        }

        run_test! {
            add_locals => [91u8]

            let _0: u8;
            let _1: u8;
            let _2: u8;
            bb0: {
                StorageLive(_1);
                StorageLive(_2);
                _1 = const 40u8;
                _2 = const 51u8;
                _0 = Add(_1, _2);
                StorageLive(_2);
                StorageLive(_1);
                return;
            }
        }

        run_test! {
            deref_something => [5u8]

            let _0: u8;
            let _1: u8;
            let _2: &u8;
            bb0: {
                StorageLive(_1);
                StorageLive(_2);
                _1 = const 5u8;
                _2 = &_1;
                _0 = *_2;
                StorageLive(_2);
                StorageLive(_1);
                return;
            }
        }

        run_test! {
            arrays => [8u8]

            let _0: u8;
            let _1: [u8; 3];
            let _2: u8;
            bb0: {
                StorageLive(_1);
                StorageLive(_2);
                _0 = const 0u8;
                _1 = [const 2u8, const 1u8, const 5u8];

                _2 = const 0u8;
                _0 = Add(_0, _1[_2]);

                _2 = const 1u8;
                _0 = Add(_0, _1[_2]);

                _2 = const 2u8;
                _0 = Add(_0, _1[_2]);
                StorageDead(_2);
                StorageDead(_1);
                return;
            }
        }

        run_test! {
            deref_chained_ref => [10u8]

            let _0: u8;
            let _1: u8;
            let _2: &u8;
            let _3: & &u8;
            bb0: {
                StorageLive(_1);
                _1 = const 10u8;
                StorageLive(_2);
                _2 = &_1;
                StorageLive(_3);
                _3 = &_2;
                _0 = **_3;
                StorageDead(_3);
                StorageDead(_2);
                StorageDead(_1);
                return;
            }
        }

        run_test! {
            deref_array_element_ref => [2u8]

            let _0: u8;
            let _1: [u8; 3];
            let _2: u8;
            let _3: &u8;
            bb0: {
                StorageLive(_1);
                _1 = [const 1u8, const 2u8, const 3u8];
                StorageLive(_2);
                _2 = const 1u8;
                StorageLive(_3);
                _3 = &_1[_2];
                _0 = *_3;
                StorageDead(_3);
                StorageDead(_2);
                StorageDead(_1);
                return;
            }
        }

        run_test! {
            mutate_via_ref_and_return_orig => [99u8]

            let _0: u8;
            let _1: u8;
            let _2: &u8;
            bb0: {
                StorageLive(_1);
                _1 = const 5u8;
                StorageLive(_2);
                _2 = &_1;
                _1 = const 99u8;
                _0 = *_2;
                StorageDead(_2);
                StorageDead(_1);
                return;
            }
        }

        run_test! {
            index_add_deref_to_element => [25u8]

            let _0: u8;
            let _1: [u8; 3];
            let _2: u8;
            let _3: &u8;
            bb0: {
                StorageLive(_1);
                _1 = [const 10u8, const 20u8, const 30u8];
                StorageLive(_2);
                _2 = const 1u8;
                StorageLive(_3);
                _3 = &_1[_2];
                _0 = Add(*_3, const 5u8);
                StorageDead(_3);
                StorageDead(_2);
                StorageDead(_1);
                return;
            }
        }

        run_test! {
            add_deref_to_constant => [110u8]

            let _0: u8;
            let _1: u8;
            let _2: &u8;
            bb0: {
                StorageLive(_1);
                _1 = const 100u8;
                StorageLive(_2);
                _2 = &_1;
                _0 = Add(*_2, const 10u8);
                StorageDead(_2);
                StorageDead(_1);
                return;
            }
        }

        run_test! {
            add_two_dereferenced_values => [12u8]

            let _0: u8;
            let _1: u8;
            let _2: u8;
            let _3: &u8;
            let _4: &u8;
            bb0: {
                StorageLive(_1);
                _1 = const 5u8;
                StorageLive(_2);
                _2 = const 7u8;
                StorageLive(_3);
                _3 = &_1;
                StorageLive(_4);
                _4 = &_2;
                _0 = Add(*_3, *_4);
                StorageDead(_4);
                StorageDead(_3);
                StorageDead(_2);
                StorageDead(_1);
                return;
            }
        }

        run_test! {
            deref_array_then_add => [20u8]

            let _0: u8;
            let _1: [u8; 2];
            let _2: u8;
            let _3: &u8;
            bb0: {
                StorageLive(_1);
                _1 = [const 10u8, const 50u8];
                StorageLive(_2);
                _2 = const 0u8;
                StorageLive(_3);
                _3 = &_1[_2];
                _0 = Add(*_3, const 10u8);
                StorageDead(_3);
                StorageDead(_2);
                StorageDead(_1);
                return;
            }
        }

        run_test! {
            deref_array_elements_add => [8u8]

            let _0: u8;
            let _1: [u8; 3];
            let _2: u8;
            let _3: u8;
            let _4: &u8;
            let _5: &u8;
            bb0: {
                StorageLive(_1);
                _1 = [const 1u8, const 3u8, const 5u8];
                StorageLive(_2);
                _2 = const 1u8;
                StorageLive(_3);
                _3 = const 2u8;
                StorageLive(_4);
                _4 = &_1[_2];
                StorageLive(_5);
                _5 = &_1[_3];
                _0 = Add(*_4, *_5);
                StorageDead(_5);
                StorageDead(_4);
                StorageDead(_3);
                StorageDead(_2);
                StorageDead(_1);
                return;
            }
        }

        run_test! {
            add_deref_to_deref_chain => [130u8]

            let _0: u8;
            let _1: u8;
            let _2: &u8;
            let _3: & &u8;
            let _4: u8;
            bb0: {
                StorageLive(_1);
                _1 = const 100u8;
                StorageLive(_2);
                _2 = &_1;
                StorageLive(_3);
                _3 = &_2;
                StorageLive(_4);
                _4 = **_3;
                _0 = Add(const 30u8, _4);
                StorageDead(_4);
                StorageDead(_3);
                StorageDead(_2);
                StorageDead(_1);
                return;
            }
        }

        run_test! {
            add_mixed_constants_and_locals => [24u8]

            let _0: u8;
            let _1: u8;
            let _2: u8;
            bb0: {
                StorageLive(_1);
                _1 = const 10u8;
                StorageLive(_2);
                _2 = const 11u8;
                _0 = Add(const 3u8, _1);
                _0 = Add(_0, _2);
                StorageDead(_2);
                StorageDead(_1);
                return;
            }
        }

        run_test! {
            goto_terminator => [3u8]

            let _0: u8;

            bb0: {
                _0 = const 1u8;
                goto -> bb1;
            }

            bb1: {
                _0 = const 2u8;
                goto -> bb2;
            }

            bb2: {
                _0 = const 3u8;
                return;
            }
        }

        run_test! {
            switch_int_terminator_target => [10u8]

            let _0: u8;

            bb0: {
                _0 = const 3u8;
                switchInt(_0) -> [0u8: bb1, 1u8: bb1, 3u8: bb2, otherwise: bb1];
            }

            bb1: {
                return;
            }

            bb2: {
                _0 = const 10u8;
                return;
            }
        }

        run_test! {
            switch_int_terminator_otherwise => [10u8]

            let _0: u8;

            bb0: {
                _0 = const 3u8;
                switchInt(_0) -> [0u8: bb1, 1u8: bb1, otherwise: bb2];
            }

            bb1: {
                return;
            }

            bb2: {
                _0 = const 10u8;
                return;
            }
        }

        run_test! {
            array_fat_pointer => [3u8]

            let _0: u8;
            let _1: [u8; 3];
            let _2: &[u8; 3];
            let _3: &[u8];

            bb0: {
                StorageLive(_1);
                StorageLive(_2);
                StorageLive(_3);

                _1 = [const 1u8, const 5u8, const 7u8];
                _2 = &_1;
                _3 = _2 as &[u8] (PointerCoercion(Unsize));

                _0 = PtrMetadata(_3);

                StorageLive(_3);
                StorageLive(_2);
                StorageLive(_1);

                return;
            }
        }

        run_test! {
            array_fat_pointer_index => [5u8]

            let _0: u8;
            let _1: [u8; 3];
            let _2: &[u8; 3];
            let _3: &[u8];
            let _4: u8;

            bb0: {
                StorageLive(_1);
                StorageLive(_2);
                StorageLive(_3);
                StorageLive(_4);

                _1 = [const 1u8, const 5u8, const 7u8];
                _2 = &_1;
                _3 = _2 as &[u8] (PointerCoercion(Unsize));

                _4 = const 1u8;
                _0 = (*_3)[_4];

                StorageLive(_4);
                StorageLive(_3);
                StorageLive(_2);
                StorageLive(_1);

                return;
            }
        }
    }
}
