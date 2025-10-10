#![recursion_limit = "256"]

mod ast;
mod ctx;
mod ir;
mod lex;
mod llvm;
mod tir;
mod util;

pub use self::{ctx::*, lex::Tok};

fn main() {
    let source = "fn main() -> u8 { 123 }";
    let ctx = Ctx::new();

    let toks = lex::Lexer::new(&ctx, source);
    let program = ast::parse(toks);
    let tir = tir::lower(&ctx, &program);

    dbg!(tir);
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::ir::ctx::IrCtx;

    macro_rules! run_test {
        ($name:ident => [$expected:expr] $($program:tt)*) => {
            #[test]
            fn $name() {
                let mut ctx = IrCtx::default();
                let program = ir_function! {
                    [&mut ctx]
                    $($program)*
                };

                let expected = $expected;

                let llvm_output = {
                    let llvm_ctx = inkwell::context::Context::create();
                    let backend = llvm::Llvm::new(&llvm_ctx, &ctx);
                    backend.run("func_Function(Key(0))")
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
