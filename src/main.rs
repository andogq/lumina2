mod interpreter;
mod ir;
mod llvm;
mod util;

use crate::{
    interpreter::Interpreter,
    ir::{ctx::IrCtx, *},
    llvm::Llvm,
};

fn main() {
    let mut ctx = IrCtx::default();

    let program1 = ir_function! {
        [&mut ctx]
        let _0: u8;
        let _1: u8;
        let _2: u8;

        bb0: {
            StorageLive(_1);
            StorageLive(_2);
            _1 = const 2_u8;
            _2 = const 3_u8;
            _0 = Mul(_1, _2);
            StorageDead(_2);
            StorageDead(_1);
            return;
        }
    };

    let program2 = ir_function! {
        [&mut ctx]
        let _0: u8;
        let _1: [u8; 3];
        let _2: u8;

        bb0: {
            StorageLive(_1);
            StorageLive(_2);
            _1 = [const 1_u8, const 2_u8, const 3_u8];
            _2 = const 1_u8;
            _2 = Add(_2, _2);
            _0 = _1[_2];
            StorageDead(_2);
            StorageDead(_1);
            return;
        }
    };

    let program3 = ir_function! {
        [&mut ctx]
        let _0: u8;

        bb0: {
            switchInt(_0) -> [5_u8: bb2, otherwise: bb1];
        }

        bb1: {
            _0 = Add(_0, const 1_u8);
            goto -> bb0;
        }

        bb2: {
            return;
        }
    };

    let mut interpreter = Interpreter::new(&ctx);
    dbg!(interpreter.run(program1));
    dbg!(interpreter.run(program2));
    dbg!(interpreter.run(program3));

    let mut ctx = IrCtx::default();
    let add_something = ir_function! {
        [&mut ctx]

        let _0: u8;
        let _1: u8;

        bb0: {
            StorageLive(_1);
            _1 = const 42_u8;
            _0 = Add(const 23_u8, _1);
            StorageDead(_1);
            return;
        }
    };
    let llvm = Llvm::new(&ctx);
    let module = llvm.new_module("something");
    module.compile(add_something, "add_something");
    let llvm_output = module.run("add_something");

    let interpreter_output = Interpreter::new(&ctx).run(add_something);

    assert_eq!(llvm_output, interpreter_output.into_u8().unwrap());
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! run_test {
        ($name:ident => [$expected:expr] $($program:tt)*) => {
            #[test]
            fn $name() {
                let mut ctx = IrCtx::default();
                let program = ir_function! {
                    [&mut ctx]
                    $($program)*
                };

                let interpreter_output = Interpreter::new(&ctx).run(program).into_u8().unwrap();
                let llvm_output = {
                    let llvm = Llvm::new(&ctx);
                    let module = llvm.new_module("module");
                    module.compile(program, stringify!($name));
                    module.run(stringify!($name))
                };

                let expected = $expected;

                assert_eq!(expected, interpreter_output);
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
}
