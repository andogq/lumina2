mod interpreter;
mod ir;
mod util;

use crate::{interpreter::Interpreter, ir::*};

fn main() {
    let program = ir! {
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
    dbg!(Interpreter::run(&program));

    let program = ir! {
        let _0: u8;
        let _1: u8;
        let _2: &u8;

        bb0: {
            StorageLive(_1);
            StorageLive(_2);
            _1 = const 1_u8;
            _2 = &_1;
            _1 = const 10_u8;
            _0 = *_2;
            StorageDead(_2);
            StorageDead(_1);
            return;
        }
    };
    dbg!(Interpreter::run(&program));
}
