mod interpreter;
mod ir;
mod util;

use crate::{interpreter::Interpreter, ir::*};

fn main() {
    let program = ir! {
        let _0;
        let _1;
        let _2;

        bb0: {
            StorageLive(_1);
            StorageLive(_2);
            _1 = const 2;
            _2 = const 3;
            _0 = Mul(copy _1, copy _2);
            StorageDead(_2);
            StorageDead(_1);
            return;
        }
    };
    dbg!(Interpreter::run(&program));

    let mut local_decls = Locals::new();
    let loc_ret = local_decls.insert(LocalDecl {});
    let loc_lhs = local_decls.insert(LocalDecl {});
    let loc_rhs = local_decls.insert(LocalDecl {});

    let mut basic_blocks = BasicBlocks::new();
    basic_blocks.insert(BasicBlockData {
        statements: vec![
            Statement::StorageLive(loc_lhs),
            Statement::StorageLive(loc_rhs),
            Statement::Assign {
                place: Place {
                    local: loc_lhs,
                    projection: vec![],
                },
                rvalue: RValue::Use(Operand::Constant(2)),
            },
            Statement::Assign {
                place: Place {
                    local: loc_rhs,
                    projection: vec![],
                },
                rvalue: RValue::Use(Operand::Constant(3)),
            },
            Statement::Assign {
                place: Place {
                    local: loc_ret,
                    projection: vec![],
                },
                rvalue: RValue::BinaryOp {
                    op: BinOp::Mul,
                    lhs: Operand::Copy(Place {
                        local: loc_lhs,
                        projection: vec![],
                    }),
                    rhs: Operand::Copy(Place {
                        local: loc_rhs,
                        projection: vec![],
                    }),
                },
            },
            Statement::StorageDead(loc_rhs),
            Statement::StorageDead(loc_lhs),
        ],
        terminator: Terminator::Return,
    });

    let one_plus_one = Body {
        basic_blocks,
        local_decls,
        arg_count: 0,
    };

    let output = Interpreter::run(&one_plus_one);
    dbg!(output);
}
