#[macro_export(local_inner_macros)]
macro_rules! ir_statement {
    // Statement in the form `Statement(params)`.
    ($statement:ident($($params:expr),* $(,)?)) => {
        $crate::ir::repr::Statement::$statement($($params,)*)
    };

    // Callback for parsing an assignment statement.
    (@cb_assign [$($place:tt)*] [$($rvalue:tt)*]) => {
        $crate::ir::repr::Statement::Assign {
            place: $crate::ir_place!($($place)*),
            rvalue: $crate::ir_rvalue!($($rvalue)*),
        }
    };

    // Assume an assignment. Split at `=`, and continue at `cb_assign`.
    ($($toks:tt)*) => {
        $crate::split_token!([=] without_trailing [ir_statement(@cb_assign)] $($toks)*)
    };
}

#[cfg(test)]
mod test {
    #![allow(clippy::just_underscores_and_digits)]
    use crate::ir::repr::{Local, Statement};

    mod statement {
        use super::*;

        #[test]
        fn simple() {
            let _0 = Local::zero();

            assert_eq!(ir_statement!(StorageLive(_0)), Statement::StorageLive(_0),);
        }
    }

    mod assign {
        use crate::ir::repr::{Constant, Operand, Place, RValue};

        use super::*;

        #[test]
        fn simple() {
            let _0 = Local::zero();

            assert_eq!(
                ir_statement!(_0 = const 1_u8),
                Statement::Assign {
                    place: Place {
                        local: _0,
                        projection: vec![]
                    },
                    rvalue: RValue::Use(Operand::Constant(Constant::U8(1)))
                }
            );
        }
    }
}
