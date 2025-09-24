#[macro_export(local_inner_macros)]
macro_rules! ir_terminator {
    (return) => {
        $crate::ir::repr::Terminator::Return
    };

    (goto -> $bb:ident) => {
        $crate::ir::repr::Terminator::Goto($bb)
    };

    (switchInt($($discriminator:tt)*) -> [$($value:literal: $bb:ident,)* otherwise: $otherwise:ident]) => {
        $crate::ir::repr::Terminator::SwitchInt {
            discriminator: ir_operand!($($discriminator)*),
            targets: ::std::vec![$(($value.into(), $bb),)*],
            otherwise: $otherwise,
        }
    };
}

#[cfg(test)]
mod test {
    #![allow(clippy::just_underscores_and_digits)]

    use crate::ir::repr::{BasicBlock, Constant, Local, Operand, Place, Terminator};

    #[test]
    fn term_return() {
        assert_eq!(ir_terminator!(return), Terminator::Return);
    }

    #[test]
    fn term_switch() {
        let _0 = Local::zero();

        let bb0 = BasicBlock::zero();
        let bb1 = BasicBlock::of(1);
        let bb2 = BasicBlock::of(2);

        assert_eq!(
            ir_terminator!(switchInt(_0) -> [0_u8: bb0, 10_u8: bb1, otherwise: bb2]),
            Terminator::SwitchInt {
                discriminator: Operand::Place(Place {
                    local: _0,
                    projection: vec![]
                }),
                targets: vec![(Constant::U8(0), bb0), (Constant::U8(10), bb1)],
                otherwise: bb2
            }
        );
    }

    #[test]
    fn term_goto() {
        let bb0 = BasicBlock::zero();

        assert_eq!(ir_terminator!(goto -> bb0), Terminator::Goto(bb0));
    }
}
