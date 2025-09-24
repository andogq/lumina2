/// Parse an operand as an [`Operand`]. If prefixed with `const`, will assume
/// [`Operand::Constant`]. Otherwise, will parse with [`ir_place`] as a [`Place`].
///
/// [`ir_place`]: crate::ir_place
/// [`Operand`]: crate::ir::Operand
/// [`Operand::Constant`]: crate::ir::Operand::Constant
/// [`Place`]: crate::ir::Place
#[macro_export(local_inner_macros)]
macro_rules! ir_operand {
    // Parse value as constant expression.
    (const $const:expr) => {
        $crate::ir::repr::Operand::Constant($const.into())
    };

    // Parse as a place, deferring to `ir_place` macro.
    ($($place:tt)*) => {
        $crate::ir::repr::Operand::Place(
            $crate::ir_place!($($place)*)
        )
    };
}

#[cfg(test)]
mod test {
    #![allow(clippy::just_underscores_and_digits)]
    use crate::ir::repr::{Constant, Local, Operand, Place};

    #[test]
    fn op_const() {
        assert_eq!(
            ir_operand!(const 123_u8),
            Operand::Constant(Constant::U8(123))
        );
    }

    #[test]
    fn op_place() {
        let _0 = Local::zero();

        assert_eq!(
            ir_operand!(_0),
            Operand::Place(Place {
                local: _0,
                projection: vec![]
            })
        );
    }
}
