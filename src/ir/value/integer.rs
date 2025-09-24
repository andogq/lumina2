use std::fmt::Debug;

use super::{Any, AnyValue, Constant, Loadable, Storable, ValueBackend};

pub trait Integer<B: ValueBackend + ?Sized>:
    Constant<B> + Loadable<B> + Storable<B> + Any<B>
{
    fn into_integer_value(self) -> IntegerValue<B>;

    fn add(bb: &B::BasicBlock, lhs: Self, rhs: Self) -> Self;
}

#[derive(Clone, Debug)]
pub enum IntegerValue<B: ValueBackend + ?Sized> {
    I8(B::I8),
    U8(B::U8),
}
impl<B: ValueBackend + ?Sized> IntegerValue<B> {
    pub fn into_i8(self) -> B::I8 {
        match self {
            Self::I8(value) => value,
            _ => panic!("expected I8"),
        }
    }

    pub fn into_u8(self) -> B::U8 {
        match self {
            Self::U8(value) => value,
            _ => panic!("expected U8"),
        }
    }

    pub fn store(self, bb: &B::BasicBlock, ptr: B::Pointer) {
        match self {
            IntegerValue::I8(i8) => i8.store(bb, ptr),
            IntegerValue::U8(u8) => u8.store(bb, ptr),
        }
    }

    pub fn into_any_value(self) -> AnyValue<B> {
        AnyValue::Integer(self)
    }
}
