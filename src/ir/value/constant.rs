use super::ValueBackend;

use crate::ir::repr::Constant as ReprConstant;

pub trait Constant<B: ValueBackend + ?Sized> {
    type Value;

    fn create(bb: &B::BasicBlock, value: Self::Value) -> Self;
}

pub enum ConstantValue<B: ValueBackend + ?Sized> {
    I8(<B::I8 as Constant<B>>::Value),
    U8(<B::U8 as Constant<B>>::Value),
}

impl<B: ValueBackend + ?Sized> ConstantValue<B> {
    pub fn into_i8(self) -> <B::I8 as Constant<B>>::Value {
        match self {
            Self::I8(value) => value,
            _ => panic!("expected I8"),
        }
    }

    pub fn into_u8(self) -> <B::U8 as Constant<B>>::Value {
        match self {
            Self::U8(value) => value,
            _ => panic!("expected U8"),
        }
    }
}

impl<B: ValueBackend + ?Sized> From<ReprConstant> for ConstantValue<B> {
    fn from(value: ReprConstant) -> Self {
        match value {
            ReprConstant::U8(value) => Self::U8(value),
            ReprConstant::I8(value) => Self::I8(value),
        }
    }
}
