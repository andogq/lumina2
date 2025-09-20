use std::fmt::Debug;

use crate::{
    ir::any_value::{Any, AnyValue},
    lower::BasicBlock,
};

pub trait ValueBackend {
    type BasicBlock: BasicBlock<Value = Self>;

    type Ty: Clone;

    type Pointer: Pointer<Self>;

    type I8: Integer<Self, Value = i8> + Clone + Debug;
    type U8: Integer<Self, Value = u8> + Clone + Debug;
}

pub trait Integer<B: ValueBackend + ?Sized>: Constant<B> + Any<B> {
    fn into_integer_value(self) -> IntegerValue<B>;

    fn add(bb: &mut B::BasicBlock, lhs: Self, rhs: Self) -> Self;
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

    pub fn store(self, bb: &mut B::BasicBlock, ptr: B::Pointer) {
        match self {
            IntegerValue::I8(i8) => i8.store(bb, ptr),
            IntegerValue::U8(u8) => u8.store(bb, ptr),
        }
    }

    pub fn into_any_value(self) -> AnyValue<B> {
        AnyValue::Integer(self)
    }
}

pub trait Constant<B: ValueBackend + ?Sized> {
    type Value;

    fn create(bb: &mut B::BasicBlock, value: Self::Value) -> Self;
}

pub trait Pointer<B: ValueBackend + ?Sized>: Any<B> + Clone {
    fn element_ptr<I: Integer<B>>(self, bb: &mut B::BasicBlock, i: I, ty: B::Ty) -> Self;

    fn deref(self, bb: &mut B::BasicBlock) -> Self;
}
