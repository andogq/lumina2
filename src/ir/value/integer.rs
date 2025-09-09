use std::fmt::Debug;

pub trait ValueBackend {
    type Ctx;

    type I8: FromConstant<Self::Ctx, i8> + Clone + Debug;
    type U8: FromConstant<Self::Ctx, u8> + Clone + Debug;
}

pub trait Integer<B: ValueBackend> {
    fn into_integer_value(self) -> IntegerValue<B>;
}

pub trait Constant<Ctx> {
    type Value;

    fn new(ctx: Ctx, value: Self::Value) -> Self;
}

pub trait FromConstant<Ctx, Value> {
    fn from_constant(ctx: Ctx, value: Value) -> Self;
}

#[derive(Clone, Debug)]
pub struct I8<B: ValueBackend>(pub B::I8);
impl<B: ValueBackend> Integer<B> for I8<B> {
    fn into_integer_value(self) -> IntegerValue<B> {
        self.into()
    }
}
impl<B: ValueBackend> Constant<B::Ctx> for I8<B> {
    type Value = i8;

    fn new(ctx: B::Ctx, value: Self::Value) -> Self {
        Self(B::I8::from_constant(ctx, value))
    }
}

#[derive(Clone, Debug)]
pub struct U8<B: ValueBackend>(pub B::U8);
impl<B: ValueBackend> Integer<B> for U8<B> {
    fn into_integer_value(self) -> IntegerValue<B> {
        self.into()
    }
}
impl<B: ValueBackend> Constant<B::Ctx> for U8<B> {
    type Value = u8;

    fn new(ctx: B::Ctx, value: Self::Value) -> Self {
        Self(B::U8::from_constant(ctx, value))
    }
}

#[derive(Clone, Debug)]
pub enum IntegerValue<B: ValueBackend> {
    I8(I8<B>),
    U8(U8<B>),
}
impl<B: ValueBackend> IntegerValue<B> {
    pub fn into_i8(self) -> I8<B> {
        match self {
            Self::I8(value) => value,
            _ => panic!("expected I8"),
        }
    }

    pub fn into_u8(self) -> U8<B> {
        match self {
            Self::U8(value) => value,
            _ => panic!("expected U8"),
        }
    }
}
impl<B: ValueBackend> From<I8<B>> for IntegerValue<B> {
    fn from(value: I8<B>) -> Self {
        Self::I8(value)
    }
}
impl<B: ValueBackend> From<U8<B>> for IntegerValue<B> {
    fn from(value: U8<B>) -> Self {
        Self::U8(value)
    }
}
