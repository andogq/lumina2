use crate::ir::integer::{IntegerValue, ValueBackend};

pub trait Any<B: ValueBackend + ?Sized> {
    fn into_any_value(self) -> AnyValue<B>;

    fn load(bb: &mut B::BasicBlock, ptr: B::Pointer) -> Self;
    fn store(self, bb: &mut B::BasicBlock, ptr: B::Pointer);
}

pub enum AnyValue<B: ValueBackend + ?Sized> {
    Integer(IntegerValue<B>),
    Pointer(B::Pointer),
}
impl<B: ValueBackend> AnyValue<B> {
    pub fn store(self, bb: &mut B::BasicBlock, ptr: B::Pointer) {
        match self {
            AnyValue::Integer(integer_value) => integer_value.store(bb, ptr),
            AnyValue::Pointer(ptr_value) => ptr_value.store(bb, ptr),
        }
    }
}
