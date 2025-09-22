use crate::ir::integer::{IntegerValue, ValueBackend};

pub trait Any<B: ValueBackend + ?Sized> {
    fn into_any_value(self) -> AnyValue<B>;

    fn load(bb: &B::BasicBlock, ptr: B::Pointer) -> Self;
    fn store(self, bb: &B::BasicBlock, ptr: B::Pointer);
}

pub enum AnyValue<B: ValueBackend + ?Sized> {
    Integer(IntegerValue<B>),
    Pointer(B::Pointer),
    FatPointer(B::FatPointer),
}
impl<B: ValueBackend> AnyValue<B> {
    pub fn into_integer_value(self) -> IntegerValue<B> {
        match self {
            Self::Integer(integer_value) => integer_value,
            _ => panic!("expected IntegerValue"),
        }
    }

    pub fn into_pointer_value(self) -> B::Pointer {
        match self {
            Self::Pointer(pointer_value) => pointer_value,
            _ => panic!("expected PointerValue"),
        }
    }

    pub fn store(self, bb: &B::BasicBlock, ptr: B::Pointer) {
        match self {
            AnyValue::Integer(integer_value) => integer_value.store(bb, ptr),
            AnyValue::Pointer(ptr_value) => ptr_value.store(bb, ptr),
            AnyValue::FatPointer(fat_ptr_value) => fat_ptr_value.store(bb, ptr),
        }
    }
}
