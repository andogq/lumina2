use super::{Any, Integer, Loadable, Storable, ValueBackend};

pub trait Pointer<B: ValueBackend + ?Sized>: Any<B> + Loadable<B> + Storable<B> + Clone {
    fn element_ptr<I: Integer<B>>(self, bb: &B::BasicBlock, i: I, ty: B::Ty) -> B::Pointer;

    fn deref(self, bb: &B::BasicBlock) -> B::Pointer;
}

pub trait FatPointer<B: ValueBackend + ?Sized>: Pointer<B> {
    // TODO: Use something more appropriate than u8
    fn from_ptr(ptr: B::Pointer, data: B::U8) -> Self;

    fn get_metadata(&self) -> B::U8;
}
