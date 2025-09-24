use super::{Any, Storable, ValueBackend};

pub trait Array<B: ValueBackend + ?Sized>: Storable<B> + Any<B> {
    fn load_count(bb: &B::BasicBlock, ptr: B::Pointer, ty: B::Ty, count: usize) -> Self;
}
