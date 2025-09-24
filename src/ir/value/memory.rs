//! Value traits for basic memory operations.

use super::ValueBackend;

pub trait Loadable<B: ValueBackend + ?Sized> {
    fn load(bb: &B::BasicBlock, ptr: B::Pointer) -> Self;
}

pub trait Storable<B: ValueBackend + ?Sized> {
    fn store(self, bb: &B::BasicBlock, ptr: B::Pointer);
}
