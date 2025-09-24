use std::fmt::Debug;

use crate::lower::BasicBlock;

pub use self::{
    any_value::{Any, AnyValue},
    array::Array,
    constant::{Constant, ConstantValue},
    integer::{Integer, IntegerValue},
    memory::{Loadable, Storable},
    pointer::{FatPointer, Pointer},
};

mod any_value;
mod array;
mod constant;
mod integer;
mod memory;
mod pointer;

pub trait ValueBackend {
    type BasicBlock: BasicBlock<Value = Self>;

    type Ty: Clone;

    type Pointer: Pointer<Self>;
    type FatPointer: FatPointer<Self>;
    type Array: Array<Self>;

    type I8: Integer<Self, Value = i8> + Clone + Debug;
    type U8: Integer<Self, Value = u8> + Clone + Debug;
}
