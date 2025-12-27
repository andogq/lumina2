use crate::{
    ir::{ast::StringPool, id::*},
    util::indexed_vec::IndexedVec,
};

#[derive(Clone, Debug, Default)]
pub struct Ctx {
    pub strings: StringPool,
    pub bindings: Bindings,
}

impl Ctx {
    pub fn new() -> Self {
        Self::default()
    }
}

#[derive(Clone, Debug, Default)]
pub struct Bindings {
    bindings: IndexedVec<BindingId, Option<StringId>>,
}

impl Bindings {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, label: Option<StringId>) -> BindingId {
        self.bindings.insert(label)
    }
}
