use crate::prelude::*;

create_id!(BindingId);

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
