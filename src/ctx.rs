use crate::prelude::*;

#[derive(Clone, Debug, Default)]
pub struct Ctx {
    pub strings: StringPool,
    pub bindings: Bindings,
    pub scopes: Scopes,
}

impl Ctx {
    pub fn new() -> Self {
        Self::default()
    }
}
