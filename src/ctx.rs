use crate::prelude::*;

#[derive(Clone, Debug, Default)]
pub struct Ctx {
    pub strings: StringPool,
    pub scopes: Scopes,
    pub errors: CErrorList,
}

impl Ctx {
    pub fn new() -> Self {
        Self::default()
    }
}
