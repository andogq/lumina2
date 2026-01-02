use crate::prelude::*;

#[derive(Debug)]
pub struct Ctx {
    pub strings: StringPool,
    pub bindings: Bindings,
    pub scopes: Scopes,
    pub errors: CErrorList,
    pub ink: inkwell::context::Context,
}

impl Ctx {
    pub fn new() -> Self {
        Self {
            strings: StringPool::new(),
            bindings: Bindings::new(),
            scopes: Scopes::new(),
            errors: CErrorList::new(),
            ink: inkwell::context::Context::create(),
        }
    }
}
