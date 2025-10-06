use std::{cell::RefCell, fmt::Display};

use crate::indexed_vec;

#[derive(Clone, Debug, Default)]
pub struct Ctx {
    pub idents: Idents,
}

indexed_vec!(pub key Ident);
indexed_vec!(pub IdentsInner<Ident, String>);

#[derive(Clone, Debug, Default)]
pub struct Idents {
    inner: RefCell<IdentsInner>,
}

impl Idents {
    pub fn intern(&self, value: String) -> Ident {
        if let Some(key) = self
            .inner
            .borrow()
            .iter_keys()
            .find(|(_, interned)| value == **interned)
            .map(|(key, _)| key)
        {
            return key;
        }

        self.inner.borrow_mut().insert(value)
    }
}

impl Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // HACK: this should output the real ident
        write!(f, "ident{}", self.0)
    }
}
