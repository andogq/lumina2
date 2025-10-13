use std::{cell::RefCell, collections::HashMap, fmt::Display};

use crate::{indexed_vec, tir::Ty};

#[derive(Clone, Debug, Default)]
pub struct Ctx {
    pub idents: Idents,
    pub ty_names: HashMap<Ident, Ty>,
}

impl Ctx {
    pub fn new() -> Self {
        let mut ctx = Self::default();

        // Preload with built-in types.
        [("u8", Ty::U8), ("i8", Ty::I8), ("bool", Ty::Boolean)]
            .into_iter()
            .for_each(|(ident, ty)| {
                let ident = ctx.idents.intern(ident.to_string());
                ctx.ty_names.insert(ident, ty);
            });

        ctx
    }
}

indexed_vec!(pub key Ident);
indexed_vec!(pub IdentsInner<Ident, String>);

#[derive(Clone, Debug, Default)]
pub struct Idents {
    inner: RefCell<IdentsInner>,
}

impl Idents {
    pub fn get(&self, ident: Ident) -> String {
        self.inner.borrow().get(ident).unwrap().to_string()
    }

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
