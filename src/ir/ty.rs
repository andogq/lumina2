use std::cell::RefCell;

use crate::indexed_vec;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub enum TyInfo {
    U8,
    I8,
    Ref(Ty),
    Slice(Ty),
    Array { ty: Ty, length: usize },
}

indexed_vec!(pub key Ty);
indexed_vec!(pub TysInner<Ty, TyInfo>);

#[derive(Clone, Debug, Default)]
pub struct Tys {
    inner: RefCell<TysInner>,
}

impl Tys {
    pub fn new() -> Self {
        Self {
            inner: RefCell::new(TysInner::new()),
        }
    }

    pub fn get(&self, ty: Ty) -> TyInfo {
        self.inner.borrow()[ty].clone()
    }

    pub fn find_or_insert(&self, ty: TyInfo) -> Ty {
        let existing = self
            .inner
            .borrow()
            .iter_keys()
            .find(|(_, test_ty)| *test_ty == &ty)
            .map(|(ty, _)| ty);

        match existing {
            Some(ty) => ty,
            None => self.inner.borrow_mut().insert(ty),
        }
    }
}
