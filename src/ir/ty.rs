use std::cell::RefCell;

use crate::{indexed_vec, ir::Pointer};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub enum TyInfo {
    U8,
    I8,
    Ref(Ty),
    Slice(Ty),
    Array { ty: Ty, length: usize },
}

impl TyInfo {
    pub fn allocated_size(&self, tys: &Tys) -> usize {
        match self {
            TyInfo::U8 => size_of::<u8>(),
            TyInfo::I8 => size_of::<i8>(),
            TyInfo::Ref(inner) => match tys.get(*inner) {
                // If a ref to a slice, it's a fat pointer.
                TyInfo::Slice(_) => size_of::<Pointer>() + size_of::<usize>(),
                _ => size_of::<Pointer>(),
            },
            TyInfo::Slice(_) => panic!("slices are unsized"),
            TyInfo::Array { ty, length } => tys.get(*ty).allocated_size(tys) * length,
        }
    }
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
