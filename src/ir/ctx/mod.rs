use crate::ir::ctx::ty::Tys;

#[derive(Clone, Debug, Default)]
pub struct Ctx {
    pub tys: Tys,
}

pub mod ty {
    use crate::{indexed_vec, ir::Value};

    #[derive(Clone, Debug, PartialEq, Eq)]
    #[non_exhaustive]
    pub enum TyInfo {
        U8,
        I8,
    }

    impl TyInfo {
        pub fn size(&self) -> usize {
            match self {
                TyInfo::U8 | TyInfo::I8 => 1,
            }
        }

        pub fn get_value(&self, bytes: &[u8]) -> Value {
            assert_eq!(
                self.size(),
                bytes.len(),
                "can only perform conversion with correct byte count"
            );

            match self {
                TyInfo::U8 => Value::U8(u8::from_ne_bytes([bytes[0]])),
                TyInfo::I8 => Value::I8(i8::from_ne_bytes([bytes[0]])),
            }
        }
    }

    indexed_vec!(pub key Ty);
    indexed_vec!(pub Tys<Ty, TyInfo>);

    impl Tys {
        pub fn find_or_insert(&mut self, ty: TyInfo) -> Ty {
            let existing = self.iter_keys().find(|(_, test_ty)| *test_ty == &ty);

            match existing {
                Some((ty, _)) => ty,
                None => self.insert(ty),
            }
        }
    }
}
