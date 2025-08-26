use crate::{indexed_vec, ir::Pointer};

macro_rules! value {
    ($($name:ident($inner:ty) [$from_fn:ident, $into_fn:ident] $(($ty_inner_ident:ident: $ty_inner:ty))?;)*) => {
        #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
        #[non_exhaustive]
        pub enum Value {
            $($name($inner),)*
        }

        impl Value {
            pub fn size(&self) -> usize {
                match self {
                    $(Self::$name(_) => ::core::mem::size_of::<$inner>(),)*
                }
            }

            pub fn to_bytes(&self) -> Vec<u8> {
                match self {
                    $(Self::$name(value) => value.to_ne_bytes().to_vec(),)*
                }
            }

            $(
                pub fn $into_fn(self) -> Option<$inner> {
                    match self {
                        Self::$name(value) => Some(value),
                        _ => None
                    }
                }

                pub fn $from_fn(value: $inner) -> Self {
                    Self::$name(value)
                }
            )*
        }

        $(
            impl From<$inner> for Value {
                fn from(value: $inner) -> Self {
                    Self::$name(value)
                }
            }
        )*

        #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
        #[non_exhaustive]
        pub enum TyInfo {
            $($name $(($ty_inner))?,)*
        }

        impl TyInfo {
            pub fn size(&self) -> usize {
                #[allow(unused)]
                match self {
                    $(Self::$name $(($ty_inner_ident))? => ::core::mem::size_of::<$inner>(),)*
                }
            }

            pub fn get_value(&self, bytes: &[u8]) -> Value {
                match self {
                    $(Self::$name $(($ty_inner_ident))? => Value::$name(<$inner>::from_ne_bytes(
                        bytes
                            .try_into()
                            .expect("can only perform conversion with correct byte type"),
                    )),)*
                }
            }
        }
    };
}

value! {
    U8(u8) [from_u8, into_u8];
    I8(i8) [from_i8, into_i8];
    Ref(Pointer) [from_ref, into_ref] (inner: Ty);
}

impl std::ops::Add for Value {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::U8(lhs), Value::U8(rhs)) => Self::U8(lhs + rhs),
            (Value::I8(lhs), Value::I8(rhs)) => Self::I8(lhs + rhs),
            (Value::Ref(_), Value::Ref(_)) => panic!("references cannot be added"),
            (lhs, rhs) => panic!("cannot add {lhs:?} + {rhs:?}"),
        }
    }
}

impl std::ops::Sub for Value {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::U8(lhs), Value::U8(rhs)) => Self::U8(lhs - rhs),
            (Value::I8(lhs), Value::I8(rhs)) => Self::I8(lhs - rhs),
            (Value::Ref(_), Value::Ref(_)) => panic!("references cannot be subtracted"),
            (lhs, rhs) => panic!("cannot subtract {lhs:?} - {rhs:?}"),
        }
    }
}

impl std::ops::Mul for Value {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::U8(lhs), Value::U8(rhs)) => Self::U8(lhs * rhs),
            (Value::I8(lhs), Value::I8(rhs)) => Self::I8(lhs * rhs),
            (Value::Ref(_), Value::Ref(_)) => panic!("references cannot be multiplied"),
            (lhs, rhs) => panic!("cannot multiply {lhs:?} * {rhs:?}"),
        }
    }
}

impl std::ops::Div for Value {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::U8(lhs), Value::U8(rhs)) => Self::U8(lhs / rhs),
            (Value::I8(lhs), Value::I8(rhs)) => Self::I8(lhs / rhs),
            (Value::Ref(_), Value::Ref(_)) => panic!("references cannot be divided"),
            (lhs, rhs) => panic!("cannot multiply {lhs:?} / {rhs:?}"),
        }
    }
}

impl std::ops::Not for Value {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Value::U8(rhs) => Value::U8(!rhs),
            Value::I8(rhs) => Value::I8(!rhs),
            Value::Ref(_) => panic!("cannot perform not on reference"),
        }
    }
}

impl std::ops::Neg for Value {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Value::U8(rhs) => Value::U8(rhs.wrapping_neg()),
            Value::I8(rhs) => Value::I8(-rhs),
            Value::Ref(_) => panic!("cannot unary op on ref"),
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
