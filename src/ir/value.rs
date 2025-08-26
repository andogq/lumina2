use crate::{indexed_vec, ir::Pointer};

#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Value {
    U8(u8),
    I8(i8),
    Ref(Pointer),
    Array(Array),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub enum TyInfo {
    U8,
    I8,
    Ref(Ty),
    Array { ty: Ty, length: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Array {
    start: Pointer,
    length: usize,
}

impl Value {
    pub fn allocated_size(&self) -> usize {
        match self {
            Value::U8(_) => size_of::<u8>(),
            Value::I8(_) => size_of::<i8>(),
            Value::Ref(_) => size_of::<Pointer>(),
            Value::Array(array) => unimplemented!(),
        }
    }

    pub fn into_u8(self) -> Option<u8> {
        match self {
            Self::U8(value) => Some(value),
            _ => None,
        }
    }

    pub fn into_i8(self) -> Option<i8> {
        match self {
            Self::I8(value) => Some(value),
            _ => None,
        }
    }

    pub fn into_ref(self) -> Option<Pointer> {
        match self {
            Self::Ref(value) => Some(value),
            _ => None,
        }
    }

    pub fn into_array(self) -> Option<Array> {
        match self {
            Self::Array(value) => Some(value),
            _ => None,
        }
    }

    pub fn from_u8(value: u8) -> Self {
        Self::U8(value)
    }

    pub fn from_i8(value: i8) -> Self {
        Self::I8(value)
    }

    pub fn from_ref(value: Pointer) -> Self {
        Self::Ref(value)
    }

    pub fn from_array(value: Array) -> Self {
        Self::Array(value)
    }
}

impl TyInfo {
    pub fn allocated_size(&self, tys: &Tys) -> usize {
        match self {
            TyInfo::U8 => size_of::<u8>(),
            TyInfo::I8 => size_of::<i8>(),
            TyInfo::Ref(_) => size_of::<Pointer>(),
            TyInfo::Array { ty, length } => tys[*ty].allocated_size(tys) * length,
        }
    }
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
            _ => panic!("cannot perform not on {self:?}"),
        }
    }
}

impl std::ops::Neg for Value {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Value::U8(rhs) => Value::U8(rhs.wrapping_neg()),
            Value::I8(rhs) => Value::I8(-rhs),
            _ => panic!("cannot unary op on {self:?}"),
        }
    }
}

impl From<u8> for Value {
    fn from(value: u8) -> Self {
        Self::U8(value)
    }
}

impl From<i8> for Value {
    fn from(value: i8) -> Self {
        Self::I8(value)
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
