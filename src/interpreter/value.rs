use crate::ir::{Pointer, Ty, TyInfo, Tys, repr::Constant};

#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Value {
    U8(u8),
    I8(i8),
    Ref(Pointer),
    Array(Vec<Value>),
    FatPointer { ptr: Pointer, data: usize },
}

impl Value {
    pub fn allocated_size(&self) -> usize {
        match self {
            Value::U8(_) => size_of::<u8>(),
            Value::I8(_) => size_of::<i8>(),
            Value::Ref(_) => size_of::<Pointer>(),
            Value::Array(_) => unimplemented!(),
            Value::FatPointer { .. } => size_of::<Pointer>() + size_of::<usize>(),
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

    // pub fn into_array(self) -> Option<Array> {
    //     match self {
    //         Self::Array(value) => Some(value),
    //         _ => None,
    //     }
    // }

    pub fn from_u8(value: u8) -> Self {
        Self::U8(value)
    }

    pub fn from_i8(value: i8) -> Self {
        Self::I8(value)
    }

    pub fn from_ref(value: Pointer) -> Self {
        Self::Ref(value)
    }

    // pub fn from_array(value: Array) -> Self {
    //     Self::Array(value)
    // }

    /// Get the [`Ty`] of this value, as if it were a constant.
    pub fn get_const_ty(&self, tys: &Tys) -> Ty {
        match self {
            Value::U8(_) => tys.find_or_insert(TyInfo::U8),
            Value::I8(_) => tys.find_or_insert(TyInfo::I8),
            Value::Ref(_) => panic!("cannot have constant reference"),
            Value::Array(values) => {
                // WARN: Assuming all values are the same type.
                assert!(
                    !values.is_empty(),
                    "cannot determine ty of empty constant array."
                );
                let value_ty = values[0].get_const_ty(tys);
                tys.find_or_insert(TyInfo::Array {
                    ty: value_ty,
                    length: values.len(),
                })
            }
            Value::FatPointer { .. } => unimplemented!(),
        }
    }
}

impl From<Constant> for Value {
    fn from(value: Constant) -> Self {
        match value {
            Constant::U8(value) => Self::U8(value),
            Constant::I8(value) => Self::I8(value),
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
