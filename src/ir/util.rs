use crate::prelude::*;

/// Helper to implement `From` and `TryFrom` to/from an enum.
#[macro_export]
macro_rules! enum_conversion {
    ([$target:ident] $($variant:ident: $ty:ty),* $(,)?) => {
        $(
            impl From<$ty> for $target {
                fn from(value: $ty) -> Self {
                    Self::$variant(value)
                }
            }

            impl TryFrom<$target> for $ty {
                type Error = $target;

                fn try_from(value: $target) -> Result<Self, $target> {
                    #[allow(unreachable_patterns)]
                    match value {
                        $target::$variant(value) => Ok(value),
                        expression => Err(expression)
                    }
                }
            }
        )*
    };
}

#[derive(Clone, Copy, Debug)]
pub enum BinaryOperation {
    Plus,
    Minus,
    Multiply,
    Divide,

    LogicalAnd,
    LogicalOr,

    BinaryAnd,
    BinaryOr,

    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

impl From<&cst::BinaryOperation> for BinaryOperation {
    fn from(operation: &cst::BinaryOperation) -> Self {
        match operation {
            cst::BinaryOperation::Plus(_) => Self::Plus,
            cst::BinaryOperation::Minus(_) => Self::Minus,
            cst::BinaryOperation::Multiply(_) => Self::Multiply,
            cst::BinaryOperation::Divide(_) => Self::Divide,
            cst::BinaryOperation::LogicalAnd(_) => Self::LogicalAnd,
            cst::BinaryOperation::LogicalOr(_) => Self::LogicalOr,
            cst::BinaryOperation::BinaryAnd(_) => Self::BinaryAnd,
            cst::BinaryOperation::BinaryOr(_) => Self::BinaryOr,
            cst::BinaryOperation::Equal(_) => Self::Equal,
            cst::BinaryOperation::NotEqual(_) => Self::NotEqual,
            cst::BinaryOperation::Less(_) => Self::Less,
            cst::BinaryOperation::LessEqual(_) => Self::LessEqual,
            cst::BinaryOperation::Greater(_) => Self::Greater,
            cst::BinaryOperation::GreaterEqual(_) => Self::GreaterEqual,
        }
    }
}

impl From<cst::BinaryOperation> for BinaryOperation {
    fn from(operation: cst::BinaryOperation) -> Self {
        Self::from(&operation)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum UnaryOperation {
    Not,
    Negative,
    Deref,
    Ref,
}

impl From<&cst::UnaryOperation> for UnaryOperation {
    fn from(operation: &cst::UnaryOperation) -> Self {
        match operation {
            cst::UnaryOperation::Not(_) => Self::Not,
            cst::UnaryOperation::Negative(_) => Self::Negative,
            cst::UnaryOperation::Deref(_) => Self::Deref,
            cst::UnaryOperation::Ref(_) => Self::Ref,
        }
    }
}

impl From<cst::UnaryOperation> for UnaryOperation {
    fn from(operation: cst::UnaryOperation) -> Self {
        Self::from(&operation)
    }
}
