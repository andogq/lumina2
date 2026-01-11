use crate::{prelude::*, ty::TypeVarId};

use super::IntegerKind;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constraint {
    /// Variable is exactly equal to [`TypeVarId`].
    Eq(TypeVarId),
    /// Variable is some kind of integer, matching [`IntegerKind`].
    Integer(IntegerKind),
    /// Variable is a reference to [`TypeVarId`].
    Reference(TypeVarId),
    /// Variable is a function.
    Function {
        /// Parameter variables of function.
        parameters: Vec<TypeVarId>,
        /// Return variable of function.
        return_ty: TypeVarId,
    },
    /// Variable is an aggregate with some number of fields..
    Aggregate(usize),
}

#[derive(Clone, Debug, Default)]
pub struct Constraints {
    constraints: Vec<(TypeVarId, Constraint)>,
}

impl Constraints {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a [`Constraint::Eq`] constraint so `lhs` and `rhs` are equal.
    pub fn equal(&mut self, lhs: impl Into<TypeVarId>, rhs: impl Into<TypeVarId>) {
        self.constraints
            .push((lhs.into(), Constraint::Eq(rhs.into())));
    }

    /// Add a [`Constraint::Integer`] where `var` is [`IntegerKind::Any`].
    pub fn integer(&mut self, var: impl Into<TypeVarId>) {
        self.constraints
            .push((var.into(), Constraint::Integer(IntegerKind::Any)));
    }

    /// Add a [`Constraint::Integer`] where `var` is [`IntegerKind::Signed`].
    pub fn integer_signed(&mut self, var: impl Into<TypeVarId>) {
        self.constraints
            .push((var.into(), Constraint::Integer(IntegerKind::Signed)));
    }

    /// Add a [`Constraint::Integer`] where `var` is [`IntegerKind::Unsigned`].
    #[expect(
        dead_code,
        reason = "future constraints may require an unsigned integer."
    )]
    pub fn integer_unsigned(&mut self, var: impl Into<TypeVarId>) {
        self.constraints
            .push((var.into(), Constraint::Integer(IntegerKind::Unsigned)));
    }

    /// Add a [`Constraint::Reference`] where `var` is a reference to `reference`.
    pub fn reference(&mut self, var: impl Into<TypeVarId>, reference: impl Into<TypeVarId>) {
        self.constraints
            .push((var.into(), Constraint::Reference(reference.into())));
    }

    /// Add a [`Constraint::Function`] where `var` is a function with `parameters` and `return_ty`.
    pub fn function(
        &mut self,
        var: impl Into<TypeVarId>,
        parameters: impl IntoIterator<Item = impl Into<TypeVarId>>,
        return_ty: impl Into<TypeVarId>,
    ) {
        self.constraints.push((
            var.into(),
            Constraint::Function {
                parameters: parameters
                    .into_iter()
                    .map(|parameter| parameter.into())
                    .collect(),
                return_ty: return_ty.into(),
            },
        ));
    }

    /// Add a [`Constraint::Aggregate`] with `size` fields.
    pub fn aggregate(&mut self, var: impl Into<TypeVarId>, size: usize) {
        self.constraints
            .push((var.into(), Constraint::Aggregate(size)));
    }
}

impl Deref for Constraints {
    type Target = [(TypeVarId, Constraint)];

    fn deref(&self) -> &Self::Target {
        &self.constraints
    }
}
