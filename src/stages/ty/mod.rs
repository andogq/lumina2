mod constraint_builder;
mod disjoint_union_set;
mod solver;

use self::disjoint_union_set::DisjointUnionSet;
use crate::{
    enum_conversion,
    ir2::hir::*,
    stages::ty::{constraint_builder::ConstraintBuilder, solver::Solver},
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum TypeVarId {
    Expr(ExprId),
    Binding(BindingId),
    Type(Type),
}

enum_conversion! {
    [TypeVarId]
    Expr: ExprId,
    Binding: BindingId,
    Type: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Constraint {
    Eq(TypeVarId, TypeVarId),
    Integer(TypeVarId, IntegerKind),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Solution {
    Type(Type),
    Literal(Literal),
}

enum_conversion! {
    [Solution]
    Type: Type,
    Literal: Literal,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Literal {
    Integer(IntegerKind),
}

enum_conversion! {
    [Literal]
    Integer: IntegerKind,
}

impl Literal {
    pub fn to_type(&self) -> Type {
        match self {
            Literal::Integer(integer_literal) => integer_literal.to_type(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum IntegerKind {
    Any,
    Signed,
    Unsigned,
}

impl IntegerKind {
    pub fn to_type(&self) -> Type {
        match self {
            IntegerKind::Signed | IntegerKind::Any => Type::I8,
            IntegerKind::Unsigned => Type::U8,
        }
    }
}

pub fn solve(hir: &Hir) {
    dbg!(hir);
    let constraints = ConstraintBuilder::build(hir);
    let tys = Solver::run(dbg!(&constraints));
    dbg!(tys);
}
