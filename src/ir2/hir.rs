use std::collections::HashMap;

use crate::{
    ir2::ast::{StringId, StringPool},
    tir::BindingId,
};

pub use self::{bindings::*, block::*, expr::*, functions::*, statement::*, type_refs::*};

pub struct Hir {
    pub functions: Functions,

    pub blocks: Vec<Block>,
    pub exprs: Vec<Expr>,

    pub bindings: Bindings,
    pub strings: StringPool,
    pub type_refs: TypeRefs,
}

mod functions {
    use super::*;

    pub struct Function {
        pub parameters: Vec<(BindingId, TypeRefId)>,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct FunctionId(usize);

    pub struct Functions {
        lookup: HashMap<BindingId, FunctionId>,
        functions: Vec<Function>,
    }
}

mod block {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct BlockId(usize);

    pub struct Block {
        statements: Vec<Statement>,
        expr: Option<ExprId>,
    }
}

mod statement {
    use super::*;

    pub enum Statement {
        Declare(DeclareStatement),
        Return(ReturnStatement),
        Expr(ExprStatement),
    }

    pub struct DeclareStatement {
        pub binding: BindingId,
        pub ty: TypeRefId,
    }

    pub struct ReturnStatement {
        pub expr: ExprId,
    }

    pub struct ExprStatement {
        pub expr: ExprId,
    }
}

mod expr {
    use crate::ir2::cst::{BinaryOp, UnaryOp};

    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct ExprId(usize);

    pub enum Expr {
        Assign(Assign),
        Binary(Binary),
        Unary(Unary),
        Switch(Switch),
        Literal(Literal),
        Call(Call),
        Variable(Variable),
    }

    pub struct Assign {
        pub variable: BindingId,
        pub value: ExprId,
    }

    pub struct Binary {
        pub lhs: ExprId,
        pub op: BinaryOp,
        pub rhs: ExprId,
    }

    pub struct Unary {
        pub op: UnaryOp,
        pub value: ExprId,
    }

    pub struct Switch {
        pub discriminator: ExprId,
        pub branches: Vec<(Literal, BlockId)>,
        pub default: Option<BlockId>,
    }

    pub enum Literal {
        Integer(usize),
        Boolean(bool),
    }

    pub struct Call {
        pub callee: ExprId,
        pub arguments: Vec<ExprId>,
    }

    pub struct Variable {
        pub binding: BindingId,
    }
}

mod type_refs {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct TypeRefId(usize);

    pub struct TypeRefs {
        lookup: HashMap<StringId, TypeRefId>,
        types: Vec<TypeRef>,
    }

    pub struct TypeRef {
        name: StringId,
        ty: Option<Type>,
    }

    pub enum Type {
        Unit,
        I8,
        U8,
        Boolean,
    }
}

mod bindings {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct BindingId(usize);

    pub struct Bindings {
        lookup: HashMap<StringId, BindingId>,
        bindings: Vec<StringId>,
    }
}
