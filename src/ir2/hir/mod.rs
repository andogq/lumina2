pub mod thir;
mod visitor;

use std::collections::HashMap;

use crate::ir2::ast::StringId;

pub use self::{
    bindings::*, block::*, expr::*, functions::*, statement::*, thir::Thir, type_refs::*,
    visitor::*,
};

#[derive(Clone, Debug)]
pub struct Hir {
    pub functions: Vec<Function>,
}

mod functions {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Function {
        pub parameters: Vec<(BindingId, Type)>,
        pub return_ty: Type,
        pub entry: BlockId,

        pub bindings: HashMap<BindingId, DeclarationTy>,
        pub blocks: Vec<Block>,
        pub exprs: Vec<Expr>,
    }

    impl Function {
        pub fn get_expr(&self, expr: ExprId) -> &Expr {
            &self.exprs[expr.0]
        }

        pub fn get_block(&self, block: BlockId) -> &Block {
            &self.blocks[block.0]
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct FunctionId(usize);
    impl FunctionId {
        pub fn new(id: usize) -> Self {
            Self(id)
        }
    }
}

mod block {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct BlockId(pub usize);
    impl BlockId {
        pub fn new(id: usize) -> Self {
            Self(id)
        }
    }

    #[derive(Clone, Debug)]
    pub struct Block {
        pub statements: Vec<Statement>,
        pub expr: ExprId,
    }
}

mod statement {
    use super::*;

    #[derive(Clone, Debug)]
    pub enum Statement {
        Declare(DeclareStatement),
        Return(ReturnStatement),
        Expr(ExprStatement),
    }

    #[derive(Clone, Debug)]
    pub struct DeclareStatement {
        pub binding: BindingId,
        pub ty: DeclarationTy,
    }

    #[derive(Clone, Debug)]
    pub enum DeclarationTy {
        Type(Type),
        Inferred(ExprId),
    }

    #[derive(Clone, Debug)]
    pub struct ReturnStatement {
        pub expr: ExprId,
    }

    #[derive(Clone, Debug)]
    pub struct ExprStatement {
        pub expr: ExprId,
    }
}

mod expr {
    use crate::{
        enum_conversion,
        ir2::cst::{BinaryOp, UnaryOp},
    };

    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct ExprId(pub usize);
    impl ExprId {
        pub fn new(id: usize) -> Self {
            Self(id)
        }
    }

    #[derive(Clone, Debug)]
    pub enum Expr {
        Assign(Assign),
        Binary(Binary),
        Unary(Unary),
        Switch(Switch),
        Literal(Literal),
        Call(Call),
        Block(BlockId),
        Variable(Variable),
        Unreachable,
    }

    #[derive(Clone, Debug)]
    pub struct Assign {
        pub variable: ExprId,
        pub value: ExprId,
    }

    #[derive(Clone, Debug)]
    pub struct Binary {
        pub lhs: ExprId,
        pub op: BinaryOp,
        pub rhs: ExprId,
    }

    #[derive(Clone, Debug)]
    pub struct Unary {
        pub op: UnaryOp,
        pub value: ExprId,
    }

    #[derive(Clone, Debug)]
    pub struct Switch {
        pub discriminator: ExprId,
        pub branches: Vec<(Literal, BlockId)>,
        pub default: Option<BlockId>,
    }

    #[derive(Clone, Debug)]
    pub enum Literal {
        Integer(usize),
        Boolean(bool),
        Unit,
    }

    #[derive(Clone, Debug)]
    pub struct Call {
        pub callee: ExprId,
        pub arguments: Vec<ExprId>,
    }

    #[derive(Clone, Debug)]
    pub struct Variable {
        pub binding: BindingId,
    }

    enum_conversion! {
        [Expr]
        Assign: Assign,
        Binary: Binary,
        Unary: Unary,
        Switch: Switch,
        Literal: Literal,
        Call: Call,
        Block: BlockId,
        Variable: Variable,
    }
}

mod type_refs {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct TypeRefId(usize);
    impl TypeRefId {
        pub fn new(id: usize) -> Self {
            Self(id)
        }
    }

    #[derive(Clone, Debug)]
    pub struct TypeRef {
        pub name: StringId,
        pub ty: Option<Type>,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    pub enum Type {
        Never,
        Unit,
        I8,
        U8,
        Boolean,
        Ref(Box<Type>),
    }

    impl Type {
        pub fn is_integer(&self) -> bool {
            matches!(self, Self::U8 | Self::I8)
        }
    }
}

mod bindings {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct BindingId(usize);
    impl BindingId {
        pub fn new(id: usize) -> Self {
            Self(id)
        }
    }
}
