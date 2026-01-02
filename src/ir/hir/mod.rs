pub mod thir;

use crate::prelude::*;

pub use self::{block::*, expr::*, functions::*, statement::*, type_refs::*};

create_id!(BlockId);
create_id!(ExprId);
create_id!(FunctionId);
create_id!(StatementId);

#[derive(Clone, Debug, Default)]
pub struct Hir {
    pub functions: IndexedVec<FunctionId, Function>,
    pub blocks: IndexedVec<BlockId, Block>,
    pub statements: IndexedVec<StatementId, Statement>,
    pub exprs: IndexedVec<ExprId, Expr>,
}

impl Index<FunctionId> for Hir {
    type Output = Function;

    fn index(&self, index: FunctionId) -> &Self::Output {
        &self.functions[index]
    }
}

impl Index<BlockId> for Hir {
    type Output = Block;

    fn index(&self, index: BlockId) -> &Self::Output {
        &self.blocks[index]
    }
}

impl Index<StatementId> for Hir {
    type Output = Statement;

    fn index(&self, index: StatementId) -> &Self::Output {
        &self.statements[index]
    }
}

impl Index<ExprId> for Hir {
    type Output = Expr;

    fn index(&self, index: ExprId) -> &Self::Output {
        &self.exprs[index]
    }
}

mod functions {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Function {
        pub binding: BindingId,
        pub parameters: Vec<(BindingId, Type)>,
        pub return_ty: Type,
        pub entry: BlockId,
    }
}

mod block {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Block {
        pub statements: Vec<StatementId>,
        pub expr: ExprId,
    }
}

mod statement {
    use super::*;

    #[derive(Clone, Debug)]
    pub enum Statement {
        Declare(DeclareStatement),
        Return(ReturnStatement),
        Break(BreakStatement),
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
    pub struct BreakStatement {
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
        ir::cst::{BinaryOp, UnaryOp},
    };

    use super::*;

    #[derive(Clone, Debug)]
    pub enum Expr {
        Assign(Assign),
        Binary(Binary),
        Unary(Unary),
        Switch(Switch),
        Loop(Loop),
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
    pub struct Loop {
        pub body: BlockId,
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
        Loop: Loop,
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
        Function {
            params: Vec<Type>,
            ret_ty: Box<Type>,
        },
    }

    impl Type {
        pub fn is_integer(&self) -> bool {
            matches!(self, Self::U8 | Self::I8)
        }
    }
}
