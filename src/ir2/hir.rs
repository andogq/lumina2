use crate::ir2::ast::StringId;

pub use self::{bindings::*, block::*, expr::*, functions::*, statement::*, type_refs::*};

pub struct Hir {
    pub functions: Vec<Function>,
    pub blocks: Vec<Block>,
    pub exprs: Vec<Expr>,
}

impl Hir {
    pub fn get_expr(&self, expr: ExprId) -> &Expr {
        &self.exprs[expr.0]
    }

    pub fn get_block(&self, block: BlockId) -> &Block {
        &self.blocks[block.0]
    }
}

mod functions {
    use super::*;

    pub struct Function {
        pub parameters: Vec<(BindingId, TypeRefId)>,
        pub entry: BlockId,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct FunctionId(usize);
    impl FunctionId {
        pub fn new(id: usize) -> Self {
            Self(id)
        }
    }
}

mod block {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct BlockId(pub(super) usize);
    impl BlockId {
        pub fn new(id: usize) -> Self {
            Self(id)
        }
    }

    pub struct Block {
        pub statements: Vec<Statement>,
        pub expr: ExprId,
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
    pub struct ExprId(pub(super) usize);
    impl ExprId {
        pub fn new(id: usize) -> Self {
            Self(id)
        }
    }

    pub enum Expr {
        Assign(Assign),
        Binary(Binary),
        Unary(Unary),
        Switch(Switch),
        Literal(Literal),
        Call(Call),
        Block(BlockId),
        Variable(Variable),
    }

    pub struct Assign {
        pub variable: ExprId,
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
        Unit,
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

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct TypeRefId(usize);
    impl TypeRefId {
        pub fn new(id: usize) -> Self {
            Self(id)
        }
    }

    pub struct TypeRef {
        pub name: StringId,
        pub ty: Option<Type>,
    }

    pub enum Type {
        Unit,
        I8,
        U8,
        Boolean,
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
