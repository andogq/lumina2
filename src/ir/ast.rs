use crate::prelude::*;

use crate::ir::cst::{BinaryOp, UnaryOp};

pub use self::{block::*, expr::*, function::*, statement::*};

create_id!(BlockId);
create_id!(ExprId);
create_id!(FunctionId);
create_id!(StatementId);

#[derive(Clone, Debug)]
pub struct Ast {
    pub function_declarations: IndexedVec<FunctionId, FunctionDeclaration>,

    pub blocks: IndexedVec<BlockId, Block>,
    pub statements: IndexedVec<StatementId, Statement>,
    pub expressions: IndexedVec<ExprId, Expr>,
}

impl Ast {
    pub fn new() -> Self {
        Self {
            function_declarations: IndexedVec::new(),
            blocks: IndexedVec::new(),
            statements: IndexedVec::new(),
            expressions: IndexedVec::new(),
        }
    }
}

impl Index<BlockId> for Ast {
    type Output = Block;

    fn index(&self, index: BlockId) -> &Self::Output {
        &self.blocks[index]
    }
}

impl Index<ExprId> for Ast {
    type Output = Expr;

    fn index(&self, index: ExprId) -> &Self::Output {
        &self.expressions[index]
    }
}

impl Index<FunctionId> for Ast {
    type Output = FunctionDeclaration;

    fn index(&self, index: FunctionId) -> &Self::Output {
        &self.function_declarations[index]
    }
}

impl Index<StatementId> for Ast {
    type Output = Statement;

    fn index(&self, index: StatementId) -> &Self::Output {
        &self.statements[index]
    }
}

mod function {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct FunctionDeclaration {
        pub name: StringId,
        pub params: Vec<FunctionParameter>,
        pub return_ty: Option<StringId>,
        pub body: BlockId,
    }

    #[derive(Clone, Debug)]
    pub struct FunctionParameter {
        pub name: StringId,
        pub ty: StringId,
    }
}

mod block {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Block {
        pub statements: Vec<StatementId>,
        pub expression: Option<ExprId>,
    }
}

mod statement {
    use crate::enum_conversion;

    use super::*;

    #[derive(Clone, Debug)]
    pub enum Statement {
        Let(LetStatement),
        Return(ReturnStatement),
        Break(BreakStatement),
        Expr(ExprStatement),
    }

    #[derive(Clone, Debug)]
    pub struct LetStatement {
        pub variable: StringId,
        pub value: ExprId,
    }

    #[derive(Clone, Debug)]
    pub struct ReturnStatement {
        pub expr: ExprId,
    }

    #[derive(Clone, Debug)]
    pub struct BreakStatement {
        pub expr: Option<ExprId>,
    }

    #[derive(Clone, Debug)]
    pub struct ExprStatement {
        pub expr: ExprId,
    }

    enum_conversion! {
        [Statement]
        Let: LetStatement,
        Return: ReturnStatement,
        Break: BreakStatement,
        Expr: ExprStatement,
    }
}

mod expr {
    use crate::enum_conversion;

    use super::*;

    #[derive(Clone, Debug)]
    pub enum Expr {
        Assign(Assign),
        Binary(Binary),
        Unary(Unary),
        If(If),
        Loop(Loop),
        Literal(Literal),
        Call(Call),
        Block(BlockId),
        Variable(Variable),
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
    pub struct If {
        pub conditions: Vec<(ExprId, BlockId)>,
        pub otherwise: Option<BlockId>,
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
        pub variable: StringId,
    }

    enum_conversion! {
        [Expr]
        Assign: Assign,
        Binary: Binary,
        Unary: Unary,
        If: If,
        Loop: Loop,
        Literal: Literal,
        Call: Call,
        Block: BlockId,
        Variable: Variable,
    }
}
