use crate::prelude::*;

pub use self::{block::*, expression::*, function::*, statement::*};

create_id!(BlockId);
create_id!(ExpressionId);
create_id!(FunctionId);
create_id!(StatementId);

#[derive(Clone, Debug)]
pub struct Ast {
    pub function_declarations: IndexedVec<FunctionId, FunctionDeclaration>,

    pub blocks: IndexedVec<BlockId, Block>,
    pub statements: IndexedVec<StatementId, Statement>,
    pub expressions: IndexedVec<ExpressionId, Expression>,
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

impl Index<ExpressionId> for Ast {
    type Output = Expression;

    fn index(&self, index: ExpressionId) -> &Self::Output {
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
        pub parameters: Vec<FunctionParameter>,
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
        pub expression: Option<ExpressionId>,
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
        Expression(ExpressionStatement),
    }

    #[derive(Clone, Debug)]
    pub struct LetStatement {
        pub variable: StringId,
        pub value: ExpressionId,
    }

    #[derive(Clone, Debug)]
    pub struct ReturnStatement {
        pub expression: ExpressionId,
    }

    #[derive(Clone, Debug)]
    pub struct BreakStatement {
        pub expression: ExpressionId,
    }

    #[derive(Clone, Debug)]
    pub struct ExpressionStatement {
        pub expression: ExpressionId,
    }

    enum_conversion! {
        [Statement]
        Let: LetStatement,
        Return: ReturnStatement,
        Break: BreakStatement,
        Expression: ExpressionStatement,
    }
}

mod expression {
    use super::*;

    #[derive(Clone, Debug)]
    pub enum Expression {
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
        pub variable: ExpressionId,
        pub value: ExpressionId,
    }

    #[derive(Clone, Debug)]
    pub struct Binary {
        pub lhs: ExpressionId,
        pub operation: BinaryOperation,
        pub rhs: ExpressionId,
    }

    #[derive(Clone, Debug)]
    pub struct Unary {
        pub operation: UnaryOperation,
        pub value: ExpressionId,
    }

    #[derive(Clone, Debug)]
    pub struct If {
        pub conditions: Vec<(ExpressionId, BlockId)>,
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
        pub callee: ExpressionId,
        pub arguments: Vec<ExpressionId>,
    }

    #[derive(Clone, Debug)]
    pub struct Variable {
        pub variable: StringId,
    }

    enum_conversion! {
        [Expression]
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
