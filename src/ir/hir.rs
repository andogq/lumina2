use crate::prelude::*;

pub use self::{block::*, expression::*, functions::*, statement::*};

create_id!(BlockId);
create_id!(ExpressionId);
create_id!(FunctionId);
create_id!(StatementId);

#[derive(Clone, Debug, Default)]
pub struct Hir {
    pub functions: IndexedVec<FunctionId, Function>,
    pub blocks: IndexedVec<BlockId, Block>,
    pub statements: IndexedVec<StatementId, Statement>,
    pub expressions: IndexedVec<ExpressionId, Expression>,
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

impl Index<ExpressionId> for Hir {
    type Output = Expression;

    fn index(&self, index: ExpressionId) -> &Self::Output {
        &self.expressions[index]
    }
}

mod functions {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Function {
        pub binding: IdentifierBindingId,
        pub parameters: Vec<(IdentifierBindingId, TypeId)>,
        pub return_ty: TypeId,
        pub entry: BlockId,
    }
}

mod block {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Block {
        pub statements: Vec<StatementId>,
        pub expression: ExpressionId,
    }
}

mod statement {
    use super::*;

    #[derive(Clone, Debug)]
    pub enum Statement {
        Declare(DeclareStatement),
        Return(ReturnStatement),
        Break(BreakStatement),
        Expression(ExpressionStatement),
    }

    #[derive(Clone, Debug)]
    pub struct DeclareStatement {
        pub binding: IdentifierBindingId,
        pub ty: DeclarationTy,
    }

    #[derive(Clone, Debug)]
    pub enum DeclarationTy {
        #[cfg_attr(
            not(test),
            expect(
                dead_code,
                reason = "will be used when variable declarations can be explicitly typed."
            )
        )]
        Type(TypeId),
        Inferred(ExpressionId),
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
}

mod expression {
    use super::*;

    #[derive(Clone, Debug)]
    pub enum Expression {
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
        Aggregate(Aggregate),
        Field(Field),
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
    pub struct Switch {
        pub discriminator: ExpressionId,
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
    }

    #[derive(Clone, Debug)]
    pub struct Call {
        pub callee: ExpressionId,
        pub arguments: Vec<ExpressionId>,
    }

    #[derive(Clone, Debug)]
    pub struct Variable {
        pub binding: IdentifierBindingId,
    }

    #[derive(Clone, Debug)]
    pub struct Aggregate {
        pub values: Vec<ExpressionId>,
    }
    impl Aggregate {
        pub const UNIT: Self = Self { values: Vec::new() };
    }

    #[derive(Clone, Debug)]
    pub struct Field {
        pub lhs: ExpressionId,
        pub field: usize,
    }

    enum_conversion! {
        [Expression]
        Assign: Assign,
        Binary: Binary,
        Unary: Unary,
        Switch: Switch,
        Loop: Loop,
        Literal: Literal,
        Call: Call,
        Block: BlockId,
        Variable: Variable,
        Aggregate: Aggregate,
        Field: Field,
    }
}
