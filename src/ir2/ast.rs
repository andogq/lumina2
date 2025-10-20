use crate::ir2::cst::{BinaryOp, UnaryOp};

pub use self::{block::*, expr::*, function::*, statement::*, string_pool::*};

#[derive(Clone, Debug)]
pub struct Ast {
    pub function_declarations: Vec<FunctionDeclaration>,

    pub blocks: Vec<Block>,
    pub expressions: Vec<Expr>,

    pub strings: StringPool,
}

impl Ast {
    pub fn new() -> Self {
        Self {
            function_declarations: Vec::new(),
            blocks: Vec::new(),
            expressions: Vec::new(),
            strings: StringPool::new(),
        }
    }

    pub fn get_block(&self, block: BlockId) -> &Block {
        &self.blocks[block.0]
    }

    pub fn get_expr(&self, expr: ExprId) -> &Expr {
        &self.expressions[expr.0]
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

    #[derive(Clone, Copy, Debug)]
    pub struct BlockId(pub(super) usize);

    impl BlockId {
        pub fn new(id: usize) -> Self {
            Self(id)
        }
    }

    #[derive(Clone, Debug)]
    pub struct Block {
        pub statements: Vec<Statement>,
        pub expression: Option<ExprId>,
    }
}

mod statement {
    use super::*;

    #[derive(Clone, Debug)]
    pub enum Statement {
        Let(LetStatement),
        Return(ReturnStatement),
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
    pub struct ExprStatement {
        pub expr: ExprId,
    }

    impl From<LetStatement> for Statement {
        fn from(value: LetStatement) -> Self {
            Self::Let(value)
        }
    }
    impl From<ReturnStatement> for Statement {
        fn from(value: ReturnStatement) -> Self {
            Self::Return(value)
        }
    }
    impl From<ExprStatement> for Statement {
        fn from(value: ExprStatement) -> Self {
            Self::Expr(value)
        }
    }
}

mod expr {
    use crate::enum_conversion;

    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct ExprId(pub(super) usize);

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
        If(If),
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
        Literal: Literal,
        Call: Call,
        Block: BlockId,
        Variable: Variable,
    }
}

mod string_pool {
    use std::collections::HashMap;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct StringId(usize);
    impl StringId {
        pub fn new(id: usize) -> Self {
            Self(id)
        }
    }

    #[derive(Clone, Debug)]
    pub struct StringPool {
        lookup: HashMap<String, StringId>,
        strings: Vec<String>,
    }

    impl StringPool {
        pub fn new() -> Self {
            Self {
                lookup: HashMap::new(),
                strings: Vec::new(),
            }
        }

        pub fn intern(&mut self, s: impl ToString) -> StringId {
            let s = s.to_string();

            if let Some(id) = self.lookup.get(&s) {
                return *id;
            }

            let id = StringId(self.strings.len());
            self.strings.push(s.clone());
            self.lookup.insert(s, id);
            id
        }

        pub fn get(&self, index: StringId) -> &str {
            &self.strings[index.0]
        }
    }
}
