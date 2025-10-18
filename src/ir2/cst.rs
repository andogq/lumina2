use crate::lex::{Tok, tok};

pub use self::{expr::*, function::*, statement::*, util::*};

/// Root node, representing a program.
pub struct Program {
    /// All items contained within this program.
    pub items: Vec<Item>,
}

/// A node which may appear at the top-level of a program.
pub enum Item {
    FunctionDeclaration(FunctionDeclaration),
}

mod function {
    use super::*;

    /// Function declaration.
    ///
    /// ```
    /// fn some_function(param_a: usize, param_b: bool) -> f64 {
    ///     // Statements...
    /// }
    /// ```
    pub struct FunctionDeclaration {
        pub tok_fn: tok::Fn,
        /// Name of the function.
        pub name: tok::Ident,
        pub tok_lparen: tok::LParen,
        /// Parameters for the function.
        pub params: PunctuatedList<FunctionParameter, tok::Comma>,
        pub tok_rparan: tok::RParen,
        /// Optional return type for the function.
        pub return_ty: Option<FunctionReturnType>,
        pub body: Block,
    }

    /// Parameter for a function declaration.
    ///
    /// ```
    /// param: ty
    /// ```
    pub struct FunctionParameter {
        /// Name of the parameter.
        pub name: tok::Ident,
        pub tok_colon: tok::Colon,
        /// Type of the parameter.
        pub ty: tok::Ident,
    }

    /// Return type for a function declaration.
    ///
    /// ```
    /// -> ty
    /// ```
    pub struct FunctionReturnType {
        pub tok_thin_arrow: tok::ThinArrow,
        /// Return type.
        pub ty: tok::Ident,
    }
}

/// Block, containing a collection of [`Statement`]s.
pub struct Block {
    pub tok_l_brace: tok::LBrace,
    /// Collection of statements.
    pub statements: Vec<Statement>,
    pub tok_r_brace: tok::RBrace,
}

mod statement {
    use super::*;

    /// A statement present within a [`Block`].
    pub enum Statement {
        Let(LetStatement),
        Return(ReturnStatement),
        Expr(ExprStatement),
    }

    /// A `let` statement creates a new binding (`name`), and assigns `value` to it.
    pub struct LetStatement {
        pub tok_let: tok::Let,
        /// Name of the variable.
        pub variable: tok::Ident,
        pub tok_eq: tok::Eq,
        /// Value that was assigned.
        pub value: Expr,
        pub tok_semicolon: tok::SemiColon,
    }

    /// A `return` statement returns `value`.
    pub struct ReturnStatement {
        pub tok_return: tok::Return,
        /// Value that is being returned.
        pub value: Expr,
        pub tok_semicolon: tok::SemiColon,
    }

    /// An in-place expression, followed by an optional semicolon.
    pub struct ExprStatement {
        /// Expression.
        pub expr: Expr,
        /// Can be optionally terminated by semicolon.
        pub tok_semicolon: Option<tok::SemiColon>,
    }
}

mod expr {
    use super::*;

    /// All possible expressions.
    pub enum Expr {
        Assign(Assign),
        Binary(Binary),
        Unary(Unary),
        If(If),
        Literal(Literal),
        Paren(Paren),
        Call(Call),
        Variable(Variable),
    }

    /// Assignment.
    ///
    /// ```
    /// some_var = 1 + 2
    /// ```
    pub struct Assign {
        /// Variable being assigned to.
        pub variable: tok::Ident,
        pub tok_eq: tok::Eq,
        /// Value of the assignment.
        pub value: Box<Expr>,
    }

    /// Binary operation.
    pub struct Binary {
        /// Left hand side of the operation.
        pub lhs: Box<Expr>,
        /// Binary operation.
        pub op: BinaryOp,
        /// Right hand side of the operation.
        pub rhs: Box<Expr>,
    }

    /// All possible binary operations.
    pub enum BinaryOp {
        Plus(tok::Plus),
        Minus(tok::Minus),
        Multiply(tok::Asterisk),
        Divide(tok::Slash),

        LogicalAnd(tok::AmpAmp),
        LogicalOr(tok::BarBar),

        BinaryAnd(tok::Amp),
        BinaryOr(tok::Bar),

        Equal(tok::EqEq),
        NotEqual(tok::BangEq),
        Less(tok::LAngle),
        LessEqual(tok::LtEq),
        Greater(tok::RAngle),
        GreaterEqual(tok::GtEq),
    }

    /// Unary operation.
    pub struct Unary {
        /// Unary operation.
        pub op: UnaryOp,
        /// Operation value.
        pub value: Box<Expr>,
    }

    /// All possible unary operations.
    pub enum UnaryOp {
        Not(tok::Bang),
        Negative(tok::Minus),
        Deref(tok::Asterisk),
        Ref(tok::Amp),
    }

    /// An `if` statement
    pub struct If {
        pub tok_if: tok::If,
        /// Condition that is being checked.
        pub condition: Box<Expr>,
        /// Block if the condition passes.
        pub then: Block,
        /// Optional trailing content of statement.
        pub trailer: Option<IfTrailer>,
    }

    /// Optional trailing section of an `if` statement.
    pub struct IfTrailer {
        pub tok_else: tok::Else,
        /// Can be followed by `if` with another condition, or a final block.
        pub if_or_block: IfOrBlock,
    }

    /// A nested [`If`] statement, or a [`Block`]. Used to terminate in [`IfTrailer`].
    pub enum IfOrBlock {
        If(Box<If>),
        Block(Block),
    }

    /// Any kind of literal.
    pub enum Literal {
        /// An integer.
        Integer(IntegerLiteral),
        /// A boolean.
        Boolean(BooleanLiteral),
    }

    /// An integer literal.
    pub struct IntegerLiteral(tok::IntLit);

    /// A boolean literal.
    pub enum BooleanLiteral {
        True(tok::True),
        False(tok::False),
    }

    /// An [`Expr`] wrapped in parentheses.
    pub struct Paren {
        pub tok_l_paren: tok::LParen,
        /// Inner expression.
        pub expr: Box<Expr>,
        pub tok_r_paren: tok::RParen,
    }

    /// Call expression.
    pub struct Call {
        /// Callee of the function.
        pub callee: Box<Expr>,
        pub tok_l_paren: tok::LParen,
        /// Arguments passed to the call.
        pub arguments: PunctuatedList<Expr, tok::Comma>,
        pub tok_r_paren: tok::RParen,
    }

    /// Variable reference.
    pub struct Variable {
        /// Variable binding.
        pub variable: tok::Ident,
    }
}

mod util {
    /// A punctuated list, with optional trailing punctuation.
    pub struct PunctuatedList<T, P> {
        pub items: Vec<T>,
        pub punctuation: Vec<P>,
    }
}
