use crate::lex::tok;

pub use self::{expr::*, function::*, statement::*, util::*};

/// Root node, representing a program.
#[derive(Clone, Debug)]
pub struct Program {
    /// All items contained within this program.
    pub items: Vec<Item>,
}

impl Program {
    pub const fn new() -> Self {
        Self { items: Vec::new() }
    }

    pub fn add_function_declaration(&mut self, function_declaration: FunctionDeclaration) {
        self.items
            .push(Item::FunctionDeclaration(function_declaration))
    }
}

/// A node which may appear at the top-level of a program.
#[derive(Clone, Debug)]
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
    #[derive(Clone, Debug)]
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
    #[derive(Clone, Debug)]
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
    #[derive(Clone, Debug)]
    pub struct FunctionReturnType {
        pub tok_thin_arrow: tok::ThinArrow,
        /// Return type.
        pub ty: tok::Ident,
    }
}

/// Block, containing a collection of [`Statement`]s.
#[derive(Clone, Debug)]
pub struct Block {
    pub tok_l_brace: tok::LBrace,
    /// Collection of statements.
    pub statements: Vec<Statement>,
    pub tok_r_brace: tok::RBrace,
}

mod statement {
    use crate::enum_conversion;

    use super::*;

    /// A statement present within a [`Block`].
    #[derive(Clone, Debug)]
    pub enum Statement {
        Let(LetStatement),
        Return(ReturnStatement),
        Expr(ExprStatement),
    }

    /// A `let` statement creates a new binding (`name`), and assigns `value` to it.
    #[derive(Clone, Debug)]
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
    #[derive(Clone, Debug)]
    pub struct ReturnStatement {
        pub tok_return: tok::Return,
        /// Value that is being returned.
        pub value: Expr,
        pub tok_semicolon: tok::SemiColon,
    }

    /// An in-place expression, followed by an optional semicolon.
    #[derive(Clone, Debug)]
    pub struct ExprStatement {
        /// Expression.
        pub expr: Expr,
        /// Can be optionally terminated by semicolon.
        pub tok_semicolon: Option<tok::SemiColon>,
    }

    enum_conversion! {
        [Statement]
        Let: LetStatement,
        Return: ReturnStatement,
        Expr: ExprStatement,
    }
}

mod expr {
    use crate::enum_conversion;

    use super::*;

    /// All possible expressions.
    #[derive(Clone, Debug)]
    pub enum Expr {
        Assign(Assign),
        Binary(Binary),
        Unary(Unary),
        If(If),
        Literal(Literal),
        Paren(Paren),
        Call(Call),
        Block(Block),
        Variable(Variable),
    }

    /// Assignment.
    ///
    /// ```
    /// some_var = 1 + 2
    /// ```
    #[derive(Clone, Debug)]
    pub struct Assign {
        /// Variable being assigned to.
        pub assignee: Box<Expr>,
        pub tok_eq: tok::Eq,
        /// Value of the assignment.
        pub value: Box<Expr>,
    }

    /// Binary operation.
    #[derive(Clone, Debug)]
    pub struct Binary {
        /// Left hand side of the operation.
        pub lhs: Box<Expr>,
        /// Binary operation.
        pub op: BinaryOp,
        /// Right hand side of the operation.
        pub rhs: Box<Expr>,
    }

    /// All possible binary operations.
    #[derive(Clone, Debug)]
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
    #[derive(Clone, Debug)]
    pub struct Unary {
        /// Unary operation.
        pub op: UnaryOp,
        /// Operation value.
        pub value: Box<Expr>,
    }

    /// All possible unary operations.
    #[derive(Clone, Debug)]
    pub enum UnaryOp {
        Not(tok::Bang),
        Negative(tok::Minus),
        Deref(tok::Asterisk),
        Ref(tok::Amp),
    }

    /// An `if` statement
    #[derive(Clone, Debug)]
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
    #[derive(Clone, Debug)]
    pub struct IfTrailer {
        pub tok_else: tok::Else,
        /// Can be followed by `if` with another condition, or a final block.
        pub if_or_block: IfOrBlock,
    }

    /// A nested [`If`] statement, or a [`Block`]. Used to terminate in [`IfTrailer`].
    #[derive(Clone, Debug)]
    pub enum IfOrBlock {
        If(Box<If>),
        Block(Block),
    }

    impl From<If> for IfOrBlock {
        fn from(value: If) -> Self {
            Self::If(Box::new(value))
        }
    }
    impl From<Block> for IfOrBlock {
        fn from(value: Block) -> Self {
            Self::Block(value)
        }
    }

    /// Any kind of literal.
    #[derive(Clone, Debug)]
    pub enum Literal {
        /// An integer.
        Integer(IntegerLiteral),
        /// A boolean.
        Boolean(BooleanLiteral),
    }

    /// An integer literal.
    #[derive(Clone, Debug)]
    pub struct IntegerLiteral(pub tok::IntLit);

    impl IntegerLiteral {
        pub fn as_usize(&self) -> usize {
            self.0.0
        }
    }

    /// A boolean literal.
    #[derive(Clone, Debug)]
    pub enum BooleanLiteral {
        True(tok::True),
        False(tok::False),
    }

    impl BooleanLiteral {
        pub fn as_bool(&self) -> bool {
            match self {
                BooleanLiteral::True(_) => true,
                BooleanLiteral::False(_) => false,
            }
        }
    }

    enum_conversion! {
        [Literal]
        Integer: IntegerLiteral,
        Boolean: BooleanLiteral,
    }

    /// An [`Expr`] wrapped in parentheses.
    #[derive(Clone, Debug)]
    pub struct Paren {
        pub tok_l_paren: tok::LParen,
        /// Inner expression.
        pub expr: Box<Expr>,
        pub tok_r_paren: tok::RParen,
    }

    /// Call expression.
    #[derive(Clone, Debug)]
    pub struct Call {
        /// Callee of the function.
        pub callee: Box<Expr>,
        pub tok_l_paren: tok::LParen,
        /// Arguments passed to the call.
        pub arguments: PunctuatedList<Expr, tok::Comma>,
        pub tok_r_paren: tok::RParen,
    }

    /// Variable reference.
    #[derive(Clone, Debug)]
    pub struct Variable {
        /// Variable binding.
        pub variable: tok::Ident,
    }

    enum_conversion! {
        [Expr]
        Assign: Assign,
        Binary: Binary,
        Unary: Unary,
        If: If,
        Literal: Literal,
        Paren: Paren,
        Call: Call,
        Block: Block,
        Variable: Variable,
    }
}

mod util {
    /// A punctuated list, with optional trailing punctuation.
    #[derive(Clone, Debug)]
    pub struct PunctuatedList<T, P> {
        pub items: Vec<T>,
        pub punctuation: Vec<P>,
    }

    impl<T, P> PunctuatedList<T, P> {
        /// Create an empty punctuated list.
        pub fn new() -> Self {
            Self {
                items: Vec::new(),
                punctuation: Vec::new(),
            }
        }

        /// Add an item to the list. Will return an error if not expecting an item.
        pub fn add_item(&mut self, item: T) -> Result<(), PunctuatedListError> {
            if !self.expecting_item() {
                return Err(PunctuatedListError::ExpectedPunctuation);
            }

            self.items.push(item);

            Ok(())
        }

        /// Add a punctuation to the list. Will return an error if not expecting a punctuation.
        pub fn add_punctuation(&mut self, punctuation: P) -> Result<(), PunctuatedListError> {
            if self.expecting_item() {
                return Err(PunctuatedListError::ExpectedItem);
            }

            self.punctuation.push(punctuation);

            Ok(())
        }

        /// Determine if ready for an item.
        fn expecting_item(&self) -> bool {
            self.items.len() == self.punctuation.len()
        }

        pub fn iter_items(&self) -> impl Iterator<Item = &T> {
            self.items.iter()
        }
    }

    #[derive(Clone, Debug)]
    pub enum PunctuatedListError {
        ExpectedItem,
        ExpectedPunctuation,
    }
}
