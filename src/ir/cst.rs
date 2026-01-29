use crate::prelude::*;

pub use self::{
    expression::{BinaryOperation, UnaryOperation, *},
    function::*,
    statement::*,
    ty::*,
    util::*,
};

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
}

/// A node which may appear at the top-level of a program.
#[derive(Clone, Debug)]
pub struct Item {
    /// Annotations attached to this item.
    pub annotations: Vec<Annotation>,
    /// The actual item.
    pub kind: ItemKind,
}

#[derive(Clone, Debug)]
pub enum ItemKind {
    TraitDeclaration(TraitDeclaration),
    TraitImplementation(TraitImplementation),
    FunctionDeclaration(FunctionDeclaration),
}

/// An annotation the source, which may or may not have a value.
///
/// ```
/// @some_annotation
///
/// @some_annotation(with_value)
/// ```
#[derive(Clone, Debug)]
pub struct Annotation {
    #[expect(dead_code, reason = "token field")]
    pub tok_at: tok::At,
    /// Key of the annotation.
    pub key: tok::Ident,
    /// Value of the annotation.
    pub value: AnnotationValue,
}

/// Value for an annotation.
#[derive(Clone, Debug)]
pub enum AnnotationValue {
    /// No value.
    None,
    /// Value within parenthesis.
    Value {
        #[expect(dead_code, reason = "token field")]
        tok_l_parenthesis: tok::LParenthesis,
        value: tok::Ident,
        #[expect(dead_code, reason = "token field")]
        tok_r_parenthesis: tok::RParenthesis,
    },
}

/// Trait declaration.
///
/// ```
/// trait MyTrait {
///     fn a() -> bool;
///     fn b(n: i32);
/// }
/// ```
#[derive(Clone, Debug)]
pub struct TraitDeclaration {
    #[expect(dead_code, reason = "token field")]
    pub tok_trait: tok::Trait,
    pub name: tok::Ident,
    #[expect(dead_code, reason = "token field")]
    pub tok_l_brace: tok::LBrace,
    pub methods: Vec<(FunctionSignature, tok::SemiColon)>,
    #[expect(dead_code, reason = "token field")]
    pub tok_r_brace: tok::RBrace,
}

/// Trait implementation.
///
/// ```
/// impl MyTrait for SomeType {
///     fn a() -> bool {
///         true
///     }
///
///     fn b(n: 123) { }
/// }
/// ```
#[derive(Clone, Debug)]
pub struct TraitImplementation {
    #[expect(dead_code, reason = "token field")]
    pub tok_impl: tok::Impl,
    pub name: tok::Ident,
    #[expect(dead_code, reason = "named fields will be implemented with struct")]
    pub tok_for: tok::For,
    pub ty: CstType,
    #[expect(dead_code, reason = "token field")]
    pub tok_l_brace: tok::LBrace,
    pub methods: Vec<FunctionDeclaration>,
    #[expect(dead_code, reason = "token field")]
    pub tok_r_brace: tok::RBrace,
}

mod function {
    use super::*;

    /// Function signature.
    ///
    /// ```
    /// fn some_function(parameter_a: usize, parameter_b: bool) -> f64
    /// ```
    #[derive(Clone, Debug)]
    pub struct FunctionSignature {
        #[expect(dead_code, reason = "token field")]
        pub tok_fn: tok::Fn,
        /// Name of the function.
        pub name: tok::Ident,
        #[expect(dead_code, reason = "token field")]
        pub tok_l_parenthesis: tok::LParenthesis,
        /// Parameters for the function.
        pub parameters: PunctuatedList<FunctionParameter, tok::Comma>,
        #[expect(dead_code, reason = "token field")]
        pub tok_r_parenthesis: tok::RParenthesis,
        /// Optional return type for the function.
        pub return_ty: Option<FunctionReturnType>,
    }

    /// Function declaration.
    ///
    /// ```
    /// fn some_function(parameter_a: usize, parameter_b: bool) -> f64 {
    ///     // Statements...
    /// }
    /// ```
    #[derive(Clone, Debug)]
    pub struct FunctionDeclaration {
        /// Signature of the function.
        pub signature: FunctionSignature,
        /// Implementation of the function.
        pub body: Block,
    }

    /// Parameter for a function declaration.
    ///
    /// ```
    /// parameter: ty
    /// ```
    #[derive(Clone, Debug)]
    pub struct FunctionParameter {
        /// Name of the parameter.
        pub name: tok::Ident,
        #[expect(dead_code, reason = "token field")]
        pub tok_colon: tok::Colon,
        /// Type of the parameter.
        pub ty: CstType,
    }

    /// Return type for a function declaration.
    ///
    /// ```
    /// -> ty
    /// ```
    #[derive(Clone, Debug)]
    pub struct FunctionReturnType {
        #[expect(dead_code, reason = "token field")]
        pub tok_thin_arrow: tok::ThinArrow,
        /// Return type.
        pub ty: CstType,
    }
}

/// Block, containing a collection of [`Statement`]s.
#[derive(Clone, Debug)]
pub struct Block {
    #[expect(dead_code, reason = "token field")]
    pub tok_l_brace: tok::LBrace,
    /// Collection of statements.
    pub statements: Vec<Statement>,
    #[expect(dead_code, reason = "token field")]
    pub tok_r_brace: tok::RBrace,
}

/// Tuple of items. Used for both a tuple of [`Expression`], and a tuple of [`CstType`].
#[derive(Clone, Debug)]
pub struct Tuple<T> {
    #[expect(dead_code, reason = "token field")]
    pub tok_l_parenthesis: tok::LParenthesis,
    pub items: PunctuatedList<T, tok::Comma>,
    #[expect(dead_code, reason = "token field")]
    pub tok_r_parenthesis: tok::RParenthesis,
}

mod ty {
    use super::*;

    /// A type, such as for parameters or variable declarations.
    #[derive(Clone, Debug)]
    pub enum CstType {
        /// A named type represented with a single [`tok::Ident`], such as `i8`.
        Named(tok::Ident),
        /// A tuple type, composed of many inner [`CstType`]s.
        Tuple(Tuple<CstType>),
    }

    enum_conversion! {
        [CstType]
        Named: tok::Ident,
        Tuple: Tuple<CstType>,
    }
}

mod statement {
    use super::*;

    /// A statement present within a [`Block`].
    #[derive(Clone, Debug)]
    pub enum Statement {
        Let(LetStatement),
        Return(ReturnStatement),
        Break(BreakStatement),
        Expression(ExpressionStatement),
    }

    /// A `let` statement creates a new binding (`name`), and assigns `value` to it.
    #[derive(Clone, Debug)]
    pub struct LetStatement {
        #[expect(dead_code, reason = "token field")]
        pub tok_let: tok::Let,
        /// Name of the variable.
        pub variable: tok::Ident,
        #[expect(dead_code, reason = "token field")]
        pub tok_eq: tok::Eq,
        /// Value that was assigned.
        pub value: Expression,
        #[expect(dead_code, reason = "token field")]
        pub tok_semicolon: tok::SemiColon,
    }

    /// A `return` statement returns `value`.
    #[derive(Clone, Debug)]
    pub struct ReturnStatement {
        #[expect(dead_code, reason = "token field")]
        pub tok_return: tok::Return,
        /// Value that is being returned.
        pub value: Option<Expression>,
        #[expect(dead_code, reason = "token field")]
        pub tok_semicolon: tok::SemiColon,
    }

    #[derive(Clone, Debug)]
    pub struct BreakStatement {
        #[expect(dead_code, reason = "token field")]
        pub tok_break: tok::Break,
        pub value: Option<Expression>,
        #[expect(dead_code, reason = "token field")]
        pub tok_semicolon: tok::SemiColon,
    }

    /// An in-place expression, followed by an optional semicolon.
    #[derive(Clone, Debug)]
    pub struct ExpressionStatement {
        /// Expression.
        pub expression: Expression,
        /// Can be optionally terminated by semicolon.
        pub tok_semicolon: Option<tok::SemiColon>,
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

    /// All possible expressions.
    #[derive(Clone, Debug)]
    pub enum Expression {
        Assign(Assign),
        Binary(Binary),
        Unary(Unary),
        If(If),
        // While(While),
        Loop(Loop),
        Literal(Literal),
        Parenthesis(Parenthesis),
        Call(Call),
        Block(Block),
        Variable(Variable),
        Tuple(Tuple<Expression>),
        Field(Field),
        QualifiedPath(QualifiedPath),
    }

    /// Assignment.
    ///
    /// ```
    /// some_var = 1 + 2
    /// ```
    #[derive(Clone, Debug)]
    pub struct Assign {
        /// Variable being assigned to.
        pub assignee: Box<Expression>,
        #[expect(dead_code, reason = "token field")]
        pub tok_eq: tok::Eq,
        /// Value of the assignment.
        pub value: Box<Expression>,
    }

    /// Binary operation.
    #[derive(Clone, Debug)]
    pub struct Binary {
        /// Left hand side of the operation.
        pub lhs: Box<Expression>,
        /// Binary operation.
        pub operation: BinaryOperation,
        /// Right hand side of the operation.
        pub rhs: Box<Expression>,
    }

    /// All possible binary operations.
    #[derive(Clone, Debug)]
    pub enum BinaryOperation {
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
        pub operation: UnaryOperation,
        /// Operation value.
        pub value: Box<Expression>,
    }

    /// All possible unary operations.
    #[derive(Clone, Debug)]
    pub enum UnaryOperation {
        Not(tok::Bang),
        Negative(tok::Minus),
        Deref(tok::Asterisk),
        Ref(tok::Amp),
    }

    /// An `if` statement
    #[derive(Clone, Debug)]
    pub struct If {
        #[expect(dead_code, reason = "token field")]
        pub tok_if: tok::If,
        /// Condition that is being checked.
        pub condition: Box<Expression>,
        /// Block if the condition passes.
        pub then: Block,
        /// Optional trailing content of statement.
        pub trailer: Option<IfTrailer>,
    }

    /// Optional trailing section of an `if` statement.
    #[derive(Clone, Debug)]
    pub struct IfTrailer {
        #[expect(dead_code, reason = "token field")]
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

    #[derive(Clone, Debug)]
    pub struct Loop {
        #[expect(dead_code, reason = "token field")]
        pub tok_loop: tok::Loop,
        pub body: Block,
    }

    // TODO: Implement while loops
    #[derive(Clone, Debug)]
    #[expect(dead_code, reason = "while statements will be implemented after loops")]
    pub struct While {
        pub tok_while: tok::While,
        pub condition: Box<Expression>,
        pub body: Block,
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
    pub struct IntegerLiteral(pub tok::IntegerLiteral);

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

    /// An [`Expression`] wrapped in parentheses.
    #[derive(Clone, Debug)]
    pub struct Parenthesis {
        #[expect(dead_code, reason = "token field")]
        pub tok_l_parenthesis: tok::LParenthesis,
        /// Inner expression.
        pub expression: Box<Expression>,
        #[expect(dead_code, reason = "token field")]
        pub tok_r_parenthesis: tok::RParenthesis,
    }

    /// Call expression.
    #[derive(Clone, Debug)]
    pub struct Call {
        /// Callee of the function.
        pub callee: Box<Expression>,
        #[expect(dead_code, reason = "token field")]
        pub tok_l_parenthesis: tok::LParenthesis,
        /// Arguments passed to the call.
        pub arguments: PunctuatedList<Expression, tok::Comma>,
        #[expect(dead_code, reason = "token field")]
        pub tok_r_parenthesis: tok::RParenthesis,
    }

    /// Variable reference.
    #[derive(Clone, Debug)]
    pub struct Variable {
        /// Variable binding.
        pub variable: tok::Ident,
    }

    /// Field access expression, such as `my_struct.field` or `my_tuple.0`.
    #[derive(Clone, Debug)]
    pub struct Field {
        pub lhs: Box<Expression>,
        #[expect(dead_code, reason = "token field")]
        pub tok_dot: tok::Dot,
        pub field: FieldKey,
    }

    /// Different accessors used within [`Field`].
    #[derive(Clone, Debug)]
    pub enum FieldKey {
        Unnamed(tok::IntegerLiteral),
        #[expect(dead_code, reason = "named fields will be implemented with struct")]
        Named(tok::Ident),
    }

    /// Qualified path.
    ///
    /// ```
    /// <Ty as Trait>::item
    /// ```
    #[derive(Clone, Debug)]
    pub struct QualifiedPath {
        #[expect(dead_code, reason = "named fields will be implemented with struct")]
        pub tok_l_angle: tok::LAngle,
        /// Self qualifier.
        pub ty: CstType,
        #[expect(dead_code, reason = "named fields will be implemented with struct")]
        pub tok_as: tok::As,
        /// Qualification.
        pub name: tok::Ident,
        #[expect(dead_code, reason = "named fields will be implemented with struct")]
        pub tok_r_angle: tok::RAngle,
        #[expect(dead_code, reason = "named fields will be implemented with struct")]
        pub tok_colon_colon: tok::ColonColon,
        /// Path item.
        pub item: tok::Ident,
    }

    enum_conversion! {
        [Expression]
        Assign: Assign,
        Binary: Binary,
        Unary: Unary,
        If: If,
        Loop: Loop,
        Literal: Literal,
        Parenthesis: Parenthesis,
        Call: Call,
        Block: Block,
        Variable: Variable,
        Tuple: Tuple<Expression>,
        Field: Field,
        QualifiedPath: QualifiedPath,
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

        /// Determine if the list has trailing punctuation.
        pub fn has_trailing(&self) -> bool {
            !self.items.is_empty() && self.items.len() == self.punctuation.len()
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
