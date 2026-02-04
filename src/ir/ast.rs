use std::collections::BTreeMap;

use crate::prelude::*;

pub use self::{block::*, expression::*, function::*, statement::*};

create_id!(BlockId);
create_id!(ExpressionId);
create_id!(FunctionId);
create_id!(StatementId);
create_id!(AstTypeId);
create_id!(TraitId);
create_id!(AnnotationId);

#[derive(Clone, Debug)]
pub struct Ast {
    pub function_declarations: IndexedVec<FunctionId, FunctionDeclaration>,

    pub blocks: IndexedVec<BlockId, Block>,
    pub statements: IndexedVec<StatementId, Statement>,
    pub expressions: IndexedVec<ExpressionId, Expression>,
    pub annotations: IndexedVec<AnnotationId, Annotation>,

    pub types: IndexedVec<AstTypeId, AstType>,

    /// Top-level function declarations.
    pub item_functions: Vec<FunctionId>,

    pub traits: IndexedVec<TraitId, Trait>,
    pub trait_implementations: Vec<TraitImplementation>,
}

impl Ast {
    pub fn new() -> Self {
        Self {
            function_declarations: IndexedVec::new(),
            blocks: IndexedVec::new(),
            statements: IndexedVec::new(),
            expressions: IndexedVec::new(),
            annotations: IndexedVec::new(),
            types: IndexedVec::new(),
            item_functions: Vec::new(),
            traits: IndexedVec::new(),
            trait_implementations: Vec::new(),
        }
    }
}

indexing! {
    Ast {
        function_declarations[FunctionId] -> FunctionDeclaration,
        blocks[BlockId] -> Block,
        statements[StatementId] -> Statement,
        expressions[ExpressionId] -> Expression,
        annotations[AnnotationId] -> Annotation,
        types[AstTypeId] -> AstType,
        traits[TraitId] -> Trait,
    }
}

/// Type representation used within the [`Ast`].
#[derive(Clone, Debug)]
pub enum AstType {
    /// Built-in alias for the type where this type representation is used.
    SelfType,
    /// A type referenced by a single interned name (eg. `i8`, `bool`).
    Named(StringId),
    /// A tuple type (`(i8, bool, u8)`).
    Tuple(Vec<AstTypeId>),
}

/// An annotation attached to an item.
#[derive(Clone, Debug)]
#[expect(dead_code, reason = "annotations not used yet")]
pub struct Annotation {
    /// Key of the annotation.
    pub key: StringId,
    /// Value of the annotation, which may or may not be present.
    pub value: Option<StringId>,
}

mod function {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct FunctionSignature {
        pub name: StringId,
        pub parameters: Vec<FunctionParameter>,
        pub return_ty: Option<AstTypeId>,
    }

    #[derive(Clone, Debug)]
    #[expect(dead_code, reason = "annotations not used yet")]
    pub struct FunctionDeclaration {
        pub annotations: Vec<AnnotationId>,
        pub signature: FunctionSignature,
        pub implementation: FunctionImplementation,
    }

    /// The implementation of a function.
    #[derive(Clone, Debug)]
    pub enum FunctionImplementation {
        /// No implementation has been provided for the function, although one may be added by a
        /// later stage.
        None,
        /// Implementation exists within the provided [`Block`].
        Body(BlockId),
    }

    #[derive(Clone, Debug)]
    pub struct FunctionParameter {
        pub name: StringId,
        pub ty: AstTypeId,
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
        Tuple(Tuple),
        Field(Field),
        QualifiedPath(QualifiedPath),
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

    #[derive(Clone, Debug)]
    pub struct Tuple {
        pub values: Vec<ExpressionId>,
    }
    impl Tuple {
        pub const UNIT: Self = Self { values: Vec::new() };
    }

    #[derive(Clone, Debug)]
    pub struct Field {
        pub lhs: ExpressionId,
        pub field: FieldKey,
    }

    #[derive(Clone, Debug)]
    pub enum FieldKey {
        Unnamed(usize),
    }

    #[derive(Clone, Debug)]
    pub struct QualifiedPath {
        pub ty: AstTypeId,
        pub name: StringId,
        pub item: StringId,
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
        Tuple: Tuple,
        Field: Field,
        QualifiedPath: QualifiedPath,
    }
}

#[derive(Clone, Debug)]
pub struct Trait {
    /// Annotations attached to this trait.
    #[expect(dead_code, reason = "annotations not used yet")]
    pub annotations: Vec<AnnotationId>,
    /// Original name of the trait.
    pub name: StringId,
    /// Methods defined within the trait.
    pub methods: BTreeMap<StringId, FunctionSignature>,
}

#[derive(Clone, Debug)]
pub struct TraitImplementation {
    /// Annotations attached to this trait implementation.
    #[expect(dead_code, reason = "annotations not used yet")]
    pub annotations: Vec<AnnotationId>,
    pub trait_name: StringId,
    pub target_ty: AstTypeId,
    pub methods: BTreeMap<StringId, FunctionId>,
}
