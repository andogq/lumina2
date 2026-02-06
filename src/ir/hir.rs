use crate::prelude::*;

pub use self::{block::*, expression::*, functions::*, statement::*};

create_id!(HirId);
create_id!(BlockId);
create_id!(ExpressionId);
create_id!(FunctionId);
create_id!(StatementId);
create_id!(TraitId);
create_id!(TraitMethodId);

#[derive(Clone, Debug, Default)]
pub struct Hir {
    nodes: IndexedVec<HirId, HirNodePtr>,
    pub functions: IndexedVec<FunctionId, Function>,
    pub blocks: IndexedVec<BlockId, Block>,
    pub statements: IndexedVec<StatementId, Statement>,
    pub expressions: IndexedVec<ExpressionId, Expression>,
    pub traits: IndexedVec<TraitId, Trait>,
    pub trait_implementations: HashMap<TraitImplementationKey, TraitImplementation>,
}

impl Hir {
    pub fn new() -> Self {
        Self::default()
    }

    /// Determine the next [`HirId`] by looking at the length of [`Self::nodes`].
    fn next_id(&self) -> HirId {
        HirId::from_id(self.nodes.len())
    }

    /// Add a [`Function`] to the HIR.
    pub fn add_function(
        &mut self,
        binding: IdentifierBindingId,
        signature: FunctionSignature,
        entry: BlockId,
    ) -> FunctionId {
        let id = self.next_id();
        let function_id = self.functions.insert(Function {
            id,
            binding,
            signature,
            entry,
        });
        self.nodes.insert(function_id.into());
        function_id
    }

    /// Add a [`Block`] to the HIR.
    pub fn add_block(&mut self, statements: Vec<StatementId>, expression: ExpressionId) -> BlockId {
        let id = self.next_id();
        let block_id = self.blocks.insert(Block {
            id,
            statements,
            expression,
        });
        self.nodes.insert(block_id.into());
        block_id
    }

    /// Add a [`Statement`] to the HIR.
    pub fn add_statement(&mut self, statement: impl Into<StatementKind>) -> StatementId {
        let id = self.next_id();
        let statement_id = self.statements.insert(Statement {
            id,
            kind: statement.into(),
        });
        self.nodes.insert(statement_id.into());
        statement_id
    }

    /// Add an [`Expression`] to the HIR.
    pub fn add_expression(&mut self, expression: impl Into<ExpressionKind>) -> ExpressionId {
        let id = self.next_id();
        let expression_id = self.expressions.insert(Expression {
            id,
            kind: expression.into(),
        });
        self.nodes.insert(expression_id.into());
        expression_id
    }

    /// Add a [`Trait`] to the HIR.
    pub fn add_trait(
        &mut self,
        name: TraitBindingId,
        method_scope: ScopeId,
        method_bindings: HashMap<IdentifierBindingId, TraitMethodId>,
        methods: IndexedVec<TraitMethodId, FunctionSignature<MaybeSelfType>>,
    ) -> TraitId {
        let id = self.next_id();
        let trait_id = self.traits.insert(Trait {
            id,
            name,
            method_scope,
            method_bindings,
            methods,
        });
        self.nodes.insert(trait_id.into());
        trait_id
    }
}

indexing! {
    Hir {
        functions[FunctionId] -> Function,
        blocks[BlockId] -> Block,
        statements[StatementId] -> Statement,
        expressions[ExpressionId] -> Expression,
        traits[TraitId] -> Trait,
    }
}

impl Index<&TraitImplementationKey> for Hir {
    type Output = TraitImplementation;

    fn index(&self, index: &TraitImplementationKey) -> &Self::Output {
        &self.trait_implementations[index]
    }
}

#[derive(Clone, Debug)]
pub enum HirNodePtr {
    Function(FunctionId),
    Block(BlockId),
    Statement(StatementId),
    Expression(ExpressionId),
    Trait(TraitId),
}

enum_conversion! {
    [HirNodePtr]
    Function: FunctionId,
    Block: BlockId,
    Statement: StatementId,
    Expression: ExpressionId,
    Trait: TraitId,
}

mod functions {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct FunctionSignature<Type = TypeId> {
        pub parameters: Vec<(IdentifierBindingId, Type)>,
        pub return_ty: Type,
    }

    impl FunctionSignature<MaybeSelfType> {
        /// Substitute any occurrences of `Self` with the provided type.
        pub fn with_self(self, current_self: TypeId) -> FunctionSignature {
            FunctionSignature {
                parameters: self
                    .parameters
                    .into_iter()
                    .map(|(binding, ty)| (binding, ty.with_self(current_self)))
                    .collect(),
                return_ty: self.return_ty.with_self(current_self),
            }
        }

        /// Resolve all types, ensuring `Self` isn't present.
        pub fn without_self(self) -> Option<FunctionSignature> {
            Some(FunctionSignature {
                parameters: self
                    .parameters
                    .into_iter()
                    .map(|(binding, ty)| Some((binding, ty.without_self()?)))
                    .collect::<Option<_>>()?,
                return_ty: self.return_ty.without_self()?,
            })
        }
    }

    #[derive(Clone, Debug)]
    pub struct Function {
        pub id: HirId,
        pub binding: IdentifierBindingId,
        pub signature: FunctionSignature,
        pub entry: BlockId,
    }
}

mod block {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Block {
        pub id: HirId,
        pub statements: Vec<StatementId>,
        pub expression: ExpressionId,
    }
}

mod statement {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Statement {
        pub id: HirId,
        pub kind: StatementKind,
    }

    #[derive(Clone, Debug)]
    pub enum StatementKind {
        Declare(DeclareStatement),
        Return(ReturnStatement),
        Break(BreakStatement),
        Expression(ExpressionStatement),
    }

    impl Deref for Statement {
        type Target = StatementKind;

        fn deref(&self) -> &Self::Target {
            &self.kind
        }
    }

    enum_conversion! {
        [StatementKind]
        Declare: DeclareStatement,
        Return: ReturnStatement,
        Break: BreakStatement,
        Expression: ExpressionStatement,
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
    pub struct Expression {
        pub id: HirId,
        pub kind: ExpressionKind,
    }

    impl Deref for Expression {
        type Target = ExpressionKind;

        fn deref(&self) -> &Self::Target {
            &self.kind
        }
    }

    #[derive(Clone, Debug)]
    pub enum ExpressionKind {
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
        Path(Path),
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

    /// A qualified path to a trait with an item.
    ///
    /// ```
    /// <Ty as TargetTrait>::item
    /// ```
    #[derive(Clone, Debug)]
    pub struct Path {
        pub ty: TypeId,
        pub target_trait: TraitId,
        pub item: TraitMethodId,
    }

    enum_conversion! {
        [ExpressionKind]
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
        Path: Path,
    }
}

#[derive(Clone, Debug)]
pub struct Trait {
    pub id: HirId,
    pub name: TraitBindingId,
    pub method_scope: ScopeId,
    pub method_bindings: HashMap<IdentifierBindingId, TraitMethodId>,
    pub methods: IndexedVec<TraitMethodId, FunctionSignature<MaybeSelfType>>,
}

// Key to identifier a specific implementation of a trait for a given type.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TraitImplementationKey {
    /// Trait that is being implemented.
    pub trait_id: TraitId,
    /// Type the trait is implemented on.
    pub ty: TypeId,
}

#[derive(Clone, Debug)]
pub struct TraitImplementation {
    /// [`FunctionId`] containing the implementation for each [`TraitMethodId`].
    pub methods: IndexedVec<TraitMethodId, FunctionId>,
}

/// A type that may be `Self`, or some other resolved type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MaybeSelfType {
    SelfType,
    Type(TypeId),
}

impl MaybeSelfType {
    /// Fetch the type, using a fallback.
    pub fn with_self(&self, current_self: TypeId) -> TypeId {
        self.without_self().unwrap_or(current_self)
    }

    /// Fetch the type, or [`None`] if [`MaybeSelfType::SelfType`].
    pub fn without_self(&self) -> Option<TypeId> {
        match self {
            MaybeSelfType::SelfType => None,
            MaybeSelfType::Type(type_id) => Some(*type_id),
        }
    }
}

impl From<TypeId> for MaybeSelfType {
    fn from(ty: TypeId) -> Self {
        Self::Type(ty)
    }
}
