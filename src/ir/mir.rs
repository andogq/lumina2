use crate::prelude::*;

pub use self::{
    basic_blocks::*,
    operand::*,
    place::*,
    rvalue::{UnaryOperation, *},
    statement::*,
    terminator::*,
};

create_id!(LocalId);
create_id!(BasicBlockId);
create_id!(StatementId);
create_id!(TerminatorId);
create_id!(FunctionId);
create_id!(OperandId);
create_id!(PlaceId);

#[derive(Clone, Debug, Default)]
pub struct Mir {
    pub functions: IndexedVec<FunctionId, Function>,
    pub basic_blocks: IndexedVec<BasicBlockId, BasicBlock>,
    pub statements: IndexedVec<StatementId, Statement>,
    pub terminators: IndexedVec<TerminatorId, Terminator>,
    pub operands: IndexedVec<OperandId, Operand>,
    pub places: IndexedVec<PlaceId, Place>,
}

indexing! {
    Mir {
        functions[FunctionId] -> Function,
        basic_blocks[BasicBlockId] -> BasicBlock,
        statements[StatementId] -> Statement,
        terminators[TerminatorId] -> Terminator,
        operands[OperandId] -> Operand,
        places[PlaceId] -> Place,
    }
}

impl Mir {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a new unterminated basic block.
    pub fn add_basic_block(&mut self) -> BasicBlockId {
        let terminator = self.terminators.insert(Terminator::Unterminated);
        self.basic_blocks.insert(BasicBlock {
            statements: Vec::new(),
            terminator,
        })
    }

    /// Add a statement to a basic block.
    pub fn add_statement(
        &mut self,
        basic_block: BasicBlockId,
        statement: impl Into<Statement>,
    ) -> StatementId {
        let id = self.statements.insert(statement.into());
        self[basic_block].statements.push(id);
        id
    }

    /// Terminate a basic block with the provided terminator. Will panic if the terminator is
    /// anything other than [`Terminator::Unterminated`].
    pub fn terminate(
        &mut self,
        basic_block: BasicBlockId,
        terminator: impl Into<Terminator>,
    ) -> TerminatorId {
        assert!(
            matches!(
                &self[self[basic_block].terminator],
                Terminator::Unterminated
            ),
            "terminating a block which is already terminated"
        );

        self.terminate_if_unterminated(basic_block, terminator)
    }

    /// Terminate a basic block only if it is currently [`Terminator::Unterminated`];.
    pub fn terminate_if_unterminated(
        &mut self,
        basic_block: BasicBlockId,
        terminator: impl Into<Terminator>,
    ) -> TerminatorId {
        let id = self[basic_block].terminator;
        let block_terminator = &mut self[id];

        if matches!(block_terminator, Terminator::Unterminated) {
            *block_terminator = terminator.into();
        }

        id
    }
}

#[derive(Clone, Debug)]
pub struct Function {
    pub return_ty: TypeId,
    pub parameters: Vec<TypeId>,
    pub binding: IdentifierBindingId,

    pub locals: IndexedVec<LocalId, (Option<IdentifierBindingId>, TypeId)>,
    pub entry: BasicBlockId,
}

impl Index<LocalId> for Function {
    type Output = (Option<IdentifierBindingId>, TypeId);

    fn index(&self, index: LocalId) -> &Self::Output {
        &self.locals[index]
    }
}

impl IndexMut<LocalId> for Function {
    fn index_mut(&mut self, index: LocalId) -> &mut Self::Output {
        &mut self.locals[index]
    }
}

mod basic_blocks {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct BasicBlock {
        pub statements: Vec<StatementId>,
        pub terminator: TerminatorId,
    }
}

mod statement {
    use super::*;

    #[derive(Clone, Debug)]
    pub enum Statement {
        Assign(Assign),
        StorageLive(StorageLive),
        StorageDead(StorageDead),
    }

    enum_conversion! {
        [Statement]
        Assign: Assign,
        StorageLive: StorageLive,
        StorageDead: StorageDead,
    }

    #[derive(Clone, Debug)]
    pub struct Assign {
        pub place: PlaceId,
        pub rvalue: RValue,
    }

    #[derive(Clone, Debug)]
    pub struct StorageLive {
        #[expect(
            dead_code,
            reason = "storage statements are not currently implemented."
        )]
        pub local: LocalId,
    }

    #[derive(Clone, Debug)]
    pub struct StorageDead {
        #[expect(
            dead_code,
            reason = "storage statements are not currently implemented."
        )]
        pub local: LocalId,
    }
}

mod terminator {
    use super::*;

    #[derive(Clone, Debug)]
    pub enum Terminator {
        Call(Call),
        Goto(Goto),
        Return,
        SwitchInteger(SwitchInteger),
        Unterminated,
    }

    enum_conversion! {
        [Terminator]
        Call: Call,
        Goto: Goto,
        SwitchInteger: SwitchInteger,
    }

    #[derive(Clone, Debug)]
    pub struct Call {
        pub function: OperandId,
        pub arguments: Vec<OperandId>,
        pub destination: PlaceId,
        pub target: BasicBlockId,
    }

    #[derive(Clone, Debug)]
    pub struct Goto {
        pub basic_block: BasicBlockId,
    }

    #[derive(Clone, Debug)]
    pub struct SwitchInteger {
        pub discriminator: OperandId,
        pub targets: Vec<(Constant, BasicBlockId)>,
        pub otherwise: BasicBlockId,
    }
}

mod place {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Place {
        pub local: LocalId,
        pub projection: Vec<Projection>,
    }

    impl From<LocalId> for Place {
        fn from(local: LocalId) -> Self {
            Self {
                local,
                projection: Vec::new(),
            }
        }
    }

    #[derive(Clone, Debug)]
    pub enum Projection {
        Deref,
        Field(usize),
    }
}

mod rvalue {
    use super::*;

    #[derive(Clone, Debug)]
    pub enum RValue {
        Use(OperandId),
        Ref(PlaceId),
        Binary(Binary),
        Unary(Unary),
        Aggregate(Aggregate),
    }

    #[derive(Clone, Debug)]
    pub struct Binary {
        pub lhs: OperandId,
        pub operation: BinaryOperation,
        pub rhs: OperandId,
    }

    pub use crate::prelude::BinaryOperation;

    #[derive(Clone, Debug)]
    pub struct Unary {
        pub operation: UnaryOperation,
        pub value: OperandId,
    }

    #[derive(Clone, Copy, Debug)]
    pub enum UnaryOperation {
        Not,
        Negative,
    }

    #[derive(Clone, Debug)]
    pub struct Aggregate {
        pub values: Vec<(OperandId, TypeId)>,
        pub ty: TypeId,
    }
}

mod operand {
    use super::*;

    #[derive(Clone, Debug)]
    pub enum Operand {
        Place(PlaceId),
        Constant(Constant),
    }

    #[derive(Clone, Debug)]
    pub enum Constant {
        U8(u8),
        I8(i8),
        Boolean(bool),
        Function(FunctionId),
    }
}
