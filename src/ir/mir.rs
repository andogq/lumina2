use crate::prelude::*;

use hir::Type;

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

impl Index<FunctionId> for Mir {
    type Output = Function;

    fn index(&self, index: FunctionId) -> &Self::Output {
        &self.functions[index]
    }
}
impl IndexMut<FunctionId> for Mir {
    fn index_mut(&mut self, index: FunctionId) -> &mut Self::Output {
        &mut self.functions[index]
    }
}
impl Index<BasicBlockId> for Mir {
    type Output = BasicBlock;

    fn index(&self, index: BasicBlockId) -> &Self::Output {
        &self.basic_blocks[index]
    }
}
impl IndexMut<BasicBlockId> for Mir {
    fn index_mut(&mut self, index: BasicBlockId) -> &mut Self::Output {
        &mut self.basic_blocks[index]
    }
}
impl Index<StatementId> for Mir {
    type Output = Statement;

    fn index(&self, index: StatementId) -> &Self::Output {
        &self.statements[index]
    }
}
impl IndexMut<StatementId> for Mir {
    fn index_mut(&mut self, index: StatementId) -> &mut Self::Output {
        &mut self.statements[index]
    }
}
impl Index<TerminatorId> for Mir {
    type Output = Terminator;

    fn index(&self, index: TerminatorId) -> &Self::Output {
        &self.terminators[index]
    }
}
impl IndexMut<TerminatorId> for Mir {
    fn index_mut(&mut self, index: TerminatorId) -> &mut Self::Output {
        &mut self.terminators[index]
    }
}
impl Index<PlaceId> for Mir {
    type Output = Place;

    fn index(&self, index: PlaceId) -> &Self::Output {
        &self.places[index]
    }
}
impl IndexMut<PlaceId> for Mir {
    fn index_mut(&mut self, index: PlaceId) -> &mut Self::Output {
        &mut self.places[index]
    }
}
impl Index<OperandId> for Mir {
    type Output = Operand;

    fn index(&self, index: OperandId) -> &Self::Output {
        &self.operands[index]
    }
}
impl IndexMut<OperandId> for Mir {
    fn index_mut(&mut self, index: OperandId) -> &mut Self::Output {
        &mut self.operands[index]
    }
}

#[derive(Clone, Debug)]
pub struct Function {
    pub return_ty: Type,
    pub parameters: Vec<Type>,
    pub binding: BindingId,

    pub locals: IndexedVec<LocalId, (Option<BindingId>, Type)>,
    pub entry: BasicBlockId,
}

impl Index<LocalId> for Function {
    type Output = (Option<BindingId>, Type);

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
        Unit,
        Function(FunctionId),
    }
}
