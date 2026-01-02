use crate::ir::hir::Type;
use crate::prelude::*;

pub use self::{basic_blocks::*, operand::*, place::*, rvalue::*, statement::*, terminator::*};

// HACK: Properly put this somewhere.
pub use hir::FunctionId;

create_id!(LocalId);
create_id!(BasicBlockId);
create_id!(StatementId);
create_id!(TerminatorId);

#[derive(Clone, Debug, Default)]
pub struct Mir {
    pub functions: IndexedVec<FunctionId, Function>,
    pub basic_blocks: IndexedVec<BasicBlockId, BasicBlock>,
    pub statements: IndexedVec<StatementId, Statement>,
    pub terminators: IndexedVec<TerminatorId, Terminator>,
}

impl Mir {
    pub fn new() -> Self {
        Self::default()
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

#[derive(Clone, Debug)]
pub struct Function {
    pub ret_ty: Type,
    pub params: Vec<Type>,
    pub binding: BindingId,

    pub locals: Vec<(Option<BindingId>, Type)>,
    pub entry: BasicBlockId,
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

    #[derive(Clone, Debug)]
    pub struct Assign {
        pub place: Place,
        pub rvalue: RValue,
    }

    #[derive(Clone, Debug)]
    pub struct StorageLive {
        pub local: LocalId,
    }

    #[derive(Clone, Debug)]
    pub struct StorageDead {
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
        SwitchInt(SwitchInt),
        Unterminated,
    }

    #[derive(Clone, Debug)]
    pub struct Call {
        pub func: Operand,
        pub args: Vec<Operand>,
        pub destination: Place,
        pub target: BasicBlockId,
    }

    #[derive(Clone, Debug)]
    pub struct Goto {
        pub basic_block: BasicBlockId,
    }

    #[derive(Clone, Debug)]
    pub struct SwitchInt {
        pub discriminator: Operand,
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

    #[derive(Clone, Debug)]
    pub enum Projection {
        Deref,
    }
}

mod rvalue {
    use crate::ir::cst::{BinaryOp, UnaryOp};

    use super::*;

    #[derive(Clone, Debug)]
    pub enum RValue {
        Use(Operand),
        Ref(Place),
        Binary(Binary),
        Unary(Unary),
    }

    #[derive(Clone, Debug)]
    pub struct Binary {
        pub lhs: Operand,
        pub op: BinaryOp,
        pub rhs: Operand,
    }

    #[derive(Clone, Debug)]
    pub struct Unary {
        pub op: UnaryOp,
        pub value: Operand,
    }
}

mod operand {
    use super::*;

    #[derive(Clone, Debug)]
    pub enum Operand {
        Place(Place),
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
