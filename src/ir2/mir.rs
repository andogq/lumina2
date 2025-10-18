use crate::ir2::hir::Type;

use self::{
    basic_blocks::*, functions::*, operand::*, place::*, rvalue::*, statement::*, terminator::*,
};

pub struct Mir {
    pub functions: Vec<Function>,
    pub basic_blocks: Vec<BasicBlock>,
}

mod functions {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct FunctionId(usize);

    pub struct Function {
        pub locals: Vec<Type>,
        pub entry: BasicBlockId,
    }

    #[derive(Clone, Copy, Debug)]
    pub struct LocalId(usize);
}

mod basic_blocks {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct BasicBlockId(usize);

    pub struct BasicBlock {
        statements: Vec<Statement>,
        terminator: Terminator,
    }
}

mod statement {
    use super::*;

    pub enum Statement {
        Assign(Assign),
        StorageLive(StorageLive),
        StorageDead(StorageDead),
    }

    pub struct Assign {
        place: Place,
        rvalue: RValue,
    }

    pub struct StorageLive {
        local: LocalId,
    }

    pub struct StorageDead {
        local: LocalId,
    }
}

mod terminator {
    use super::*;

    pub enum Terminator {
        Call(Call),
        Goto(Goto),
        Return,
        SwitchInt(SwitchInt),
    }

    pub struct Call {
        pub func: Operand,
        pub args: Vec<Operand>,
        pub destination: Place,
        pub target: BasicBlockId,
    }

    pub struct Goto {
        pub basic_block: BasicBlockId,
    }

    pub struct SwitchInt {
        pub discriminator: Operand,
        pub targets: Vec<(Constant, BasicBlockId)>,
        pub otherwise: BasicBlockId,
    }
}

mod place {
    use super::*;

    pub struct Place {
        local: LocalId,
        projection: Vec<Projection>,
    }

    pub enum Projection {
        Deref,
    }
}

mod rvalue {
    use crate::ir2::cst::{BinaryOp, UnaryOp};

    use super::*;

    pub enum RValue {
        Use(Operand),
        Ref(Place),
        Binary(Binary),
        Unary(Unary),
    }

    pub struct Binary {
        pub lhs: Operand,
        pub op: BinaryOp,
        pub rhs: Operand,
    }

    pub struct Unary {
        pub op: UnaryOp,
        pub value: Operand,
    }
}

mod operand {
    use super::*;

    pub enum Operand {
        Place(Place),
        Constant(Constant),
    }

    pub enum Constant {
        U8(u8),
        I8(i8),
        Boolean(bool),
    }
}
