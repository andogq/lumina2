use std::collections::HashMap;

use crate::ir2::{
    ast::{StringId, StringPool},
    hir::{BindingId, Type},
};

pub use self::{
    basic_blocks::*, functions::*, operand::*, place::*, rvalue::*, statement::*, terminator::*,
};

#[derive(Clone, Debug)]
pub struct Mir {
    pub functions: Vec<Function>,
    pub strings: StringPool,
    pub binding_to_string: HashMap<BindingId, StringId>,
}

impl Mir {
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
            strings: StringPool::new(),
            binding_to_string: HashMap::new(),
        }
    }
}

mod functions {
    use crate::ir2::hir::BindingId;

    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct FunctionId(pub usize);
    impl FunctionId {
        pub fn new(id: usize) -> Self {
            Self(id)
        }
    }

    #[derive(Clone, Debug)]
    pub struct Function {
        pub ret_ty: Type,
        pub params: Vec<Type>,
        pub binding: BindingId,

        pub locals: Vec<(Option<BindingId>, Type)>,
        pub entry: BasicBlockId,

        pub basic_blocks: Vec<BasicBlock>,
    }

    #[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
    pub struct LocalId(pub usize);
    impl LocalId {
        pub fn new(id: usize) -> Self {
            Self(id)
        }
    }
}

mod basic_blocks {
    use super::*;

    #[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
    pub struct BasicBlockId(pub usize);
    impl BasicBlockId {
        pub fn new(id: usize) -> Self {
            Self(id)
        }
    }

    #[derive(Clone, Debug)]
    pub struct BasicBlock {
        pub statements: Vec<Statement>,
        pub terminator: Terminator,
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
    use crate::ir2::cst::{BinaryOp, UnaryOp};

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
