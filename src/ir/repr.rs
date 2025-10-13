//! Intermediate representation.

use std::fmt::Display;

use crate::{Ident, indexed_vec, tir::Ty};

/// Representation of a function.
#[derive(Clone, Debug)]
pub struct Function {
    pub name: Ident,
    /// All basic blocks that build this function.
    pub basic_blocks: BasicBlocks,
    /// Local declarations used within this function.
    pub local_decls: Locals,
    /// Number of arguments passed to this function. These will be populated in the first `1..n`
    /// locals.
    pub arg_count: usize,
}

impl Function {
    pub fn new(name: Ident) -> Self {
        Self {
            name,
            basic_blocks: Default::default(),
            local_decls: Default::default(),
            arg_count: Default::default(),
        }
    }
}

impl Default for Function {
    fn default() -> Self {
        Self::new(Ident::zero())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}
indexed_vec!(pub key BasicBlock);
indexed_vec!(pub BasicBlocks<BasicBlock, BasicBlockData>);

impl Display for BasicBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalDecl {
    pub ty: Ty,
}
indexed_vec!(pub key Local);
indexed_vec!(pub Locals<Local, LocalDecl>);

impl Display for Local {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_{}", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement {
    /// Assign a value into a place.
    Assign {
        /// Target to store value.
        place: Place,
        /// Value to assign.
        rvalue: RValue,
    },
    /// Deallocate a local on the stack.
    StorageDead(Local),
    /// Allocate a local on the stack.
    StorageLive(Local),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Terminator {
    /// Call a function.
    Call {
        /// The pointer to the function to call.
        func: Operand,
        /// Arguments to pass to the function.
        args: Vec<Operand>,
        /// Destination for the return value.
        destination: Place,
        /// Basic block to continue to after call returns.
        target: BasicBlock,
    },
    /// Continue execution from a basic block.
    Goto(BasicBlock),
    /// Return from the current function.
    Return,
    /// Switch over a collection of integers.
    SwitchInt {
        /// Discriminator for the operation.
        discriminator: Operand,
        /// Collection of target values, and basic block to jump to if matched.
        targets: Vec<(Constant, BasicBlock)>,
        otherwise: BasicBlock,
    },
    Unreachable,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RValue {
    Use(Operand),
    Ref(Place),
    BinaryOp {
        op: BinOp,
        lhs: Operand,
        rhs: Operand,
    },
    UnaryOp {
        op: UnOp,
        rhs: Operand,
    },
    Aggregate {
        values: Vec<Operand>,
    },
    Cast {
        kind: CastKind,
        op: Operand,
        ty: Ty,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CastKind {
    PointerCoercion(PointerCoercion),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PointerCoercion {
    Unsize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,

    LogicalAnd,
    LogicalOr,
    BitAnd,
    BitOr,

    Eq,
    Ne,
    Gt,
    Lt,
    Ge,
    Le,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
    PtrMetadata,
}

/// Describes how to 'create' a value. Essentially, where does a value come from, and how to get
/// it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    /// Copy the value from a place.
    Place(Place),
    /// Value is a constant.
    Constant(Constant),
}

/// Represents a location in memory. Locations derive from a [`Local`], with a collection of
/// [`Projection`]s applied.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Place {
    /// Originating local.
    pub local: Local,
    /// Projections applied to the local.
    pub projection: Vec<Projection>,
}

/// Possible operations to perform on a [`Place`], in order to access some underlying data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Projection {
    /// Dereference the parent place.
    Deref,
    /// Access a field by taking a parent place, and adding the field offset to the parent's
    /// address.
    Field(usize),
    /// Offset the parent's address plus an offset defined by an index from a local.
    Index(Local),
}

/// Constant value present within IR.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constant {
    U8(u8),
    I8(i8),
    Boolean(bool),
}
impl From<u8> for Constant {
    fn from(value: u8) -> Self {
        Self::U8(value)
    }
}
impl From<i8> for Constant {
    fn from(value: i8) -> Self {
        Self::I8(value)
    }
}
