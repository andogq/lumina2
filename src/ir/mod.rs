pub mod ctx;
mod ir_macro;
mod pointer;
mod value;

pub use self::{pointer::Pointer, value::*};
use crate::{indexed_vec, ir::ctx::Ctx};

/// Representation of a function.
#[derive(Clone, Debug, Default)]
pub struct Body {
    pub ctx: Ctx,

    /// All basic blocks that build this function.
    pub basic_blocks: BasicBlocks,
    /// Local declarations used within this function.
    pub local_decls: Locals,
    /// Number of arguments passed to this function. These will be populated in the first `1..n`
    /// locals.
    pub arg_count: usize,
}

#[derive(Clone, Debug)]
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}
indexed_vec!(pub key BasicBlock);
indexed_vec!(pub BasicBlocks<BasicBlock, BasicBlockData>);

#[derive(Clone, Debug)]
pub struct LocalDecl {
    pub ty: Ty,
}
indexed_vec!(pub key Local);
indexed_vec!(pub Locals<Local, LocalDecl>);

#[derive(Clone, Debug)]
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

#[derive(Clone, Debug)]
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
        targets: Vec<(Value, BasicBlock)>,
        otherwise: BasicBlock,
    },
}

#[derive(Clone, Debug)]
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
}

#[derive(Clone, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug)]
pub enum UnOp {
    Not,
    Neg,
}

/// Describes how to 'create' a value. Essentially, where does a value come from, and how to get
/// it.
#[derive(Clone, Debug)]
pub enum Operand {
    /// Copy the value from a place.
    Place(Place),
    /// Value is a constant.
    Constant(Value),
}

/// Represents a location in memory. Locations derive from a [`Local`], with a collection of
/// [`Projection`]s applied.
#[derive(Clone, Debug)]
pub struct Place {
    /// Originating local.
    pub local: Local,
    /// Projections applied to the local.
    pub projection: Vec<Projection>,
}

/// Possible operations to perform on a [`Place`], in order to access some underlying data.
#[derive(Clone, Debug)]
pub enum Projection {
    /// Dereference the parent place.
    Deref,
    /// Access a field by taking a parent place, and adding the field offset to the parent's
    /// address.
    Field(usize),
    /// Offset the parent's address plus an offset defined by an index from a local.
    Index(Local),
}
