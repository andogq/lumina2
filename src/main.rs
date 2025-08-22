use crate::{interpreter::Interpreter, util::indexed_vec::Key};

mod interpreter;
mod util;

/// Representation of a function.
#[derive(Clone, Debug, Default)]
struct Body {
    /// All basic blocks that build this function.
    basic_blocks: BasicBlocks,
    /// Local declarations used within this function.
    local_decls: Locals,
    /// Number of arguments passed to this function. These will be populated in the first `1..n`
    /// locals.
    arg_count: usize,
}

#[derive(Clone, Debug)]
struct BasicBlockData {
    statements: Vec<Statement>,
    terminator: Terminator,
}
indexed_vec!(key BasicBlock);
indexed_vec!(BasicBlocks<BasicBlock, BasicBlockData>);

#[derive(Clone, Debug)]
struct LocalDecl {}
indexed_vec!(key Local);
indexed_vec!(Locals<Local, LocalDecl>);

#[derive(Clone, Debug)]
enum Statement {
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
enum Terminator {
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
        targets: Vec<(usize, BasicBlock)>,
        otherwise: BasicBlock,
    },
}

#[derive(Clone, Debug)]
enum RValue {
    Use(Operand),
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
enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug)]
enum UnOp {
    Not,
    Neg,
}

/// Describes how to 'create' a value. Essentially, where does a value come from, and how to get
/// it.
#[derive(Clone, Debug)]
enum Operand {
    /// Copy the value from a place.
    Copy(Place),
    /// Move the value from a place. Moving from this place will cause it to be invalidated.
    Move(Place),
    /// Value is a constant.
    Constant(usize),
}

/// Represents a location in memory. Locations derive from a [`Local`], with a collection of
/// [`Projection`]s applied.
#[derive(Clone, Debug)]
struct Place {
    /// Originating local.
    local: Local,
    /// Projections applied to the local.
    projection: Vec<Projection>,
}

/// Possible operations to perform on a [`Place`], in order to access some underlying data.
#[derive(Clone, Debug)]
enum Projection {
    /// Dereference the parent place.
    Deref,
    /// Access a field by taking a parent place, and adding the field offset to the parent's
    /// address.
    Field(usize),
    /// Offset the parent's address plus an offset defined by an index from a local.
    Index(Local),
}

macro_rules! ir {
    (local($program:ident) $local:ident) => {
        let $local = $program.local_decls.insert(LocalDecl {});
    };

    (basic_block($program:ident) $bb:ident: { $($body:tt)* }) => {
        let $bb = $program.basic_blocks.insert(ir!(split(build_basic_block) [] [] [$($body)*]));
    };

    (build_basic_block [$([$($statements:tt)*])*] [$($terminator:tt)*]) => {
        BasicBlockData {
            statements: vec![
                $(ir!(statement [$($statements)*])),*
            ],
            terminator: ir!(terminator [$($terminator)*]),
        }
    };

    // StorageLive(_0)
    (statement [$statement:ident($($params:ident),* $(,)?)]) => {
        Statement::$statement($($params,)*)
    };

    // Assume assignment
    (statement [$($tt:tt)*]) => {
        ir!(split_assign(assign_statement) [] [$($tt)*])
    };

    (assign_statement [$($lhs:tt)*] [$($rhs:tt)*]) => {
        Statement::Assign {
            place: ir!(parse_place [$($lhs)*]),
            rvalue: ir!(parse_rvalue [$($rhs)*]),
        }
    };

    (parse_place [$local:ident]) => {
        Place {
            local: $local,
            projection: vec![],
        }
    };

    (parse_rvalue [$op:ident($($params:tt)*)]) => {
        ir!(split_params(rvalue_op_with_params($op)) [] [] [$($params)*])
    };
    (rvalue_op_with_params($op:ident) [$($rhs:tt)*]) => {
        RValue::UnaryOp {
            op: UnOp::$op,
            rhs: ir!(parse_operand [$($rhs)*]),
        }
    };
    (rvalue_op_with_params($op:ident) [$($lhs:tt)*] [$($rhs:tt)*]) => {
        RValue::BinaryOp {
            op: BinOp::$op,
            lhs: ir!(parse_operand [$($lhs)*]),
            rhs: ir!(parse_operand [$($rhs)*]),
        }
    };

    (parse_rvalue [$($operand:tt)*]) => {
        RValue::Use(ir!(parse_operand [$($operand)*]))
    };

    (parse_operand [const $value:literal]) => {
        Operand::Constant($value)
    };
    (parse_operand [copy $($place:tt)*]) => {
        Operand::Copy(ir!(parse_place [$($place)*]))
    };
    (parse_operand [move $($place:tt)*]) => {
        Operand::Move(ir!(parse_place [$($place)*]))
    };

    (terminator [return]) => {
        Terminator::Return
    };

    (split_params($($callback:tt)*) [$($params:tt)*] [] []) => {
        ir!($($callback)* $($params)*)
    };
    (split_params($($callback:tt)*) [$($params:tt)*] [$($current:tt)*] [$(, $($rest:tt)*)?]) => {
        ir!(split_params($($callback)*) [$($params)* [$($current)*]] [] [$($($rest)*)?])
    };
    (split_params($($callback:tt)*) [$($params:tt)*] [$($current:tt)*] [$tok:tt $($rest:tt)*]) => {
        ir!(split_params($($callback)*) [$($params)*] [$($current)* $tok] [$($rest)*])
    };

    (split_assign($callback:ident) [$($lhs:tt)*] [= $($rest:tt)*]) => {
        ir!($callback [$($lhs)*] [$($rest)*])
    };

    (split_assign($callback:ident) [$($lhs:tt)*] [$tok:tt $($rest:tt)*]) => {
        ir!(split_assign($callback) [$($lhs)* $tok] [$($rest)*])
    };

    (split($callback:ident) [$($statements:tt)*] [$($current:tt)*] [;]) => {
        ir!($callback [$($statements)*] [$($current)*])
    };
    (split($callback:ident) [$($statements:tt)*] [$($current:tt)*] [; $($rest:tt)+]) => {
        ir!(split($callback) [$($statements)* [$($current)*]] [] [$($rest)+])
    };
    (split($callback:ident) [$($statements:tt)*] [$($current:tt)*] [$tok:tt $($rest:tt)+]) => {
        ir!(split($callback) [$($statements)*] [$($current)* $tok] [$($rest)+])
    };

    (munch($program:ident)[let $local:ident; $($rest:tt)*]) => {
        ir!(local($program) $local);
        ir!(munch($program)[$($rest)*]);
    };

    (munch($program:ident)[$bb:ident: { $($body:tt)* } $($rest:tt)*]) => {
        ir!(basic_block($program) $bb: { $($body)* });
    };
}
macro_rules! ir_base {
    ($($tt:tt)*) => {{
        let mut program = Body::default();

        ir!(munch(program) [$($tt)*]);

        program
    }};
}

fn main() {
    let program = ir_base! {
        let _0;
        let _1;
        let _2;

        bb0: {
            StorageLive(_1);
            StorageLive(_2);
            _1 = const 2;
            _2 = const 3;
            _0 = Mul(copy _1, copy _2);
            StorageDead(_2);
            StorageDead(_1);
            return;
        }
    };
    dbg!(Interpreter::run(&program));

    let mut local_decls = Locals::new();
    let loc_ret = local_decls.insert(LocalDecl {});
    let loc_lhs = local_decls.insert(LocalDecl {});
    let loc_rhs = local_decls.insert(LocalDecl {});

    let mut basic_blocks = BasicBlocks::new();
    basic_blocks.insert(BasicBlockData {
        statements: vec![
            Statement::StorageLive(loc_lhs),
            Statement::StorageLive(loc_rhs),
            Statement::Assign {
                place: Place {
                    local: loc_lhs,
                    projection: vec![],
                },
                rvalue: RValue::Use(Operand::Constant(2)),
            },
            Statement::Assign {
                place: Place {
                    local: loc_rhs,
                    projection: vec![],
                },
                rvalue: RValue::Use(Operand::Constant(3)),
            },
            Statement::Assign {
                place: Place {
                    local: loc_ret,
                    projection: vec![],
                },
                rvalue: RValue::BinaryOp {
                    op: BinOp::Mul,
                    lhs: Operand::Copy(Place {
                        local: loc_lhs,
                        projection: vec![],
                    }),
                    rhs: Operand::Copy(Place {
                        local: loc_rhs,
                        projection: vec![],
                    }),
                },
            },
            Statement::StorageDead(loc_rhs),
            Statement::StorageDead(loc_lhs),
        ],
        terminator: Terminator::Return,
    });

    let one_plus_one = Body {
        basic_blocks,
        local_decls,
        arg_count: 0,
    };

    let output = Interpreter::run(&one_plus_one);
    dbg!(output);
}
