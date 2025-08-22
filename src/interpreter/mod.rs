mod stack;

use crate::{
    BasicBlock, BinOp, Body, Local, Operand, Place, Projection, RValue, Statement, Terminator,
    UnOp, indexed_vec,
    interpreter::stack::{Pointer, Stack},
};

#[derive(Clone, Debug)]
pub struct Interpreter {
    locals: InterpreterLocals,
    stack: Stack,
}

impl Interpreter {
    fn new() -> Self {
        Self {
            locals: InterpreterLocals::new(),
            stack: Stack::new(),
        }
    }

    pub fn run(body: &Body) -> usize {
        let mut interpreter = Self::new();

        interpreter.stack.push_frame();

        // Create the locals.
        for _local in &*body.local_decls {
            let ptr = interpreter.stack.get_frame().alloca();
            interpreter.new_local(ptr);
        }

        let return_local = Local::zero();
        interpreter.alive_local(return_local);

        let mut next_block = BasicBlock::zero();
        loop {
            let block = &body.basic_blocks[next_block];

            for statement in &block.statements {
                match statement {
                    Statement::Assign { place, rvalue } => {
                        let target_ptr = interpreter.resolve_place(place);
                        let value = interpreter.resolve_rvalue(rvalue);
                        interpreter.stack[target_ptr] = value;
                    }
                    Statement::StorageDead(local) => interpreter.kill_local(*local),
                    Statement::StorageLive(local) => interpreter.alive_local(*local),
                }
            }

            match &block.terminator {
                Terminator::Call {
                    func,
                    args,
                    destination,
                    target,
                } => todo!(),
                Terminator::Goto(basic_block) => next_block = *basic_block,
                Terminator::Return => break,
                Terminator::SwitchInt {
                    discriminator,
                    targets,
                    otherwise,
                } => {
                    let discriminator = interpreter.resolve_operand(discriminator);
                    next_block = targets
                        .iter()
                        .find(|(value, _)| discriminator == *value)
                        .map(|(_, block)| *block)
                        .unwrap_or(*otherwise);
                }
            }
        }

        let offset = interpreter.get_alive_local(return_local).ptr;
        let output = interpreter.stack[offset];

        interpreter.stack.pop_frame();

        output
    }

    fn new_local(&mut self, ptr: Pointer) -> Local {
        self.locals.insert(InterpreterLocal {
            ptr,
            state: LocalState::Dead,
        })
    }

    fn alive_local(&mut self, local: Local) {
        let local = &mut self.locals[local];
        local.state = LocalState::Alive;
    }

    fn kill_local(&mut self, local: Local) {
        let local = &mut self.locals[local];
        local.state = LocalState::Dead;
    }

    /// Read a local from the stack. Will panic if it's not alive.
    fn read_local(&self, local: Local) -> usize {
        self.stack[&self.get_alive_local(local).ptr]
    }

    fn get_alive_local(&self, local: Local) -> &InterpreterLocal {
        let local = &self.locals[local];
        assert!(
            matches!(local.state, LocalState::Alive),
            "can only read from alive local"
        );
        local
    }

    /// Resolve a place into an offset in the stack.
    fn resolve_place(&self, place: &Place) -> Pointer {
        let mut ptr = self.get_alive_local(place.local).ptr;

        for proj in &place.projection {
            match proj {
                // Look up `ptr` in the stack, and replace `ptr` with that value.
                Projection::Deref => ptr = Pointer::new(self.stack[ptr]),
                Projection::Field(field_offset) => ptr += *field_offset,
                Projection::Index(index_local) => ptr += self.read_local(*index_local),
            }
        }

        ptr
    }

    fn resolve_rvalue(&self, rvalue: &RValue) -> usize {
        match rvalue {
            RValue::Use(operand) => self.resolve_operand(operand),
            RValue::BinaryOp { op, lhs, rhs } => {
                let lhs = self.resolve_operand(lhs);
                let rhs = self.resolve_operand(rhs);

                match op {
                    BinOp::Add => lhs + rhs,
                    BinOp::Sub => lhs - rhs,
                    BinOp::Mul => lhs * rhs,
                    BinOp::Div => lhs / rhs,
                }
            }
            RValue::UnaryOp { op, rhs } => {
                let rhs = self.resolve_operand(rhs);

                match op {
                    UnOp::Not => !rhs,
                    UnOp::Neg => rhs.wrapping_neg(),
                }
            }
        }
    }

    /// Return the value of the provided operand
    fn resolve_operand(&self, operand: &Operand) -> usize {
        match operand {
            Operand::Copy(place) => self.stack[self.resolve_place(place)],
            Operand::Move(place) => todo!(),
            Operand::Constant(value) => *value,
        }
    }
}

indexed_vec!(InterpreterLocals<Local, InterpreterLocal>);

#[derive(Clone, Debug)]
struct InterpreterLocal {
    state: LocalState,
    ptr: Pointer,
}

#[derive(Clone, Debug)]
enum LocalState {
    Alive,
    Dead,
    Moved,
}
