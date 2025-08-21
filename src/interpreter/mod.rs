use crate::{
    BasicBlock, BinOp, Body, Local, Operand, Place, Projection, RValue, Statement, Terminator,
    UnOp, indexed_vec,
};

#[derive(Clone, Debug)]
pub struct Interpreter {
    locals: InterpreterLocals,
    stack: [usize; 128],
    sp: usize,
}

impl Interpreter {
    fn new() -> Self {
        Self {
            locals: InterpreterLocals::new(),
            stack: [0; 128],
            sp: 0,
        }
    }

    pub fn run(body: &Body) -> usize {
        let mut interpreter = Self::new();

        // Create the locals.
        for _local in &*body.local_decls {
            interpreter.new_local();
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

        let InterpreterLocal::Alive { offset } = interpreter.locals[return_local] else {
            panic!("return local must be alive");
        };

        interpreter.stack[offset]
    }

    fn new_local(&mut self) -> Local {
        self.locals.insert(InterpreterLocal::Dead)
    }

    fn alive_local(&mut self, local: Local) {
        let local = &mut self.locals[local];
        *local = InterpreterLocal::Alive { offset: self.sp };
        self.sp += 1;
    }

    fn kill_local(&mut self, local: Local) {
        let local @ &mut InterpreterLocal::Alive { offset } = &mut self.locals[local] else {
            return;
        };
        assert_eq!(offset, self.sp - 1, "can only kill local in stack order");
        *local = InterpreterLocal::Dead;
        self.sp -= 1;
    }

    /// Read a local from the stack. Will panic if it's not alive.
    fn read_local(&self, local: Local) -> usize {
        self.stack[self.read_local_offset(local)]
    }

    /// Read a local's offset in the stack. Will panic if it's not alive.
    fn read_local_offset(&self, local: Local) -> usize {
        let InterpreterLocal::Alive { offset } = self.locals[local] else {
            panic!("local must be alive to read from it");
        };

        offset
    }

    /// Resolve a place into an offset in the stack.
    fn resolve_place(&self, place: &Place) -> usize {
        let mut ptr = self.read_local_offset(place.local);

        for proj in &place.projection {
            match proj {
                // Look up `ptr` in the stack, and replace `ptr` with that value.
                Projection::Deref => ptr = self.stack[ptr],
                Projection::Field(field_offset) => ptr += field_offset,
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
enum InterpreterLocal {
    Alive { offset: usize },
    Dead,
}
