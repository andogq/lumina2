mod stack;

use crate::{
    BasicBlock, BinOp, Body, Local, Operand, Place, Pointer, Projection, RValue, Statement,
    Terminator, Ty, TyInfo, Tys, UnOp, Value, indexed_vec, interpreter::stack::Stack,
};

#[derive(Clone, Debug)]
pub struct Interpreter {
    // TODO: This should be in a ctx.
    tys: Tys,
    locals: InterpreterLocals,
    stack: Stack,
}

impl Interpreter {
    fn new(tys: Tys) -> Self {
        Self {
            tys,
            locals: InterpreterLocals::new(),
            stack: Stack::new(),
        }
    }

    pub fn run(body: &Body) -> Value {
        let mut interpreter = Self::new(
            // HACK: don't clone
            body.ctx.tys.clone(),
        );

        interpreter.stack.push_frame();

        // Create the locals.
        for local_decl in &*body.local_decls {
            let ptr = interpreter
                .stack
                .get_frame()
                .alloca(interpreter.tys[local_decl.ty].size());
            interpreter.new_local(local_decl.ty, ptr);
        }

        let return_local = Local::zero();
        interpreter.alive_local(return_local);

        let mut next_block = BasicBlock::zero();
        loop {
            let block = &body.basic_blocks[next_block];

            for statement in &block.statements {
                match statement {
                    Statement::Assign { place, rvalue } => {
                        let (target_ptr, target_ty) = interpreter.resolve_place(place);
                        let value = interpreter.resolve_rvalue(rvalue);

                        let target_ty = &interpreter.tys[target_ty];

                        if !matches!(
                            (&value, target_ty),
                            (Value::U8(_), TyInfo::U8)
                                | (Value::I8(_), TyInfo::I8)
                                // TODO: Check inner type of ref
                                | (Value::Ref(_), TyInfo::Ref(_))
                        ) {
                            panic!("mis-matched value and target type: {target_ty:?}, {value:?}");
                        }

                        interpreter.stack.write(target_ptr, &value.to_bytes());
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

        let local = interpreter.get_alive_local(return_local);
        let ty = &interpreter.tys[local.ty];
        let mut buf = vec![0; ty.size()];
        interpreter.stack.read(local.ptr, &mut buf);
        let output = ty.get_value(&buf);

        interpreter.stack.pop_frame();

        output
    }

    fn new_local(&mut self, ty: Ty, ptr: Pointer) -> Local {
        self.locals.insert(InterpreterLocal {
            ty,
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
    fn read_local(&self, local: Local) -> Value {
        let local = self.get_alive_local(local);
        let ty = &self.tys[local.ty];

        let mut buf = vec![0; ty.size()];
        self.stack.read(local.ptr, &mut buf);

        ty.get_value(&buf)
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
    fn resolve_place(&mut self, place: &Place) -> (Pointer, Ty) {
        let local = self.get_alive_local(place.local);

        let mut ty = &self.tys[local.ty];
        let mut ptr = local.ptr;

        for proj in &place.projection {
            match proj {
                // Look up `ptr` in the stack, and replace `ptr` with that value.
                Projection::Deref => {
                    // Read the reference pointer out of memory.
                    let mut buf = vec![0; ty.size()];
                    self.stack.read(ptr, &mut buf);
                    ptr = ty
                        .get_value(&buf)
                        .into_ref()
                        .expect("expected to read ref pointer from stack");

                    // Determine the type of the reference.
                    let TyInfo::Ref(inner_ty) = ty else {
                        panic!("cannot deref non-pointer: {ty:?}");
                    };
                    ty = &self.tys[*inner_ty];
                }
                Projection::Field(field_offset) => {
                    ptr += *field_offset;

                    match ty {
                        _ => panic!("cannot project field on ty without field"),
                    };
                }
                Projection::Index(index_local) => {
                    unimplemented!();
                    // TODO: This probably will need a `usize` type.
                    // ptr += self.read_local(*index_local),
                }
            }
        }

        (ptr, self.tys.find_or_insert(ty.clone()))
    }

    fn resolve_rvalue(&mut self, rvalue: &RValue) -> Value {
        match rvalue {
            RValue::Use(operand) => self.resolve_operand(operand),
            RValue::Ref(place) => {
                let (ptr, _ty) = self.resolve_place(place);

                Value::Ref(ptr)
            }
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
                    UnOp::Neg => -rhs,
                }
            }
        }
    }

    /// Return the value of the provided operand
    fn resolve_operand(&mut self, operand: &Operand) -> Value {
        match operand {
            Operand::Place(place) => {
                let (ptr, ty) = self.resolve_place(place);

                let ty = &self.tys[ty];

                let mut buf = vec![0; ty.size()];
                self.stack.read(ptr, &mut buf);

                ty.get_value(&buf)
            }
            Operand::Constant(value) => value.clone(),
        }
    }
}

indexed_vec!(InterpreterLocals<Local, InterpreterLocal>);

#[derive(Clone, Debug)]
struct InterpreterLocal {
    ty: Ty,
    state: LocalState,
    ptr: Pointer,
}

#[derive(Clone, Debug)]
enum LocalState {
    Alive,
    Dead,
}
