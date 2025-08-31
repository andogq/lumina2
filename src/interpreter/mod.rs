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
                .alloca(interpreter.tys[local_decl.ty].allocated_size(&interpreter.tys));
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
                                // TODO: Check length and inner ty
                                | (Value::Array(_), TyInfo::Array { .. })
                        ) {
                            panic!("mis-matched value and target type: {target_ty:?}, {value:?}");
                        }

                        interpreter.stack.write_value(
                            target_ptr,
                            target_ty,
                            value,
                            &interpreter.tys,
                        );
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
        let output = interpreter
            .stack
            .read_value(local.ptr, local.ty, &interpreter.tys);

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

        self.stack.read_value(local.ptr, local.ty, &self.tys)
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

        let mut ty = local.ty;
        let mut ptr = local.ptr;

        for proj in &place.projection {
            match proj {
                // Look up `ptr` in the stack, and replace `ptr` with that value.
                Projection::Deref => {
                    // Read the reference pointer out of memory.
                    ptr = self
                        .stack
                        .read_value(ptr, ty, &self.tys)
                        .into_ref()
                        .unwrap();

                    // Determine the type of the reference.
                    let TyInfo::Ref(inner_ty) = &self.tys[ty] else {
                        panic!("cannot deref non-pointer: {ty:?}");
                    };
                    ty = *inner_ty;
                }
                Projection::Field(field_offset) => {
                    ptr += *field_offset;

                    match ty {
                        _ => panic!("cannot project field on ty without field"),
                    };
                }
                Projection::Index(index_local) => {
                    let TyInfo::Array {
                        ty: array_item_ty,
                        length,
                    } = &self.tys[ty]
                    else {
                        panic!("can only index array, found {ty:?}");
                    };

                    let index_local = self.get_alive_local(*index_local);
                    let index = self
                        .stack
                        .read_value(index_local.ptr, index_local.ty, &self.tys)
                        .into_u8()
                        .expect("index must be u8") as usize;

                    assert!(
                        index < *length,
                        "cannot index beyond array bounds: {index} (length is {length})"
                    );

                    // Perform the indexing on the pointer.
                    ptr += index * self.tys[*array_item_ty].allocated_size(&self.tys);

                    // Update the type.
                    ty = *array_item_ty;
                }
            }
        }

        (ptr, ty)
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
            RValue::Aggregate { values } => Value::Array(
                values
                    .iter()
                    .map(|value| self.resolve_operand(value))
                    .collect(),
            ),
        }
    }

    /// Return the value of the provided operand
    fn resolve_operand(&mut self, operand: &Operand) -> Value {
        match operand {
            Operand::Place(place) => {
                let (ptr, ty) = self.resolve_place(place);

                self.stack.read_value(ptr, ty, &self.tys)
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
