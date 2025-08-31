mod stack;

use crate::{
    BasicBlock, BinOp, Local, Operand, Place, Pointer, Projection, RValue, Statement, Terminator,
    Ty, TyInfo, UnOp, Value, indexed_vec,
    interpreter::stack::Stack,
    ir::ctx::{Function, IrCtx},
};

#[derive(Clone, Debug)]
pub struct Interpreter {
    ctx: IrCtx,
    locals: InterpreterLocals,
    stack: Stack,
}

impl Interpreter {
    pub fn new(ctx: IrCtx) -> Self {
        Self {
            ctx,
            locals: InterpreterLocals::new(),
            stack: Stack::new(),
        }
    }

    pub fn run(&mut self, function: Function) -> Value {
        // HACK: Don't do this
        self.stack = Stack::new();
        self.locals = InterpreterLocals::new();

        self.stack.push_frame();

        // TODO: Don't clone here.
        let body = &self.ctx.functions[function].clone();

        // Create the locals.
        for local_decl in &*body.local_decls {
            let ptr = self
                .stack
                .get_frame()
                .alloca(self.ctx.tys[local_decl.ty].allocated_size(&self.ctx.tys));
            self.locals.insert(InterpreterLocal {
                ty: local_decl.ty,
                ptr,
                state: LocalState::Dead,
            });
        }

        let return_local = Local::zero();
        self.alive_local(return_local);

        let mut next_block = BasicBlock::zero();
        loop {
            let block = &body.basic_blocks[next_block];

            for statement in &block.statements {
                match statement {
                    Statement::Assign { place, rvalue } => {
                        let (target_ptr, target_ty) = self.resolve_place(place);
                        let (value, value_ty) = self.resolve_rvalue(rvalue);

                        let target_ty = &self.ctx.tys[target_ty];
                        let value_ty = &self.ctx.tys[value_ty];

                        assert_eq!(target_ty, value_ty, "cannot assign mismatched tys");

                        self.stack
                            .write_value(target_ptr, target_ty, value, &self.ctx.tys);
                    }
                    Statement::StorageDead(local) => self.kill_local(*local),
                    Statement::StorageLive(local) => self.alive_local(*local),
                }
            }

            match &block.terminator {
                Terminator::Call { .. } => todo!(),
                Terminator::Goto(basic_block) => next_block = *basic_block,
                Terminator::Return => break,
                Terminator::SwitchInt {
                    discriminator,
                    targets,
                    otherwise,
                } => {
                    let (discriminator, _) = self.resolve_operand(discriminator);
                    next_block = targets
                        .iter()
                        .find(|(value, _)| discriminator == *value)
                        .map(|(_, block)| *block)
                        .unwrap_or(*otherwise);
                }
            }
        }

        let local = self.get_alive_local(return_local);
        let output = self.stack.read_value(local.ptr, local.ty, &self.ctx.tys);

        self.stack.pop_frame();

        output
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

        self.stack.read_value(local.ptr, local.ty, &self.ctx.tys)
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
                        .read_value(ptr, ty, &self.ctx.tys)
                        .into_ref()
                        .unwrap();

                    // Determine the type of the reference.
                    let TyInfo::Ref(inner_ty) = &self.ctx.tys[ty] else {
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
                    } = &self.ctx.tys[ty]
                    else {
                        panic!("can only index array, found {ty:?}");
                    };

                    let index_local = self.get_alive_local(*index_local);
                    let index = self
                        .stack
                        .read_value(index_local.ptr, index_local.ty, &self.ctx.tys)
                        .into_u8()
                        .expect("index must be u8") as usize;

                    assert!(
                        index < *length,
                        "cannot index beyond array bounds: {index} (length is {length})"
                    );

                    // Perform the indexing on the pointer.
                    ptr += index * self.ctx.tys[*array_item_ty].allocated_size(&self.ctx.tys);

                    // Update the type.
                    ty = *array_item_ty;
                }
            }
        }

        (ptr, ty)
    }

    fn resolve_rvalue(&mut self, rvalue: &RValue) -> (Value, Ty) {
        match rvalue {
            RValue::Use(operand) => self.resolve_operand(operand),
            RValue::Ref(place) => {
                let (ptr, ty) = self.resolve_place(place);

                (Value::Ref(ptr), ty)
            }
            RValue::BinaryOp { op, lhs, rhs } => {
                let (lhs, lhs_ty) = self.resolve_operand(lhs);
                let (rhs, rhs_ty) = self.resolve_operand(rhs);

                if lhs_ty != rhs_ty {
                    panic!("lhs ty ({lhs_ty:?}) must equal rhs ty ({rhs_ty:?})");
                }

                (
                    match op {
                        BinOp::Add => lhs + rhs,
                        BinOp::Sub => lhs - rhs,
                        BinOp::Mul => lhs * rhs,
                        BinOp::Div => lhs / rhs,
                    },
                    // NOTE: Reuse lhs ty, since it should be the same as rhs ty.
                    lhs_ty,
                )
            }
            RValue::UnaryOp { op, rhs } => {
                let (rhs, ty) = self.resolve_operand(rhs);

                (
                    match op {
                        UnOp::Not => !rhs,
                        UnOp::Neg => -rhs,
                    },
                    ty,
                )
            }
            RValue::Aggregate { values } => {
                assert!(!values.is_empty(), "cannot aggregate empty array");

                let (values, tys): (Vec<_>, Vec<_>) = values
                    .iter()
                    .map(|value| self.resolve_operand(value))
                    .unzip();

                assert!(tys.iter().all(|ty| *ty == tys[0]));

                (
                    Value::Array(values),
                    self.ctx.tys.find_or_insert(TyInfo::Array {
                        ty: tys[0],
                        length: tys.len(),
                    }),
                )
            }
        }
    }

    /// Return the value of the provided operand
    fn resolve_operand(&mut self, operand: &Operand) -> (Value, Ty) {
        match operand {
            Operand::Place(place) => {
                let (ptr, ty) = self.resolve_place(place);

                (self.stack.read_value(ptr, ty, &self.ctx.tys), ty)
            }
            Operand::Constant(value) => (value.clone(), value.get_const_ty(&mut self.ctx.tys)),
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
