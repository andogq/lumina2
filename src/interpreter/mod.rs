mod stack;

use crate::{
    BasicBlock, BinOp, Local, Operand, Place, Pointer, Projection, RValue, Statement, Terminator,
    Ty, TyInfo, UnOp, Value, indexed_vec,
    interpreter::stack::Stack,
    ir::{
        CastKind, PointerCoercion,
        ctx::{Function, IrCtx},
    },
};

#[derive(Clone, Debug)]
pub struct Interpreter<'ctx> {
    ctx: &'ctx IrCtx,
    locals: InterpreterLocals,
    stack: Stack,
}

impl<'ctx> Interpreter<'ctx> {
    pub fn new(ctx: &'ctx IrCtx) -> Self {
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
            let ptr = self.stack.get_frame().alloca(
                self.ctx
                    .tys
                    .get(local_decl.ty)
                    .allocated_size(&self.ctx.tys),
            );
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

                        let target_ty = &self.ctx.tys.get(target_ty);
                        let value_ty = &self.ctx.tys.get(value_ty);

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
        let mut ptr_data = None;

        for proj in &place.projection {
            let mut next_ptr_data = None;

            match proj {
                // Look up `ptr` in the stack, and replace `ptr` with that value.
                Projection::Deref => {
                    // Read the reference pointer out of memory.
                    ptr = match self.stack.read_value(ptr, ty, &self.ctx.tys) {
                        Value::Ref(ptr) => ptr,
                        Value::FatPointer { ptr, data } => {
                            next_ptr_data = Some(data);

                            ptr
                        }
                        _ => panic!("cannot dereference non-pointer"),
                    };

                    // Determine the type of the reference.
                    let TyInfo::Ref(inner_ty) = &self.ctx.tys.get(ty) else {
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
                    let (array_item_ty, length) = match self.ctx.tys.get(ty) {
                        TyInfo::Array { ty, length } => (ty, length),
                        TyInfo::Slice(ty) => (ty, ptr_data.expect("pointer data from fat deref")),
                        _ => {
                            panic!("can only index array, found {:?}", self.ctx.tys.get(ty));
                        }
                    };

                    let index_local = self.get_alive_local(*index_local);
                    let index = self
                        .stack
                        .read_value(index_local.ptr, index_local.ty, &self.ctx.tys)
                        .into_u8()
                        .expect("index must be u8") as usize;

                    assert!(
                        index < length,
                        "cannot index beyond array bounds: {index} (length is {length})"
                    );

                    // Perform the indexing on the pointer.
                    ptr += index
                        * self
                            .ctx
                            .tys
                            .get(array_item_ty)
                            .allocated_size(&self.ctx.tys);

                    // Update the type.
                    ty = array_item_ty;
                }
            }

            ptr_data = next_ptr_data;
        }

        (ptr, ty)
    }

    fn resolve_rvalue(&mut self, rvalue: &RValue) -> (Value, Ty) {
        match rvalue {
            RValue::Use(operand) => self.resolve_operand(operand),
            RValue::Ref(place) => {
                let (ptr, ty) = self.resolve_place(place);

                (
                    Value::Ref(ptr),
                    self.ctx.tys.find_or_insert(TyInfo::Ref(ty)),
                )
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

                match op {
                    UnOp::Not => (!rhs, ty),
                    UnOp::Neg => (-rhs, ty),
                    UnOp::PtrMetadata => {
                        let Value::FatPointer { ptr: _, data } = rhs else {
                            panic!("can only access pointer metadata metadata of fat pointer");
                        };

                        (
                            // HACK: Don't force data into u8
                            Value::U8(data as u8),
                            self.ctx.tys.find_or_insert(TyInfo::U8),
                        )
                    }
                }
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
            RValue::Cast {
                kind,
                op,
                ty: cast_ty,
            } => {
                let (op, op_ty) = self.resolve_operand(op);

                match kind {
                    CastKind::PointerCoercion(PointerCoercion::Unsize) => {
                        let TyInfo::Ref(ref_ty) = self.ctx.tys.get(*cast_ty) else {
                            panic!("can only unsize coerce to reference");
                        };
                        let TyInfo::Ref(op_ty) = self.ctx.tys.get(op_ty) else {
                            panic!("can only unsize coerce if operand is a reference");
                        };

                        let op_ty = self.ctx.tys.get(op_ty);
                        let ref_ty = self.ctx.tys.get(ref_ty);

                        match (op_ty, ref_ty) {
                            (
                                TyInfo::Array {
                                    ty: inner_ty,
                                    length,
                                },
                                TyInfo::Slice(slice_ty),
                            ) if inner_ty == slice_ty => {
                                let Value::Ref(ptr) = op else {
                                    panic!("cast operand expected to be pointer");
                                };

                                (Value::FatPointer { ptr, data: length }, *cast_ty)
                            }
                            (op_ty, ref_ty) => panic!(
                                "cannot coerce pointer to {op_ty:?} into pointer of {ref_ty:?}"
                            ),
                        }
                    }
                }
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
            Operand::Constant(value) => (value.clone(), value.get_const_ty(&self.ctx.tys)),
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
