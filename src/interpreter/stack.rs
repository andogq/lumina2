use crate::ir::{Pointer, Ty, TyInfo, Tys, Value};

#[derive(Clone, Debug)]
pub struct Stack {
    buf: [u8; 1024],
    frames: Vec<Frame>,
    sp: usize,
}

impl Stack {
    pub fn new() -> Self {
        Self {
            buf: [0; 1024],
            frames: Vec::new(),
            sp: 0,
        }
    }

    pub fn push_frame(&mut self) {
        self.frames.push(Frame { start: self.sp });
    }

    pub fn pop_frame(&mut self) {
        let frame = self.frames.pop().expect("at least one frame on the stack");
        self.sp = frame.start;
    }

    pub fn get_frame(&mut self) -> FrameRef<'_> {
        let frame = self.frames.last().expect("at least one frame on the stack");

        FrameRef {
            buf: &mut self.buf[frame.start..],
            sp: &mut self.sp,
        }
    }

    /// Will serialise the provided value to the location of `ptr`. The stack pointer will not be
    /// advanced, and no checks will be performed to validate if the write is valid.
    pub fn write_value(&mut self, ptr: Pointer, ty: &TyInfo, value: Value, tys: &Tys) {
        let buf = &mut self.buf[*ptr..*ptr + ty.allocated_size(tys)];

        match value {
            Value::U8(value) => buf.copy_from_slice(&value.to_ne_bytes()),
            Value::I8(value) => buf.copy_from_slice(&value.to_ne_bytes()),
            Value::Ref(pointer) => buf.copy_from_slice(&pointer.to_ne_bytes()),
            Value::Array(array) => {
                array.into_iter().enumerate().for_each(|(i, value)| {
                    let TyInfo::Array { ty, length: _ } = ty else {
                        panic!("need array");
                    };
                    let ty = tys.get(*ty);

                    let ptr = ptr + (i * ty.allocated_size(tys));
                    self.write_value(ptr, &ty, value, tys);
                });
            }
        }
    }

    pub fn read_value(&self, ptr: Pointer, ty: Ty, tys: &Tys) -> Value {
        let ty = &tys.get(ty);
        let ty_size = ty.allocated_size(tys);

        let buf = &self.buf[*ptr..*ptr + ty_size];

        match ty {
            TyInfo::U8 => Value::from_u8(u8::from_ne_bytes(buf.try_into().unwrap())),
            TyInfo::I8 => Value::from_i8(i8::from_ne_bytes(buf.try_into().unwrap())),
            TyInfo::Ref(_) => {
                Value::from_ref(Pointer::new(usize::from_ne_bytes(buf.try_into().unwrap())))
            }
            TyInfo::Slice(_) => unimplemented!(),
            TyInfo::Array { ty: _, length: _ } => unimplemented!(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Frame {
    start: usize,
}

pub struct FrameRef<'s> {
    sp: &'s mut usize,
    buf: &'s mut [u8],
}

impl<'s> FrameRef<'s> {
    pub fn alloca(&mut self, amount: usize) -> Pointer {
        let ptr = Pointer::new(*self.sp);
        *self.sp += amount;
        ptr
    }
}
