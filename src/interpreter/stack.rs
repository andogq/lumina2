use std::ops::{Add, AddAssign};

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

    pub fn read(&self, ptr: Pointer, buf: &mut [u8]) {
        buf.copy_from_slice(&self.buf[ptr.0..ptr.0 + buf.len()]);
    }

    pub fn write(&mut self, ptr: Pointer, bytes: &[u8]) {
        self.buf[ptr.0..ptr.0 + bytes.len()].copy_from_slice(bytes);
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
        let ptr = Pointer(*self.sp);
        *self.sp += amount;
        ptr
    }
}

/// Pointer into the stack.
#[derive(Clone, Copy, Debug)]
pub struct Pointer(usize);
impl Pointer {
    pub fn new(ptr: usize) -> Self {
        Self(ptr)
    }
}

impl Add<usize> for Pointer {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        Self(self.0 + rhs)
    }
}

impl AddAssign<usize> for Pointer {
    fn add_assign(&mut self, rhs: usize) {
        self.0 += rhs;
    }
}
