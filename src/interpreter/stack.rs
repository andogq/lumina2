use std::ops::{Add, AddAssign, Index, IndexMut};

#[derive(Clone, Debug)]
pub struct Stack {
    buf: [usize; 1024],
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
}

impl Index<&Pointer> for Stack {
    type Output = usize;

    fn index(&self, ptr: &Pointer) -> &Self::Output {
        &self.buf[ptr.0]
    }
}

impl Index<Pointer> for Stack {
    type Output = usize;

    fn index(&self, ptr: Pointer) -> &Self::Output {
        &self[&ptr]
    }
}

impl IndexMut<&Pointer> for Stack {
    fn index_mut(&mut self, ptr: &Pointer) -> &mut Self::Output {
        &mut self.buf[ptr.0]
    }
}

impl IndexMut<Pointer> for Stack {
    fn index_mut(&mut self, ptr: Pointer) -> &mut Self::Output {
        &mut self[&ptr]
    }
}

#[derive(Clone, Debug)]
pub struct Frame {
    start: usize,
}

pub struct FrameRef<'s> {
    sp: &'s mut usize,
    buf: &'s mut [usize],
}

impl<'s> FrameRef<'s> {
    pub fn alloca(&mut self) -> Pointer {
        let ptr = Pointer(*self.sp);
        *self.sp += 1;
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
