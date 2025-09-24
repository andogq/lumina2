use std::ops::{Add, AddAssign, Deref};

/// Pointer into memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Pointer(usize);
impl Pointer {
    pub fn new(ptr: usize) -> Self {
        Self(ptr)
    }
}

impl Deref for Pointer {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
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
