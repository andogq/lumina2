#[derive(Clone, Debug)]
pub enum Ty {
    I8,
    U8,
    Boolean,
    Unit,
    Unreachable,
    Ref(Box<Ty>),
    Slice(Box<Ty>),
    Array(Box<Ty>, usize),
}

impl std::hash::Hash for Ty {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
    }
}

impl PartialEq for Ty {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Ref(l0), Self::Ref(r0)) => l0 == r0,
            (Self::Slice(l0), Self::Slice(r0)) => l0 == r0,
            (Self::Array(l0, l1), Self::Array(r0, r1)) => l0 == r0 && l1 == r1,
            (Self::Unreachable, _) | (_, Self::Unreachable) => true,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

impl Eq for Ty {}
