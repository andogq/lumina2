#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Ty {
    I8,
    U8,
    Unit,
    Ref(Box<Ty>),
    Slice(Box<Ty>),
    Array(Box<Ty>, usize),
}
