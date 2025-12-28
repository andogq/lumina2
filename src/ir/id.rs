use std::{fmt::Debug, hash::Hash};

macro_rules! create_id {
    ($id:ident) => {
        #[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
        pub struct $id(usize);

        impl Id for $id {
            fn from_id(id: usize) -> Self {
                Self(id)
            }

            fn into_id(self) -> usize {
                self.0
            }
        }
    };
}

create_id!(ScopeId);
create_id!(StringId);
create_id!(BindingId);

pub trait Id: Clone + Copy + Debug + Eq + PartialEq + Hash {
    fn from_id(id: usize) -> Self;
    fn into_id(self) -> usize;
}
