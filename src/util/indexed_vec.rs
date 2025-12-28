use crate::prelude::*;

#[derive(Clone, Debug)]
pub struct IndexedVec<K, V>(Vec<V>, PhantomData<fn() -> K>);

impl<K, V> IndexedVec<K, V> {
    pub fn new() -> Self {
        Self(Vec::new(), PhantomData)
    }

    #[doc(hidden)]
    pub fn from_vec(vec: Vec<V>) -> Self {
        Self(vec, PhantomData)
    }
}

impl<K, V> IndexedVec<K, V>
where
    K: Id,
{
    pub fn insert(&mut self, value: V) -> K {
        let key = K::from_id(self.0.len());
        self.0.push(value);
        key
    }

    pub fn get(&self, key: K) -> Option<&V> {
        self.0.get(key.into_id())
    }

    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.0.get_mut(key.into_id())
    }

    pub fn iter_keys(&self) -> impl Iterator<Item = (K, &V)> {
        self.0.iter().enumerate().map(|(i, v)| (K::from_id(i), v))
    }
}

impl<K, V> Index<K> for IndexedVec<K, V>
where
    K: Id,
{
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<K, V> IndexMut<K> for IndexedVec<K, V>
where
    K: Id,
{
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

impl<K, V> Default for IndexedVec<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Deref for IndexedVec<K, V> {
    type Target = [V];

    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

#[macro_export]
macro_rules! indexed_vec {
    ($($toks:tt)*) => (
        $crate::util::indexed_vec::IndexedVec::from_vec(::std::vec![$($toks)*])
    );
}

/// Create a new-type ID, which implements the [`Id`] trait, suitable for use with [`IndexedVec`].
///
/// [`IndexedVec`]: crate::util::indexed_vec::IndexedVec
#[macro_export]
macro_rules! create_id {
    ($id:ident) => {
        #[derive(
            ::core::clone::Clone,
            ::core::marker::Copy,
            ::core::fmt::Debug,
            ::core::cmp::Eq,
            ::core::cmp::PartialEq,
            ::core::hash::Hash,
        )]
        pub struct $id(usize);

        impl $crate::util::indexed_vec::Id for $id {
            fn from_id(id: usize) -> Self {
                Self(id)
            }

            fn into_id(self) -> usize {
                self.0
            }
        }
    };
}

pub trait Id: Clone + Copy + Debug + Eq + PartialEq + Hash {
    fn from_id(id: usize) -> Self;
    fn into_id(self) -> usize;
}
