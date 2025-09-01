use std::{
    fmt::Display,
    marker::PhantomData,
    ops::{Deref, Index, IndexMut},
};

/// Helper macro to create a vec which is indexed by a new-typed value.
#[macro_export]
macro_rules! indexed_vec {
    ($vis:vis key $key:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
        $vis struct $key($crate::util::indexed_vec::Key);

        #[allow(unused)]
        impl $key {
            $vis fn zero() -> Self {
                Self($crate::util::indexed_vec::Key::zero())
            }

            $vis fn of(n: usize) -> Self {
                Self($crate::util::indexed_vec::Key::of(n))
            }
        }

        impl From<$crate::util::indexed_vec::Key> for $key {
            fn from(key: $crate::util::indexed_vec::Key) -> Self {
                Self(key)
            }
        }

        impl From<$key> for $crate::util::indexed_vec::Key {
            fn from(key: $key) -> Self {
                key.0
            }
        }
    };

    ($vis:vis $name:ident<$key:ident, $value:ty>) => {
        $vis type $name = $crate::util::indexed_vec::IndexedVec<$key, $value>;
    };
}

#[derive(Clone, Debug)]
pub struct IndexedVec<K, V>(Vec<V>, PhantomData<fn() -> K>);

impl<K, V> IndexedVec<K, V> {
    pub fn new() -> Self {
        Self(Vec::new(), PhantomData)
    }
}

impl<K, V> IndexedVec<K, V>
where
    K: From<Key> + Into<Key>,
{
    pub fn insert(&mut self, value: V) -> K {
        let key = Key(self.0.len()).into();
        self.0.push(value);
        key
    }

    pub fn get(&self, key: K) -> Option<&V> {
        self.0.get(key.into().0)
    }

    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.0.get_mut(key.into().0)
    }

    pub fn iter_keys(&self) -> impl Iterator<Item = (K, &V)> {
        self.0.iter().enumerate().map(|(i, v)| (Key(i).into(), v))
    }
}

impl<K, V> Index<K> for IndexedVec<K, V>
where
    K: From<Key> + Into<Key>,
{
    type Output = V;

    fn index(&self, key: K) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<K, V> IndexMut<K> for IndexedVec<K, V>
where
    K: From<Key> + Into<Key>,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Key(usize);

impl Key {
    pub fn zero() -> Self {
        Self(0)
    }

    pub fn of(n: usize) -> Self {
        Self(n)
    }
}

impl Display for Key {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}
