use crate::prelude::*;

/// A set mapping IDs (`I`) to data (`T`).
///
/// IDs which are equivalent can be merged, to point at each other and the associated data.
#[derive(Clone, Debug)]
pub struct DisjointUnionSet<I, T>(IndexedVec<I, Record<I, T>>);

/// Record stored within [`DisjointUnionSet`].
#[derive(Clone, Debug)]
enum Record<I, T> {
    /// This node contains data.
    Root(T),
    /// This node points to another node.
    Redirect(I),
}

impl<I, T> Record<I, T> {
    /// Consume this record, and extract the [`Record::Root`] variant.
    pub fn into_root(self) -> Option<T> {
        match self {
            Self::Root(root) => Some(root),
            _ => None,
        }
    }

    /// From a record reference, and extract the [`Record::Root`] variant.
    pub fn as_root(&self) -> Option<&T> {
        match self {
            Self::Root(root) => Some(root),
            _ => None,
        }
    }
}

impl<I, T> DisjointUnionSet<I, T>
where
    I: Id,
{
    /// Create an empty set.
    pub fn new() -> Self {
        Self(IndexedVec::new())
    }

    /// Insert a value into the set, producing the ID which corresponds to the new root.
    pub fn insert(&mut self, data: T) -> I {
        self.0.insert(Record::Root(data))
    }

    /// Find the root starting at a given ID.
    ///
    /// This will compress the path as it traverses.
    pub fn find_root(&mut self, id: I) -> I {
        match &self.0[id] {
            Record::Root(_) => id,
            Record::Redirect(next_id) => {
                // Recurse to find the root.
                let root = self.find_root(*next_id);
                // Root has been found, update this node to point directly at it.
                self.0[id] = Record::Redirect(root);
                root
            }
        }
    }

    /// Fetch the data associated with an ID.
    pub fn get(&mut self, id: I) -> &T {
        let id = self.find_root(id);
        self.0[id]
            .as_root()
            .expect("`find_root` ensures that ID points to a root")
    }

    /// Fetch the data associate with multiple nodes.
    pub fn get_multiple<const N: usize>(&mut self, ids: [I; N]) -> [&T; N] {
        ids
            // Perform path compression on all IDs first.
            .map(|id| self.find_root(id))
            // Manually fetch each node to bypass borrow checker.
            .map(|id| {
                self.0[id]
                    .as_root()
                    .expect("`find_root` ensures that ID points to a root")
            })
    }

    /// Redirect `target` to point to `to`.
    ///
    /// If the IDs are already equivalent, [`None`] will be returned. Otherwise [`Some`] will be
    /// returned containing the data that was previously held in `target`.
    pub fn redirect(&mut self, target: I, to: I) -> Option<T> {
        let target = self.find_root(target);
        let to = self.find_root(to);

        if target == to {
            return None;
        }

        Some(
            std::mem::replace(&mut self.0[target], Record::Redirect(to))
                .into_root()
                .expect("`find_root` ensures that ID points to a root"),
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;

    create_id!(TestId);

    type Set = DisjointUnionSet<TestId, usize>;

    #[fixture]
    fn map() -> Set {
        Set::new()
    }

    #[fixture]
    fn init_map<const N: usize>(mut map: Set) -> (Set, [TestId; N]) {
        let ids = std::array::from_fn(|i| map.insert(i));

        (map, ids)
    }

    #[rstest]
    fn no_parent(#[from(init_map)] (mut map, id): (Set, [TestId; 1])) {
        assert_eq!(map.find_root(id[0]), id[0], "should be in set by itself");
    }

    #[rstest]
    fn single_parent(#[from(init_map)] (mut map, id): (Set, [TestId; 2])) {
        assert_eq!(
            map.redirect(id[0], id[1]).unwrap(),
            0,
            "node should originally hold `0`"
        );
        assert_eq!(
            map.find_root(id[0]),
            id[1],
            "node should point to `1` after redirect"
        );

        let [lhs, rhs] = map.get_multiple([id[0], id[1]]);
        assert_eq!(lhs, rhs, "should contain the same value");
    }

    #[rstest]
    fn already_in_same_set(#[from(init_map)] (mut map, id): (Set, [TestId; 2])) {
        assert_eq!(map.redirect(id[0], id[1]).unwrap(), 0);
        assert_eq!(
            map.redirect(id[1], id[0]),
            None,
            "redirect shouldn't occur since nodes are already equal"
        );
        assert_eq!(
            map.find_root(id[0]),
            map.find_root(id[1]),
            "should remain in same set, even if already union"
        );
    }

    #[rstest]
    fn self_union(#[from(init_map)] (mut map, id): (Set, [TestId; 1])) {
        assert_eq!(
            map.redirect(id[0], id[0]),
            None,
            "redirect shouldn't occur since nodes are already equal"
        );
        assert_eq!(map.find_root(id[0]), id[0]);
    }

    #[rstest]
    fn deep_parent(#[from(init_map)] (mut map, id): (Set, [TestId; 4])) {
        assert_eq!(map.redirect(id[0], id[1]).unwrap(), 0);
        assert_eq!(map.redirect(id[1], id[2]).unwrap(), 1);
        assert_eq!(map.redirect(id[2], id[3]).unwrap(), 2);

        assert_eq!(*map.get(id[0]), 3);
        assert_eq!(*map.get(id[1]), 3);
        assert_eq!(*map.get(id[2]), 3);
        assert_eq!(*map.get(id[3]), 3);

        assert_eq!(
            map.find_root(id[0]),
            map.find_root(id[1]),
            "nodes should be in same set"
        );
        assert_eq!(
            map.find_root(id[0]),
            map.find_root(id[2]),
            "nodes should be in same set"
        );
        assert_eq!(
            map.find_root(id[0]),
            map.find_root(id[3]),
            "nodes should be in same set"
        );
    }

    #[rstest]
    fn disjoint_sets(#[from(init_map)] (mut map, id): (Set, [TestId; 4])) {
        assert_eq!(map.redirect(id[0], id[1]).unwrap(), 0);
        assert_eq!(map.redirect(id[2], id[3]).unwrap(), 2);

        assert_ne!(
            map.find_root(id[0]),
            map.find_root(id[2]),
            "nodes should not be in same set"
        );
    }
}
