use crate::prelude::*;

#[derive(Clone, Debug)]
pub struct DisjointUnionSet<T>(HashMap<T, (T, usize)>);

impl<T> DisjointUnionSet<T>
where
    T: Clone + Copy + PartialEq + Eq + Hash,
{
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn union_sets(&mut self, lhs: T, rhs: T) -> T {
        let mut lhs = self.get(lhs);
        let mut rhs = self.get(rhs);

        if lhs.0 == rhs.0 {
            return lhs.0;
        }

        // Ensure the rhs is the shortest side.
        if rhs.1 > lhs.1 {
            std::mem::swap(&mut lhs, &mut rhs);
        }

        let root = lhs.0;
        self.0.insert(rhs.0, (root, 1));
        root
    }

    pub fn find_set(&self, id: T) -> T {
        self.get(id).0
    }

    pub fn keys(&self) -> impl Iterator<Item = &T> {
        self.0.keys()
    }

    fn get(&self, id: T) -> (T, usize) {
        let Some((parent, depth)) = self.0.get(&id) else {
            return (id, 0);
        };

        let (node, node_depth) = self.get(*parent);

        (node, depth + node_depth)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[fixture]
    fn map() -> DisjointUnionSet<usize> {
        DisjointUnionSet::<usize>::new()
    }

    #[rstest]
    fn no_parent(map: DisjointUnionSet<usize>) {
        assert_eq!(map.find_set(0), 0, "should be in set by itself");
    }

    #[rstest]
    fn single_parent(mut map: DisjointUnionSet<usize>) {
        map.union_sets(0, 1);
        assert_eq!(map.find_set(0), map.find_set(1), "should be in same set");
    }

    #[rstest]
    fn already_in_same_set(mut map: DisjointUnionSet<usize>) {
        map.union_sets(0, 1);
        map.union_sets(1, 0);
        assert_eq!(
            map.find_set(0),
            map.find_set(1),
            "should remain in same set, even if already union"
        );
    }

    #[rstest]
    fn self_union(mut map: DisjointUnionSet<usize>) {
        map.union_sets(0, 0);
        assert_eq!(map.find_set(0), map.find_set(0));
    }

    #[rstest]
    fn deep_parent(mut map: DisjointUnionSet<usize>) {
        map.union_sets(0, 1);
        map.union_sets(1, 2);
        map.union_sets(2, 3);

        assert_eq!(
            map.find_set(0),
            map.find_set(1),
            "nodes should be in same set"
        );
        assert_eq!(
            map.find_set(0),
            map.find_set(2),
            "nodes should be in same set"
        );
        assert_eq!(
            map.find_set(0),
            map.find_set(3),
            "nodes should be in same set"
        );
    }

    #[rstest]
    fn disjoint_sets(mut map: DisjointUnionSet<usize>) {
        map.union_sets(0, 1);
        map.union_sets(2, 3);

        assert_ne!(
            map.find_set(0),
            map.find_set(2),
            "nodes should not be in same set"
        );
    }
}
