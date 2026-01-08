use crate::{prelude::*, ty::TypeVarId};

#[derive(Clone, Debug)]
pub struct DisjointUnionSet(HashMap<TypeVarId, (TypeVarId, usize)>);

impl DisjointUnionSet {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn union_sets(&mut self, lhs: TypeVarId, rhs: TypeVarId) -> TypeVarId {
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

    pub fn find_set(&self, id: TypeVarId) -> TypeVarId {
        self.get(id).0
    }

    pub fn keys(&self) -> impl Iterator<Item = &TypeVarId> {
        self.0.keys()
    }

    fn get(&self, id: TypeVarId) -> (TypeVarId, usize) {
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
    fn type_var<const N: usize>() -> [TypeVarId; N] {
        (0..N)
            .map(TypeVarId::from_id)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    #[fixture]
    fn map() -> DisjointUnionSet {
        DisjointUnionSet::new()
    }

    #[rstest]
    fn no_parent(type_var: [TypeVarId; 1], map: DisjointUnionSet) {
        assert_eq!(
            map.find_set(type_var[0]),
            type_var[0],
            "should be in set by itself"
        );
    }

    #[rstest]
    fn single_parent(type_var: [TypeVarId; 2], mut map: DisjointUnionSet) {
        map.union_sets(type_var[0], type_var[1]);
        assert_eq!(
            map.find_set(type_var[0]),
            map.find_set(type_var[1]),
            "should be in same set"
        );
    }

    #[rstest]
    fn already_in_same_set(type_var: [TypeVarId; 2], mut map: DisjointUnionSet) {
        map.union_sets(type_var[0], type_var[1]);
        map.union_sets(type_var[1], type_var[0]);
        assert_eq!(
            map.find_set(type_var[0]),
            map.find_set(type_var[1]),
            "should remain in same set, even if already union"
        );
    }

    #[rstest]
    fn self_union(type_var: [TypeVarId; 1], mut map: DisjointUnionSet) {
        map.union_sets(type_var[0], type_var[0]);
        assert_eq!(map.find_set(type_var[0]), map.find_set(type_var[0]));
    }

    #[rstest]
    fn deep_parent(type_var: [TypeVarId; 4], mut map: DisjointUnionSet) {
        map.union_sets(type_var[0], type_var[1]);
        map.union_sets(type_var[1], type_var[2]);
        map.union_sets(type_var[2], type_var[3]);

        assert_eq!(
            map.find_set(type_var[0]),
            map.find_set(type_var[1]),
            "nodes should be in same set"
        );
        assert_eq!(
            map.find_set(type_var[0]),
            map.find_set(type_var[2]),
            "nodes should be in same set"
        );
        assert_eq!(
            map.find_set(type_var[0]),
            map.find_set(type_var[3]),
            "nodes should be in same set"
        );
    }

    #[rstest]
    fn disjoint_sets(type_var: [TypeVarId; 4], mut map: DisjointUnionSet) {
        map.union_sets(type_var[0], type_var[1]);
        map.union_sets(type_var[2], type_var[3]);

        assert_ne!(
            map.find_set(type_var[0]),
            map.find_set(type_var[2]),
            "nodes should not be in same set"
        );
    }
}
