use std::collections::HashMap;

use crate::stages::ty::TypeVarId;

#[derive(Clone, Debug)]
pub struct DisjointUnionSet(HashMap<TypeVarId, (TypeVarId, usize)>);

impl DisjointUnionSet {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn union_sets(&mut self, lhs: TypeVarId, rhs: TypeVarId) -> TypeVarId {
        let mut lhs = self.get(&lhs);
        let mut rhs = self.get(&rhs);

        if lhs.0 == rhs.0 {
            return lhs.0.clone();
        }

        // Ensure the rhs is the shortest side.
        if rhs.1 > lhs.1 {
            std::mem::swap(&mut lhs, &mut rhs);
        }

        let root = lhs.0.clone();
        self.0.insert(rhs.0.clone(), (root.clone(), 1));
        root
    }

    pub fn find_set<'u: 'i, 'i>(&'u self, id: &'i TypeVarId) -> &'i TypeVarId {
        self.get(id).0
    }

    pub fn keys(&self) -> impl Iterator<Item = &TypeVarId> {
        self.0.keys()
    }

    fn depth(&self, id: &TypeVarId) -> usize {
        self.get(id).1
    }

    fn is_root(&self, id: &TypeVarId) -> bool {
        self.depth(id) == 0
    }

    fn get<'i, 'u: 'i>(&'u self, id: &'i TypeVarId) -> (&'i TypeVarId, usize) {
        let Some((parent, depth)) = self.0.get(id) else {
            return (id, 0);
        };

        let (node, node_depth) = self.get(parent);

        (node, depth + node_depth)
    }
}

#[cfg(test)]
mod test {
    use crate::ir2::hir::ExprId;

    use super::*;

    use rstest::*;

    #[fixture]
    fn expr<const N: usize>() -> [TypeVarId; N] {
        (0..N)
            .map(|i| TypeVarId::from(ExprId::new(i)))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    #[fixture]
    fn map() -> DisjointUnionSet {
        DisjointUnionSet::new()
    }

    #[rstest]
    fn no_parent(expr: [TypeVarId; 1], map: DisjointUnionSet) {
        assert_eq!(
            map.find_set(&expr[0]),
            &expr[0],
            "should be in set by itself"
        );
    }

    #[rstest]
    fn single_parent(expr: [TypeVarId; 2], mut map: DisjointUnionSet) {
        map.union_sets(expr[0].clone(), expr[1].clone());
        assert_eq!(
            map.find_set(&expr[0]),
            map.find_set(&expr[1]),
            "should be in same set"
        );
    }

    #[rstest]
    fn already_in_same_set(expr: [TypeVarId; 2], mut map: DisjointUnionSet) {
        map.union_sets(expr[0].clone(), expr[1].clone());
        map.union_sets(expr[1].clone(), expr[0].clone());
        assert_eq!(
            map.find_set(&expr[0]),
            map.find_set(&expr[1]),
            "should remain in same set, even if already union"
        );
    }

    #[rstest]
    fn self_union(expr: [TypeVarId; 1], mut map: DisjointUnionSet) {
        map.union_sets(expr[0].clone(), expr[0].clone());
        assert_eq!(map.find_set(&expr[0]), map.find_set(&expr[0]),);
    }

    #[rstest]
    fn deep_parent(expr: [TypeVarId; 4], mut map: DisjointUnionSet) {
        map.union_sets(expr[0].clone(), expr[1].clone());
        map.union_sets(expr[1].clone(), expr[2].clone());
        map.union_sets(expr[2].clone(), expr[3].clone());

        assert_eq!(
            map.find_set(&expr[0]),
            map.find_set(&expr[1]),
            "nodes should be in same set"
        );
        assert_eq!(
            map.find_set(&expr[0]),
            map.find_set(&expr[2]),
            "nodes should be in same set"
        );
        assert_eq!(
            map.find_set(&expr[0]),
            map.find_set(&expr[3]),
            "nodes should be in same set"
        );
    }

    #[rstest]
    fn disjoint_sets(expr: [TypeVarId; 4], mut map: DisjointUnionSet) {
        map.union_sets(expr[0].clone(), expr[1].clone());
        map.union_sets(expr[2].clone(), expr[3].clone());

        assert_ne!(
            map.find_set(&expr[0]),
            map.find_set(&expr[2]),
            "nodes should not be in same set"
        );
    }
}
