use std::collections::{HashMap, hash_map::Entry};

use crate::stages::ty::TypeVarId;

#[derive(Clone, Debug)]
pub struct UnionFind(HashMap<TypeVarId, (TypeVarId, usize)>);

impl UnionFind {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn set_parent(&mut self, id: TypeVarId, parent: TypeVarId) {
        match self.0.entry(id) {
            Entry::Occupied(mut occupied_entry) => {
                let (parent, depth) = occupied_entry.get_mut();
                todo!()
            }
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert((parent, 1));
            }
        }
    }

    pub fn resolve<'u: 'i, 'i>(&'u self, id: &'i TypeVarId) -> &'i TypeVarId {
        self.get(id).0
    }

    pub fn depth(&self, id: &TypeVarId) -> usize {
        self.get(id).1
    }

    pub fn is_root(&self, id: &TypeVarId) -> bool {
        self.depth(id) == 0
    }

    pub fn get<'i, 'u: 'i>(&'u self, id: &'i TypeVarId) -> (&'i TypeVarId, usize) {
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

    #[test]
    fn no_parent() {
        let expr = TypeVarId::from(ExprId::new(0));
        let map = UnionFind::new();

        assert_eq!(map.get(&expr), (&expr, 0));
    }

    #[test]
    fn single_parent() {
        let [expr0, expr1] = [0, 1].map(|i| TypeVarId::from(ExprId::new(i)));
        let mut map = UnionFind::new();

        map.set_parent(expr0.clone(), expr1.clone());
        assert_eq!(map.get(&expr0), (&expr1, 1));
    }

    #[test]
    fn deep_parent() {
        let [expr0, expr1, expr2, expr3] = [0, 1, 2, 3].map(|i| TypeVarId::from(ExprId::new(i)));
        let mut map = UnionFind::new();

        map.set_parent(expr0.clone(), expr1.clone());
        map.set_parent(expr1.clone(), expr2.clone());
        map.set_parent(expr2.clone(), expr3.clone());
        assert_eq!(map.get(&expr0), (&expr3, 3));
    }
}
