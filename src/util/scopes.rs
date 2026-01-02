use crate::prelude::*;

create_id!(ScopeId);
create_id!(BindingId);

#[derive(Clone, Debug, Default)]
struct Scope {
    parent: Option<ScopeId>,
    bindings: HashMap<StringId, BindingId>,
    types: HashMap<StringId, TypeRefId>,
}

impl Scope {
    fn new() -> Self {
        Self::default()
    }

    fn new_with_parent(parent: ScopeId) -> Self {
        let mut scope = Self::new();
        scope.parent = Some(parent);
        scope
    }
}

#[derive(Clone, Debug)]
struct BindingMeta {
    scope: ScopeId,
    string: StringId,
}

#[derive(Clone, Debug)]
pub struct Scopes {
    scopes: IndexedVec<ScopeId, Scope>,
    bindings: IndexedVec<BindingId, BindingMeta>,

    global: ScopeId,
}

impl Scopes {
    pub fn new() -> Self {
        let mut scopes = IndexedVec::new();
        let global = scopes.insert(Scope::default());

        Self {
            scopes,
            bindings: IndexedVec::new(),
            global,
        }
    }

    pub fn nest_scope(&mut self, parent: ScopeId) -> ScopeId {
        self.scopes.insert(Scope::new_with_parent(parent))
    }

    pub fn nest_scope_global(&mut self) -> ScopeId {
        self.nest_scope(self.global)
    }

    pub fn declare(&mut self, scope: ScopeId, string: StringId) -> BindingId {
        let binding = self.bindings.insert(BindingMeta { scope, string });
        self.scopes[scope].bindings.insert(string, binding);
        binding
    }

    pub fn declare_global(&mut self, string: StringId) -> BindingId {
        self.declare(self.global, string)
    }

    pub fn resolve(&self, scope: ScopeId, string: StringId) -> BindingId {
        let scope = &self.scopes[scope];
        if let Some(binding) = scope.bindings.get(&string) {
            *binding
        } else {
            self.resolve(scope.parent.unwrap(), string)
        }
    }

    /// Search through all scopes for the provided string.
    pub fn find_scope(&self, string: StringId) -> Vec<(ScopeId, BindingId)> {
        self.scopes
            .iter_pairs()
            .filter_map(|(scope_id, scope)| Some((scope_id, *scope.bindings.get(&string)?)))
            .collect()
    }

    pub fn to_string(&self, binding: BindingId) -> StringId {
        self.bindings[binding].string
    }
}

impl Default for Scopes {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[fixture]
    fn scopes() -> Scopes {
        Scopes::new()
    }

    #[fixture]
    fn string() -> StringId {
        StringId::from_id(0)
    }

    #[rstest]
    fn declare_and_resolve_binding(mut scopes: Scopes, string: StringId) {
        let scope = scopes.nest_scope_global();
        assert_eq!(
            scopes.declare(scope, string),
            scopes.resolve(scope, string),
            "resolved binding must be same as declared",
        );
    }

    #[rstest]
    fn declare_shadowing(mut scopes: Scopes, string: StringId) {
        let scope = scopes.nest_scope_global();
        assert_ne!(
            scopes.declare(scope, string),
            scopes.declare(scope, string),
            "re-declared binding must differ",
        );
    }

    #[rstest]
    fn scope_modification(mut scopes: Scopes, string: StringId) {
        let outer = scopes.nest_scope_global();
        let top_binding = scopes.declare(outer, string);
        assert_eq!(
            top_binding,
            scopes.resolve(outer, string),
            "binding should resolve to top scope"
        );

        let inner = scopes.nest_scope(outer);
        assert_eq!(
            top_binding,
            scopes.resolve(inner, string),
            "binding should bubble to top scope",
        );

        let inner_binding = scopes.declare(inner, string);
        assert_ne!(
            top_binding, inner_binding,
            "bindings in different scopes must be different"
        );
        assert_eq!(
            inner_binding,
            scopes.resolve(inner, string),
            "binding should resolve to inner scope",
        );

        assert_eq!(
            top_binding,
            scopes.resolve(outer, string),
            "binding should bubble to top scope after popping scope",
        );
    }
}
