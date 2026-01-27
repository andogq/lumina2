use crate::prelude::*;

create_id!(ScopeId);
create_id!(InnerBindingId);

/// The ID of a [`Binding`] of a given [`BindingKind`].
#[derive(Debug)]
pub struct BindingId<B: BindingKind> {
    /// ID of the binding, as provided by [`Scopes::bindings`].
    id: InnerBindingId,
    /// Marker of the binding kind.
    kind: PhantomData<fn() -> B>,
}
impl<B: BindingKind> BindingId<B> {
    /// Create a new binding from an ID.
    fn new(id: InnerBindingId) -> Self {
        Self {
            id,
            kind: PhantomData,
        }
    }

    /// Create a new instance from a raw ID, for use in tests.
    #[cfg(test)]
    pub(crate) fn from_id(id: usize) -> Self {
        Self::new(InnerBindingId::from_id(id))
    }
}
impl<B: BindingKind> Clone for BindingId<B> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<B: BindingKind> Copy for BindingId<B> {}
impl<B: BindingKind> PartialEq for BindingId<B> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl<B: BindingKind> Eq for BindingId<B> {}
impl<B: BindingKind> Hash for BindingId<B> {
    #[mutants::skip(reason = "tests don't cover hashing")]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

/// A [`BindingId`] representing an [`Identifier`].
pub type IdentifierBindingId = BindingId<Identifier>;
/// A [`BindingId`] representing a [`Trait`].
pub type TraitBindingId = BindingId<Trait>;

/// A binding is comprised of the [`StringId`], and a [`BindingKind`].
///
/// This allows bindings to be shadowed depending on the context, and enforces separation of
/// different uses in the type system.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct Binding<B: BindingKind> {
    /// String this binding was created from.
    string: StringId,
    /// The [kind] of this binding.
    ///
    /// [kind]: BindingKind
    kind: PhantomData<fn() -> B>,
}
impl<B: BindingKind> Binding<B> {
    /// Create a new binding with the [`StringId`].
    fn new(string: StringId) -> Self {
        Self {
            string,
            kind: PhantomData,
        }
    }
}

/// Type-erased version of [`Binding`], using [`BindingKindMarker`] instead of a generic.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct ErasedBinding {
    /// String this binding was created from.
    string: StringId,
    // Kind of the binding.
    kind: BindingKindMarker,
}

impl<B: BindingKind> From<Binding<B>> for ErasedBinding {
    fn from(binding: Binding<B>) -> Self {
        Self {
            string: binding.string,
            kind: B::get_marker(),
        }
    }
}

#[derive(Clone, Debug, Default)]
struct Scope {
    /// Parent scope, if one exists.
    parent: Option<ScopeId>,
    /// All bindings defined within this scope, and their corresponding ID.
    bindings: HashMap<ErasedBinding, InnerBindingId>,
}

impl Scope {
    /// Create a new empty scope.
    fn new() -> Self {
        Self::default()
    }

    /// Create a new scope with a parent.
    fn new_with_parent(parent: ScopeId) -> Self {
        let mut scope = Self::new();
        scope.parent = Some(parent);
        scope
    }
}

/// Wrapper over [`TypeId`], used to type-erase [`BindingKindMarker`].
///
/// [`TypeId`]: std::any::TypeId
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
struct BindingKindMarker(std::any::TypeId);

/// Marker trait for different kinds of bindings.
pub trait BindingKind: 'static + Debug {
    /// Produce the type-erased [`BindingKindMarker`] for this binding kind.
    #[expect(
        private_interfaces,
        reason = "trait shouldn't be implemented outside of this module"
    )]
    fn get_marker() -> BindingKindMarker {
        BindingKindMarker(std::any::TypeId::of::<Self>())
    }
}

/// A [`Binding`] used for identifiers, such as variables or function names.
#[derive(Debug)]
pub struct Identifier;
impl BindingKind for Identifier {}

/// A [`Binding`] used for trait names.
#[derive(Debug)]
pub struct Trait;
impl BindingKind for Trait {}

/// Metadata associated with a [`Binding`].
#[derive(Clone, Debug)]
struct BindingMeta {
    /// Scope in which this binding exists.
    #[expect(dead_code, reason = "will be useful information in the future")]
    scope: ScopeId,
    /// The actual [`ErasedBinding`].
    binding: ErasedBinding,
}

/// Tracks all scopes that have been declared during compilation.
#[derive(Clone, Debug)]
pub struct Scopes {
    /// All scopes.
    scopes: IndexedVec<ScopeId, Scope>,
    /// All bindings.
    bindings: IndexedVec<InnerBindingId, BindingMeta>,
    /// The global scope.
    global: ScopeId,
}

impl Scopes {
    /// Create a new collection of scopes.
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

    /// Declare a new [`Binding`] within the provided [`Scope`].
    pub fn declare<B: BindingKind>(&mut self, scope: ScopeId, string: StringId) -> BindingId<B> {
        /// Declare a binding without any generics.
        fn declare_binding(
            scopes: &mut Scopes,
            scope: ScopeId,
            binding: ErasedBinding,
        ) -> InnerBindingId {
            // Create a new binding ID.
            let binding_id = scopes.bindings.insert(BindingMeta {
                scope,
                binding: binding.clone(),
            });
            // Record the scope the binding was placed into.
            scopes.scopes[scope].bindings.insert(binding, binding_id);
            binding_id
        }

        let binding = Binding::<B>::new(string);
        let binding_id = declare_binding(self, scope, binding.into());
        BindingId::new(binding_id)
    }

    /// Declare a new [`Binding`] in the global [`Scope`].
    pub fn declare_global<B: BindingKind>(&mut self, string: StringId) -> BindingId<B> {
        self.declare(self.global, string)
    }

    /// Resolve a [`StringId`] in some [`Scope`] into a [`BindingId`] matching the [`BindingKind`].
    pub fn resolve<B: BindingKind>(&self, scope: ScopeId, string: StringId) -> BindingId<B> {
        /// Search for an [`ErasedBinding`], starting from the provided [`Scope`] and searching
        /// upwards through parents.
        fn resolve_binding(
            scopes: &Scopes,
            scope: ScopeId,
            binding: ErasedBinding,
        ) -> InnerBindingId {
            let scope = &scopes.scopes[scope];
            if let Some(binding) = scope.bindings.get(&binding) {
                *binding
            } else {
                resolve_binding(scopes, scope.parent.unwrap(), binding)
            }
        }

        let binding = Binding::<B>::new(string);
        let binding_id = resolve_binding(self, scope, binding.into());
        // Turn the ID into the typed representation, which is fine to do given that
        // `resolve_binding` uses `B` as its search key.
        BindingId::<B>::new(binding_id)
    }

    /// Resolve a [`StringId`] in the global [`Scope`] into a [`BindingId`] matching the
    /// [`BindingKind`].
    pub fn resolve_global<B: BindingKind>(&self, string: StringId) -> BindingId<B> {
        self.resolve(self.global, string)
    }

    /// Search through all scopes for the provided string.
    #[cfg(test)]
    pub fn find_scope<B: BindingKind>(&self, string: StringId) -> Vec<(ScopeId, BindingId<B>)> {
        let binding = Binding::<B>::new(string).into();
        self.scopes
            .iter_pairs()
            .filter_map(|(scope_id, scope)| {
                Some((scope_id, BindingId::new(*scope.bindings.get(&binding)?)))
            })
            .collect()
    }

    pub fn to_string<B: BindingKind>(&self, binding: BindingId<B>) -> StringId {
        self.bindings[binding.id].binding.string
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
            scopes.declare::<Identifier>(scope, string),
            scopes.resolve::<Identifier>(scope, string),
            "resolved binding must be same as declared",
        );
    }

    #[rstest]
    fn declare_shadowing(mut scopes: Scopes, string: StringId) {
        let scope = scopes.nest_scope_global();
        assert_ne!(
            scopes.declare::<Identifier>(scope, string),
            scopes.declare::<Identifier>(scope, string),
            "re-declared binding must differ",
        );
    }

    #[rstest]
    fn scope_modification(mut scopes: Scopes, string: StringId) {
        let outer = scopes.nest_scope_global();
        let top_binding = scopes.declare::<Identifier>(outer, string);
        assert_eq!(
            top_binding,
            scopes.resolve::<Identifier>(outer, string),
            "binding should resolve to top scope"
        );

        let inner = scopes.nest_scope(outer);
        assert_eq!(
            top_binding,
            scopes.resolve::<Identifier>(inner, string),
            "binding should bubble to top scope",
        );

        let inner_binding = scopes.declare::<Identifier>(inner, string);
        assert_ne!(
            top_binding, inner_binding,
            "bindings in different scopes must be different"
        );
        assert_eq!(
            inner_binding,
            scopes.resolve::<Identifier>(inner, string),
            "binding should resolve to inner scope",
        );

        assert_eq!(
            top_binding,
            scopes.resolve::<Identifier>(outer, string),
            "binding should bubble to top scope after popping scope",
        );
    }

    #[rstest]
    fn declare_different_kinds(mut scopes: Scopes, string: StringId) {
        let scope = scopes.nest_scope_global();

        let identifier = scopes.declare::<Identifier>(scope, string);
        let trait_name = scopes.declare::<Trait>(scope, string);

        // Must receive different IDs.
        assert_ne!(identifier.id, trait_name.id);

        // Must resolve to the original binding ID.
        assert_eq!(scopes.resolve::<Identifier>(scope, string), identifier);
        assert_eq!(scopes.resolve::<Trait>(scope, string), trait_name);
    }
}
