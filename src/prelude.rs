// Various IRs.
pub use crate::ir::{ast, cst, hir, hir::thir, mir};

// Common items.
pub use crate::{
    create_id,
    ctx::Ctx,
    indexed_vec,
    lex::{Lexer, Tok, tok},
    util::{bindings::Bindings, indexed_vec::IndexedVec, scopes::Scopes, string_pool::StringPool},
};

// IDs and associated traits.
pub use crate::{
    // TODO: This needs to be  moved
    ir::hir::TypeRefId,
    // TODO: This needs to be  moved
    stages::ty::TypeVarId,
    util::{bindings::BindingId, indexed_vec::Id, scopes::ScopeId, string_pool::StringId},
};

// Common items from standard library.
pub use ::std::{
    collections::HashMap,
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
    ops::{Deref, DerefMut, Index, IndexMut},
};

#[allow(clippy::items_after_test_module)]
#[cfg(test)]
mod test {
    pub use insta::*;
    pub use rstest::*;
}

#[cfg(test)]
pub use test::*;
