// Various IRs.
pub use crate::ir::{BinaryOperation, UnaryOperation, ast, cst, hir, mir, thir};

// Common items.
pub use crate::{
    ctx::Ctx,
    error::{CError, CErrorId, CErrorKind, CErrorList, CResult, ErrorMeta},
    lex::{Lexer, Tok, tok},
    passes::{Pass, PassResult, PassSuccess},
    util::{indexed_vec::IndexedVec, scopes::Scopes, string_pool::StringPool},
};

// Macros
pub use crate::{create_id, enum_conversion, indexed_vec, run_and_report};

// IDs and associated traits.
pub use crate::{
    // TODO: This needs to be  moved
    ir::hir::TypeRefId,
    // TODO: This needs to be  moved
    ty::TypeVarId,
    util::{
        indexed_vec::Id,
        scopes::{BindingId, ScopeId},
        string_pool::StringId,
    },
};

// Common items from standard library.
pub use ::std::{
    collections::HashMap,
    fmt::{Debug, Display},
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
