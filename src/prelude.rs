// Various IRs.
pub use crate::ir::{BinaryOperation, UnaryOperation, ast, cst, hir, mir, thir};

// Common items.
pub use crate::{
    ctx::Ctx,
    error::{CError, CErrorId, CErrorList, CResult, ErrorMeta},
    lex::{Lexer, Tok, tok},
    passes::{Pass, PassResult, PassSuccess},
    ty::{Type, Types},
    util::{indexed_vec::IndexedVec, scopes::Scopes, string_pool::StringPool},
};

// Macros
pub use crate::{create_id, enum_conversion, run_and_report};

// IDs and associated traits.
pub use crate::{
    // TODO: This needs to be  moved
    ty::{TypeId, TypeVar},
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
    ops::{Deref, Index, IndexMut},
};

// Test utilities.
#[cfg(test)]
pub use crate::{
    // Allow inspection of error kinds within tests.
    error::CErrorKind,
    // Allow manual creation of `IndexedVec`.
    indexed_vec,
};
#[cfg(test)]
pub use ::{insta::*, rstest::*};
