use crate::prelude::*;

use crate::passes::hir_gen::HirGenError;

/// Compiler result, an alias for [`Result`] with [`CError`] as the error value.
pub type CResult<T> = Result<T, CError>;

/// Collection of errors which may occur during compilation.
#[derive(Clone, Debug, thiserror::Error)]
#[error(transparent)]
pub enum CErrorKind {
    HirGen(#[from] HirGenError),
}

/// An error that may occur during compilation.
///
/// Wraps [`CErrorKind`] with additional metadata to assist with the understanding of the error.
#[derive(Clone, Debug, thiserror::Error)]
pub struct CError {
    /// Specific error information.
    kind: CErrorKind,

    /// Optional user-friendly message to accompany the error.
    message: Option<String>,
    /// Indicates whether this error is fatal, meaning that compilation could not continue.
    fatal: bool,
}

impl CError {
    /// Mark this error as fatal.
    pub fn fatal(mut self) -> Self {
        self.fatal = true;
        self
    }

    /// Add the following message to the error.
    pub fn with_message(mut self, message: impl ToString) -> Self {
        self.message = Some(message.to_string());
        self
    }
}

impl Deref for CError {
    type Target = CErrorKind;

    fn deref(&self) -> &Self::Target {
        &self.kind
    }
}

impl Display for CError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.fatal {
            write!(f, "FATAL: ")?;
        }

        Display::fmt(&self.kind, f)?;

        if let Some(message) = &self.message {
            write!(f, " ({message})")?;
        }

        Ok(())
    }
}

impl<T> From<T> for CError
where
    CErrorKind: From<T>,
{
    fn from(value: T) -> Self {
        Self {
            kind: value.into(),
            message: None,
            fatal: false,
        }
    }
}

create_id!(CErrorId);

/// A collection of errors, each with a unique ID.
#[derive(Clone, Debug, Default)]
pub struct CErrorList(IndexedVec<CErrorId, CError>);

impl CErrorList {
    /// Create a new instance.
    pub fn new() -> Self {
        Self::default()
    }

    /// Report the provided error, returning it's ID.
    pub fn report(&mut self, error: CError) -> CErrorId {
        self.0.insert(error)
    }

    /// Produce an iterator over all errors.
    pub fn iter(&self) -> impl Iterator<Item = &CError> {
        self.0.iter()
    }

    /// Produce an iterator over all fatal errors.
    pub fn iter_fatal(&self) -> impl Iterator<Item = &CError> {
        self.iter().filter(|err| err.fatal)
    }
}

impl Index<CErrorId> for CErrorList {
    type Output = CError;

    fn index(&self, index: CErrorId) -> &Self::Output {
        &self.0[index]
    }
}
