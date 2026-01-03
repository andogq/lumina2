use crate::prelude::*;

use crate::passes::{hir_gen::HirGenError, mir_gen::MirGenError, thir_gen::ThirGenError};

/// Compiler result, an alias for [`Result`] with [`CError`] as the error value.
pub type CResult<T> = Result<T, CError>;

/// Collection of errors which may occur during compilation.
#[derive(Clone, Debug, thiserror::Error)]
#[error(transparent)]
#[expect(
    clippy::enum_variant_names,
    reason = "postfix `Gen` refers to the name of the pass from which the errors originate"
)]
pub enum CErrorKind {
    HirGen(#[from] HirGenError),
    ThirGen(#[from] ThirGenError),
    MirGen(#[from] MirGenError),
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
    /// Report the provided error, returning it's ID.
    pub fn report(&mut self, error: impl Into<CError>) -> CErrorId {
        self.0.insert(error.into())
    }

    /// Produce an iterator over all errors.
    pub fn iter(&self) -> impl Iterator<Item = &CError> {
        self.0.iter()
    }

    /// Produce an iterator over all fatal errors.
    pub fn iter_fatal(&self) -> impl Iterator<Item = &CError> {
        self.iter().filter(|err| err.fatal)
    }

    /// Produce an iterator over all non-fatal errors.
    pub fn iter_non_fatal(&self) -> impl Iterator<Item = &CError> {
        self.iter().filter(|err| !err.fatal)
    }
}

impl Index<CErrorId> for CErrorList {
    type Output = CError;

    fn index(&self, index: CErrorId) -> &Self::Output {
        &self.0[index]
    }
}

/// Methods available on error-like items, to annotate them with additional metadata.
pub trait ErrorMeta {
    /// Mark this error as fatal.
    fn fatal(self) -> Self;

    /// Add the following message to the error.
    fn with_message(self, message: impl ToString) -> Self;
}

/// Metadata methods can be directly implemented on [`CError`], to set the underlying struct
/// values.
impl ErrorMeta for CError {
    fn fatal(mut self) -> Self {
        self.fatal = true;
        self
    }

    fn with_message(mut self, message: impl ToString) -> Self {
        self.message = Some(message.to_string());
        self
    }
}

/// Metadata methods can be passed through to the error value, if present.
impl<T> ErrorMeta for CResult<T> {
    fn fatal(self) -> Self {
        self.map_err(|err| err.fatal())
    }

    fn with_message(self, message: impl ToString) -> Self {
        self.map_err(|err| err.with_message(message))
    }
}

/// Run the provided closure, report the error, and add the resulting ID to a collection.
///
/// ```
/// # use crate::prelude::{Ctx, CResult};
/// # fn something_that_errors() -> CResult<()> {
/// #     Ok(())
/// # }
/// let mut ctx = Ctx::default();
/// let mut errors = Vec::new();
///
/// run_and_report!(ctx, errors, || something_that_errors());
///
/// assert_eq!(errors.len(), 1);
/// ```
#[macro_export]
macro_rules! run_and_report {
    // spell-checker:disable-next-line
    ($ctx:expr, $errors:expr, $f:expr) => {
        $f().map_err(|err| $ctx.errors.report(err)).map_err(|err| {
            $errors.push(err);
            err
        })
    };
}
