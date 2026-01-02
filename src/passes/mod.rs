pub mod ast_gen;
pub mod codegen;
pub mod cst_gen;
pub mod hir_gen;
pub mod mir_gen;
pub mod thir_gen;

use crate::prelude::*;

pub trait Pass<'ctx, 'input> {
    /// Input required for this pass.
    type Input: ?Sized;

    /// Output produced by this pass.
    type Output;

    type Extra;

    /// Run the pass with the provided context and input.
    fn run(
        ctx: &'ctx mut Ctx,
        input: &'input Self::Input,
        extra: Self::Extra,
    ) -> PassResult<Self::Output>;
}

/// A pass may result in a success (something can be produced, even if it's incomplete), or a
/// failure caused by a fatal error.
pub type PassResult<T> = Result<PassSuccess<T>, CErrorId>;
/// A pass may succeed fully, or with errors.
#[must_use]
pub enum PassSuccess<T> {
    /// Completely successful pass.
    Ok(T),
    /// Partially successful pass, with some errors produced.
    Partial {
        /// Outcome of this pass.
        outcome: T,
        /// Produced (non-fatal) errors.
        errors: Vec<CErrorId>,
    },
}

impl<T> PassSuccess<T> {
    /// Produce the success based on the provided errors. If no errors are provided, then
    /// [`PassSuccess::Ok`] is assumed.
    pub fn new(outcome: T, errors: Vec<CErrorId>) -> Self {
        if errors.is_empty() {
            Self::Ok(outcome)
        } else {
            Self::Partial { outcome, errors }
        }
    }

    /// Produce a reference to the outcome.
    pub fn outcome(&self) -> &T {
        match self {
            Self::Ok(outcome) => outcome,
            Self::Partial { outcome, .. } => outcome,
        }
    }

    /// Produce a slice to the errors.
    pub fn errors(&self) -> &[CErrorId] {
        match self {
            Self::Ok(_) => &[],
            Self::Partial { errors, .. } => errors,
        }
    }

    /// Consume the success and produce the outcome.
    pub fn into_outcome(self) -> T {
        match self {
            Self::Ok(outcome) => outcome,
            Self::Partial { outcome, .. } => outcome,
        }
    }
}

impl<T> From<T> for PassSuccess<T> {
    fn from(value: T) -> Self {
        Self::Ok(value)
    }
}
