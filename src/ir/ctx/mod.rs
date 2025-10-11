use crate::{indexed_vec, ir::repr::Body, tir::FunctionId};

#[derive(Clone, Debug, Default)]
pub struct IrCtx {
    pub functions: Functions,
}

indexed_vec!(pub Functions<FunctionId, Body>);
