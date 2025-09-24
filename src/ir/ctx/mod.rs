use crate::{
    indexed_vec,
    ir::{Tys, repr::Body},
};

#[derive(Clone, Debug, Default)]
pub struct IrCtx {
    pub tys: Tys,
    pub functions: Functions,
}

indexed_vec!(pub key Function);
indexed_vec!(pub Functions<Function, Body>);
