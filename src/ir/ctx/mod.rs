use crate::{Idents, indexed_vec, ir::repr::Function, tir::FunctionId};

#[derive(Clone, Debug)]
pub struct IrCtx {
    pub functions: Functions,
    pub idents: Idents,
}

impl IrCtx {
    pub fn new(idents: Idents) -> Self {
        Self {
            functions: Functions::new(),
            idents,
        }
    }
}

indexed_vec!(pub Functions<FunctionId, Function>);
