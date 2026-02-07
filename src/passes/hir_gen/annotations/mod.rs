mod intrinsic;

use crate::{
    ir::hir::{HirId, HirNodePtr},
    passes::hir_gen::annotations::intrinsic::intrinsic_handler,
    prelude::*,
};

/// An annotation attached to an item.
#[derive(Clone, Debug)]
#[expect(dead_code, reason = "annotations not used yet")]
pub struct Annotation {
    /// Key of the annotation.
    pub key: StringId,
    /// Value of the annotation, which may or may not be present.
    pub value: Option<StringId>,
}

impl Annotation {
    pub fn new(key: StringId, value: Option<StringId>) -> Self {
        Self { key, value }
    }

    pub fn key(key: StringId) -> Self {
        Self::new(key, None)
    }

    pub fn key_value(key: StringId, value: StringId) -> Self {
        Self::new(key, Some(value))
    }
}

pub fn run_annotation_handlers(ctx: &mut Ctx, hir: &mut hir::Hir) {
    // HACK: Don't clone all annotations.
    for (node, annotations) in hir.annotations.clone() {
        for annotation in annotations {
            let key = ctx.strings.get(annotation.key);
            let Some(handler) = ANNOTATIONS.get(key) else {
                eprintln!("annotation `{key}` is not supported");
                continue;
            };

            handler(ctx, hir, node);
        }
    }
}

pub type AnnotationHandler = fn(ctx: &mut Ctx, hir: &mut hir::Hir, hir_node: HirId);

lazy_static! {
    static ref ANNOTATIONS: BTreeMap<&'static str, AnnotationHandler> =
        BTreeMap::from_iter([("intrinsic", intrinsic_handler as AnnotationHandler)]);
}
