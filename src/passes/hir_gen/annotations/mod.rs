mod intrinsic;

use crate::prelude::*;

fn run<A: Annotation>(ctx: &mut Ctx, ast: &ast::Ast, hir: &mut hir::Hir) {
    for (id, node) in A::Node::get_all(ast).iter_pairs() {
        // Filter out all nodes where the ID doesn't match.
        if node
            .annotations()
            .iter()
            .map(|annotation| &ast[*annotation])
            .all(|annotation| A::NAME != ctx.strings.get(annotation.key))
        {
            continue;
        }

        A::map(ctx, ast, hir, id, todo!());
    }
}

pub trait Annotation {
    /// Name which this annotation applies to.
    ///
    /// ```txt
    /// @some_annotation
    /// fn my_fn() {}
    /// ```
    ///
    /// To select this annotation:
    ///
    /// ```
    /// impl Annotation for SomeAnnotation {
    ///     const NAME: &'static str = "some_annotation";
    ///
    ///     // ...
    /// }
    /// ```
    const NAME: &'static str;

    /// Kind of AST node this attribute expects to be attached to.
    type Node: AttributeNode;

    /// Annotation processing implementation.
    fn map(
        ctx: &mut Ctx,
        ast: &ast::Ast,
        hir: &mut hir::Hir,
        ast_node: <Self::Node as AttributeNode>::AstId,
        hir_node: <Self::Node as AttributeNode>::HirId,
    );
}

pub trait AttributeNode: Sized {
    /// AST ID associated with this node.
    type AstId: Id;

    /// HIR ID.
    type HirId: Id;

    /// Fetch a list of all nodes from the AST.
    fn get_all(ast: &ast::Ast) -> &IndexedVec<Self::AstId, Self>;

    /// Fetch a list of all annotations.
    fn annotations(&self) -> &[ast::AnnotationId];
}

impl AttributeNode for ast::FunctionDeclaration {
    type AstId = ast::FunctionId;
    type HirId = hir::FunctionId;

    fn get_all(ast: &ast::Ast) -> &IndexedVec<Self::AstId, Self> {
        &ast.function_declarations
    }

    fn annotations(&self) -> &[ast::AnnotationId] {
        &self.annotations
    }
}
