mod constraint_builder;
mod disjoint_union_set;
mod solver;

use std::collections::HashMap;

use self::disjoint_union_set::DisjointUnionSet;
use crate::{
    enum_conversion,
    ir2::hir::*,
    stages::ty::{constraint_builder::ConstraintBuilder, solver::Solver},
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeVarId {
    Expr(ExprId),
    Binding(BindingId),
    Type(Type),
}

enum_conversion! {
    [TypeVarId]
    Expr: ExprId,
    Binding: BindingId,
    Type: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Constraint {
    Eq(TypeVarId, TypeVarId),
    Integer(TypeVarId, IntegerKind),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Solution {
    Type(Type),
    Literal(Literal),
}

enum_conversion! {
    [Solution]
    Type: Type,
    Literal: Literal,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Literal {
    Integer(IntegerKind),
}

enum_conversion! {
    [Literal]
    Integer: IntegerKind,
}

impl Literal {
    pub fn to_type(&self) -> Type {
        match self {
            Literal::Integer(integer_literal) => integer_literal.to_type(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum IntegerKind {
    Any,
    Signed,
    Unsigned,
}

impl IntegerKind {
    pub fn to_type(&self) -> Type {
        match self {
            IntegerKind::Signed | IntegerKind::Any => Type::I8,
            IntegerKind::Unsigned => Type::U8,
        }
    }
}

pub fn solve(hir: &Hir) -> HashMap<TypeVarId, Type> {
    let constraints = ConstraintBuilder::build(hir);
    Solver::run(dbg!(&constraints))
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::{
        ir2::*,
        lex::{lex2::Lexer, tok},
        stages::{parse::Parse, *},
    };

    use rstest::*;

    fn get_ty(expr: &str) -> Type {
        // Tokenise the source.
        let mut lexer = Lexer::new(expr);
        // Parse into CST.
        let expr = cst::Expr::parse(&mut lexer);
        // Ensure that the entirety of the source was consumed.
        lexer.expect::<tok::Eof>().unwrap();

        // Create a new AST builder, and lower the expression.
        let cst_program = cst::Program::new();
        let mut builder = ast_builder::AstBuilder::new(&cst_program);
        let expr_id = builder.lower_expr(&expr);

        // Finalise the AST.
        let mut ast = builder.build();

        // HACK: Manually add a block to the AST with the expression. Then insert a
        // function declaration with the block as the body.
        {
            let block_id = ast.blocks.len();
            ast.blocks.push(ast::Block {
                statements: vec![ast::Statement::Expr(ast::ExprStatement { expr: expr_id })],
                expression: None,
            });
            ast.function_declarations.push(ast::FunctionDeclaration {
                name: ast::StringId::new(2),
                params: Vec::new(),
                return_ty: None,
                body: ast::BlockId::new(block_id),
            });
        }

        // Lower the AST into the HIR.
        let mut hir_builder = hir_builder::HirBuilder::new(&ast);
        hir_builder.lower_functions();

        // Capture the new expression ID.
        let expr_id = hir_builder.expr_mapping[&expr_id];

        // Extract the HIR.
        let hir = hir_builder.build();

        // Run type inference.
        let tys = solve(&hir);

        // Fetch the expression type.
        tys.get(&expr_id.into()).unwrap().clone()
    }

    #[rstest]
    #[case("1", Type::I8)]
    #[case("1 + 2", Type::I8)]
    #[case("1 - 2", Type::I8)]
    #[case("1 & 2", Type::I8)]
    #[case("true && true", Type::Boolean)]
    #[case("1 < 2", Type::Boolean)]
    #[case("{ 1 }", Type::I8)]
    #[case("{ 1; }", Type::Unit)]
    #[case("{ let a = 1; }", Type::Unit)]
    #[case("{ let a = 1; 1 }", Type::I8)]
    #[case("{ let a = 1; a }", Type::I8)]
    fn assert_expr_ty(#[case] expr: &str, #[case] ty: Type) {
        assert_eq!(get_ty(expr), ty);
    }
}
