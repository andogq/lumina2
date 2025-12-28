mod constraint_builder;
mod disjoint_union_set;
mod solver;

use crate::prelude::*;

use self::disjoint_union_set::DisjointUnionSet;
use crate::{
    enum_conversion,
    ir::hir::*,
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
    Eq(TypeVarId),
    Integer(IntegerKind),
    Reference(TypeVarId),
    Function {
        params: Vec<TypeVarId>,
        ret_ty: TypeVarId,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Solution {
    Type(Type),
    Reference(TypeVarId),
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
            Self::Integer(integer_literal) => integer_literal.to_type(),
        }
    }

    pub fn can_coerce(&self, ty: &Type) -> bool {
        match self {
            Self::Integer(integer_literal) => integer_literal.can_coerce(ty),
        }
    }

    pub fn narrow(&self, other: &Literal) -> Option<Literal> {
        match (self, other) {
            (Self::Integer(lhs), Self::Integer(rhs)) => Some(Self::Integer(lhs.narrow(rhs)?)),
            _ => None,
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

    pub fn can_coerce(&self, ty: &Type) -> bool {
        matches!(
            (self, ty),
            (Self::Any, Type::U8 | Type::I8)
                | (Self::Signed, Type::I8)
                | (Self::Unsigned, Type::U8)
        )
    }

    pub fn narrow(&self, other: &IntegerKind) -> Option<IntegerKind> {
        match (self, other) {
            (lhs, rhs) if lhs == rhs => Some(lhs.clone()),
            (Self::Any, answer) | (answer, Self::Any) => Some(answer.clone()),
            _ => None,
        }
    }
}

pub fn solve(hir: &Hir) -> HashMap<FunctionId, HashMap<TypeVarId, Type>> {
    // Collect all function parameters.
    let function_declarations = hir
        .functions
        .iter()
        .map(|f| {
            (
                TypeVarId::Binding(f.binding),
                Constraint::Eq(
                    Type::Function {
                        params: f.parameters.iter().map(|(_, ty)| ty.clone()).collect(),
                        ret_ty: Box::new(f.return_ty.clone()),
                    }
                    .into(),
                ),
            )
        })
        .collect::<Vec<_>>();

    // Run the solver for each function in isolation.
    hir.functions
        .iter()
        .enumerate()
        .map(|(id, f)| {
            (
                FunctionId::new(id),
                ConstraintBuilder::build(f, function_declarations.iter().cloned()),
            )
        })
        .inspect(|(id, constraints)| {
            dbg!(id, constraints);
        })
        .map(|(id, constraints)| (id, Solver::run(&constraints)))
        .collect()
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::stages::{parse::Parse, *};

    fn get_ty(expr: &str) -> Type {
        let mut ctx = Ctx::default();

        // Tokenise the source.
        let mut lexer = Lexer::new(expr);
        // Parse into CST.
        let expr = cst::Expr::parse(&mut lexer);
        // Ensure that the entirety of the source was consumed.
        lexer.expect::<tok::Eof>().unwrap();

        // Create a new AST builder, and lower the expression.
        let cst_program = cst::Program::new();
        let mut builder = ast_builder::AstBuilder::new(&cst_program);
        let expr_id = builder.lower_expr(&mut ctx, &expr);

        // Finalise the AST.
        let mut ast = builder.build(&mut ctx);

        // HACK: Manually add a block to the AST with the expression. Then insert a
        // function declaration with the block as the body.
        let function_id = {
            let block_id = ast.blocks.insert(ast::Block {
                statements: vec![ast::Statement::Expr(ast::ExprStatement { expr: expr_id })],
                expression: None,
            });
            ast.function_declarations.insert(ast::FunctionDeclaration {
                name: ctx.strings.intern("main"),
                params: Vec::new(),
                return_ty: None,
                body: block_id,
            })
        };

        // Lower the AST into the HIR.
        let mut hir_builder = hir_builder::HirBuilder::new(&ast);
        hir_builder.lower_functions(&mut ctx);

        // Capture the new expression ID.
        let expr_id = hir_builder.expr_mapping[&expr_id];

        // Extract the HIR.
        let hir = hir_builder.build(&mut ctx);

        // Run type inference.
        let tys = solve(&hir);

        // Fetch the expression type.
        tys.get(
            // HACK: Not guaranteed to be 0
            &FunctionId::new(0),
        )
        .unwrap()
        .get(&expr_id.into())
        .unwrap()
        .clone()
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
