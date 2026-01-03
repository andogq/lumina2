mod disjoint_union_set;
pub mod solver;

use crate::prelude::*;

use self::disjoint_union_set::DisjointUnionSet;
use crate::{enum_conversion, ir::hir::*};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeVarId {
    Expression(ExpressionId),
    Binding(BindingId),
    Type(Type),
}

enum_conversion! {
    [TypeVarId]
    Expression: ExpressionId,
    Binding: BindingId,
    Type: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constraint {
    Eq(TypeVarId),
    Integer(IntegerKind),
    Reference(TypeVarId),
    Function {
        parameters: Vec<TypeVarId>,
        return_ty: TypeVarId,
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
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntegerKind {
    Any,
    Signed,
    #[allow(
        dead_code,
        reason = "future constraints may require an unsigned integer."
    )]
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

#[cfg(test)]
mod test {
    use super::*;

    use crate::passes::{ast_gen::AstGen, cst_gen::Parse, hir_gen::HirGen, thir_gen::ThirGen};

    fn get_ty(expression: &str) -> Type {
        let mut ctx = Ctx::new();

        // Tokenise the source.
        let mut lexer = Lexer::new(expression);
        // Parse into CST.
        let expression = cst::Expression::parse(&mut lexer);
        // Ensure that the entirety of the source was consumed.
        lexer.expect::<tok::Eof>().unwrap();

        // Create a new AST builder, and lower the expression.
        let mut ast_pass = AstGen::new(&mut ctx);
        let expression_id = ast_pass.lower_expression(&expression);

        // Finalise the AST.
        let mut ast = ast_pass.ast;

        // Variable which the expression will be assigned to.
        let variable = ctx.strings.intern("output_variable");

        // HACK: Manually add a block to the AST with the expression. Then insert a
        // function declaration with the block as the body.
        {
            let statement_id = ast
                .statements
                .insert(ast::Statement::Let(ast::LetStatement {
                    variable,
                    value: expression_id,
                }));
            let block_id = ast.blocks.insert(ast::Block {
                statements: vec![statement_id],
                expression: None,
            });
            ast.function_declarations.insert(ast::FunctionDeclaration {
                name: ctx.strings.intern("main"),
                parameters: Vec::new(),
                return_ty: None,
                body: block_id,
            })
        };

        // Lower the AST into the HIR.
        let hir = HirGen::run(&mut ctx, &ast, ()).unwrap().into_outcome();
        // Run type inference.
        let thir = ThirGen::run(&mut ctx, &hir, ()).unwrap().into_outcome();

        // HACK: Search through all scopes to find the binding corresponding to `variable`.
        let binding = {
            let scopes = ctx.scopes.find_scope(variable);

            assert_eq!(
                scopes.len(),
                1,
                "only one scope can contain `output_variable`"
            );

            scopes[0].1
        };

        // The type of the binding will correspond with the type of the expression.
        thir.types.get(&binding.into()).unwrap().clone()
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
    fn assert_expression_ty(#[case] expression: &str, #[case] ty: Type) {
        assert_eq!(get_ty(expression), ty);
    }
}
