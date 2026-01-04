mod disjoint_union_set;
pub mod solver;

use crate::prelude::*;

use self::disjoint_union_set::DisjointUnionSet;
use crate::{enum_conversion, ir::hir::*};

create_id!(TypeId);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Never,
    I8,
    U8,
    Boolean,
    Ref(TypeId),
    Function {
        parameters: Vec<TypeId>,
        return_ty: TypeId,
    },
    Tuple(Vec<TypeId>),
}

impl Type {
    /// Helper to construct `()`, which is a [`Type::Tuple`] with no fields.
    pub const UNIT: Type = Type::Tuple(Vec::new());
}

/// Interned collection of types.
#[derive(Clone, Debug)]
pub struct Types {
    /// Types which are already inserted.
    inserted: HashMap<Type, TypeId>,
    /// Interned types.
    types: IndexedVec<TypeId, Type>,
}
impl Types {
    /// Create a new instance, with primitive types already inserted.
    pub fn new() -> Self {
        let mut types = IndexedVec::new();

        let inserted = [Type::Never, Type::UNIT, Type::I8, Type::U8, Type::Boolean]
            .into_iter()
            .map(|ty| (ty.clone(), types.insert(ty)))
            .collect();

        Self { types, inserted }
    }

    /// Get the [`TypeId`] for the provided [`Type`], inserting it if it doesn't currently exist.
    pub fn get(&mut self, ty: Type) -> TypeId {
        *self
            .inserted
            .entry(ty.clone())
            .or_insert_with(|| self.types.insert(ty))
    }

    /// Fetch the type for unit (a [`Type::Tuple`] with no fields).
    pub fn unit(&self) -> TypeId {
        self.inserted[&Type::UNIT]
    }

    /// Fetch the type for [`Type::Never`].
    pub fn never(&self) -> TypeId {
        self.inserted[&Type::Never]
    }

    /// Fetch the type for [`Type::I8`].
    pub fn i8(&self) -> TypeId {
        self.inserted[&Type::I8]
    }

    /// Fetch the type for [`Type::U8`].
    pub fn u8(&self) -> TypeId {
        self.inserted[&Type::U8]
    }

    /// Fetch the type for [`Type::Boolean`].
    pub fn boolean(&self) -> TypeId {
        self.inserted[&Type::Boolean]
    }

    /// Fetch the type for a [`Type::Function`] with the provided parameters and return type.
    pub fn function(
        &mut self,
        parameters: impl IntoIterator<Item = TypeId>,
        return_ty: TypeId,
    ) -> TypeId {
        self.get(Type::Function {
            parameters: Vec::from_iter(parameters),
            return_ty,
        })
    }

    /// Fetch the type for a [`Type::Tuple`] with the items.
    pub fn tuple(&mut self, items: impl IntoIterator<Item = TypeId>) -> TypeId {
        self.get(Type::Tuple(Vec::from_iter(items)))
    }

    /// Fetch the type for a [`Type::Ref`] of a given type.
    pub fn ref_of(&mut self, ty: TypeId) -> TypeId {
        self.get(Type::Ref(ty))
    }

    /// Calculate the size of a type.
    pub fn size_of(&self, ty: TypeId) -> usize {
        match &self[ty] {
            Type::Never => todo!("work out what to do with this"),
            Type::I8 => 1,
            Type::U8 => 1,
            Type::Boolean => 1,
            Type::Ref(_) => todo!("pointer size"),
            Type::Function { .. } => todo!("pointer size"),
            Type::Tuple(type_ids) => type_ids.clone().iter().map(|ty| self.size_of(*ty)).sum(),
        }
    }

    /// Calculate the offset of a field in a type.
    pub fn offset_of(&self, ty: TypeId, field: usize) -> Option<usize> {
        match &self[ty] {
            Type::Tuple(type_ids) => {
                if field >= type_ids.len() {
                    return None;
                }

                // Calculate offset by adding size of all previous fields.
                Some(
                    type_ids
                        .iter()
                        .take(field)
                        .map(|ty| self.size_of(*ty))
                        .sum(),
                )
            }
            _ => {
                if field == 0 {
                    Some(0)
                } else {
                    None
                }
            }
        }
    }
}
impl Index<TypeId> for Types {
    type Output = Type;

    fn index(&self, index: TypeId) -> &Self::Output {
        &self.types[index]
    }
}
impl Default for Types {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TypeVarId {
    Expression(ExpressionId),
    Binding(BindingId),
    Type(TypeId),
}

enum_conversion! {
    [TypeVarId]
    Expression: ExpressionId,
    Binding: BindingId,
    Type: TypeId,
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
    Aggregate(Vec<TypeVarId>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Solution {
    Type(TypeId),
    Reference(TypeVarId),
    Literal(Literal),
    Tuple(Vec<TypeVarId>),
}

enum_conversion! {
    [Solution]
    Type: TypeId,
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
    pub fn to_type(&self, types: &Types) -> TypeId {
        match self {
            Self::Integer(integer_literal) => integer_literal.to_type(types),
        }
    }

    pub fn can_coerce(&self, types: &Types, ty: TypeId) -> bool {
        match self {
            Self::Integer(integer_literal) => integer_literal.can_coerce(types, ty),
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
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "future constraints may require an unsigned integer."
        )
    )]
    Unsigned,
}

impl IntegerKind {
    pub fn to_type(&self, types: &Types) -> TypeId {
        match self {
            IntegerKind::Signed | IntegerKind::Any => types.i8(),
            IntegerKind::Unsigned => types.u8(),
        }
    }

    pub fn can_coerce(&self, types: &Types, ty: TypeId) -> bool {
        matches!(
            (self, &types[ty]),
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
        let ty = *thir.types.get(&binding.into()).unwrap();
        ctx.types[ty].clone()
    }

    #[rstest]
    #[case("1", Type::I8)]
    #[case("1 + 2", Type::I8)]
    #[case("1 - 2", Type::I8)]
    #[case("1 & 2", Type::I8)]
    #[case("true && true", Type::Boolean)]
    #[case("1 < 2", Type::Boolean)]
    #[case("{ 1 }", Type::I8)]
    #[case("{ 1; }", Type::UNIT)]
    #[case("{ let a = 1; }", Type::UNIT)]
    #[case("{ let a = 1; 1 }", Type::I8)]
    #[case("{ let a = 1; a }", Type::I8)]
    fn assert_expression_ty(#[case] expression: &str, #[case] ty: Type) {
        assert_eq!(get_ty(expression), ty);
    }
}
