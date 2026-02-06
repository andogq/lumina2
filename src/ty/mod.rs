mod constraints;
mod disjoint_union_set;
mod solver;

use crate::prelude::*;

pub use self::{
    constraints::{Constraint, Constraints},
    disjoint_union_set::DisjointUnionSet,
    solver::Solver,
};

use hir::*;

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
            // WARN: Should be linked to target.
            Type::Ref(_) => std::mem::size_of::<usize>(),
            // WARN: Should be linked to target.
            Type::Function { .. } => std::mem::size_of::<usize>(),
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

#[derive(Clone, Debug, Default)]
pub struct TypeVars {
    vars: IndexedVec<TypeVarId, TypeVar>,
}

impl TypeVars {
    /// Create a new instance.
    pub fn new() -> Self {
        Self::default()
    }

    /// Fetch the ID of the provided type variable.
    pub fn intern(&mut self, var: impl Into<TypeVar>) -> TypeVarId {
        let var = var.into();
        if let Some((id, _)) = self
            .vars
            .iter_pairs()
            .find(|(_, test_var)| **test_var == var)
        {
            return id;
        }

        self.vars.insert(var)
    }

    pub fn get(&self, var: impl Into<TypeVar>) -> TypeVarId {
        let var = var.into();
        self.vars
            .iter_pairs()
            .find(|(_, test_var)| **test_var == var)
            .unwrap()
            .0
    }
}

impl Index<TypeVarId> for TypeVars {
    type Output = TypeVar;

    fn index(&self, index: TypeVarId) -> &Self::Output {
        &self.vars[index]
    }
}

create_id!(TypeVarId);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeVar {
    /// Variable is an expression.
    Expression(ExpressionId),
    /// Variable is a binding.
    Binding(IdentifierBindingId),
    /// Variable is a type.
    Type(TypeId),
    /// Variable is a field on another variable.
    Field(TypeVarId, usize),
}

enum_conversion! {
    [TypeVar]
    Expression: ExpressionId,
    Binding: IdentifierBindingId,
    Type: TypeId,
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
                | (Self::Unsigned, Type::U8 | Type::I8)
                | (_, Type::Never) // Allow never to propagate.
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
            let statement_id = ast.add_statement(ast::LetStatement {
                variable,
                value: expression_id,
            });
            let block_id = ast.add_block(vec![statement_id], None);
            let function_id = ast.add_function_declaration(
                ast::FunctionSignature {
                    name: ctx.strings.intern("main"),
                    parameters: Vec::new(),
                    return_ty: None,
                },
                ast::FunctionImplementation::Body(block_id),
            );
            // Add function as top level function.
            ast.item_functions.push(function_id);
        }

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
        let ty = thir.type_of(binding);
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

    mod literal {
        use super::*;

        #[test]
        fn coerce_literal_pass_through() {
            let types = Types::new();
            let literal = Literal::Integer(IntegerKind::Any);
            assert!(literal.can_coerce(&types, types.i8()));
            assert!(!literal.can_coerce(&types, types.boolean()));
        }

        #[rstest]
        #[case::any_unsigned(IntegerKind::Any, Type::U8, true)]
        #[case::any_signed(IntegerKind::Any, Type::I8, true)]
        #[case::any_non_integer(IntegerKind::Any, Type::Boolean, false)]
        #[case::signed_unsigned(IntegerKind::Signed, Type::U8, false)]
        #[case::signed_signed(IntegerKind::Signed, Type::I8, true)]
        #[case::signed_non_integer(IntegerKind::Signed, Type::Boolean, false)]
        #[case::unsigned_unsigned(IntegerKind::Unsigned, Type::U8, true)]
        #[case::unsigned_signed(IntegerKind::Unsigned, Type::I8, true)]
        #[case::unsigned_non_integer(IntegerKind::Unsigned, Type::Boolean, false)]
        fn coerce_integer(#[case] integer: IntegerKind, #[case] ty: Type, #[case] valid: bool) {
            let mut types = Types::new();
            let ty = types.get(ty);
            assert_eq!(integer.can_coerce(&types, ty), valid);
        }

        #[rstest]
        #[case::all_any(IntegerKind::Any, IntegerKind::Any, Some(IntegerKind::Any))]
        #[case::all_signed(IntegerKind::Signed, IntegerKind::Signed, Some(IntegerKind::Signed))]
        #[case::all_unsigned(
            IntegerKind::Unsigned,
            IntegerKind::Unsigned,
            Some(IntegerKind::Unsigned)
        )]
        #[case::signed_unsigned(IntegerKind::Signed, IntegerKind::Unsigned, None)]
        #[case::any_signed(IntegerKind::Any, IntegerKind::Signed, Some(IntegerKind::Signed))]
        #[case::any_unsigned(IntegerKind::Any, IntegerKind::Unsigned, Some(IntegerKind::Unsigned))]
        fn narrow_integer(
            #[case] lhs: IntegerKind,
            #[case] rhs: IntegerKind,
            #[case] expect: Option<IntegerKind>,
        ) {
            assert_eq!(lhs.narrow(&rhs), expect);
        }
    }

    mod types {
        use super::*;

        #[test]
        fn offset_of_primitive_field_0() {
            let types = Types::new();
            let ty = types.u8();
            assert_eq!(types.offset_of(ty, 0), Some(0));
        }

        #[test]
        fn offset_of_primitive_field_1() {
            let types = Types::new();
            let ty = types.u8();
            assert_eq!(types.offset_of(ty, 1), None);
        }

        #[test]
        fn offset_of_tuple() {
            let mut types = Types::new();
            let ty = types.tuple([types.u8(), types.boolean()]);
            assert_eq!(types.offset_of(ty, 0), Some(0));
            assert_eq!(types.offset_of(ty, 1), Some(1));
            assert_eq!(types.offset_of(ty, 2), None);
        }
    }
}
