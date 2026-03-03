mod disjoint_union_set;

use crate::prelude::*;

pub use self::disjoint_union_set::DisjointUnionSet;

create_id!(TypeId);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type<T = TypeId> {
    Never,
    I8,
    U8,
    Boolean,
    Composite(CompositeType<T>),
}

impl<T> From<CompositeType<T>> for Type<T> {
    fn from(composite: CompositeType<T>) -> Self {
        Self::Composite(composite)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CompositeType<T = TypeId> {
    Ref(T),
    Function { parameters: Vec<T>, return_ty: T },
    Tuple(Vec<T>),
}

impl Type {
    /// Helper to construct `()`, which is a [`CompositeType::Tuple`] with no fields.
    pub const UNIT: Type = Type::Composite(CompositeType::Tuple(Vec::new()));
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
        self.get(
            CompositeType::Function {
                parameters: Vec::from_iter(parameters),
                return_ty,
            }
            .into(),
        )
    }

    /// Fetch the type for a [`Type::Tuple`] with the items.
    pub fn tuple(&mut self, items: impl IntoIterator<Item = TypeId>) -> TypeId {
        self.get(CompositeType::Tuple(Vec::from_iter(items)).into())
    }

    /// Fetch the type for a [`Type::Ref`] of a given type.
    pub fn ref_of(&mut self, ty: TypeId) -> TypeId {
        self.get(CompositeType::Ref(ty).into())
    }

    /// Calculate the size of a type.
    pub fn size_of(&self, ty: TypeId) -> usize {
        match &self[ty] {
            Type::Never => todo!("work out what to do with this"),
            Type::I8 => 1,
            Type::U8 => 1,
            Type::Boolean => 1,
            // WARN: Should be linked to target.
            Type::Composite(CompositeType::Ref(_)) => std::mem::size_of::<usize>(),
            // WARN: Should be linked to target.
            Type::Composite(CompositeType::Function { .. }) => std::mem::size_of::<usize>(),
            Type::Composite(CompositeType::Tuple(type_ids)) => {
                type_ids.clone().iter().map(|ty| self.size_of(*ty)).sum()
            }
        }
    }

    /// Calculate the offset of a field in a type.
    pub fn offset_of(&self, ty: TypeId, field: usize) -> Option<usize> {
        match &self[ty] {
            Type::Composite(CompositeType::Tuple(type_ids)) => {
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
