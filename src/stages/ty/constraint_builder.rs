use std::collections::HashMap;

use crate::{
    ir2::{
        cst::{BinaryOp, UnaryOp},
        hir::*,
    },
    stages::ty::{Constraint, TypeVarId},
};

use super::IntegerKind;

pub struct ConstraintBuilder {
    functions: HashMap<FunctionId, (Vec<Type>, Type)>,
    constraints: Vec<(TypeVarId, Constraint)>,
}

impl ConstraintBuilder {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            constraints: Vec::new(),
        }
    }

    pub fn build(hir: &Hir) -> Vec<(TypeVarId, Constraint)> {
        let mut builder = ConstraintBuilder::new();
        hir.visit(&mut builder);
        builder.constraints
    }
}

impl HirVisitor for ConstraintBuilder {
    type FunctionVisitor = Self;

    fn visit_function_declaration(
        &mut self,
        id: FunctionId,
        params: Vec<(BindingId, Type)>,
        return_ty: Type,
        block: &Block,
    ) {
        // Constrain the bindings
        self.constraints.extend(
            params
                .iter()
                .map(|(binding, ty)| ((*binding).into(), Constraint::Eq(ty.clone().into()))),
        );

        // TODO: Build constraint for `return_ty` once the function ID is attached

        // Ensure block expression yields the return type.
        self.constraints
            .push((block.expr.into(), Constraint::Eq(return_ty.clone().into())));

        // Record the function signature.
        self.functions.insert(
            id,
            (params.into_iter().map(|(_, ty)| ty).collect(), return_ty),
        );
    }

    fn visit_function(&mut self, _id: FunctionId, visit: impl FnOnce(&mut Self::FunctionVisitor)) {
        visit(self);
    }
}

impl HirFunctionVisitor for ConstraintBuilder {
    fn visit_variable_declaration(&mut self, binding: BindingId, ty: DeclarationTy) {
        match ty {
            // Constrain the binding to the type it's assigned to.
            DeclarationTy::Type(ty) => self
                .constraints
                .push((binding.into(), Constraint::Eq(ty.into()))),
            // Constrain the binding to the inferred expression.
            DeclarationTy::Inferred(expr_id) => self
                .constraints
                .push((binding.into(), Constraint::Eq(expr_id.into()))),
        }
    }

    fn visit_return(&mut self, value: ExprId, return_ty: Type) {
        self.constraints
            .push((value.into(), Constraint::Eq(return_ty.into())));
    }

    fn visit_assign(&mut self, id: ExprId, assign: &Assign) {
        self.constraints.extend([
            // Value must match variable.
            (assign.value.into(), Constraint::Eq(assign.variable.into())),
            // The actual expression resolves to unit.
            (id.into(), Constraint::Eq(Type::Unit.into())),
        ]);
    }

    fn visit_binary(&mut self, id: ExprId, binary: &Binary) {
        match binary.op {
            BinaryOp::Plus(_)
            | BinaryOp::Minus(_)
            | BinaryOp::Multiply(_)
            | BinaryOp::Divide(_)
            | BinaryOp::BinaryAnd(_)
            | BinaryOp::BinaryOr(_) => {
                self.constraints.extend([
                    // Operands must equal each other.
                    (binary.lhs.into(), Constraint::Eq(binary.rhs.into())),
                    // Operands should be integers.
                    (binary.lhs.into(), Constraint::Integer(IntegerKind::Any)),
                    (binary.rhs.into(), Constraint::Integer(IntegerKind::Any)),
                    // Result is the same as the input.
                    (id.into(), Constraint::Eq(binary.lhs.into())),
                ]);
            }
            BinaryOp::Equal(_) | BinaryOp::NotEqual(_) => {
                self.constraints.extend([
                    // Operands must be identical
                    (binary.lhs.into(), Constraint::Eq(binary.rhs.into())),
                    // Results in a boolean.
                    (id.into(), Constraint::Eq(Type::Boolean.into())),
                ]);
            }
            BinaryOp::Greater(_)
            | BinaryOp::GreaterEqual(_)
            | BinaryOp::Less(_)
            | BinaryOp::LessEqual(_) => {
                self.constraints.extend([
                    // Operands must be identical
                    (binary.lhs.into(), Constraint::Eq(binary.rhs.into())),
                    // Operands should be integers.
                    // TODO: Probably should check they are ordinals.
                    (binary.lhs.into(), Constraint::Integer(IntegerKind::Any)),
                    (binary.rhs.into(), Constraint::Integer(IntegerKind::Any)),
                    // Results in a boolean.
                    (id.into(), Constraint::Eq(Type::Boolean.into())),
                ]);
            }
            BinaryOp::LogicalAnd(_) | BinaryOp::LogicalOr(_) => {
                self.constraints.extend([
                    // Operands must be booleans.
                    (binary.lhs.into(), Constraint::Eq(Type::Boolean.into())),
                    (binary.rhs.into(), Constraint::Eq(Type::Boolean.into())),
                    // Results in a boolean.
                    (id.into(), Constraint::Eq(Type::Boolean.into())),
                ]);
            }
        }
    }

    fn visit_unary(&mut self, id: ExprId, unary: &Unary) {
        match unary.op {
            UnaryOp::Not(_) => {
                self.constraints.extend([
                    // Output is same as input.
                    (id.into(), Constraint::Eq(unary.value.into())),
                    // Operand can be any integer.
                    (unary.value.into(), Constraint::Integer(IntegerKind::Any)),
                ]);
            }
            UnaryOp::Negative(_) => {
                self.constraints.extend([
                    // Output is same as input.
                    (id.into(), Constraint::Eq(unary.value.into())),
                    // Operand can be any integer.
                    (unary.value.into(), Constraint::Integer(IntegerKind::Signed)),
                ]);
            }
            UnaryOp::Deref(_) => {
                // Make sure that operand is a pointer, and output is inner type of pointer.
                self.constraints
                    .push((unary.value.into(), Constraint::Reference(id.into())));
            }
            UnaryOp::Ref(_) => self
                .constraints
                .push((id.into(), Constraint::Reference(unary.value.into()))),
        }
    }

    fn visit_switch(
        &mut self,
        id: ExprId,
        discriminator: ExprId,
        branches: Vec<(&Literal, &Block)>,
        default: Option<&Block>,
    ) {
        self.constraints
            .extend(branches.iter().flat_map(|(literal, block)| {
                [
                    // Branch literal must match discriminator.
                    (discriminator.into(), constraint_from_literal(literal)),
                    // Block which is resolved must match this expression.
                    (block.expr.into(), Constraint::Eq(id.into())),
                ]
            }));

        // Ensure the default branch matches the expression, or unit if there is no default branch.
        // TODO: This does not handle branches which are exhaustive.
        self.constraints.push((
            id.into(),
            Constraint::Eq(match default {
                Some(default) => default.expr.into(),
                None => Type::Unit.into(),
            }),
        ));
    }

    fn visit_literal(&mut self, id: ExprId, literal: &Literal) {
        self.constraints
            .push((id.into(), constraint_from_literal(literal)));
    }

    fn visit_call(&mut self, id: ExprId, call: &Call) {
        todo!()
    }

    fn visit_block(&mut self, id: ExprId, block: &Block) {
        self.constraints
            .push((id.into(), Constraint::Eq(block.expr.into())))
    }

    fn visit_variable(&mut self, id: ExprId, variable: BindingId) {
        self.constraints
            .push((id.into(), Constraint::Eq(variable.into())));
    }

    fn visit_unreachable(&mut self, id: ExprId) {
        self.constraints
            .push((id.into(), Constraint::Eq(Type::Never.into())));
    }
}

fn constraint_from_literal(literal: &Literal) -> Constraint {
    match literal {
        Literal::Integer(_) => Constraint::Integer(IntegerKind::Any),
        Literal::Boolean(_) => Constraint::Eq(Type::Boolean.into()),
        Literal::Unit => Constraint::Eq(Type::Unit.into()),
    }
}

#[cfg(test)]
mod test {
    use crate::lex::tok;

    use super::*;

    use insta::*;
    use rstest::*;

    #[fixture]
    fn builder() -> ConstraintBuilder {
        ConstraintBuilder::new()
    }

    #[rstest]
    #[case("simple", [], Type::Unit)]
    #[case("return int", [], Type::I8)]
    #[case("params", [(BindingId::new(0), Type::I8), (BindingId::new(1), Type::Boolean)], Type::Boolean)]
    fn function_expression(
        mut builder: ConstraintBuilder,
        #[case] name: &str,
        #[case] params: impl IntoIterator<Item = (BindingId, Type)>,
        #[case] return_ty: Type,
    ) {
        let params = params.into_iter().collect::<Vec<_>>();
        builder.visit_function_declaration(
            FunctionId::new(0),
            params.clone(),
            return_ty.clone(),
            &Block {
                statements: Vec::new(),
                expr: ExprId::new(0),
            },
        );
        assert_debug_snapshot!(
            name,
            builder.constraints,
            &format!("{params:?} => {return_ty:?}")
        );
    }

    #[rstest]
    #[case("inferred", DeclarationTy::Inferred(ExprId::new(0)))]
    #[case("with unit", DeclarationTy::Type(Type::Unit))]
    #[case("with type", DeclarationTy::Type(Type::I8))]
    fn variable_declaration(
        mut builder: ConstraintBuilder,
        #[case] name: &str,
        #[case] ty: DeclarationTy,
    ) {
        builder.visit_variable_declaration(BindingId::new(0), ty.clone());
        assert_debug_snapshot!(name, builder.constraints, &format!("{ty:?}"));
    }

    #[rstest]
    #[case("assign", Assign { variable: ExprId::new(1), value: ExprId::new(2) })]
    fn assign_constraint(
        mut builder: ConstraintBuilder,
        #[case] name: &str,
        #[case] assign: Assign,
    ) {
        builder.visit_assign(ExprId::new(0), &assign);
        assert_debug_snapshot!(name, builder.constraints, &format!("{assign:?}"));
    }

    #[rstest]
    #[case(
        "plus",
        Binary {
            lhs: ExprId::new(1),
            op: BinaryOp::Plus(tok::Plus),
            rhs: ExprId::new(2),
        },
    )]
    #[case(
        "logical and",
        Binary {
            lhs: ExprId::new(1),
            op: BinaryOp::LogicalAnd(tok::AmpAmp),
            rhs: ExprId::new(2),
        },
    )]
    #[case(
        "equal",
        Binary {
            lhs: ExprId::new(1),
            op: BinaryOp::Equal(tok::EqEq),
            rhs: ExprId::new(2),
        },
    )]
    #[case(
        "greater",
        Binary {
            lhs: ExprId::new(1),
            op: BinaryOp::Greater(tok::RAngle),
            rhs: ExprId::new(2),
        },
    )]
    fn binary_constraint(
        mut builder: ConstraintBuilder,
        #[case] name: &str,
        #[case] binary: Binary,
    ) {
        builder.visit_binary(ExprId::new(0), &binary);
        assert_debug_snapshot!(name, builder.constraints, &format!("{binary:?}"));
    }

    #[rstest]
    #[case("negative", Unary { op: UnaryOp::Negative(tok::Minus), value: ExprId::new(1) })]
    fn unary_constraint(mut builder: ConstraintBuilder, #[case] name: &str, #[case] unary: Unary) {
        builder.visit_unary(ExprId::new(0), &unary);
        assert_debug_snapshot!(name, builder.constraints, &format!("{unary:?}"));
    }

    // #[rstest]
    // fn switch_constraint(
    //     mut builder: ConstraintBuilder,
    //     #[case] name: &str,
    //     #[case] discriminator: ExprId,
    //     #[case] branches: impl IntoIterator<Item = (Literal, Block)>,
    //     #[case] default: Option<Block>,
    // ) {
    //     builder.visit_switch()
    // }
}
