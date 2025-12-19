use crate::{
    ir2::{
        cst::{BinaryOp, UnaryOp},
        hir::*,
    },
    stages::ty::Constraint,
};

use super::IntegerKind;

pub struct ConstraintBuilder {
    constraints: Vec<Constraint>,
}

impl ConstraintBuilder {
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
        }
    }

    pub fn build(hir: &Hir) -> Vec<Constraint> {
        let mut builder = ConstraintBuilder::new();
        hir.visit(&mut builder);
        builder.constraints
    }
}

impl HirVisitor for ConstraintBuilder {
    fn visit_function_declaration(
        &mut self,
        params: Vec<(BindingId, Type)>,
        return_ty: Type,
        body: &Block,
    ) {
        // Build constraints for all the parameters.
        self.constraints.extend(
            params
                .iter()
                .map(|(binding, ty)| Constraint::Eq((*binding).into(), ty.clone().into())),
        );

        // TODO: Build constraint for `return_ty` once the function ID is attached

        // Ensure the expression of the body resolves to the return type.
        self.constraints
            .push(Constraint::Eq(body.expr.into(), return_ty.into()));
    }

    fn visit_variable_declaration(&mut self, binding: BindingId, ty: DeclarationTy) {
        match ty {
            // Constrain the binding to the type it's assigned to.
            DeclarationTy::Type(ty) => self
                .constraints
                .push(Constraint::Eq(binding.into(), ty.into())),
            // Constrain the binding to the inferred expression.
            DeclarationTy::Inferred(expr_id) => self
                .constraints
                .push(Constraint::Eq(binding.into(), expr_id.into())),
        }
    }

    fn visit_return(&mut self, value: ExprId, return_ty: Type) {
        self.constraints
            .push(Constraint::Eq(value.into(), return_ty.into()))
    }

    fn visit_assign(&mut self, id: ExprId, assign: &Assign) {
        self.constraints.extend([
            // Value must match variable.
            Constraint::Eq(assign.value.into(), assign.variable.into()),
            // The actual expression resolves to unit.
            Constraint::Eq(id.into(), Type::Unit.into()),
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
                    Constraint::Eq(binary.lhs.into(), binary.rhs.into()),
                    // Operands should be integers.
                    Constraint::Integer(binary.lhs.into(), IntegerKind::Any),
                    Constraint::Integer(binary.rhs.into(), IntegerKind::Any),
                    // Result is the same as the input.
                    Constraint::Eq(id.into(), binary.lhs.into()),
                ]);
            }
            BinaryOp::Equal(_) | BinaryOp::NotEqual(_) => {
                self.constraints.extend([
                    // Operands must be identical
                    Constraint::Eq(binary.lhs.into(), binary.rhs.into()),
                    // Results in a boolean.
                    Constraint::Eq(id.into(), Type::Boolean.into()),
                ]);
            }
            BinaryOp::Greater(_)
            | BinaryOp::GreaterEqual(_)
            | BinaryOp::Less(_)
            | BinaryOp::LessEqual(_) => {
                self.constraints.extend([
                    // Operands must be identical
                    Constraint::Eq(binary.lhs.into(), binary.rhs.into()),
                    // Operands should be integers.
                    // TODO: Probably should check they are ordinals.
                    Constraint::Integer(binary.lhs.into(), IntegerKind::Any),
                    Constraint::Integer(binary.rhs.into(), IntegerKind::Any),
                    // Results in a boolean.
                    Constraint::Eq(id.into(), Type::Boolean.into()),
                ]);
            }
            BinaryOp::LogicalAnd(_) | BinaryOp::LogicalOr(_) => {
                self.constraints.extend([
                    // Operands must be booleans.
                    Constraint::Eq(binary.lhs.into(), Type::Boolean.into()),
                    Constraint::Eq(binary.rhs.into(), Type::Boolean.into()),
                    // Results in a boolean.
                    Constraint::Eq(id.into(), Type::Boolean.into()),
                ]);
            }
        }
    }

    fn visit_unary(&mut self, id: ExprId, unary: &Unary) {
        match unary.op {
            UnaryOp::Not(_) => {
                self.constraints.extend([
                    // Output is same as input.
                    Constraint::Eq(id.into(), unary.value.into()),
                    // Operand can be any integer.
                    Constraint::Integer(unary.value.into(), IntegerKind::Any),
                ]);
            }
            UnaryOp::Negative(_) => {
                self.constraints.extend([
                    // Output is same as input.
                    Constraint::Eq(id.into(), unary.value.into()),
                    // Operand can be any integer.
                    Constraint::Integer(unary.value.into(), IntegerKind::Signed),
                ]);
            }
            UnaryOp::Deref(_) => {
                // Make sure that operand is a pointer, and output is inner type of pointer.
                self.constraints
                    .extend([Constraint::Reference(unary.value.into(), id.into())]);
            }
            UnaryOp::Ref(_) => self
                .constraints
                .extend([Constraint::Reference(id.into(), unary.value.into())]),
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
                    constraint_from_literal(literal, discriminator),
                    // Block which is resolved must match this expression.
                    Constraint::Eq(block.expr.into(), id.into()),
                ]
            }));

        // Ensure the default branch matches the expression, or unit if there is no default branch.
        // TODO: This does not handle branches which are exhaustive.
        self.constraints.push(Constraint::Eq(
            id.into(),
            match default {
                Some(default) => default.expr.into(),
                None => Type::Unit.into(),
            },
        ));
    }

    fn visit_literal(&mut self, id: ExprId, literal: &Literal) {
        self.constraints.push(constraint_from_literal(literal, id));
    }

    fn visit_call(&mut self, id: ExprId, call: &Call) {
        todo!()
    }

    fn visit_block(&mut self, id: ExprId, block: &Block) {
        self.constraints
            .push(Constraint::Eq(id.into(), block.expr.into()))
    }

    fn visit_variable(&mut self, id: ExprId, variable: BindingId) {
        self.constraints
            .push(Constraint::Eq(id.into(), variable.into()));
    }

    fn visit_unreachable(&mut self, id: ExprId) {
        self.constraints
            .push(Constraint::Eq(id.into(), Type::Never.into()));
    }
}

fn constraint_from_literal(literal: &Literal, expr: ExprId) -> Constraint {
    match literal {
        Literal::Integer(_) => Constraint::Integer(expr.into(), IntegerKind::Any),
        Literal::Boolean(_) => Constraint::Eq(expr.into(), Type::Boolean.into()),
        Literal::Unit => Constraint::Eq(expr.into(), Type::Unit.into()),
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
