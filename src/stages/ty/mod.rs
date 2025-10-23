mod solve;

use crate::{
    ir2::{
        cst::{BinaryOp, UnaryOp},
        hir::*,
    },
    stages::ty::solve::{Guess, Solver},
};

pub fn build_solver(hir: &Hir) -> Solver {
    let mut builder = SolverBuilder::new();
    hir.visit(&mut builder);
    builder.build()
}

#[derive(Clone, Debug)]
struct SolverBuilder {
    solver: Solver,
}

impl SolverBuilder {
    pub fn new() -> Self {
        Self {
            solver: Solver::new(),
        }
    }

    pub fn build(self) -> Solver {
        self.solver
    }
}

impl HirVisitor for SolverBuilder {
    fn visit_function_declaration(&mut self, params: Vec<Type>, return_ty: Type, body: &Block) {
        // Body must evaluate to return type.
        self.solver.add_solution(body.expr, return_ty);

        // TODO: Save function declaration.
    }

    fn visit_assign(&mut self, id: ExprId, assign: &Assign) {
        // LHS and RHS must be the same.
        self.solver.add_constraint(assign.variable, assign.value);
        // This expression yields nothing.
        self.solver.add_solution(id, Type::Unit);
    }

    fn visit_binary(&mut self, id: ExprId, binary: &Binary) {
        match binary.op {
            BinaryOp::Plus(_)
            | BinaryOp::Minus(_)
            | BinaryOp::Multiply(_)
            | BinaryOp::Divide(_)
            | BinaryOp::BinaryAnd(_)
            | BinaryOp::BinaryOr(_) => {
                // Operands must be identical.
                self.solver.add_constraint(binary.lhs, binary.rhs);

                // Result will match type of operands.
                self.solver.add_constraint(id, binary.lhs);

                // Operands and result should be an integer.
                self.solver.add_guess(binary.lhs, Guess::AnyInteger);
                self.solver.add_guess(binary.rhs, Guess::AnyInteger);
                self.solver.add_guess(id, Guess::AnyInteger);
            }
            BinaryOp::Equal(_) | BinaryOp::NotEqual(_) => {
                // Operands must be identical.
                self.solver.add_constraint(binary.lhs, binary.rhs);

                // Result will be boolean.
                self.solver.add_solution(id, Type::Boolean);
            }
            BinaryOp::Greater(_)
            | BinaryOp::GreaterEqual(_)
            | BinaryOp::Less(_)
            | BinaryOp::LessEqual(_) => {
                // Operands must be identical.
                self.solver.add_constraint(binary.lhs, binary.rhs);

                // Result will be boolean.
                self.solver.add_solution(id, Type::Boolean);

                // TODO: Probably need a better way to ensure the types are ordinal.
                self.solver.add_guess(binary.lhs, Guess::AnyInteger);
                self.solver.add_guess(binary.rhs, Guess::AnyInteger);
            }
            BinaryOp::LogicalAnd(_) | BinaryOp::LogicalOr(_) => {
                // Operands must be boolean.
                self.solver.add_solution(binary.lhs, Type::Boolean);
                self.solver.add_solution(binary.rhs, Type::Boolean);
                // Will result in a boolean.
                self.solver.add_solution(id, Type::Boolean);
            }
        }
    }

    fn visit_unary(&mut self, id: ExprId, unary: &Unary) {
        match unary.op {
            UnaryOp::Not(_) => {
                // Output type is same as input.
                self.solver.add_constraint(id, unary.value);
                // Inputs and outputs should be an integer.
                self.solver.add_guess(unary.value, Guess::AnyInteger);
                self.solver.add_guess(id, Guess::AnyInteger);
            }
            UnaryOp::Negative(_) => {
                // Output type is same as input.
                self.solver.add_constraint(id, unary.value);
                // Inputs and outputs should be a signed integer.
                self.solver.add_guess(unary.value, Guess::SignedInteger);
                self.solver.add_guess(id, Guess::SignedInteger);
            }
            UnaryOp::Deref(_) => {
                // TODO: Make sure that operand is a pointer.
                // TODO: Make sure output is inner type of pointer.
                todo!()
            }
            UnaryOp::Ref(_) => {
                // TODO: Make sure output is a reference to the inner type.
                todo!()
            }
        }
    }

    fn visit_switch(
        &mut self,
        id: ExprId,
        discriminator: ExprId,
        branches: Vec<(&Literal, &Block)>,
        default: Option<&Block>,
    ) {
        for (value, block) in branches {
            // Branch value must match discriminator type.
            self.visit_literal(discriminator, value);

            // This expression must resolve to the same as the block.
            self.solver.add_constraint(id, block.expr);
        }

        if let Some(default) = default {
            // Ensure default branch matches expression.
            self.solver.add_constraint(id, default.expr);
        } else {
            // No default branch, so this expression must resolve to unit.
            // TODO: This does not work if all branches are exhaustive.
            self.solver.add_solution(id, Type::Unit);
        }
    }

    fn visit_literal(&mut self, id: ExprId, literal: &Literal) {
        match literal {
            Literal::Integer(_) => self.solver.add_guess(id, Guess::AnyInteger),
            Literal::Boolean(_) => self.solver.add_solution(id, Type::Boolean),
            Literal::Unit => self.solver.add_solution(id, Type::Unit),
        }
    }

    fn visit_call(&mut self, id: ExprId, call: &Call) {
        // TODO: Enforce that callee is a function
        // TODO: Enforce type of args matches function signature
    }

    fn visit_block(&mut self, id: ExprId, block: &Block) {
        // Expression resolves to the type of the block.
        self.solver.add_constraint(id, block.expr);
    }

    fn visit_variable(&mut self, id: ExprId, variable: &Variable, declaration: &DeclarationTy) {
        match declaration {
            DeclarationTy::Type(ty) => self.solver.add_solution(id, ty.clone()),
            DeclarationTy::Inferred(expr_id) => self.solver.add_constraint(id, *expr_id),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::lex::tok;

    use super::*;

    #[test]
    fn build_binary() {
        let mut builder = SolverBuilder::new();
        builder.visit_binary(
            ExprId::new(0),
            &Binary {
                lhs: ExprId::new(1),
                op: BinaryOp::LogicalAnd(tok::AmpAmp),
                rhs: ExprId::new(2),
            },
        );
        let solver = builder.build();
        dbg!(solver);
        assert!(false);
    }
}
