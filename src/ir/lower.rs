use std::collections::HashMap;

use crate::{
    Ctx, ast,
    ir::{ctx::IrCtx, repr::*},
    tir::{self, BindingId, Ty},
};

pub fn lower(ctx: &Ctx, tir: &tir::Program) -> IrCtx {
    let mut ir = IrCtx::default();

    for (id, function) in tir.functions.iter_keys() {
        let mut builder = FunctionBuilder::new(
            function
                .bindings
                .iter_keys()
                .map(|(id, binding)| (id, binding.clone())),
            function.ret.clone(),
        );

        let ret_value = builder.ret_value;

        lower_block(&mut builder, &function.block, ret_value);

        // TODO: Check when to do this.
        builder.terminate(Terminator::Return);

        ir.functions.insert(builder.build());
    }

    ir
}

#[derive(Clone)]
struct FunctionBuilder {
    body: Body,
    bindings: HashMap<BindingId, Local>,
    ret_value: Local,
    statements: Vec<Statement>,
}

impl FunctionBuilder {
    fn new(bindings: impl Iterator<Item = (BindingId, tir::Binding)>, ret_ty: Ty) -> Self {
        let mut body = Body::default();
        let ret_value = body.local_decls.insert(LocalDecl { ty: ret_ty });
        let bindings = bindings
            .map(|(id, binding)| (id, body.local_decls.insert(LocalDecl { ty: binding.ty })))
            .collect();

        Self {
            body,
            ret_value,
            bindings,
            statements: Vec::new(),
        }
    }

    fn build(self) -> Body {
        assert!(self.statements.is_empty());
        self.body
    }

    fn push_statement(&mut self, statement: Statement) {
        self.statements.push(statement);
    }

    fn terminate(&mut self, terminator: Terminator) {
        self.body.basic_blocks.insert(BasicBlockData {
            statements: std::mem::take(&mut self.statements),
            terminator,
        });
    }

    fn create_temporary(&mut self, ty: Ty) -> Local {
        let temp = self.body.local_decls.insert(LocalDecl { ty });
        self.push_statement(Statement::StorageLive(temp));
        temp
    }
}

fn lower_block(builder: &mut FunctionBuilder, block: &tir::Block, result_value: Local) {
    for statement in &block.statements {
        match statement {
            tir::Statement::Declaration { binding, value } => todo!(),
            tir::Statement::Expr { expr, semicolon } => {
                lower_expr(
                    builder,
                    expr,
                    // TODO: This should only use the result value if it's the last statement.
                    result_value,
                );
            }
        }
    }
}

fn lower_expr(builder: &mut FunctionBuilder, expr: &tir::Expr, result_value: Local) {
    match &expr.kind {
        tir::ExprKind::Assignment { binding, value } => todo!(),
        tir::ExprKind::Literal(literal) => builder.push_statement(Statement::Assign {
            place: Place {
                local: result_value,
                projection: Vec::new(),
            },
            rvalue: RValue::Use(Operand::Constant(match literal {
                tir::Literal::I8(i8) => Constant::I8(*i8),
                tir::Literal::U8(u8) => Constant::U8(*u8),
            })),
        }),
        tir::ExprKind::If {
            condition,
            block,
            otherwise,
        } => todo!(),
        tir::ExprKind::Field { expr, field } => todo!(),
        tir::ExprKind::Index { expr, index } => todo!(),
        tir::ExprKind::Block(block) => todo!(),
        tir::ExprKind::BinOp { lhs, op, rhs } => {
            let lhs_temp = builder.create_temporary(lhs.ty.clone());
            let rhs_temp = builder.create_temporary(rhs.ty.clone());

            lower_expr(builder, lhs, lhs_temp);
            lower_expr(builder, rhs, rhs_temp);

            builder.push_statement(Statement::Assign {
                place: Place {
                    local: result_value,
                    projection: Vec::new(),
                },
                rvalue: RValue::BinaryOp {
                    op: match op {
                        ast::BinOp::Plus => BinOp::Add,
                        ast::BinOp::Minus => BinOp::Sub,
                        ast::BinOp::Multiply => BinOp::Mul,
                        ast::BinOp::Divide => BinOp::Div,
                        ast::BinOp::LogicAnd => todo!(),
                        ast::BinOp::LogicOr => todo!(),
                        ast::BinOp::BitAnd => todo!(),
                        ast::BinOp::BitOr => todo!(),
                        ast::BinOp::Eq => todo!(),
                        ast::BinOp::Ne => todo!(),
                        ast::BinOp::Gt => todo!(),
                        ast::BinOp::Ge => todo!(),
                        ast::BinOp::Lt => todo!(),
                        ast::BinOp::Le => todo!(),
                    },
                    lhs: Operand::Place(Place {
                        local: lhs_temp,
                        projection: Vec::new(),
                    }),
                    rhs: Operand::Place(Place {
                        local: rhs_temp,
                        projection: Vec::new(),
                    }),
                },
            });
        }
        tir::ExprKind::UnOp { op, rhs } => todo!(),
        tir::ExprKind::Variable(binding) => todo!(),
    }
}
