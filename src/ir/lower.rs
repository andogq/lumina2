use std::collections::HashMap;

use crate::{
    Ctx,
    ir::{ctx::IrCtx, repr::*},
    tir,
};

pub fn lower(ctx: &Ctx, tir: &tir::Program) -> IrCtx {
    let mut ir = IrCtx::default();

    for (id, function) in tir.functions.iter_keys() {
        let mut body = Body::default();

        // Create local for return value.
        let ret_value = body.local_decls.insert(LocalDecl { ty: function.ret });

        // Allocate all bindings
        let bindings = function
            .bindings
            .iter_keys()
            .map(|(id, binding)| (id, body.local_decls.insert(LocalDecl { ty: binding.ty })))
            .collect::<HashMap<_, _>>();

        let block = lower_block(ctx, &function.block, ret_value);
        body.basic_blocks.insert(block);

        ir.functions.insert(body);
    }

    ir
}

fn lower_block(ctx: &Ctx, block: &tir::Block, result_value: Local) -> BasicBlockData {
    let mut statements = Vec::new();
    for statement in &block.statements {
        match statement {
            tir::Statement::Declaration { binding, value } => todo!(),
            tir::Statement::Expr { expr, semicolon } => {
                lower_expr(
                    ctx,
                    &mut statements,
                    expr,
                    // TODO: This should only use the result value if it's the last statement.
                    result_value,
                );
            }
        }
    }

    // TODO: No clue what this should be.
    let terminator = Terminator::Return;

    BasicBlockData {
        statements,
        terminator,
    }
}

fn lower_expr(ctx: &Ctx, statements: &mut Vec<Statement>, expr: &tir::Expr, result_value: Local) {
    match &expr.kind {
        tir::ExprKind::Assignment { binding, value } => todo!(),
        tir::ExprKind::Literal(literal) => statements.push(Statement::Assign {
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
        tir::ExprKind::BinOp { lhs, op, rhs } => todo!(),
        tir::ExprKind::UnOp { op, rhs } => todo!(),
        tir::ExprKind::Variable(binding) => todo!(),
    }
}
