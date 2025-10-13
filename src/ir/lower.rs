use std::collections::HashMap;

use crate::{
    Ctx, Ident, ast,
    ir::{ctx::IrCtx, repr::*},
    tir::{self, BindingId, Ty},
};

pub fn lower(ctx: &Ctx, tir: &tir::Program) -> IrCtx {
    let mut ir = IrCtx::new(ctx.idents.clone());

    for (id, function) in tir.functions.iter_keys() {
        let mut builder = FunctionBuilder::new(
            function.name,
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
    body: Function,
    current_block: BasicBlock,
    bindings: HashMap<BindingId, Local>,
    ret_value: Local,
}

impl FunctionBuilder {
    fn new(
        name: Ident,
        bindings: impl Iterator<Item = (BindingId, tir::Binding)>,
        ret_ty: Ty,
    ) -> Self {
        let mut body = Function::new(name);
        let ret_value = body.local_decls.insert(LocalDecl { ty: ret_ty });
        let bindings = bindings
            .map(|(id, binding)| (id, body.local_decls.insert(LocalDecl { ty: binding.ty })))
            .collect();
        let current_block = body.basic_blocks.insert(BasicBlockData {
            statements: Vec::new(),
            terminator: Terminator::Unreachable,
        });

        Self {
            body,
            ret_value,
            bindings,
            current_block,
        }
    }

    fn build(self) -> Function {
        self.body
    }

    fn new_block(&mut self) -> BasicBlock {
        self.body.basic_blocks.insert(BasicBlockData {
            statements: Vec::new(),
            terminator: Terminator::Unreachable,
        })
    }

    fn set_current_block(&mut self, current_block: BasicBlock) {
        self.current_block = current_block;
    }

    fn current_block(&self) -> BasicBlock {
        self.current_block
    }

    fn push_statement(&mut self, statement: Statement) {
        self.body.basic_blocks[self.current_block]
            .statements
            .push(statement);
    }

    fn terminate(&mut self, terminator: Terminator) {
        let current_terminator = &mut self.body.basic_blocks[self.current_block].terminator;
        assert_eq!(*current_terminator, Terminator::Unreachable);
        *current_terminator = terminator;
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
            tir::Statement::Declaration { binding, value } => {
                let local = builder.bindings[binding];
                lower_expr(builder, value, local);
            }
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
        tir::ExprKind::Assignment { binding, value } => {
            let place = expr_to_place(builder, binding);

            let value_temp = builder.create_temporary(value.ty.clone());
            lower_expr(builder, value, value_temp);

            builder.push_statement(Statement::Assign {
                place,
                rvalue: RValue::Use(Operand::Place(Place {
                    local: value_temp,
                    projection: Vec::new(),
                })),
            });
        }
        tir::ExprKind::Literal(literal) => builder.push_statement(Statement::Assign {
            place: Place {
                local: result_value,
                projection: Vec::new(),
            },
            rvalue: RValue::Use(Operand::Constant(match literal {
                tir::Literal::I8(i8) => Constant::I8(*i8),
                tir::Literal::U8(u8) => Constant::U8(*u8),
                tir::Literal::Boolean(bool) => Constant::Boolean(*bool),
            })),
        }),
        tir::ExprKind::Switch {
            discriminator,
            targets,
            otherwise,
        } => {
            let discriminator_temp = builder.create_temporary(discriminator.ty.clone());
            lower_expr(builder, discriminator, discriminator_temp);

            let current_block = builder.current_block();

            let final_block = builder.new_block();

            let targets = targets
                .iter()
                .map(|(target, block)| {
                    let ir_block = builder.new_block();

                    builder.set_current_block(ir_block);
                    lower_block(builder, block, result_value);
                    builder.terminate(Terminator::Goto(final_block));

                    let target = match target {
                        tir::Literal::I8(i8) => Constant::I8(*i8),
                        tir::Literal::U8(u8) => Constant::U8(*u8),
                        tir::Literal::Boolean(bool) => Constant::Boolean(*bool),
                    };

                    (target, ir_block)
                })
                .collect();

            let otherwise_block = builder.new_block();
            builder.set_current_block(otherwise_block);
            builder.terminate(Terminator::Goto(final_block));

            // Return back to the original block, to insert the terminator.
            builder.set_current_block(current_block);
            builder.terminate(Terminator::SwitchInt {
                discriminator: Operand::Place(Place {
                    local: discriminator_temp,
                    projection: Vec::new(),
                }),
                targets,
                otherwise: otherwise_block,
            });

            builder.set_current_block(final_block);
        }
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
                        ast::BinOp::LogicAnd => BinOp::LogicalAnd,
                        ast::BinOp::LogicOr => BinOp::LogicalOr,
                        ast::BinOp::BitAnd => BinOp::BitAnd,
                        ast::BinOp::BitOr => BinOp::BitOr,
                        ast::BinOp::Eq => BinOp::Eq,
                        ast::BinOp::Ne => BinOp::Ne,
                        ast::BinOp::Gt => BinOp::Gt,
                        ast::BinOp::Ge => BinOp::Ge,
                        ast::BinOp::Lt => BinOp::Lt,
                        ast::BinOp::Le => BinOp::Le,
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
        tir::ExprKind::Variable(binding) => builder.push_statement(Statement::Assign {
            place: Place {
                local: result_value,
                projection: Vec::new(),
            },
            rvalue: RValue::Use(Operand::Place(Place {
                local: builder.bindings[binding],
                projection: Vec::new(),
            })),
        }),
    }
}

fn expr_to_place(builder: &mut FunctionBuilder, expr: &tir::Expr) -> Place {
    match &expr.kind {
        tir::ExprKind::Variable(binding_id) => Place {
            local: builder.bindings[binding_id],
            projection: Vec::new(),
        },
        expr => panic!("invalid lhs: {expr:?}"),
    }
}
