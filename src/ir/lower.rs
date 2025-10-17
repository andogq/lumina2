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

        let ret_value = lower_block(&mut builder, &function.block);
        // TODO: No clue if this should be done
        builder.push_statement(Statement::Assign {
            place: Place {
                local: builder.ret_value,
                projection: Vec::new(),
            },
            rvalue: RValue::Use(ret_value),
        });

        // Account for blocks which already end with an explicit 'return'.
        if builder.body.basic_blocks[builder.current_block].terminator != Terminator::Return {
            builder.terminate(Terminator::Return);
        }

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
        if let Statement::Assign {
            rvalue: RValue::Use(Operand::Constant(Constant::Unit)),
            ..
        } = statement
        {
            println!("WARN: assigning unit to statement");
            return;
        }

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

fn lower_block(builder: &mut FunctionBuilder, block: &tir::Block) -> Operand {
    let mut last_value = Operand::Constant(Constant::Unit);
    for statement in &block.statements {
        last_value = Operand::Constant(Constant::Unit);
        match statement {
            tir::Statement::Declaration { binding, value } => {
                let local = builder.bindings[binding];
                let value = lower_expr(builder, value);
                builder.push_statement(Statement::Assign {
                    place: Place {
                        local,
                        projection: Vec::new(),
                    },
                    rvalue: RValue::Use(value),
                });
            }
            tir::Statement::Return(expr) => {
                // Lower the expression into the return position.
                let value = lower_expr(builder, expr);
                builder.push_statement(Statement::Assign {
                    place: Place {
                        local: builder.ret_value,
                        projection: Vec::new(),
                    },
                    rvalue: RValue::Use(value),
                });
                builder.terminate(Terminator::Return);
            }
            tir::Statement::Expr { expr, semicolon } => {
                last_value = lower_expr(builder, expr);
            }
        }
    }
    last_value
}

fn lower_expr(builder: &mut FunctionBuilder, expr: &tir::Expr) -> Operand {
    match &expr.kind {
        tir::ExprKind::Assignment { binding, value } => {
            let place = expr_to_place(builder, binding);
            let value = lower_expr(builder, value);

            builder.push_statement(Statement::Assign {
                place,
                rvalue: RValue::Use(value),
            });

            Operand::Constant(Constant::Unit)
        }
        tir::ExprKind::Literal(literal) => Operand::Constant(match literal {
            tir::Literal::I8(i8) => Constant::I8(*i8),
            tir::Literal::U8(u8) => Constant::U8(*u8),
            tir::Literal::Boolean(bool) => Constant::Boolean(*bool),
            tir::Literal::Fn(fn_id) => Constant::FnItem(*fn_id),
        }),
        tir::ExprKind::Switch {
            discriminator,
            targets,
            otherwise,
        } => {
            let discriminator = lower_expr(builder, discriminator);

            let current_block = builder.current_block();

            let final_block = builder.new_block();

            let merge_local =
                (expr.ty != Ty::Unit).then(|| builder.create_temporary(expr.ty.clone()));

            let targets = targets
                .iter()
                .map(|(target, block)| {
                    let ir_block = builder.new_block();

                    builder.set_current_block(ir_block);
                    let result = lower_block(builder, block);
                    if let Some(merge_local) = merge_local {
                        builder.push_statement(Statement::Assign {
                            place: Place {
                                local: merge_local,
                                projection: Vec::new(),
                            },
                            rvalue: RValue::Use(result),
                        });
                    }
                    // HACK: Only update the terminator if it's not a return statement.
                    if !matches!(
                        builder.body.basic_blocks[builder.current_block].terminator,
                        Terminator::Return
                    ) {
                        builder.terminate(Terminator::Goto(final_block));
                    }

                    let target = match target {
                        tir::Literal::I8(i8) => Constant::I8(*i8),
                        tir::Literal::U8(u8) => Constant::U8(*u8),
                        tir::Literal::Boolean(bool) => Constant::Boolean(*bool),
                        tir::Literal::Fn(..) => panic!("cannot use function as target of switch"),
                    };

                    (target, ir_block)
                })
                .collect();

            let otherwise_block = builder.new_block();
            builder.set_current_block(otherwise_block);
            let otherwise_value = lower_block(builder, otherwise);
            if let Some(merge_local) = merge_local {
                builder.push_statement(Statement::Assign {
                    place: Place {
                        local: merge_local,
                        projection: Vec::new(),
                    },
                    rvalue: RValue::Use(otherwise_value),
                });
            }
            builder.terminate(Terminator::Goto(final_block));

            // Return back to the original block, to insert the terminator.
            builder.set_current_block(current_block);
            builder.terminate(Terminator::SwitchInt {
                discriminator,
                targets,
                otherwise: otherwise_block,
            });

            builder.set_current_block(final_block);

            if let Some(merge_local) = merge_local {
                Operand::Place(Place {
                    local: merge_local,
                    projection: Vec::new(),
                })
            } else {
                Operand::Constant(Constant::Unit)
            }
        }
        tir::ExprKind::Field { expr, field } => todo!(),
        tir::ExprKind::Index { expr, index } => todo!(),
        tir::ExprKind::Block(block) => todo!(),
        tir::ExprKind::BinOp { lhs, op, rhs } => {
            let lhs = lower_expr(builder, lhs);
            let rhs = lower_expr(builder, rhs);

            let result_value = Place {
                local: builder.create_temporary(expr.ty.clone()),
                projection: Vec::new(),
            };

            builder.push_statement(Statement::Assign {
                place: result_value.clone(),
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
                    lhs,
                    rhs,
                },
            });

            Operand::Place(result_value)
        }
        tir::ExprKind::UnOp { op, rhs } => {
            let result_value = Place {
                local: builder.create_temporary(expr.ty.clone()),
                projection: Vec::new(),
            };

            let statement = Statement::Assign {
                place: result_value.clone(),
                rvalue: match op {
                    ast::UnOp::Ref => RValue::Ref(expr_to_place(builder, rhs)),
                    ast::UnOp::Deref => {
                        let mut rhs = expr_to_place(builder, rhs);
                        rhs.projection.push(Projection::Deref);
                        RValue::Use(Operand::Place(rhs))
                    }
                    ast::UnOp::Minus => {
                        let rhs = lower_expr(builder, rhs);
                        RValue::UnaryOp { op: UnOp::Neg, rhs }
                    }
                },
            };
            builder.push_statement(statement);

            Operand::Place(result_value)
        }
        tir::ExprKind::Variable(binding) => Operand::Place(Place {
            local: builder.bindings[binding],
            projection: Vec::new(),
        }),
        tir::ExprKind::Call { callee, args } => {
            let func = lower_expr(builder, callee);
            let args = args.iter().map(|arg| lower_expr(builder, arg)).collect();

            let result_value = Place {
                local: builder.create_temporary(expr.ty.clone()),
                projection: Vec::new(),
            };

            let next_bb = builder.new_block();
            builder.terminate(Terminator::Call {
                func,
                args,
                destination: result_value.clone(),
                target: next_bb,
            });
            builder.set_current_block(next_bb);
            Operand::Place(result_value)
        }
    }
}

fn expr_to_place(builder: &mut FunctionBuilder, expr: &tir::Expr) -> Place {
    match &expr.kind {
        tir::ExprKind::Variable(binding_id) => Place {
            local: builder.bindings[binding_id],
            projection: Vec::new(),
        },
        tir::ExprKind::UnOp {
            op: ast::UnOp::Deref,
            rhs,
        } => {
            let mut rhs = expr_to_place(builder, rhs);
            // TODO: Not sure if this is append or prepend
            rhs.projection.push(Projection::Deref);
            rhs
        }
        expr => panic!("invalid lhs: {expr:?}"),
    }
}
