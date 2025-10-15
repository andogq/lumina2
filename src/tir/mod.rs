mod ty;

use std::collections::HashMap;

use crate::{
    Ctx, Ident,
    ast::{self, BinOp, UnOp},
    indexed_vec,
    util::indexed_vec::Key,
};

pub use self::ty::Ty;

#[derive(Clone, Debug, Default)]
pub struct Program {
    pub functions: Functions,
    pub function_bindings: HashMap<Ident, FunctionId>,
}

indexed_vec!(pub key FunctionId);
indexed_vec!(pub Functions<FunctionId, Function>);

#[derive(Clone, Debug)]
pub struct Function {
    pub name: Ident,
    pub bindings: Bindings,
    pub params: Vec<Param>,
    pub ret: Ty,
    pub block: Block,
}

indexed_vec!(pub key BindingId);
indexed_vec!(pub Bindings<BindingId, Binding>);

impl Bindings {
    fn has(&self, ident: Ident) -> bool {
        self.iter().any(|binding| binding.ident == ident)
    }
}

#[derive(Clone, Debug)]
pub struct Binding {
    pub ident: Ident,
    pub ty: Ty,
}

#[derive(Clone, Debug)]
pub struct Param {
    pub ident: Ident,
    pub binding: BindingId,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub ty: Ty,
    pub statements: Vec<Statement>,
    pub yield_statement: bool,
}

#[derive(Clone, Debug)]
pub enum Statement {
    Declaration { binding: BindingId, value: Expr },
    Expr { expr: Expr, semicolon: bool },
    Return(Expr),
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub ty: Ty,
    pub kind: ExprKind,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Assignment {
        binding: Box<Expr>,
        value: Box<Expr>,
    },
    Literal(Literal),
    Switch {
        discriminator: Box<Expr>,
        targets: Vec<(Literal, Block)>,
        otherwise: Block,
    },
    Field {
        expr: Box<Expr>,
        // TODO: Maybe not this
        field: Ident,
    },
    Index {
        expr: Box<Expr>,
        index: Box<Expr>,
    },
    Block(Block),
    BinOp {
        lhs: Box<Expr>,
        op: BinOp,
        rhs: Box<Expr>,
    },
    UnOp {
        op: UnOp,
        rhs: Box<Expr>,
    },
    Variable(BindingId),
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
}

#[derive(Clone, Debug)]
pub enum Literal {
    I8(i8),
    U8(u8),
    Boolean(bool),
    Fn(FunctionId),
}

pub fn lower(ctx: &Ctx, ast: &ast::Program) -> Program {
    let mut program = Program::default();

    let fn_bindings = ast
        .functions
        .iter()
        .enumerate()
        .map(|(id, func)| {
            // HACK: Mega hack
            let id = FunctionId(Key::of(id));

            (
                func.name,
                (
                    id,
                    Ty::Fn(
                        func.params
                            .iter()
                            .map(|(_, ty)| ctx.ty_names[ty].clone())
                            .collect(),
                        Box::new(
                            func.ret
                                .as_ref()
                                .map(|ty| ctx.ty_names[ty].clone())
                                .unwrap_or(Ty::Unit),
                        ),
                    ),
                ),
            )
        })
        .collect::<HashMap<_, _>>();

    for ast_function in &ast.functions {
        let mut bindings = Bindings::default();

        let params = ast_function
            .params
            .iter()
            .map(|(ident, ty_name)| Param {
                ident: *ident,
                binding: bindings.insert(Binding {
                    ident: *ident,
                    ty: ctx.ty_names[ty_name].clone(),
                }),
            })
            .collect();

        let ret = ast_function
            .ret
            .map(|ret| ctx.ty_names[&ret].clone())
            .unwrap_or(Ty::Unit);

        let block = lower_block(ctx, &fn_bindings, &mut bindings, &ret, &ast_function.body);

        assert_eq!(ret, block.ty);

        let function_id = program.functions.insert(Function {
            name: ast_function.name,
            bindings,
            params,
            ret,
            block,
        });
        program
            .function_bindings
            .insert(ast_function.name, function_id);
    }

    program
}

fn lower_block(
    ctx: &Ctx,
    fn_bindings: &HashMap<Ident, (FunctionId, Ty)>,
    bindings: &mut Bindings,
    ret_ty: &Ty,
    block: &ast::Block,
) -> Block {
    assert!(
        !block
            .statements
            .iter()
            .take(block.statements.len() - 1)
            .filter_map(|statement| match statement {
                ast::Statement::Expr {
                    expr,
                    semicolon: false,
                } => Some(expr),
                _ => None,
            })
            .any(|expr| !matches!(expr, ast::Expr::Block(_) | ast::Expr::If { .. })),
        "only last statement, or block-like expressions (if, block, etc) can omit semicolon"
    );

    let statements = block
        .statements
        .iter()
        .map(|statement| lower_statement(ctx, fn_bindings, bindings, ret_ty, statement))
        .collect::<Vec<_>>();

    assert!(
        statements
            .iter()
            .take(statements.len() - 1)
            .filter_map(|statement| match statement {
                Statement::Expr { expr, .. } => Some(expr),
                _ => None,
            })
            .all(|expr| expr.ty == Ty::Unit),
        "all expression statements except the last must resolve to unit type"
    );

    let (yield_statement, ty) = statements
        .last()
        .and_then(|statement| match statement {
            Statement::Expr { expr, semicolon } if !*semicolon => Some((true, expr.ty.clone())),
            Statement::Return(_) => Some((false, Ty::Unreachable)),
            _ => None,
        })
        .unwrap_or((false, Ty::Unit));

    Block {
        ty,
        statements,
        yield_statement,
    }
}

fn lower_statement(
    ctx: &Ctx,
    fn_bindings: &HashMap<Ident, (FunctionId, Ty)>,
    bindings: &mut Bindings,
    ret_ty: &Ty,
    statement: &ast::Statement,
) -> Statement {
    match statement {
        ast::Statement::Declaration {
            binding,
            ty_annotation,
            value,
        } => {
            let value = lower_expr(ctx, fn_bindings, bindings, ret_ty, value);
            let ty = match ty_annotation {
                Some(ty_annotation) => {
                    let ty = ctx.ty_names[ty_annotation].clone();
                    assert_eq!(ty, value.ty);
                    ty
                }
                None => value.ty.clone(),
            };

            Statement::Declaration {
                binding: {
                    // TODO: Shadowing
                    assert!(!bindings.has(*binding));

                    bindings.insert(Binding {
                        ident: *binding,
                        ty,
                    })
                },
                value,
            }
        }
        ast::Statement::Return(expr) => {
            let expr = lower_expr(ctx, fn_bindings, bindings, ret_ty, expr);
            // Ensure that the expression's type matches the function's return type.
            assert_eq!(expr.ty, *ret_ty);
            Statement::Return(expr)
        }
        ast::Statement::Expr { expr, semicolon } => Statement::Expr {
            expr: lower_expr(ctx, fn_bindings, bindings, ret_ty, expr),
            semicolon: *semicolon,
        },
    }
}

fn lower_expr(
    ctx: &Ctx,
    fn_bindings: &HashMap<Ident, (FunctionId, Ty)>,
    bindings: &mut Bindings,
    ret_ty: &Ty,
    expr: &ast::Expr,
) -> Expr {
    match expr {
        ast::Expr::Assignment { binding, value } => {
            let binding = lower_expr(ctx, fn_bindings, bindings, ret_ty, binding);
            let value = lower_expr(ctx, fn_bindings, bindings, ret_ty, value);

            // TODO: Should these types be equivalent?
            assert_eq!(binding.ty, value.ty);

            Expr {
                ty: Ty::Unit,
                kind: ExprKind::Assignment {
                    binding: Box::new(binding),
                    value: Box::new(value),
                },
            }
        }
        ast::Expr::Literal(literal) => {
            let (ty, literal) = match literal {
                // TODO: Literal could be i8 or u8, depending on what it's around.
                ast::Literal::Integer(literal) => (Ty::U8, Literal::U8(*literal as u8)),
                ast::Literal::Boolean(bool) => (Ty::Boolean, Literal::Boolean(*bool)),
            };

            Expr {
                ty,
                kind: ExprKind::Literal(literal),
            }
        }
        ast::Expr::If {
            condition,
            block,
            otherwise,
        } => {
            let condition = lower_expr(ctx, fn_bindings, bindings, ret_ty, condition);
            assert_eq!(condition.ty, Ty::Boolean);

            let block = lower_block(ctx, fn_bindings, bindings, ret_ty, block);

            let otherwise = if let Some(otherwise) = otherwise {
                let otherwise = lower_block(ctx, fn_bindings, bindings, ret_ty, otherwise);
                // Both branches should return the same type.
                assert_eq!(otherwise.ty, block.ty);
                otherwise
            } else {
                assert_eq!(block.ty, Ty::Unit);
                Block {
                    ty: Ty::Unit,
                    statements: vec![],
                    yield_statement: true,
                }
            };

            Expr {
                ty: block.ty.clone(),
                kind: ExprKind::Switch {
                    discriminator: Box::new(condition),
                    targets: vec![(Literal::Boolean(true), block)],
                    otherwise,
                },
            }
        }
        ast::Expr::Field { expr, field } => todo!(),
        ast::Expr::Index { expr, index } => todo!(),
        ast::Expr::Block(block) => {
            let block = lower_block(ctx, fn_bindings, bindings, ret_ty, block);
            Expr {
                ty: block.ty.clone(),
                kind: ExprKind::Block(block),
            }
        }
        ast::Expr::BinOp { lhs, op, rhs } => {
            let lhs = lower_expr(ctx, fn_bindings, bindings, ret_ty, lhs);
            let rhs = lower_expr(ctx, fn_bindings, bindings, ret_ty, rhs);

            let ty = match (&lhs.ty, op, &rhs.ty) {
                (
                    lhs @ (Ty::U8 | Ty::I8),
                    BinOp::Plus
                    | BinOp::Minus
                    | BinOp::Multiply
                    | BinOp::Divide
                    | BinOp::BitAnd
                    | BinOp::BitOr,
                    rhs @ (Ty::U8 | Ty::I8),
                ) if lhs == rhs => lhs.clone(),
                (Ty::Boolean, BinOp::LogicAnd | BinOp::LogicOr, Ty::Boolean) => Ty::Boolean,
                (
                    lhs @ (Ty::U8 | Ty::I8),
                    BinOp::Eq | BinOp::Ne | BinOp::Gt | BinOp::Ge | BinOp::Lt | BinOp::Le,
                    rhs @ (Ty::U8 | Ty::I8),
                ) if lhs == rhs => Ty::Boolean,

                (lhs, op, rhs) => panic!("cannot apply bin: {lhs:?} {op} {rhs:?}"),
            };

            Expr {
                ty,
                kind: ExprKind::BinOp {
                    lhs: Box::new(lhs),
                    op: op.clone(),
                    rhs: Box::new(rhs),
                },
            }
        }
        ast::Expr::UnOp { op, rhs } => {
            let rhs = lower_expr(ctx, fn_bindings, bindings, ret_ty, rhs);

            let ty = match (op, &rhs.ty) {
                (UnOp::Deref, Ty::Ref(inner)) => *inner.clone(),
                (UnOp::Minus, rhs @ Ty::I8) => rhs.clone(),
                (UnOp::Ref, rhs) => Ty::Ref(Box::new(rhs.clone())),
                (op, rhs) => panic!("cannot apply unary: {op} {rhs:?}"),
            };

            Expr {
                ty,
                kind: ExprKind::UnOp {
                    op: op.clone(),
                    rhs: Box::new(rhs),
                },
            }
        }
        ast::Expr::Match {
            discriminator,
            arms,
            otherwise,
        } => todo!(),
        ast::Expr::Call { callee, args } => {
            let callee = lower_expr(ctx, fn_bindings, bindings, ret_ty, callee);
            let args = args
                .iter()
                .map(|arg| lower_expr(ctx, fn_bindings, bindings, ret_ty, arg))
                .collect::<Vec<_>>();

            let Ty::Fn(fn_arg_tys, fn_ret_ty) = &callee.ty else {
                panic!("expected callee to be function, but found: {:?}", callee.ty);
            };

            assert!(
                args.iter()
                    .zip(fn_arg_tys.iter())
                    .all(|(arg, param)| arg.ty == *param),
                "function arguments must match signature"
            );

            Expr {
                ty: *fn_ret_ty.clone(),
                kind: ExprKind::Call {
                    callee: Box::new(callee),
                    args,
                },
            }
        }
        ast::Expr::Variable(ident) => {
            if let Some((id, binding)) = bindings
                .iter_keys()
                .find(|(_, binding)| binding.ident == *ident)
            {
                Expr {
                    ty: binding.ty.clone(),
                    kind: ExprKind::Variable(id),
                }
            } else if let Some((id, ty)) = fn_bindings.get(ident) {
                Expr {
                    ty: ty.clone(),
                    kind: ExprKind::Literal(Literal::Fn(id.clone())),
                }
            } else {
                panic!("unknown bindings: {ident}");
            }
        }
    }
}
