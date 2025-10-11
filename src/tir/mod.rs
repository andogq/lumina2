use crate::{
    Ctx, Ident,
    ast::{self, BinOp, UnOp},
    indexed_vec,
    ir::{Ty, TyInfo},
};

#[derive(Clone, Debug, Default)]
pub struct Program {
    pub functions: Functions,
}

indexed_vec!(pub key FunctionId);
indexed_vec!(pub Functions<FunctionId, Function>);

#[derive(Clone, Debug)]
pub struct Function {
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
    If {
        condition: Box<Expr>,
        block: Block,
        otherwise: Option<Block>,
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
    Variable(Binding),
}

#[derive(Clone, Debug)]
pub enum Literal {
    I8(i8),
    U8(u8),
}

pub fn lower(ctx: &Ctx, ast: &ast::Program) -> Program {
    let mut program = Program::default();

    for ast_function in &ast.functions {
        let mut bindings = Bindings::default();

        let params = ast_function
            .params
            .iter()
            .map(|(ident, ty_name)| Param {
                ident: *ident,
                binding: bindings.insert(Binding {
                    ident: *ident,
                    ty: ctx.ty_names[ty_name],
                }),
            })
            .collect();

        let ret = ast_function
            .ret
            .map(|ret| ctx.ty_names[&ret])
            .unwrap_or_else(|| ctx.tys.find_or_insert(TyInfo::Unit));

        let block = lower_block(ctx, &mut bindings, &ast_function.body);

        assert_eq!(ret, block.ty);

        program.functions.insert(Function {
            bindings,
            params,
            ret,
            block,
        });
    }

    program
}

fn lower_block(ctx: &Ctx, bindings: &mut Bindings, block: &ast::Block) -> Block {
    let statements = block
        .statements
        .iter()
        .map(|statement| lower_statement(ctx, bindings, statement))
        .collect::<Vec<_>>();

    assert!(
        statements
            .iter()
            .take(statements.len() - 1)
            .filter_map(|statement| match statement {
                Statement::Expr { semicolon, .. } => Some(semicolon),
                _ => None,
            })
            .all(|semicolon| *semicolon),
        "only final expression can omit semicolon"
    );

    let unit_ty = ctx.tys.find_or_insert(TyInfo::Unit);
    let (yield_statement, ty) = statements
        .last()
        .and_then(|statement| match statement {
            Statement::Expr { expr, semicolon } if !*semicolon => Some((true, expr.ty)),
            _ => None,
        })
        .unwrap_or((false, unit_ty));

    Block {
        ty,
        statements,
        yield_statement,
    }
}

fn lower_statement(ctx: &Ctx, bindings: &mut Bindings, statement: &ast::Statement) -> Statement {
    match statement {
        ast::Statement::Declaration {
            binding,
            ty_annotation,
            value,
        } => {
            let value = lower_expr(ctx, bindings, value);
            let ty = match ty_annotation {
                Some(ty_annotation) => {
                    let ty = ctx.ty_names[ty_annotation];
                    assert_eq!(ty, value.ty);
                    ty
                }
                None => value.ty,
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
        ast::Statement::Expr { expr, semicolon } => Statement::Expr {
            expr: lower_expr(ctx, bindings, expr),
            semicolon: *semicolon,
        },
    }
}

fn lower_expr(ctx: &Ctx, bindings: &mut Bindings, expr: &ast::Expr) -> Expr {
    match expr {
        ast::Expr::Assignment { binding, value } => {
            let binding = lower_expr(ctx, bindings, binding);
            let value = lower_expr(ctx, bindings, value);

            // TODO: Should these types be equivalent?
            assert_eq!(binding.ty, value.ty);

            Expr {
                ty: ctx.tys.find_or_insert(TyInfo::Unit),
                kind: ExprKind::Assignment {
                    binding: Box::new(binding),
                    value: Box::new(value),
                },
            }
        }
        ast::Expr::Literal(literal) => {
            let (ty, literal) = match literal {
                // TODO: Literal could be i8 or u8, depending on what it's around.
                ast::Literal::Integer(literal) => (
                    ctx.tys.find_or_insert(TyInfo::U8),
                    Literal::U8(*literal as u8),
                ),
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
            let condition = lower_expr(ctx, bindings, condition);
            assert_eq!(
                condition.ty,
                ctx.tys.find_or_insert(
                    // TODO: Boolean
                    TyInfo::U8
                )
            );

            let block = lower_block(ctx, bindings, block);

            let otherwise = if let Some(otherwise) = otherwise {
                let otherwise = lower_block(ctx, bindings, otherwise);
                // Both branches should return the same type.
                assert_eq!(otherwise.ty, block.ty);
                Some(otherwise)
            } else {
                assert_eq!(block.ty, ctx.tys.find_or_insert(TyInfo::Unit));
                None
            };

            Expr {
                ty: block.ty,
                kind: ExprKind::If {
                    condition: Box::new(condition),
                    block,
                    otherwise,
                },
            }
        }
        ast::Expr::Field { expr, field } => todo!(),
        ast::Expr::Index { expr, index } => todo!(),
        ast::Expr::Block(block) => {
            let block = lower_block(ctx, bindings, block);
            Expr {
                ty: block.ty,
                kind: ExprKind::Block(block),
            }
        }
        ast::Expr::BinOp { lhs, op, rhs } => {
            let lhs = lower_expr(ctx, bindings, lhs);
            let rhs = lower_expr(ctx, bindings, rhs);

            let ty = match (ctx.tys.get(lhs.ty), op, ctx.tys.get(rhs.ty)) {
                (
                    lhs @ (TyInfo::U8 | TyInfo::I8),
                    BinOp::Plus
                    | BinOp::Minus
                    | BinOp::Multiply
                    | BinOp::Divide
                    | BinOp::BitAnd
                    | BinOp::BitOr,
                    rhs @ (TyInfo::U8 | TyInfo::I8),
                ) if lhs == rhs => ctx.tys.find_or_insert(lhs),
                // TODO: Boolean
                (lhs @ TyInfo::U8, BinOp::LogicAnd | BinOp::LogicOr, TyInfo::U8) => {
                    ctx.tys.find_or_insert(lhs)
                }
                (
                    lhs @ (TyInfo::U8 | TyInfo::I8),
                    BinOp::Eq | BinOp::Ne | BinOp::Gt | BinOp::Ge | BinOp::Lt | BinOp::Le,
                    rhs @ (TyInfo::U8 | TyInfo::I8),
                ) if lhs == rhs => ctx.tys.find_or_insert(
                    // TODO: Boolean
                    TyInfo::U8,
                ),
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
            let rhs = lower_expr(ctx, bindings, rhs);

            let ty = match (op, ctx.tys.get(rhs.ty)) {
                (UnOp::Deref, TyInfo::Ref(inner)) => inner,
                (UnOp::Minus, rhs @ TyInfo::I8) => ctx.tys.find_or_insert(rhs),
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
        ast::Expr::Call => todo!(),
        ast::Expr::Variable(ident) => todo!(),
    }
}
