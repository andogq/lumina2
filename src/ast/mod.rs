use std::fmt::Display;

use crate::{
    Ident, Tok,
    lex::{Lexer, Span},
};

#[derive(Clone, Debug)]
pub struct Program {
    pub functions: Vec<Function>,
}

impl Program {
    fn new() -> Self {
        Self {
            functions: Vec::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Function {
    pub name: Ident,
    pub params: Vec<(Ident, Ident)>,
    pub ret: Option<Ident>,
    pub body: Block,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub statements: Vec<Statement>,
}

impl Block {
    fn new() -> Self {
        Self {
            statements: Vec::new(),
        }
    }
}

impl Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        for statement in &self.statements {
            writeln!(f, "{statement}")?;
        }

        write!(f, "}}")?;

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub enum Statement {
    Declaration {
        binding: Ident,
        ty_annotation: Option<Ident>,
        value: Expr,
    },
    Expr {
        expr: Expr,
        semicolon: bool,
    },
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Declaration {
                binding,
                ty_annotation,
                value,
            } => {
                write!(f, "let {binding}")?;

                if let Some(ty_annotation) = ty_annotation {
                    write!(f, ": {ty_annotation}")?;
                }

                write!(f, " = {value};")?;

                Ok(())
            }
            Statement::Expr { expr, semicolon } => {
                write!(f, "{expr}")?;

                if *semicolon {
                    writeln!(f, ";")?;
                }

                Ok(())
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum Expr {
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
    Match {
        discriminator: Box<Expr>,
        // TODO: Proper pattern matching.
        arms: Vec<(Literal, Box<Expr>)>,
        otherwise: Box<Expr>,
    },
    Call,
    Variable(Ident),
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Assignment { binding, value } => write!(f, "{binding} = {value}"),
            Expr::Literal(literal) => write!(f, "{literal}"),
            Expr::If {
                condition,
                block,
                otherwise,
            } => {
                write!(f, "if {condition} {block}")?;

                if let Some(otherwise) = otherwise {
                    write!(f, "else {otherwise}")?;
                }

                Ok(())
            }
            Expr::Field { expr, field } => write!(f, "{expr}.{field}"),
            Expr::Index { expr, index } => write!(f, "{expr}[{index}]"),
            Expr::Block(block) => write!(f, "{block}"),
            Expr::BinOp { lhs, op, rhs } => write!(f, "({lhs} {op} {rhs})"),
            Expr::UnOp { op, rhs } => write!(f, "({op}{rhs})"),
            Expr::Match {
                discriminator,
                arms,
                otherwise,
            } => {
                writeln!(f, "match {discriminator} {{")?;
                for (value, body) in arms {
                    writeln!(f, "  {value} => {body},")?;
                }
                writeln!(f, "  _ => {otherwise},")?;
                write!(f, "}}")?;

                Ok(())
            }
            Expr::Call => todo!(),
            Expr::Variable(ident) => write!(f, "{ident}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Literal {
    Integer(usize),
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Integer(value) => write!(f, "{value}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum BinOp {
    Plus,
    Minus,
    Multiply,
    Divide,
    LogicAnd,
    LogicOr,
    BitAnd,
    BitOr,
    Eq,
    Ne,
    Gt,
    Ge,
    Lt,
    Le,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinOp::Plus => write!(f, "+"),
            BinOp::Minus => write!(f, "-"),
            BinOp::Multiply => write!(f, "*"),
            BinOp::Divide => write!(f, "/"),
            BinOp::LogicAnd => write!(f, "&&"),
            BinOp::LogicOr => write!(f, "||"),
            BinOp::BitAnd => write!(f, "&"),
            BinOp::BitOr => write!(f, "|"),
            BinOp::Eq => write!(f, "=="),
            BinOp::Ne => write!(f, "!="),
            BinOp::Gt => write!(f, ">"),
            BinOp::Ge => write!(f, ">="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Le => write!(f, "<="),
        }
    }
}

#[derive(Clone, Debug)]
pub enum UnOp {
    Deref,
    Minus,
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnOp::Deref => write!(f, "*"),
            UnOp::Minus => write!(f, "-"),
        }
    }
}

pub fn parse(mut toks: Lexer<'_, '_, impl Iterator<Item = (Tok, Span)>>) -> Program {
    let mut program = Program::new();

    while toks.peek().is_some() {
        if toks.try_expect(Tok::Eof) {
            break;
        }

        toks.expect(Tok::Fn);

        let name = toks.ident();

        toks.expect(Tok::LParen);

        // Parse arguments.
        let mut params = Vec::new();
        let mut trailing_comma = true;
        while !matches!(toks.peek().unwrap().0, Tok::RParen) {
            if !trailing_comma {
                panic!("argument followed without trailing comma");
            }

            let name = toks.ident();
            toks.expect(Tok::Colon);
            let ty = toks.ident();
            params.push((name, ty));

            trailing_comma = toks.try_expect(Tok::Comma);
        }
        toks.expect(Tok::RParen);

        // Optional return type.
        let ret = toks.try_expect(Tok::ThinArrow).then(|| toks.ident());

        let body = parse_block(&mut toks);
        program.functions.push(Function {
            name,
            params,
            ret,
            body,
        });
    }

    program
}

fn parse_block(toks: &mut Lexer<'_, '_, impl Iterator<Item = (Tok, Span)>>) -> Block {
    let mut block = Block::new();

    toks.expect(Tok::LBrace);

    while !matches!(toks.peek().unwrap().0, Tok::RBrace) {
        if toks.try_expect(Tok::Let) {
            let binding = toks.ident();

            let ty_annotation = toks.try_expect(Tok::Colon).then(|| toks.ident());

            toks.expect(Tok::Eq);

            let value = parse_expr(toks);

            toks.expect(Tok::SemiColon);

            block.statements.push(Statement::Declaration {
                binding,
                ty_annotation,
                value,
            });
        } else {
            let expr = parse_expr(toks);
            let semicolon = toks.try_expect(Tok::SemiColon);

            block.statements.push(Statement::Expr { expr, semicolon });
        }
    }

    toks.expect(Tok::RBrace);

    block
}

fn parse_expr(toks: &mut Lexer<'_, '_, impl Iterator<Item = (Tok, Span)>>) -> Expr {
    /// Parse a prefix expression
    fn parse_prefix(toks: &mut Lexer<'_, '_, impl Iterator<Item = (Tok, Span)>>) -> Expr {
        match &toks.peek().unwrap().0 {
            Tok::Ident(ident) => Expr::Variable(toks.ident()),
            Tok::IntLit(lit) => Expr::Literal(Literal::Integer(toks.int_lit())),

            Tok::Minus => {
                toks.expect(Tok::Minus);

                Expr::UnOp {
                    op: UnOp::Minus,
                    rhs: Box::new(parse_with_precedence(toks, Precedence::Prefix)),
                }
            }

            Tok::LBrace => Expr::Block(parse_block(toks)),

            Tok::If => {
                toks.expect(Tok::If);

                Expr::If {
                    condition: Box::new(parse_expr(toks)),
                    block: parse_block(toks),
                    otherwise: toks.try_expect(Tok::Else).then(|| parse_block(toks)),
                }
            }

            Tok::Eof => panic!("unexpected eof"),
            tok => panic!("unexpected token: {tok}"),
        }
    }

    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    enum Precedence {
        Lowest,
        Assign,
        Binary,
        Equality,
        Sum,
        Multiply,
        Prefix,
        Cast,
        Call,
    }

    impl Precedence {
        fn of(tok: &Tok) -> Self {
            match tok {
                Tok::LParen | Tok::LBracket => Self::Call,
                Tok::Asterisk | Tok::Slash => Self::Multiply,
                Tok::Plus | Tok::Minus => Self::Sum,
                Tok::EqEq | Tok::BangEq | Tok::GtEq | Tok::LtEq | Tok::LAngle | Tok::RAngle => {
                    Self::Equality
                }
                Tok::Amp | Tok::Bar => Self::Binary,
                Tok::Eq => Self::Assign,
                _ => Self::Lowest,
            }
        }
    }

    fn parse_with_precedence(
        toks: &mut Lexer<'_, '_, impl Iterator<Item = (Tok, Span)>>,
        precedence: Precedence,
    ) -> Expr {
        let mut expr = parse_prefix(toks);

        while let Some((tok, _)) = toks
            .peek()
            .filter(|(tok, _)| precedence < Precedence::of(tok))
        {
            match tok {
                Tok::Plus => {
                    expr = Expr::BinOp {
                        lhs: Box::new(expr),
                        op: BinOp::Plus,
                        rhs: {
                            let precedence = Precedence::of(&toks.expect(Tok::Plus));
                            Box::new(parse_with_precedence(toks, precedence))
                        },
                    }
                }
                Tok::Minus => {
                    expr = Expr::BinOp {
                        lhs: Box::new(expr),
                        op: BinOp::Minus,
                        rhs: {
                            let precedence = Precedence::of(&toks.expect(Tok::Minus));
                            Box::new(parse_with_precedence(toks, precedence))
                        },
                    }
                }
                Tok::Asterisk => {
                    expr = Expr::BinOp {
                        lhs: Box::new(expr),
                        op: BinOp::Multiply,
                        rhs: {
                            let precedence = Precedence::of(&toks.expect(Tok::Asterisk));
                            Box::new(parse_with_precedence(toks, precedence))
                        },
                    }
                }
                Tok::Slash => {
                    expr = Expr::BinOp {
                        lhs: Box::new(expr),
                        op: BinOp::Divide,
                        rhs: {
                            let precedence = Precedence::of(&toks.expect(Tok::Slash));
                            Box::new(parse_with_precedence(toks, precedence))
                        },
                    }
                }
                Tok::AmpAmp => {
                    expr = Expr::BinOp {
                        lhs: Box::new(expr),
                        op: BinOp::LogicAnd,
                        rhs: {
                            let precedence = Precedence::of(&toks.expect(Tok::AmpAmp));
                            Box::new(parse_with_precedence(toks, precedence))
                        },
                    }
                }
                Tok::BarBar => {
                    expr = Expr::BinOp {
                        lhs: Box::new(expr),
                        op: BinOp::LogicOr,
                        rhs: {
                            let precedence = Precedence::of(&toks.expect(Tok::BarBar));
                            Box::new(parse_with_precedence(toks, precedence))
                        },
                    }
                }
                Tok::Amp => {
                    expr = Expr::BinOp {
                        lhs: Box::new(expr),
                        op: BinOp::BitAnd,
                        rhs: {
                            let precedence = Precedence::of(&toks.expect(Tok::Amp));
                            Box::new(parse_with_precedence(toks, precedence))
                        },
                    }
                }
                Tok::Bar => {
                    expr = Expr::BinOp {
                        lhs: Box::new(expr),
                        op: BinOp::BitOr,
                        rhs: {
                            let precedence = Precedence::of(&toks.expect(Tok::Bar));
                            Box::new(parse_with_precedence(toks, precedence))
                        },
                    }
                }

                Tok::Eq => {
                    expr = Expr::Assignment {
                        binding: Box::new(expr),
                        value: {
                            let precedence = Precedence::of(&toks.expect(Tok::Eq));
                            Box::new(parse_with_precedence(toks, precedence))
                        },
                    }
                }

                Tok::LBracket => {
                    expr = Expr::Index {
                        expr: Box::new(expr),
                        index: {
                            let precedence = Precedence::of(&toks.expect(Tok::LBracket));
                            Box::new(parse_with_precedence(toks, precedence))
                        },
                    }
                }

                Tok::LParen => {
                    todo!("call parsing")
                }
                _ => todo!(),
            }
        }

        expr
    }

    parse_with_precedence(toks, Precedence::Lowest)
}

#[cfg(test)]
mod test {
    use crate::Ctx;

    use super::*;

    use insta::*;
    use rstest::*;

    #[rstest]
    #[case("int_lit", [Tok::IntLit(123), Tok::Eof])]
    #[case("ident", [Tok::Ident("some_ident".to_string()), Tok::Eof])]
    #[case("add", [Tok::IntLit(123), Tok::Plus, Tok::IntLit(321), Tok::Eof])]
    #[case("add_mul", [Tok::IntLit(123), Tok::Plus, Tok::IntLit(321), Tok::Asterisk, Tok::IntLit(999), Tok::Eof])]
    #[case("un_op", [Tok::Minus, Tok::IntLit(123), Tok::Eof])]
    #[case("un_op_add_mul", [Tok::IntLit(123), Tok::Plus, Tok::Minus, Tok::IntLit(321), Tok::Asterisk, Tok::IntLit(999), Tok::Eof])]
    #[case("assignment", [Tok::Ident("some_ident".to_string()), Tok::Eq, Tok::IntLit(123), Tok::Plus, Tok::Ident("other_ident".to_string()), Tok::Eof])]
    fn expr(#[case] name: &str, #[case] toks: impl IntoIterator<Item = Tok>) {
        let mut settings = insta::Settings::clone_current();
        settings.set_snapshot_suffix(name.to_string());
        let _guard = settings.bind_to_scope();

        let ctx = Ctx::default();

        assert_snapshot!(parse_expr(&mut Lexer::from_iter(
            &ctx,
            toks.into_iter().map(|tok| (tok, Span::default()))
        )));
    }
}
