use std::fmt::{Display, Formatter};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    LAngle,
    RAngle,

    Eq,
    Plus,
    Minus,
    Asterisk,
    Slash,
    Amp,
    Bar,
    Colon,
    SemiColon,
    Comma,

    EqEq,
    BangEq,
    GtEq,
    LtEq,
    AmpAmp,
    BarBar,

    ThinArrow,

    Fn,
    Let,
    Return,
    If,
    Else,

    Eof,

    Ident(String),
    IntLit(usize),
}

impl Display for Tok {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Tok::LParen => write!(f, "("),
            Tok::RParen => write!(f, ")"),
            Tok::LBrace => write!(f, "{{"),
            Tok::RBrace => write!(f, "}}"),
            Tok::LBracket => write!(f, "["),
            Tok::RBracket => write!(f, "]"),
            Tok::LAngle => write!(f, "<"),
            Tok::RAngle => write!(f, ">"),

            Tok::Eq => write!(f, "="),
            Tok::Plus => write!(f, "+"),
            Tok::Minus => write!(f, "-"),
            Tok::Asterisk => write!(f, "*"),
            Tok::Slash => write!(f, "/"),
            Tok::Amp => write!(f, "&"),
            Tok::Bar => write!(f, "|"),
            Tok::Colon => write!(f, ":"),
            Tok::SemiColon => write!(f, ";"),
            Tok::Comma => write!(f, ","),

            Tok::EqEq => write!(f, "=="),
            Tok::BangEq => write!(f, "!="),
            Tok::GtEq => write!(f, ">="),
            Tok::LtEq => write!(f, "<="),
            Tok::AmpAmp => write!(f, "&&"),
            Tok::BarBar => write!(f, "||"),

            Tok::ThinArrow => write!(f, "->"),

            Tok::Fn => write!(f, "fn"),
            Tok::Let => write!(f, "let"),
            Tok::Return => write!(f, "return"),
            Tok::If => write!(f, "if"),
            Tok::Else => write!(f, "else"),

            Tok::Ident(ident) => write!(f, "{ident}"),
            Tok::IntLit(lit) => write!(f, "{lit}"),

            Tok::Eof => write!(f, "<Eof>"),
        }
    }
}
