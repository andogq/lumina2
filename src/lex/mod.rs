use std::{
    iter::Peekable,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    str::Chars,
};

use crate::{Ctx, Ident};

pub use self::tok::Tok;

pub mod lex2;
pub mod tok;

pub struct Lexer<'ctx, 'src, I>
where
    I: Iterator<Item = (Tok, Span)>,
{
    ctx: &'ctx Ctx,
    tokens: Peekable<I>,
    src: PhantomData<&'src ()>,
}

impl<'ctx, 'src, I> Deref for Lexer<'ctx, 'src, I>
where
    I: Iterator<Item = (Tok, Span)>,
{
    type Target = Peekable<I>;

    fn deref(&self) -> &Self::Target {
        &self.tokens
    }
}

impl<'ctx, 'src, I> DerefMut for Lexer<'ctx, 'src, I>
where
    I: Iterator<Item = (Tok, Span)>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.tokens
    }
}

impl<'ctx, 'src> Lexer<'ctx, 'src, TokenIter<'src>> {
    pub fn new(ctx: &'ctx Ctx, source: &'src str) -> Self {
        Self::from_iter(ctx, TokenIter::new(source))
    }
}

impl<'ctx, 'src, I> Lexer<'ctx, 'src, I>
where
    I: Iterator<Item = (Tok, Span)>,
{
    pub fn from_iter(ctx: &'ctx Ctx, iter: I) -> Self {
        Self {
            ctx,
            tokens: iter.peekable(),
            src: PhantomData,
        }
    }

    /// Advance the token stream, expecting the given token.
    pub fn expect(&mut self, tok: Tok) -> Tok {
        let next = self.tokens.next().unwrap().0;
        assert_eq!(next, tok);
        next
    }

    pub fn try_expect(&mut self, tok: Tok) -> bool {
        self.tokens.next_if(|(next, _)| next == &tok).is_some()
    }

    /// Advance the token stream, expecting an ident.
    pub fn ident(&mut self) -> Ident {
        let (tok, _) = self.next().unwrap();

        let Tok::Ident(ident) = tok else {
            panic!("expected ident, found {tok}");
        };

        self.ctx.idents.intern(ident)
    }

    pub fn int_lit(&mut self) -> usize {
        let (tok, _) = self.next().unwrap();

        let Tok::IntLit(lit) = tok else {
            panic!("expected int, found {tok}");
        };

        lit
    }
}

pub struct TokenIter<'src> {
    source: Peekable<Chars<'src>>,
    span: Span,
    state: State,
}

impl<'src> TokenIter<'src> {
    fn new(source: &'src str) -> Self {
        Self {
            source: source.chars().peekable(),
            span: Span::new(),
            state: State::Ready,
        }
    }

    /// Step to the next character.
    fn step_char(&mut self) -> Option<char> {
        let c = self.source.next()?;
        self.span.next_char();
        Some(c)
    }

    /// Advance and skip all whitespace.
    fn skip_whitespace(&mut self) {
        while self
            .source
            .peek()
            .map(|c| c.is_whitespace())
            .unwrap_or(false)
        {
            self.step_char();
        }
    }

    fn next_tok(&mut self) -> Option<(Tok, Span)> {
        Some((
            match (self.state.reset(), self.source.peek()) {
                // !=
                (State::Compound(CompoundChar::Bang), Some('=')) => {
                    self.step_char();
                    Tok::BangEq
                }
                // ==
                (State::Compound(CompoundChar::Eq), Some('=')) => {
                    self.step_char();
                    Tok::EqEq
                }
                // <=
                (State::Compound(CompoundChar::LAngle), Some('=')) => {
                    self.step_char();
                    Tok::LtEq
                }
                // >=
                (State::Compound(CompoundChar::RAngle), Some('=')) => {
                    self.step_char();
                    Tok::GtEq
                }

                // &&
                (State::Compound(CompoundChar::Amp), Some('&')) => {
                    self.step_char();
                    Tok::AmpAmp
                }
                // ||
                (State::Compound(CompoundChar::Bar), Some('|')) => {
                    self.step_char();
                    Tok::BarBar
                }
                // ->
                (State::Compound(CompoundChar::Minus), Some('>')) => {
                    self.step_char();
                    Tok::ThinArrow
                }

                // =
                (State::Compound(CompoundChar::Eq), _) => Tok::Eq,
                // <
                (State::Compound(CompoundChar::LAngle), _) => Tok::LAngle,
                // >
                (State::Compound(CompoundChar::RAngle), _) => Tok::RAngle,
                // &
                (State::Compound(CompoundChar::Amp), _) => Tok::Amp,
                // |
                (State::Compound(CompoundChar::Bar), _) => Tok::Bar,
                // -
                (State::Compound(CompoundChar::Minus), _) => Tok::Minus,

                (State::Ready, Some('=')) => {
                    self.state = State::Compound(CompoundChar::Eq);
                    self.step_char();
                    return self.next_tok();
                }
                (State::Ready, Some('<')) => {
                    self.state = State::Compound(CompoundChar::LAngle);
                    self.step_char();
                    return self.next_tok();
                }
                (State::Ready, Some('>')) => {
                    self.state = State::Compound(CompoundChar::RAngle);
                    self.step_char();
                    return self.next_tok();
                }
                (State::Ready, Some('|')) => {
                    self.state = State::Compound(CompoundChar::Bar);
                    self.step_char();
                    return self.next_tok();
                }
                (State::Ready, Some('&')) => {
                    self.state = State::Compound(CompoundChar::Amp);
                    self.step_char();
                    return self.next_tok();
                }
                (State::Ready, Some('!')) => {
                    self.state = State::Compound(CompoundChar::Bang);
                    self.step_char();
                    return self.next_tok();
                }
                (State::Ready, Some('-')) => {
                    self.state = State::Compound(CompoundChar::Minus);
                    self.step_char();
                    return self.next_tok();
                }

                // +
                (State::Ready, Some('+')) => {
                    self.step_char();
                    Tok::Plus
                }
                // *
                (State::Ready, Some('*')) => {
                    self.step_char();
                    Tok::Asterisk
                }
                // /
                (State::Ready, Some('/')) => {
                    self.step_char();
                    Tok::Slash
                }
                // :
                (State::Ready, Some(':')) => {
                    self.step_char();
                    Tok::Colon
                }
                // ;
                (State::Ready, Some(';')) => {
                    self.step_char();
                    Tok::SemiColon
                }
                // ,
                (State::Ready, Some(',')) => {
                    self.step_char();
                    Tok::Comma
                }

                // (
                (State::Ready, Some('(')) => {
                    self.step_char();
                    Tok::LParen
                }
                // )
                (State::Ready, Some(')')) => {
                    self.step_char();
                    Tok::RParen
                }
                // [
                (State::Ready, Some('[')) => {
                    self.step_char();
                    Tok::LBracket
                }
                // ]
                (State::Ready, Some(']')) => {
                    self.step_char();
                    Tok::RBracket
                }
                // {
                (State::Ready, Some('{')) => {
                    self.step_char();
                    Tok::LBrace
                }
                // }
                (State::Ready, Some('}')) => {
                    self.step_char();
                    Tok::RBrace
                }

                (State::Ready, Some(&c)) if c.is_ascii_alphabetic() || c == '_' => {
                    self.step_char();
                    self.state = State::Ident(c.to_string());
                    return self.next_tok();
                }
                (State::Ident(mut ident), Some(&c)) if c.is_ascii_alphanumeric() || c == '_' => {
                    self.step_char();
                    ident.push(c);
                    self.state = State::Ident(ident);
                    return self.next_tok();
                }
                (State::Ident(ident), _) => match ident.as_str() {
                    "true" => Tok::True,
                    "false" => Tok::False,

                    "fn" => Tok::Fn,
                    "let" => Tok::Let,
                    "return" => Tok::Return,
                    "if" => Tok::If,
                    "else" => Tok::Else,
                    _ => Tok::Ident(ident),
                },

                (State::Ready, Some(&c)) if c.is_ascii_digit() => {
                    self.step_char();
                    self.state = State::Literal(c.to_string());
                    return self.next_tok();
                }
                (State::Literal(mut lit), Some(&c)) if c.is_ascii_digit() => {
                    self.step_char();
                    lit.push(c);
                    self.state = State::Literal(lit);
                    return self.next_tok();
                }
                (State::Literal(lit), _) => Tok::IntLit(lit.parse().unwrap()),

                (State::Ready, None) => {
                    self.state = State::Done;
                    Tok::Eof
                }

                // Eof emitted, truly finished.
                (State::Done, None) => {
                    return None;
                }

                (state, Some(c)) => {
                    panic!("unknown character encountered: {c} in {state:?}");
                }
                (state, None) => {
                    panic!("unexpected eof: {state:?}");
                }
            },
            self.span.clone(),
        ))
    }
}

impl<'src> Iterator for TokenIter<'src> {
    type Item = (Tok, Span);

    fn next(&mut self) -> Option<Self::Item> {
        self.skip_whitespace();
        self.next_tok()
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Span {
    line: usize,
    col: usize,
}

impl Span {
    pub fn new() -> Self {
        Self::default()
    }

    fn next_line(&mut self) {
        self.line += 1;
        self.col = 0;
    }

    fn next_char(&mut self) {
        self.col += 1;
    }
}

#[derive(Clone, Debug)]
enum State {
    Ready,
    Compound(CompoundChar),
    Ident(String),
    Literal(String),
    Done,
}

#[derive(Clone, Debug)]
enum CompoundChar {
    Eq,
    LAngle,
    RAngle,
    Bar,
    Amp,
    Bang,
    Minus,
}

impl State {
    fn reset(&mut self) -> Self {
        let s = self.clone();
        *self = State::Ready;
        s
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use rstest::*;

    #[rstest]
    #[case("(", &[Tok::LParen, Tok::Eof])]
    #[case(")", &[Tok::RParen, Tok::Eof])]
    #[case("{", &[Tok::LBrace, Tok::Eof])]
    #[case("}", &[Tok::RBrace, Tok::Eof])]
    #[case("[", &[Tok::LBracket, Tok::Eof])]
    #[case("]", &[Tok::RBracket, Tok::Eof])]
    #[case("<", &[Tok::LAngle, Tok::Eof])]
    #[case(">", &[Tok::RAngle, Tok::Eof])]
    #[case("=", &[Tok::Eq, Tok::Eof])]
    #[case("+", &[Tok::Plus, Tok::Eof])]
    #[case("-", &[Tok::Minus, Tok::Eof])]
    #[case("*", &[Tok::Asterisk, Tok::Eof])]
    #[case("/", &[Tok::Slash, Tok::Eof])]
    #[case("&", &[Tok::Amp, Tok::Eof])]
    #[case("|", &[Tok::Bar, Tok::Eof])]
    #[case(":", &[Tok::Colon, Tok::Eof])]
    #[case(";", &[Tok::SemiColon, Tok::Eof])]
    #[case(",", &[Tok::Comma, Tok::Eof])]
    #[case("==", &[Tok::EqEq, Tok::Eof])]
    #[case("!=", &[Tok::BangEq, Tok::Eof])]
    #[case(">=", &[Tok::GtEq, Tok::Eof])]
    #[case("<=", &[Tok::LtEq, Tok::Eof])]
    #[case("&&", &[Tok::AmpAmp, Tok::Eof])]
    #[case("||", &[Tok::BarBar, Tok::Eof])]
    #[case("->", &[Tok::ThinArrow, Tok::Eof])]
    #[case("true", &[Tok::True, Tok::Eof])]
    #[case("false", &[Tok::False, Tok::Eof])]
    #[case("fn", &[Tok::Fn, Tok::Eof])]
    #[case("let", &[Tok::Let, Tok::Eof])]
    #[case("return", &[Tok::Return, Tok::Eof])]
    #[case("if", &[Tok::If, Tok::Eof])]
    #[case("some_ident", &[Tok::Ident("some_ident".to_string()), Tok::Eof])]
    #[case("123", &[Tok::IntLit(123), Tok::Eof])]
    fn single_token(#[case] source: &str, #[case] toks: &[Tok]) {
        assert_eq!(
            TokenIter::new(source)
                .map(|(tok, _)| tok)
                .collect::<Vec<_>>(),
            toks
        );
    }
}
