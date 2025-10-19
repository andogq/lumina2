use std::{iter::Peekable, str::Chars};

use crate::Tok;

pub struct Lexer<'src> {
    chars: Peekable<Chars<'src>>,
    current_tok: Option<Tok>,
}

impl<'src> Lexer<'src> {
    /// Create a new lexer from the provided source.
    pub fn new(source: &'src str) -> Self {
        Self {
            chars: source.chars().peekable(),
            current_tok: None,
        }
    }

    /// Peek at the next token.
    pub fn peek(&mut self) -> &Tok {
        if let Some(ref tok) = self.current_tok {
            return tok;
        }

        let next_tok = self.advance();
        self.current_tok.insert(next_tok)
    }

    /// Produce the next token.
    pub fn next(&mut self) -> Tok {
        if let Some(tok) = self.current_tok.take() {
            return tok;
        }

        self.advance()
    }

    /// Produce the next token if it matches the provided generic. If it does not match, the lexer
    /// will not be advanced.
    pub fn next_if<T: TryFrom<Tok, Error = Tok>>(&mut self) -> Option<T> {
        match self.expect::<T>() {
            Ok(tok) => Some(tok),
            Err(tok) => {
                assert!(self.current_tok.is_none());
                self.current_tok = Some(tok);
                None
            }
        }
    }

    /// Produce the next token if it matches the provided generic. If it does not match, the lexer
    /// will still be advanced.
    pub fn expect<T: TryFrom<Tok, Error = Tok>>(&mut self) -> Result<T, Tok> {
        T::try_from(self.next())
    }

    /// Collect all tokens into a [`Vec`]. It is guaranteed to end with a single [`Eof`] token.
    ///
    /// [`Eof`]: crate::lex::tok::Eof
    #[cfg(test)]
    fn collect(mut self) -> Vec<Tok> {
        std::iter::from_fn(|| Some(self.next()))
            .take_while(|tok| !matches!(tok, Tok::Eof))
            .chain([Tok::Eof])
            .collect()
    }

    fn skip_whitespace(&mut self) {
        while self
            .chars
            .peek()
            .map(|c| c.is_whitespace())
            .unwrap_or(false)
        {
            self.chars.next();
        }
    }

    fn peek_char(&mut self) -> Option<char> {
        self.skip_whitespace();
        self.chars.peek().cloned()
    }

    fn next_char(&mut self) -> Option<char> {
        self.skip_whitespace();
        self.chars.next()
    }

    /// Advance to the next token.
    fn advance(&mut self) -> Tok {
        let Some(char) = self.peek_char() else {
            return Tok::Eof;
        };

        match char {
            '+' => {
                self.next_char();
                Tok::Plus
            }
            '*' => {
                self.next_char();
                Tok::Asterisk
            }
            '/' => {
                self.next_char();
                Tok::Slash
            }
            ':' => {
                self.next_char();
                Tok::Colon
            }
            ';' => {
                self.next_char();
                Tok::SemiColon
            }
            ',' => {
                self.next_char();
                Tok::Comma
            }
            '(' => {
                self.next_char();
                Tok::LParen
            }
            ')' => {
                self.next_char();
                Tok::RParen
            }
            '[' => {
                self.next_char();
                Tok::LBracket
            }
            ']' => {
                self.next_char();
                Tok::RBracket
            }
            '{' => {
                self.next_char();
                Tok::LBrace
            }
            '}' => {
                self.next_char();
                Tok::RBrace
            }

            '!' => {
                self.next_char();

                match self.peek_char() {
                    Some('=') => {
                        self.next_char();
                        Tok::BangEq
                    }
                    _ => Tok::Bang,
                }
            }
            '=' => {
                self.next_char();

                match self.peek_char() {
                    Some('=') => {
                        self.next_char();
                        Tok::EqEq
                    }
                    _ => Tok::Eq,
                }
            }
            '<' => {
                self.next_char();

                match self.peek_char() {
                    Some('=') => {
                        self.next_char();
                        Tok::LtEq
                    }
                    _ => Tok::LAngle,
                }
            }
            '>' => {
                self.next_char();

                match self.peek_char() {
                    Some('=') => {
                        self.next_char();
                        Tok::GtEq
                    }
                    _ => Tok::RAngle,
                }
            }
            '&' => {
                self.next_char();

                match self.peek_char() {
                    Some('&') => {
                        self.next_char();
                        Tok::AmpAmp
                    }
                    _ => Tok::Amp,
                }
            }
            '|' => {
                self.next_char();

                match self.peek_char() {
                    Some('|') => {
                        self.next_char();
                        Tok::BarBar
                    }
                    _ => Tok::Bar,
                }
            }
            '-' => {
                self.next_char();

                match self.peek_char() {
                    Some('>') => {
                        self.next_char();
                        Tok::ThinArrow
                    }
                    _ => Tok::Minus,
                }
            }

            char if char.is_numeric() => Tok::IntLit(
                std::iter::from_fn(|| {
                    let c = self
                        .chars
                        .peek()
                        .and_then(|c| Some(c.to_digit(10)? as usize))?;
                    self.next_char();
                    Some(c)
                })
                .reduce(|value, c| (value * 10) + c)
                .expect("int literal with at least one digit"),
            ),

            char if char.is_alphabetic() || char == '_' => {
                let ident =
                    std::iter::from_fn(|| self.chars.next_if(|c| c.is_alphanumeric() || *c == '_'))
                        .collect::<String>();

                match ident.as_str() {
                    "true" => Tok::True,
                    "false" => Tok::False,
                    "fn" => Tok::Fn,
                    "let" => Tok::Let,
                    "return" => Tok::Return,
                    "else" => Tok::Else,
                    "if" => Tok::If,
                    _ => Tok::Ident(ident),
                }
            }

            char => {
                eprintln!("unknown character: {char}");

                self.next_char();

                // TODO: Produce error token.
                Tok::Eof
            }
        }
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
    #[case("u32", &[Tok::Ident("u32".to_string()), Tok::Eof])]
    #[case("123", &[Tok::IntLit(123), Tok::Eof])]
    fn single_token(#[case] source: &str, #[case] toks: &[Tok]) {
        assert_eq!(Lexer::new(source).collect(), toks);
    }
}
