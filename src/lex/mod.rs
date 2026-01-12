use std::{
    iter::{Enumerate, Peekable},
    str::Chars,
};

pub use self::tok::Tok;

pub mod tok;

pub struct Lexer<'src> {
    chars: Peekable<Enumerate<Chars<'src>>>,
    current_tok: Option<Tok>,
    length: usize,
}

impl<'src> Lexer<'src> {
    /// Create a new lexer from the provided source.
    pub fn new(source: &'src str) -> Self {
        Self {
            chars: source.chars().enumerate().peekable(),
            current_tok: None,
            length: source.len(),
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
            .map(|(_, c)| c.is_whitespace())
            .unwrap_or(false)
        {
            self.chars.next().expect("char to advance");
        }
    }

    fn peek_char(&mut self) -> Option<char> {
        self.skip_whitespace();
        self.chars.peek().map(|(_, c)| *c)
    }

    fn next_char(&mut self) -> Option<char> {
        self.skip_whitespace();
        let (_, c) = self.chars.next()?;
        Some(c)
    }

    /// Advance to the next character, expecting a certain character to have been stepped.
    fn expect_char(&mut self, c: char) {
        let next_c = self.next_char().unwrap();
        assert_eq!(c, next_c);
    }

    // Determine the current character offset
    fn current_offset(&mut self) -> usize {
        self.chars
            .peek()
            .map(|(i, _)| *i)
            // If reached end of iterator, produce length of source.
            .unwrap_or(self.length)
    }

    /// Advance to the next token.
    fn advance(&mut self) -> Tok {
        let Some(char) = self.peek_char() else {
            return Tok::Eof;
        };

        let start_offset = self.current_offset();

        let tok = match char {
            '+' => {
                self.expect_char('+');
                Tok::Plus
            }
            '*' => {
                self.expect_char('*');
                Tok::Asterisk
            }
            '/' => {
                self.expect_char('/');
                Tok::Slash
            }
            ':' => {
                self.expect_char(':');
                Tok::Colon
            }
            ';' => {
                self.expect_char(';');
                Tok::SemiColon
            }
            ',' => {
                self.expect_char(',');
                Tok::Comma
            }
            '.' => {
                self.expect_char('.');
                Tok::Dot
            }
            '(' => {
                self.expect_char('(');
                Tok::LParenthesis
            }
            ')' => {
                self.expect_char(')');
                Tok::RParenthesis
            }
            '[' => {
                self.expect_char('[');
                Tok::LBracket
            }
            ']' => {
                self.expect_char(']');
                Tok::RBracket
            }
            '{' => {
                self.expect_char('{');
                Tok::LBrace
            }
            '}' => {
                self.expect_char('}');
                Tok::RBrace
            }

            '!' => {
                self.expect_char('!');

                match self.peek_char() {
                    Some('=') => {
                        self.expect_char('=');
                        Tok::BangEq
                    }
                    _ => Tok::Bang,
                }
            }
            '=' => {
                self.expect_char('=');

                match self.peek_char() {
                    Some('=') => {
                        self.expect_char('=');
                        Tok::EqEq
                    }
                    _ => Tok::Eq,
                }
            }
            '<' => {
                self.expect_char('<');

                match self.peek_char() {
                    Some('=') => {
                        self.expect_char('=');
                        Tok::LtEq
                    }
                    _ => Tok::LAngle,
                }
            }
            '>' => {
                self.expect_char('>');

                match self.peek_char() {
                    Some('=') => {
                        self.expect_char('=');
                        Tok::GtEq
                    }
                    _ => Tok::RAngle,
                }
            }
            '&' => {
                self.expect_char('&');

                match self.peek_char() {
                    Some('&') => {
                        self.expect_char('&');
                        Tok::AmpAmp
                    }
                    _ => Tok::Amp,
                }
            }
            '|' => {
                self.expect_char('|');

                match self.peek_char() {
                    Some('|') => {
                        self.expect_char('|');
                        Tok::BarBar
                    }
                    _ => Tok::Bar,
                }
            }
            '-' => {
                self.expect_char('-');

                match self.peek_char() {
                    Some('>') => {
                        self.expect_char('>');
                        Tok::ThinArrow
                    }
                    _ => Tok::Minus,
                }
            }

            char if char.is_numeric() => Tok::IntegerLiteral(
                std::iter::from_fn(|| {
                    self.chars
                        .next_if(|(_, c)| c.is_numeric())
                        .and_then(|(_, c)| Some(c.to_digit(10)? as usize))
                })
                .reduce(|value, c| (value * 10) + c)
                .expect("integer literal with at least one digit"),
            ),

            char if char.is_alphabetic() || char == '_' => {
                let ident = std::iter::from_fn(|| {
                    self.chars
                        .next_if(|(_, c)| c.is_alphanumeric() || *c == '_')
                        .map(|(_, c)| c)
                })
                .collect::<String>();

                assert!(!ident.is_empty());

                match ident.as_str() {
                    "true" => Tok::True,
                    "false" => Tok::False,
                    "fn" => Tok::Fn,
                    "let" => Tok::Let,
                    "return" => Tok::Return,
                    "else" => Tok::Else,
                    "if" => Tok::If,
                    "loop" => Tok::Loop,
                    "break" => Tok::Break,
                    "while" => Tok::While,
                    "trait" => Tok::Trait,
                    "impl" => Tok::Impl,
                    "for" => Tok::For,
                    _ => Tok::Ident(ident),
                }
            }

            char => {
                eprintln!("unknown character: {char}");

                self.expect_char(char);

                // TODO: Produce error token.
                Tok::Eof
            }
        };

        assert_ne!(
            start_offset,
            self.current_offset(),
            "expected to advance characters to produce token"
        );

        tok
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::prelude::*;

    #[rstest]
    #[case("(", &[Tok::LParenthesis, Tok::Eof])]
    #[case(")", &[Tok::RParenthesis, Tok::Eof])]
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
    #[case("break", &[Tok::Break, Tok::Eof])]
    #[case("return", &[Tok::Return, Tok::Eof])]
    #[case("if", &[Tok::If, Tok::Eof])]
    #[case("loop", &[Tok::Loop, Tok::Eof])]
    #[case("while", &[Tok::While, Tok::Eof])]
    #[case("trait", &[Tok::Trait, Tok::Eof])]
    #[case("impl", &[Tok::Impl, Tok::Eof])]
    #[case("for", &[Tok::For, Tok::Eof])]
    #[case("some_ident", &[Tok::Ident("some_ident".to_string()), Tok::Eof])]
    #[case("u32", &[Tok::Ident("u32".to_string()), Tok::Eof])]
    #[case("123", &[Tok::IntegerLiteral(123), Tok::Eof])]
    #[case::zero("0", &[Tok::IntegerLiteral(0), Tok::Eof])]
    #[case::whitespace_keyword("   true ", &[Tok::True, Tok::Eof])]
    #[case::whitespace_symbol("   -> ", &[Tok::ThinArrow, Tok::Eof])]
    #[case::whitespace_between_tokens("  =  true    ;", &[Tok::Eq, Tok::True, Tok::SemiColon, Tok::Eof])]
    #[case::whitespace_between_idents("if else", &[Tok::If, Tok::Else, Tok::Eof])]
    #[case::invalid("`abc", &[Tok::Eof])]
    fn tokens(#[case] source: &str, #[case] toks: &[Tok]) {
        assert_eq!(Lexer::new(source).collect(), toks);
    }

    #[rstest]
    #[case::empty("", [])]
    #[case::whitespace("      ", [])]
    #[case::non_whitespace("abc", ['a', 'b', 'c'])]
    #[case::mix(" a  b c   ", ['a', 'b', 'c'])]
    fn next_char(#[case] source: &str, #[case] chars: impl IntoIterator<Item = char>) {
        let mut lexer = Lexer::new(source);

        for c in chars {
            assert_eq!(lexer.next_char().unwrap(), c);
        }

        assert!(lexer.next_char().is_none());
    }

    #[rstest]
    #[case::only_char("a", 'a')]
    #[case::preceding_whitespace("     a", 'a')]
    #[case::trailing("abc", 'a')]
    #[should_panic]
    #[case::empty("", 'a')]
    #[should_panic]
    #[case::different("a", 'b')]
    fn expect_char(#[case] source: &str, #[case] c: char) {
        let mut lexer = Lexer::new(source);
        lexer.expect_char(c);
    }
}
