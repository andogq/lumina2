use crate::{
    Tok,
    ir2::cst::{self, PunctuatedList},
    lex::lex2::Lexer,
};

pub trait Parse {
    fn parse(lexer: &mut Lexer<'_>) -> Self;
}

impl Parse for cst::Program {
    fn parse(lexer: &mut Lexer<'_>) -> Self {
        let mut program = cst::Program::new();

        loop {
            match lexer.peek() {
                Tok::Eof => break,
                Tok::Fn => {
                    let function_declaration = cst::FunctionDeclaration::parse(lexer);
                    program.add_function_declaration(function_declaration);
                }
                tok => {
                    eprintln!("Unknown tok: {tok}");
                }
            }
        }

        program
    }
}

mod function {
    use super::*;
    impl Parse for cst::FunctionDeclaration {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            cst::FunctionDeclaration {
                tok_fn: lexer.expect().unwrap(),
                name: lexer.expect().unwrap(),
                tok_lparen: lexer.expect().unwrap(),
                params: PunctuatedList::parse_while(lexer, |tok| !matches!(tok, Tok::RParen)),
                tok_rparan: lexer.expect().unwrap(),
                return_ty: lexer
                    .next_if()
                    .map(|tok_thin_arrow| cst::FunctionReturnType {
                        tok_thin_arrow,
                        ty: lexer.expect().unwrap(),
                    }),
                body: cst::Block::parse(lexer),
            }
        }
    }

    impl Parse for cst::FunctionParameter {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                name: lexer.expect().unwrap(),
                tok_colon: lexer.expect().unwrap(),
                ty: lexer.expect().unwrap(),
            }
        }
    }
}

impl Parse for cst::Block {
    fn parse(lexer: &mut Lexer<'_>) -> Self {
        let tok_l_brace = lexer.expect().unwrap();

        let mut statements = Vec::new();

        let tok_r_brace = loop {
            if let Some(tok) = lexer.next_if() {
                break tok;
            }

            statements.push(cst::Statement::parse(lexer));
        };

        Self {
            tok_l_brace,
            statements,
            tok_r_brace,
        }
    }
}

mod statement {
    use super::*;

    impl Parse for cst::Statement {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            match lexer.peek() {
                Tok::Let => cst::LetStatement::parse(lexer).into(),
                Tok::Return => cst::ReturnStatement::parse(lexer).into(),
                _ => cst::ExprStatement::parse(lexer).into(),
            }
        }
    }

    impl Parse for cst::LetStatement {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                tok_let: lexer.expect().unwrap(),
                variable: lexer.expect().unwrap(),
                tok_eq: lexer.expect().unwrap(),
                value: cst::Expr::parse(lexer),
                tok_semicolon: lexer.expect().unwrap(),
            }
        }
    }

    impl Parse for cst::ReturnStatement {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                tok_return: lexer.expect().unwrap(),
                value: cst::Expr::parse(lexer),
                tok_semicolon: lexer.expect().unwrap(),
            }
        }
    }

    impl Parse for cst::ExprStatement {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                expr: cst::Expr::parse(lexer),
                tok_semicolon: lexer.next_if(),
            }
        }
    }
}

mod expr {
    use super::*;

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
        // TODO: Don't have multiple precedence functions
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

    impl Parse for cst::Expr {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self::parse_with_precedence(lexer, Precedence::Lowest)
        }
    }

    impl cst::Expr {
        fn parse_with_precedence(lexer: &mut Lexer<'_>, precedence: Precedence) -> Self {
            let mut expr = Self::parse_prefix(lexer);

            loop {
                let tok = lexer.peek();

                if precedence >= Precedence::of(tok) {
                    break;
                }

                match tok {
                    Tok::Plus
                    | Tok::Minus
                    | Tok::Asterisk
                    | Tok::Slash
                    | Tok::AmpAmp
                    | Tok::BarBar
                    | Tok::Amp
                    | Tok::Bar
                    | Tok::EqEq
                    | Tok::BangEq
                    | Tok::LAngle
                    | Tok::RAngle
                    | Tok::LtEq
                    | Tok::GtEq => expr = cst::Binary::parse(lexer, expr).into(),
                    Tok::Eq => expr = cst::Assign::parse(lexer, expr).into(),
                    Tok::LParen => expr = cst::Call::parse(lexer, expr).into(),
                    _ => panic!("unknown tok: {tok}"),
                }
            }

            expr
        }

        fn parse_prefix(lexer: &mut Lexer<'_>) -> Self {
            match lexer.peek() {
                Tok::Ident(_) => cst::Variable::parse(lexer).into(),
                Tok::IntLit(_) | Tok::True | Tok::False => cst::Literal::parse(lexer).into(),
                Tok::Minus | Tok::Amp | Tok::Asterisk => cst::Unary::parse(lexer).into(),
                Tok::LBrace => cst::Block::parse(lexer).into(),
                Tok::LParen => cst::Paren::parse(lexer).into(),
                Tok::If => cst::If::parse(lexer).into(),
                tok => panic!("unexpected tok: {tok}"),
            }
        }
    }

    impl cst::Assign {
        fn parse(lexer: &mut Lexer<'_>, assignee: cst::Expr) -> Self {
            Self {
                assignee: Box::new(assignee),
                tok_eq: lexer.expect().unwrap(),
                value: Box::new(cst::Expr::parse_with_precedence(lexer, Precedence::Assign)),
            }
        }
    }

    impl cst::Binary {
        fn parse(lexer: &mut Lexer<'_>, lhs: cst::Expr) -> Self {
            let op = cst::BinaryOp::parse(lexer);
            let rhs = cst::Expr::parse_with_precedence(lexer, op.precedence());

            Self {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            }
        }
    }

    impl Parse for cst::BinaryOp {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            match lexer.peek() {
                Tok::Plus => Self::Plus(lexer.expect().unwrap()),
                Tok::Minus => Self::Minus(lexer.expect().unwrap()),
                Tok::Asterisk => Self::Multiply(lexer.expect().unwrap()),
                Tok::Slash => Self::Divide(lexer.expect().unwrap()),

                Tok::AmpAmp => Self::LogicalAnd(lexer.expect().unwrap()),
                Tok::BarBar => Self::LogicalOr(lexer.expect().unwrap()),

                Tok::Amp => Self::BinaryAnd(lexer.expect().unwrap()),
                Tok::Bar => Self::BinaryOr(lexer.expect().unwrap()),

                Tok::Eq => Self::Equal(lexer.expect().unwrap()),
                Tok::BangEq => Self::NotEqual(lexer.expect().unwrap()),
                Tok::LAngle => Self::Less(lexer.expect().unwrap()),
                Tok::LtEq => Self::LessEqual(lexer.expect().unwrap()),
                Tok::RAngle => Self::Greater(lexer.expect().unwrap()),
                Tok::GtEq => Self::GreaterEqual(lexer.expect().unwrap()),

                tok => panic!("unknown binary operation: {tok}"),
            }
        }
    }

    impl cst::BinaryOp {
        fn precedence(&self) -> Precedence {
            match self {
                Self::Plus(_) | Self::Minus(_) => Precedence::Sum,
                Self::Multiply(_) | Self::Divide(_) => Precedence::Multiply,
                Self::Equal(_)
                | Self::NotEqual(_)
                | Self::GreaterEqual(_)
                | Self::Greater(_)
                | Self::LessEqual(_)
                | Self::Less(_) => Precedence::Equality,
                Self::LogicalAnd(_) | Self::LogicalOr(_) => Precedence::Binary,
                _ => Precedence::Lowest,
            }
        }
    }

    impl Parse for cst::Unary {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                op: cst::UnaryOp::parse(lexer),
                value: Box::new(cst::Expr::parse_with_precedence(lexer, Precedence::Prefix)),
            }
        }
    }

    impl Parse for cst::UnaryOp {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            match lexer.peek() {
                Tok::Bang => Self::Not(lexer.expect().unwrap()),
                Tok::Minus => Self::Negative(lexer.expect().unwrap()),
                Tok::Asterisk => Self::Deref(lexer.expect().unwrap()),
                Tok::Amp => Self::Ref(lexer.expect().unwrap()),
                tok => panic!("unknown unary operation: {tok}"),
            }
        }
    }

    impl Parse for cst::If {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                tok_if: lexer.expect().unwrap(),
                condition: Box::new(cst::Expr::parse(lexer)),
                then: cst::Block::parse(lexer),
                trailer: lexer.next_if().map(|tok_else| cst::IfTrailer {
                    tok_else,
                    if_or_block: cst::IfOrBlock::parse(lexer),
                }),
            }
        }
    }

    impl Parse for cst::IfOrBlock {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            match lexer.peek() {
                Tok::If => cst::If::parse(lexer).into(),
                Tok::LBrace => cst::Block::parse(lexer).into(),
                tok => panic!("expected if or block, found: {tok}"),
            }
        }
    }

    impl Parse for cst::Literal {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            match lexer.peek() {
                Tok::True => cst::BooleanLiteral::True(lexer.expect().unwrap()).into(),
                Tok::False => cst::BooleanLiteral::False(lexer.expect().unwrap()).into(),
                Tok::IntLit(_) => cst::IntegerLiteral(lexer.expect().unwrap()).into(),
                tok => panic!("expected literal, found: {tok}"),
            }
        }
    }

    impl Parse for cst::Paren {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                tok_l_paren: lexer.expect().unwrap(),
                expr: Box::new(cst::Expr::parse(lexer)),
                tok_r_paren: lexer.expect().unwrap(),
            }
        }
    }

    impl cst::Call {
        fn parse(lexer: &mut Lexer<'_>, callee: cst::Expr) -> Self {
            Self {
                callee: Box::new(callee),
                tok_l_paren: lexer.expect().unwrap(),
                arguments: cst::PunctuatedList::parse_while(lexer, |tok| {
                    !matches!(tok, Tok::RParen)
                }),
                tok_r_paren: lexer.expect().unwrap(),
            }
        }
    }

    impl Parse for cst::Variable {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                variable: lexer.expect().unwrap(),
            }
        }
    }
}

mod util {
    use super::*;

    impl<T: Parse, P: TryFrom<Tok, Error = Tok>> cst::PunctuatedList<T, P> {
        /// Parse from the lexer while `check` returns `true`. The check will be run immediately before
        /// each item is parsed.
        pub fn parse_while(lexer: &mut Lexer<'_>, check: impl Fn(&Tok) -> bool) -> Self {
            let mut list = Self::new();

            while check(lexer.peek()) {
                // Parse the item.
                list.add_item(T::parse(lexer)).unwrap();

                // Check if punctuation is next.
                if let Some(punctuation) = lexer.next_if() {
                    // Save punctuation, and continue parsing.
                    list.add_punctuation(punctuation).unwrap();
                } else {
                    // No more punctuation, list complete.
                    break;
                }
            }

            list
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use insta::*;
    use rstest::*;

    #[rstest]
    #[case("int_lit", "123")]
    #[case("ident", "some_ident")]
    #[case("add", "123 + 321")]
    #[case("add_mul", "123 + 321 * 999")]
    #[case("un_op", "-123")]
    #[case("un_op_add_mull", "123 + -321 * 999")]
    #[case("assignment", "some_ident = 123 + other_ident")]
    fn expr(#[case] name: &str, #[case] source: &str) {
        let mut lexer = Lexer::new(source);
        let expr = cst::Expr::parse(&mut lexer);

        assert_eq!(lexer.next(), Tok::Eof);

        assert_debug_snapshot!(name, expr, source);
    }
}
