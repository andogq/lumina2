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
        Logical,
        Equality,
        Binary,
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
                Tok::Amp | Tok::Bar => Self::Binary,
                Tok::EqEq | Tok::BangEq | Tok::GtEq | Tok::LtEq | Tok::LAngle | Tok::RAngle => {
                    Self::Equality
                }
                Tok::AmpAmp | Tok::BarBar => Self::Logical,
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

                if precedence > Precedence::of(tok) {
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
                    _ => break,
                }
            }

            expr
        }

        fn parse_prefix(lexer: &mut Lexer<'_>) -> Self {
            match lexer.peek() {
                Tok::Ident(_) => cst::Variable::parse(lexer).into(),
                Tok::IntLit(_) | Tok::True | Tok::False => cst::Literal::parse(lexer).into(),
                Tok::Minus | Tok::Amp | Tok::Asterisk | Tok::Bang => {
                    cst::Unary::parse(lexer).into()
                }
                Tok::LBrace => cst::Block::parse(lexer).into(),
                Tok::LParen => cst::Paren::parse(lexer).into(),
                Tok::If => cst::If::parse(lexer).into(),
                tok => panic!("unexpected tok: {tok}"),
            }
        }
    }

    impl cst::Assign {
        pub(super) fn parse(lexer: &mut Lexer<'_>, assignee: cst::Expr) -> Self {
            Self {
                assignee: Box::new(assignee),
                tok_eq: lexer.expect().unwrap(),
                value: Box::new(cst::Expr::parse_with_precedence(lexer, Precedence::Assign)),
            }
        }
    }

    impl cst::Binary {
        pub(super) fn parse(lexer: &mut Lexer<'_>, lhs: cst::Expr) -> Self {
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
                Self::LogicalAnd(_) | Self::LogicalOr(_) => Precedence::Logical,
                Self::BinaryAnd(_) | Self::BinaryOr(_) => Precedence::Binary,
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
        pub fn parse(lexer: &mut Lexer<'_>, callee: cst::Expr) -> Self {
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

    impl<T: Parse, P: TryFrom<Tok, Error = Tok>> Parse for cst::PunctuatedList<T, P> {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self::parse_while(lexer, |tok| !matches!(tok, Tok::Eof))
        }
    }

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
    use crate::lex::tok;

    use super::*;

    use insta::*;
    use rstest::*;

    fn test_with_lexer(source: &str, test: impl FnOnce(&mut Lexer<'_>)) {
        let mut lexer = Lexer::new(source);
        test(&mut lexer);
        assert_eq!(lexer.next(), Tok::Eof)
    }

    mod expr {
        use super::*;

        #[rstest]
        #[case("expr_int_lit", "123")]
        #[case("expr_ident", "some_ident")]
        #[case("expr_add", "123 + 321")]
        #[case("expr_add_mul", "123 + 321 * 999")]
        #[case("expr_un_op", "-123")]
        #[case("expr_un_op_add_mul", "123 + -321 * 999")]
        #[case("expr_assignment", "some_ident = 123 + other_ident")]
        #[case("expr_logical_and", "true && something")]
        fn expr(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let expr = cst::Expr::parse(lexer);
                assert_debug_snapshot!(name, expr, source);
            });
        }

        #[rstest]
        #[case("assign_simple", "= some_value")]
        #[case("assign_expression", "= 1 + 2")]
        fn assign(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let assign = cst::Assign::parse(
                    lexer,
                    cst::Expr::Variable(cst::Variable {
                        variable: tok::Ident("some_ident".to_string()),
                    }),
                );
                assert_debug_snapshot!(name, assign, &format!("some_ident {source}"));
            });
        }

        #[rstest]
        #[case("binary_variable", "+ b")]
        #[case("binary_literal", "+ 2")]
        #[case("binary_logical_and", "&& 2")]
        fn binary(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let binary = cst::Binary::parse(
                    lexer,
                    cst::Expr::Variable(cst::Variable {
                        variable: tok::Ident("a".to_string()),
                    }),
                );
                assert_debug_snapshot!(name, binary, &format!("a {source}"));
            });
        }

        #[rstest]
        #[case("unary_variable", "-b")]
        #[case("unary_literal", "!2")]
        fn unary(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let unary = cst::Unary::parse(lexer);
                assert_debug_snapshot!(name, unary, source);
            });
        }

        #[rstest]
        #[case("if_only_if", "if condition { something }")]
        #[case("if_if_else", "if condition { something } else { something_else }")]
        #[case(
            "if_if_else_if",
            "if condition { something } else if other { something_else }"
        )]
        #[case(
            "if_if_else_if_else",
            "if condition { something } else if other { something_else } else { final }"
        )]
        #[case(
            "if_if_else_if_else_if_else",
            "if condition { something } else if other { something_else } else if another { thing } else { final }"
        )]
        fn if_expr(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let if_expr = cst::If::parse(lexer);
                assert_debug_snapshot!(name, if_expr, source);
            });
        }

        #[rstest]
        #[case("literal_true", "true")]
        #[case("literal_false", "false")]
        #[case("literal_int_0", "0")]
        #[case("literal_int_1", "1")]
        #[case("literal_int_123", "123")]
        fn literal(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let literal = cst::Literal::parse(lexer);
                assert_debug_snapshot!(name, literal, source);
            });
        }

        #[rstest]
        #[case("paren_ident", "(some_ident)")]
        #[case("paren_literal", "(123)")]
        #[case("paren_double", "((some_ident))")]
        fn paren(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let paren = cst::Paren::parse(lexer);
                assert_debug_snapshot!(name, paren, source);
            });
        }

        #[rstest]
        #[case("call_no_args", "()")]
        #[case("call_single_arg", "(1)")]
        #[case("call_single_arg_trailing", "(1,)")]
        #[case("call_multiple_args", "(1, 2, 3)")]
        #[case("call_multiple_args_trailing", "(1, 2, 3,)")]
        fn call(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let call = cst::Call::parse(
                    lexer,
                    cst::Expr::Variable(cst::Variable {
                        variable: tok::Ident("a".to_string()),
                    }),
                );
                assert_debug_snapshot!(name, call, &format!("a{source}"));
            });
        }

        #[rstest]
        #[case("variable_simple", "abc")]
        fn variable(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let variable = cst::Variable::parse(lexer);
                assert_debug_snapshot!(name, variable, source);
            });
        }
    }

    #[rstest]
    #[case("block_empty", "{ }")]
    #[case("block_expr", "{ 1 }")]
    #[case("block_statements", "{ let a = 1; let b = 1; }")]
    #[case("block_statements_and_expr", "{ let a = 1; let b = 1; 1 }")]
    fn block(#[case] name: &str, #[case] source: &str) {
        test_with_lexer(source, |lexer| {
            let block = cst::Block::parse(lexer);
            assert_debug_snapshot!(name, block, source);
        });
    }

    mod statements {
        use super::*;

        #[rstest]
        #[case("let_simple", "let a = 1;")]
        fn let_statement(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let let_statement = cst::LetStatement::parse(lexer);
                assert_debug_snapshot!(name, let_statement, source);
            });
        }

        #[rstest]
        #[case("return_simple", "return 1;")]
        fn return_statement(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let return_statement = cst::ReturnStatement::parse(lexer);
                assert_debug_snapshot!(name, return_statement, source);
            });
        }

        #[rstest]
        #[case("expr_no_semicolon", "1")]
        #[case("expr_semicolon", "1;")]
        fn expr_statement(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let expr_statement = cst::ExprStatement::parse(lexer);
                assert_debug_snapshot!(name, expr_statement, source);
            });
        }

        #[rstest]
        #[case("statements_let", "let a = 1;")]
        #[case("statements_return", "return 1;")]
        #[case("statements_expr", "1")]
        fn statements(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let statement = cst::Statement::parse(lexer);
                assert_debug_snapshot!(name, statement, source);
            });
        }
    }

    #[rstest]
    #[case("function_basic", "fn some_func() {}")]
    #[case("function_with_params", "fn some_func(a: u32, b: bool) {}")]
    #[case("function_with_return", "fn some_func() -> u32 {}")]
    #[case("function_with_body", "fn some_func() { let a = 1; 1 + 2; }")]
    #[case(
        "function_with_everything",
        "fn some_func(a: u32, b: bool) -> bool { let a = 1; 1 + 2; }"
    )]
    fn function(#[case] name: &str, #[case] source: &str) {
        test_with_lexer(source, |lexer| {
            let statement = cst::FunctionDeclaration::parse(lexer);
            assert_debug_snapshot!(name, statement, source);
        });
    }

    mod util {
        use super::*;

        #[rstest]
        #[case("punctuated_empty", "")]
        #[case("punctuated_single", "123")]
        #[case("punctuated_single_trailing", "123,")]
        #[case("punctuated_multiple", "123,321,456")]
        #[case("punctuated_multiple_trailing", "123,321,456,")]
        fn punctuated(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let list = PunctuatedList::<cst::Literal, tok::Comma>::parse(lexer);
                assert_debug_snapshot!(name, list, source);
            });
        }
    }
}
