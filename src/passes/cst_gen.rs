use crate::prelude::*;

use cst::PunctuatedList;

pub struct CstGen;
impl<'ctx, 'src> Pass<'ctx, 'src> for CstGen {
    type Input = str;
    type Output = cst::Program;
    type Extra = ();

    fn run(_ctx: &'ctx mut Ctx, src: &'src str, _extra: ()) -> PassResult<Self::Output> {
        let mut lexer = Lexer::new(src);
        Ok(PassSuccess::Ok(cst::Program::parse(&mut lexer)))
    }
}

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
                tok_l_parenthesis: lexer.expect().unwrap(),
                parameters: PunctuatedList::parse_while(lexer, |tok| {
                    !matches!(tok, Tok::RParenthesis)
                }),
                tok_r_parenthesis: lexer.expect().unwrap(),
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
                Tok::Break => cst::BreakStatement::parse(lexer).into(),
                _ => cst::ExpressionStatement::parse(lexer).into(),
            }
        }
    }

    impl Parse for cst::LetStatement {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                tok_let: lexer.expect().unwrap(),
                variable: lexer.expect().unwrap(),
                tok_eq: lexer.expect().unwrap(),
                value: cst::Expression::parse(lexer),
                tok_semicolon: lexer.expect().unwrap(),
            }
        }
    }

    impl Parse for cst::ReturnStatement {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                tok_return: lexer.expect().unwrap(),
                value: cst::Expression::parse(lexer),
                tok_semicolon: lexer.expect().unwrap(),
            }
        }
    }

    impl Parse for cst::BreakStatement {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                tok_break: lexer.expect().unwrap(),
                // If the next token isn't a semicolon, continue parsing.
                value: (!matches!(lexer.peek(), Tok::SemiColon))
                    .then(|| cst::Expression::parse(lexer)),
                tok_semicolon: lexer.expect().unwrap(),
            }
        }
    }

    impl Parse for cst::ExpressionStatement {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                expression: cst::Expression::parse(lexer),
                tok_semicolon: lexer.next_if(),
            }
        }
    }
}

mod expression {
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
        #[expect(dead_code, reason = "cast expressions are not currently implemented.")]
        Cast,
        Call,
    }

    impl Precedence {
        // TODO: Don't have multiple precedence functions
        fn of(tok: &Tok) -> Self {
            match tok {
                Tok::LParenthesis | Tok::LBracket => Self::Call,
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

    impl Parse for cst::Expression {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self::parse_with_precedence(lexer, Precedence::Lowest)
        }
    }

    impl cst::Expression {
        fn parse_with_precedence(lexer: &mut Lexer<'_>, precedence: Precedence) -> Self {
            let mut expression = Self::parse_prefix(lexer);

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
                    | Tok::GtEq => expression = cst::Binary::parse(lexer, expression).into(),
                    Tok::Eq => expression = cst::Assign::parse(lexer, expression).into(),
                    Tok::LParenthesis => expression = cst::Call::parse(lexer, expression).into(),
                    _ => break,
                }
            }

            expression
        }

        fn parse_prefix(lexer: &mut Lexer<'_>) -> Self {
            match lexer.peek() {
                Tok::Ident(_) => cst::Variable::parse(lexer).into(),
                Tok::IntegerLiteral(_) | Tok::True | Tok::False => {
                    cst::Literal::parse(lexer).into()
                }
                Tok::Minus | Tok::Amp | Tok::Asterisk | Tok::Bang => {
                    cst::Unary::parse(lexer).into()
                }
                Tok::LBrace => cst::Block::parse(lexer).into(),
                Tok::LParenthesis => cst::Parenthesis::parse(lexer).into(),
                Tok::If => cst::If::parse(lexer).into(),
                Tok::Loop => cst::Loop::parse(lexer).into(),
                tok => panic!("unexpected tok: {tok}"),
            }
        }
    }

    impl cst::Assign {
        pub(super) fn parse(lexer: &mut Lexer<'_>, assignee: cst::Expression) -> Self {
            Self {
                assignee: Box::new(assignee),
                tok_eq: lexer.expect().unwrap(),
                value: Box::new(cst::Expression::parse_with_precedence(
                    lexer,
                    Precedence::Assign,
                )),
            }
        }
    }

    impl cst::Binary {
        pub(super) fn parse(lexer: &mut Lexer<'_>, lhs: cst::Expression) -> Self {
            let operation = cst::BinaryOperation::parse(lexer);
            let rhs = cst::Expression::parse_with_precedence(lexer, operation.precedence());

            Self {
                lhs: Box::new(lhs),
                operation,
                rhs: Box::new(rhs),
            }
        }
    }

    impl Parse for cst::BinaryOperation {
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

                Tok::EqEq => Self::Equal(lexer.expect().unwrap()),
                Tok::BangEq => Self::NotEqual(lexer.expect().unwrap()),
                Tok::LAngle => Self::Less(lexer.expect().unwrap()),
                Tok::LtEq => Self::LessEqual(lexer.expect().unwrap()),
                Tok::RAngle => Self::Greater(lexer.expect().unwrap()),
                Tok::GtEq => Self::GreaterEqual(lexer.expect().unwrap()),

                tok => panic!("unknown binary operation: {tok}"),
            }
        }
    }

    impl cst::BinaryOperation {
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
            }
        }
    }

    impl Parse for cst::Unary {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                operation: cst::UnaryOperation::parse(lexer),
                value: Box::new(cst::Expression::parse_with_precedence(
                    lexer,
                    Precedence::Prefix,
                )),
            }
        }
    }

    impl Parse for cst::UnaryOperation {
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
                condition: Box::new(cst::Expression::parse(lexer)),
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

    impl Parse for cst::Loop {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                tok_loop: lexer.expect().unwrap(),
                body: cst::Block::parse(lexer),
            }
        }
    }

    impl Parse for cst::Literal {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            match lexer.peek() {
                Tok::True => cst::BooleanLiteral::True(lexer.expect().unwrap()).into(),
                Tok::False => cst::BooleanLiteral::False(lexer.expect().unwrap()).into(),
                Tok::IntegerLiteral(_) => cst::IntegerLiteral(lexer.expect().unwrap()).into(),
                tok => panic!("expected literal, found: {tok}"),
            }
        }
    }

    impl Parse for cst::Parenthesis {
        fn parse(lexer: &mut Lexer<'_>) -> Self {
            Self {
                tok_l_parenthesis: lexer.expect().unwrap(),
                expression: Box::new(cst::Expression::parse(lexer)),
                tok_r_parenthesis: lexer.expect().unwrap(),
            }
        }
    }

    impl cst::Call {
        pub fn parse(lexer: &mut Lexer<'_>, callee: cst::Expression) -> Self {
            Self {
                callee: Box::new(callee),
                tok_l_parenthesis: lexer.expect().unwrap(),
                arguments: cst::PunctuatedList::parse_while(lexer, |tok| {
                    !matches!(tok, Tok::RParenthesis)
                }),
                tok_r_parenthesis: lexer.expect().unwrap(),
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
    use super::*;

    fn test_with_lexer(source: &str, test: impl FnOnce(&mut Lexer<'_>)) {
        let mut lexer = Lexer::new(source);
        test(&mut lexer);
        assert_eq!(lexer.next(), Tok::Eof)
    }

    mod expression {
        use super::*;

        #[rstest]
        #[case("expression_integer_literal", "123")]
        #[case("expression_ident", "some_ident")]
        #[case("expression_add", "123 + 321")]
        #[case("expression_add_mul", "123 + 321 * 999")]
        #[case("expression_unary_operation", "-123")]
        #[case("expression_unary_operation_add_mul", "123 + -321 * 999")]
        #[case("expression_assignment", "some_ident = 123 + other_ident")]
        #[case("expression_logical_and", "true && something")]
        fn expression(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let expression = cst::Expression::parse(lexer);
                assert_debug_snapshot!(name, expression, source);
            });
        }

        #[rstest]
        #[case("assign_simple", "= some_value")]
        #[case("assign_expression", "= 1 + 2")]
        fn assign(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let assign = cst::Assign::parse(
                    lexer,
                    cst::Expression::Variable(cst::Variable {
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
                    cst::Expression::Variable(cst::Variable {
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
        fn if_expression(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let if_expression = cst::If::parse(lexer);
                assert_debug_snapshot!(name, if_expression, source);
            });
        }

        #[rstest]
        #[case("literal_true", "true")]
        #[case("literal_false", "false")]
        #[case("literal_integer_0", "0")]
        #[case("literal_integer_1", "1")]
        #[case("literal_integer_123", "123")]
        fn literal(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let literal = cst::Literal::parse(lexer);
                assert_debug_snapshot!(name, literal, source);
            });
        }

        #[rstest]
        #[case("parenthesis_ident", "(some_ident)")]
        #[case("parenthesis_literal", "(123)")]
        #[case("parenthesis_double", "((some_ident))")]
        fn parenthesis(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let parenthesis = cst::Parenthesis::parse(lexer);
                assert_debug_snapshot!(name, parenthesis, source);
            });
        }

        #[rstest]
        #[case("call_no_arguments", "()")]
        #[case("call_single_argument", "(1)")]
        #[case("call_single_argument_trailing", "(1,)")]
        #[case("call_multiple_arguments", "(1, 2, 3)")]
        #[case("call_multiple_arguments_trailing", "(1, 2, 3,)")]
        fn call(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let call = cst::Call::parse(
                    lexer,
                    cst::Expression::Variable(cst::Variable {
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
    #[case("block_expression", "{ 1 }")]
    #[case("block_statements", "{ let a = 1; let b = 1; }")]
    #[case("block_statements_and_expression", "{ let a = 1; let b = 1; 1 }")]
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
        #[case("expression_no_semicolon", "1")]
        #[case("expression_semicolon", "1;")]
        fn expression_statement(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let expression_statement = cst::ExpressionStatement::parse(lexer);
                assert_debug_snapshot!(name, expression_statement, source);
            });
        }

        #[rstest]
        #[case("statements_let", "let a = 1;")]
        #[case("statements_return", "return 1;")]
        #[case("statements_expression", "1")]
        fn statements(#[case] name: &str, #[case] source: &str) {
            test_with_lexer(source, |lexer| {
                let statement = cst::Statement::parse(lexer);
                assert_debug_snapshot!(name, statement, source);
            });
        }
    }

    #[rstest]
    #[case("function_basic", "fn some_function() {}")]
    #[case("function_with_parameters", "fn some_function(a: u32, b: bool) {}")]
    #[case("function_with_return", "fn some_function() -> u32 {}")]
    #[case("function_with_body", "fn some_function() { let a = 1; 1 + 2; }")]
    #[case(
        "function_with_everything",
        "fn some_function(a: u32, b: bool) -> bool { let a = 1; 1 + 2; }"
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
