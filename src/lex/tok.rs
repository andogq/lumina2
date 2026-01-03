macro_rules! toks {
    (@inner { $($items:tt)* } $variant:ident, $($rest:tt)*) => {
        toks!(
            @inner
            { $($items)* $variant => stringify!($variant), }
            $($rest)*
        );
    };

    // spell-checker:disable-next-line
    (@inner { $($items:tt)* } $variant:ident => $fmt:expr, $($rest:tt)*) => {
        toks!(
            @inner
            { $($items)* $variant => $fmt, }
            $($rest)*
        );
    };

    (@inner { $($items:tt)* } $variant:ident($inner:ty), $($rest:tt)*) => {
        toks!(
            @inner
            { $($items)* $variant($inner, tmp) => tmp, }
            $($rest)*
        );
    };

    // spell-checker:disable-next-line
    (@inner { $($variant:ident $(($inner:ty, $binding:ident))? => $fmt:expr,)* }) => {
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub enum Tok {
            $($variant $(($inner))?,)*
        }

        impl ::std::fmt::Display for Tok {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                match self {
                    $(Self::$variant $(($binding))? => ::std::write!(f, "{}", $fmt),)*
                }
            }
        }

        $(
            #[derive(Clone, Debug, PartialEq, Eq)]
            pub struct $variant$((pub $inner))?;

            impl ::std::convert::From<$variant> for Tok {
                fn from(#[allow(unused, reason = "variants without fields may not be used.")] value: $variant) -> Self {
                    toks!(@from_impl value => $variant $(($inner))?)
                }
            }

            impl ::std::convert::TryFrom<Tok> for $variant {
                type Error = Tok;

                fn try_from(value: Tok) -> ::std::result::Result<Self, Self::Error> {
                    toks!(@try_from_impl value => $variant $(($inner))?)
                }
            }
        )*
    };

    (@from_impl $value:ident => $variant:ident($inner:ty)) => {
        Self::$variant($value.0)
    };

    (@from_impl $value:ident => $variant:ident) => {
        Self::$variant
    };

    (@try_from_impl $value:ident => $variant:ident($inner:ty)) => {
        match $value {
            Tok::$variant(inner) => ::std::result::Result::Ok($variant(inner)),
            tok => ::std::result::Result::Err(tok),
        }
    };

    (@try_from_impl $value:ident => $variant:ident) => {
        match $value {
            Tok::$variant => ::std::result::Result::Ok($variant),
            tok => ::std::result::Result::Err(tok),
        }
    };

    ($($inner:tt)*) => {
        toks!(
            @inner
            {}
            $($inner)*
        );
    };
}

toks! {
    LParenthesis => "(",
    RParenthesis => ")",
    LBrace => "{{",
    RBrace => "}}",
    LBracket => "[",
    RBracket => "]",
    LAngle => "<",
    RAngle => ">",

    Eq => "=",
    Plus => "+",
    Minus => "-",
    Asterisk => "*",
    Slash => "/",
    Amp => "&",
    Bar => "|",
    Colon => ":",
    SemiColon => ";",
    Comma => ",",
    Bang => "!",

    EqEq => "==",
    BangEq => "!=",
    GtEq => ">=",
    LtEq => "<=",
    AmpAmp => "&&",
    BarBar => "||",

    ThinArrow => "->",

    True => "true",
    False => "false",

    Fn => "fn",
    Let => "let",
    Break => "break",
    Return => "return",
    If => "if",
    Else => "else",
    Loop => "loop",
    While => "while",

    Eof => "<Eof>",

    Ident(String),
    IntegerLiteral(usize),
}
