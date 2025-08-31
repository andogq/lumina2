/// Accepts a split token, an optional mode, a callback, and a series of tokens. Will call the
/// callback with tokens wrapped in `[]`, after separating them at the provided token. The token
/// will not be included.
///
/// The mode is optional, and may be:
///
/// - `with_trailing`: a trailing semicolon must be present
/// - `without_trailing`: a trailing semicolon must not be present
/// - _default_: a trailing semicolon may or may not be present
///
/// ```
/// split_token!([token] mode [callback(args)] tokens)
///
/// // produces
///
/// callback!(args [occurence_1] [occurence_2])
/// ```
///
#[macro_export(local_inner_macros)]
macro_rules! split_token {
    // Entrypoint.
    ([$tok:tt] $($mode:ident)? [$($callback:tt)+] $($tokens:tt)*) => {
        split_token!(step($tok) -> $($mode)? [$($callback)+] [] [] $($tokens)*)
    };

    /*
     * Token matching.
     *
     * Duplicate one of the following rules with a new token after `step` to support splitting
     * different tokens.
     */
    // Next token is semicolon. Extend `parts` with contents of `current`, and recurse.
    (step(;) -> $($mode:ident)? [$($callback:tt)+] [$($parts:tt)*] [$($current:tt)*] ; $($rest:tt)*) => {
        split_token!(step(;) -> $($mode)? [$($callback)+] [$($parts)* [$($current)*]] [] $($rest)*)
    };
    // Next token is equals. Extend `parts` with contents of `current`, and recurse.
    (step(=) -> $($mode:ident)? [$($callback:tt)+] [$($parts:tt)*] [$($current:tt)*] = $($rest:tt)*) => {
        split_token!(step(=) -> $($mode)? [$($callback)+] [$($parts)* [$($current)*]] [] $($rest)*)
    };
    // Next token is comma. Extend `parts` with contents of `current`, and recurse.
    (step(,) -> $($mode:ident)? [$($callback:tt)+] [$($parts:tt)*] [$($current:tt)*] , $($rest:tt)*) => {
        split_token!(step(,) -> $($mode)? [$($callback)+] [$($parts)* [$($current)*]] [] $($rest)*)
    };

    // Catch all case, token is unknown. Add it to `current`, and recurse.
    (step($tok:tt) -> $($mode:ident)? [$($callback:tt)+] [$($parts:tt)*] [$($current:tt)*] $test_tok:tt $($rest:tt)*) => {
        split_token!(step($tok) -> $($mode)? [$($callback)+] [$($parts)*] [$($current)* $test_tok] $($rest)*)
    };

    // No more tokens, trailing required, current is empty (therefore previous was semicolon).
    (step($tok:tt) -> with_trailing [$($callback:tt)+] [$($parts:tt)*] []) => {
        split_token!(callback -> [$($callback)+] [$($parts)*])
    };

    // No more tokens, no trailing, current has tokens.
    (step($tok:tt) -> without_trailing [$($callback:tt)+] [$($parts:tt)*] [$($current:tt)+]) => {
        split_token!(callback -> [$($callback)+] [$($parts)* [$($current)+]])
    };

    // No preference on trailing semicolon, so add a new part if it's required.
    (step($tok:tt) -> [$($callback:tt)+] [$($parts:tt)*] [$($($current:tt)+)?]) => {
        split_token!(callback -> [$($callback)+] [$($parts)* $([$($current)+])?])
    };

    // Call the callback macro, providing any optional arguments provided, followed by each part.
    (callback -> [$callback:ident $(($($args:tt)*))?] [$($parts:tt)*]) => {
        $callback!($($($args)*)? $($parts)*)
    };
}

#[cfg(test)]
mod test {
    #[test]
    fn semicolon() {
        assert_eq!(split_token!([;] [stringify] a; b; c;), "[a] [b] [c]");
    }

    #[test]
    fn equals() {
        assert_eq!(split_token!([=] [stringify] a = b = c =), "[a] [b] [c]");
    }

    #[test]
    fn comma() {
        assert_eq!(split_token!([,] [stringify] a, b, c), "[a] [b] [c]");
    }

    #[test]
    fn comma_trailing() {
        assert_eq!(split_token!([,] [stringify] a, b, c,), "[a] [b] [c]");
    }

    #[test]
    fn callback_args() {
        assert_eq!(
            split_token!([;] [stringify(arg_1 something (nested, list))] a; b; c;),
            "arg_1 something(nested, list)[a] [b] [c]"
        );
    }

    #[test]
    fn statements() {
        assert_eq!(
            split_token!([;] [stringify] let a = 1; let b = 2; let something = { let d = 3; 4 }),
            "[let a = 1] [let b = 2] [let something = { let d = 3; 4 }]"
        );
    }
}
