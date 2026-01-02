#![recursion_limit = "256"]

mod ctx;
mod error;
mod ir;
mod lex;
mod passes;
mod prelude;
mod stages;
mod util;

use crate::prelude::*;

/// Helper to define a compiler pipeline.
///
/// A mutable reference to [`Ctx`] is passed within `[]` (`&mut ctx`), and the input for the
/// pipeline is provided on the left of `=>` (`source`). Then, a list of 'steps' in the form of
/// types which implement [`Pass`] are listed within `{}`. Each step accepts extra information,
/// including:
///
/// - `[debug]`: debug print the output of this step upon completion.
/// - `=> (&ink)`: provide `&ink` as the `extra` parameter in [`Pass::run`].
///
/// ```
/// let mut ctx = Ctx::new();
/// let ink = inkwell::context::Context::create();
/// let source = "fn main() -> u8 { 1 }";
///
/// let hir = pipeline! {
///     [&mut ctx]
///     source => {
///         |> passes::cst_gen::CstGen
///         |> passes::ast_gen::AstGen [debug]
///         |> passes::hir_gen::HirGen
///         |> passes::thir_gen::ThirGen
///         |> passes::mir_gen::MirGen
///         |> passes::codegen::Codegen => (&ink)
///     }
/// };
/// ```
macro_rules! pipeline {
    ([$ctx:expr] $input:expr => { $(|> $pass:ty $(=> ($extra:expr))? $([$($meta:tt)+])*)* }) => {{
        let input = $input;

        $(
            let input = <$pass>::run(
                $ctx,
                &input,
                pipeline!(@extra $($extra)?),
            ).unwrap().into_outcome();

            $(pipeline!(@meta [input, $pass] $($meta)*);)*
        )*

        input
    }};

    (@extra $extra:expr) => {
        $extra
    };

    (@extra ) => {
        ()
    };

    (@meta [$input:ident, $pass:ty] debug) => {
        eprintln!("{} => {:#?}", stringify!($pass), $input);
    };
}

fn run(source: &str) -> u8 {
    let mut ctx = Ctx::new();
    let ink = inkwell::context::Context::create();

    let module = pipeline! {
        [&mut ctx]
        source => {
            |> passes::cst_gen::CstGen
            |> passes::ast_gen::AstGen
            |> passes::hir_gen::HirGen
            |> passes::thir_gen::ThirGen
            |> passes::mir_gen::MirGen
            |> passes::codegen::Codegen => (&ink)
        }
    };

    {
        let engine = module
            .create_jit_execution_engine(inkwell::OptimizationLevel::None)
            .unwrap();
        let fn_main =
            unsafe { engine.get_function::<unsafe extern "C" fn() -> u8>("main") }.unwrap();
        unsafe { fn_main.call() }
    }
}

fn main() {
    let result = run(r#"fn main() -> u8 {
            let count = 0;

            loop {
                if count >= 3 {
                    break;
                }

                count = count + 1;
            }

            count
        }"#);

    dbg!(result);
}

#[cfg(test)]
mod test {
    use super::*;

    mod full {
        use super::*;

        #[test]
        fn implicit_return_u8() {
            assert_eq!(run("fn main() -> u8 { 42 }"), 42);
        }

        #[test]
        fn basic_expression() {
            assert_eq!(run("fn main() -> u8 { 1 + 2 }"), 3);
        }

        #[test]
        fn variables() {
            assert_eq!(
                run("fn main() -> u8 { let a = 1; let b = 123; a + b }"),
                124
            );
        }

        #[test]
        fn booleans() {
            assert_eq!(
                run("fn main() -> bool { let my_bool = true; let other_bool = false; my_bool }"),
                1
            );
        }

        #[test]
        fn if_statement() {
            assert_eq!(run("fn main() -> u8 { if true { 123 } else { 99 } }"), 123);
        }

        #[test]
        fn if_variable() {
            assert_eq!(
                run("fn main() -> u8 { let a = if true { 123 } else { 44 }; let b = a + 10; b }"),
                133
            );
        }

        #[test]
        fn reassignment() {
            assert_eq!(run("fn main() -> u8 { let a = 1; a = 2; a }"), 2);
        }

        #[test]
        fn conditional_reassignment() {
            assert_eq!(
                run("fn main() -> u8 { let a = 1; if a == 1 { a = 2; } a }"),
                2
            );
        }

        #[test]
        fn explicit_return() {
            assert_eq!(run("fn main() -> u8 { return 1; }"), 1);
        }

        #[test]
        fn conditional_return() {
            assert_eq!(run("fn main() -> u8 { if true { return 2; } 1 }"), 2);
        }

        #[test]
        fn reference() {
            assert_eq!(run("fn main() -> u8 { let a = 123; let b = &a; *b }"), 123);
        }

        #[test]
        fn assign_to_reference() {
            assert_eq!(
                run("fn main() -> u8 { let a = 123; let b = &a; *b = 44; a }"),
                44
            );
        }

        #[test]
        fn so_many_refs() {
            assert_eq!(
                run(
                    "fn main() -> u8 { let a = 123; let b = 111; let a_ref = &a; let b_ref = &b; *a_ref = *b_ref; a }"
                ),
                111
            );
        }

        #[test]
        fn fns() {
            assert_eq!(
                run("fn cool_fn() -> u8 { return 123; } fn main() -> u8 { cool_fn() }"),
                123
            );
        }

        #[test]
        fn params() {
            assert_eq!(
                run("fn double(a: u8) -> u8 { a * 2 } fn main() -> u8 { double(3) }"),
                6
            );
        }

        #[test]
        fn fib() {
            assert_eq!(
                run(r#"
                    fn fib(n: u8) -> u8 {
                        if n <= 1 {
                            return n;
                        }

                        fib(n - 1) + fib(n - 2)
                    }

                    fn main() -> u8 {
                        fib(12)
                    }
                "#),
                144
            );
        }

        #[test]
        fn function_as_value() {
            assert_eq!(
                run(
                    "fn a() -> u8 { 123 } fn b() -> u8 { 99 } fn main() -> u8 { let func = if true { a } else { b }; func() }"
                ),
                123
            );
        }
    }
}
