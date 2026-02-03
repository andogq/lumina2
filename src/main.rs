#![recursion_limit = "256"]
#![warn(clippy::allow_attributes_without_reason)]

mod ctx;
mod error;
mod ir;
mod lex;
mod passes;
mod prelude;
mod query;
mod ty;
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
    // spell-checker:disable-next-line
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

    // spell-checker:disable-next-line
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

#[mutants::skip(reason = "helper function to quickly run a script.")]
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

    let fatal_error_count = ctx.errors.iter_fatal().count();
    if fatal_error_count > 0 {
        let error_plural = if fatal_error_count == 1 {
            "error"
        } else {
            "errors"
        };
        eprintln!("{fatal_error_count} fatal {error_plural} occurred during compilation:");

        for (i, error) in ctx.errors.iter_fatal().enumerate() {
            eprintln!("Error {i}/{fatal_error_count}:");
            eprintln!("{error}");
            eprintln!();
        }

        panic!("Compilation failed with fatal error");
    }

    let non_fatal_count = ctx.errors.iter_non_fatal().count();
    if non_fatal_count > 0 {
        let error_plural = if non_fatal_count == 1 {
            "error"
        } else {
            "errors"
        };
        eprintln!("{non_fatal_count} {error_plural} occurred during compilation:");

        for (i, error) in ctx.errors.iter_non_fatal().enumerate() {
            eprintln!("Error {i}/{fatal_error_count}:");
            eprintln!("{error}");
            eprintln!();
        }
    }

    {
        let engine = module
            .create_jit_execution_engine(inkwell::OptimizationLevel::None)
            .unwrap();
        let fn_main =
            unsafe { engine.get_function::<unsafe extern "C" fn() -> u8>("main") }.unwrap();
        unsafe { fn_main.call() }
    }
}

#[mutants::skip(reason = "entry point for binary.")]
fn main() {
    let result = run(r#"fn main() -> u8 { let a = (1, 2, true); a.0 }"#);

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
                run(
                    "fn main() -> bool { let my_bool = true; let other_bool = false; my_bool && other_bool }"
                ),
                0
            );
        }

        #[rstest]
        #[case::add("1 + 2", "u8", 3)]
        #[case::sub("10 - 4", "u8", 6)]
        #[case::mul("10 * 4", "u8", 40)]
        #[case::div("12 / 4", "u8", 3)]
        #[case::div_signed("-12 / -4", "i8", 3)]
        #[case::logical_and("true && true", "bool", 1)]
        #[case::logical_or("true || false", "bool", 1)]
        #[case::bitwise_and("3 & 2", "u8", 2)]
        #[case::bitwise_or("4 | 2", "u8", 6)]
        #[case::less_signed("-4 < -3", "bool", 1)]
        #[case::less_equal_signed("-4 <= -4", "bool", 1)]
        #[case::greater_equal_signed("-5 <= -4", "bool", 1)]
        fn binary_operations(#[case] source: &str, #[case] return_ty: &str, #[case] output: u8) {
            assert_eq!(
                run(&format!("fn main() -> {return_ty} {{ {source} }}")),
                output
            );
        }

        #[rstest]
        #[case::less("<", 1)]
        #[case::less_equal("<=", 1)]
        #[case::greater(">", 0)]
        #[case::greater_equal(">=", 0)]
        fn binary_unsigned_operations(#[case] symbol: &str, #[case] output: u8) {
            assert_eq!(
                run(&format!(
                    "fn cmp(lhs: u8, rhs: u8) -> bool {{ lhs {symbol} rhs }}  fn main() -> bool {{ cmp(3, 4) }}"
                )),
                output
            );
        }

        #[rstest]
        // --- Arithmetic Precedence ---
        #[case::mul_add("2 + 3 * 4", "u8", 14)] // (3 * 4) + 2
        #[case::add_mul("3 * 4 + 2", "u8", 14)] // (3 * 4) + 2
        #[case::div_sub("10 - 6 / 2", "u8", 7)] // 10 - (6 / 2)
        #[case::complex_maths("1 + 2 * 3 - 4 / 2", "u8", 5)] // 1 + 6 - 2
        // --- Bitwise Operations (&, |) ---
        #[case::sum_bitwise("1 + 2 & 1", "u8", 1)] // (1 + 2) & 1 = 3 & 1 = 1
        #[case::bitwise_and_or("1 | 2 & 2", "u8", 3)] // 1 | (2 & 2) = 1 | 2 = 3
        #[case::bitwise_complex("1 + 1 | 2 * 2", "u8", 6)] // (1+1) | (2*2) = 2 | 4 = 6
        // --- Comparison vs Arithmetic/Bitwise ---
        #[case::cmp_add("1 + 2 < 4", "bool", 1)] // (1 + 2) < 4
        #[case::cmp_mul("10 < 2 * 6", "bool", 1)] // 10 < (12)
        #[case::bitwise_cmp("3 & 1 == 1", "bool", 1)] // (3 & 1) == 1 -> 1 == 1
        // --- Logical Precedence ---
        #[case::cmp_logical("1 == 1 && 2 == 3", "bool", 0)] // (1==1) && (2==3)
        #[case::logic_precedence("true || false && false", "bool", 1)] // true || (false && false)
        #[case::logic_mixed("5 > 3 && 2 == 2", "bool", 1)]
        // --- Brackets (Explicit Override) ---
        #[case::brackets_sum("(2 + 3) * 4", "u8", 20)]
        #[case::brackets_logic("(true || false) && false", "bool", 0)]
        #[case::brackets_bitwise("1 + (2 & 1)", "u8", 1)]
        #[case::nested_brackets("2 * (3 + (10 / 5))", "u8", 10)]
        // --- Signed Operations ---
        #[case::div_signed("-12 / -4", "i8", 3)]
        #[case::less_signed("-4 < -3", "bool", 1)]
        #[case::assign_right_associative("{ let x = (); let y = 0; x = y = 5; y }", "u8", 5)]
        fn precedence_operations(
            #[case] source: &str,
            #[case] return_ty: &str,
            #[case] output: u8,
        ) {
            assert_eq!(
                run(&format!("fn main() -> {return_ty} {{ {source} }}")),
                output
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
        fn function_values() {
            assert_eq!(
                run(
                    "fn get1() -> u8 { 1 } fn get2() -> u8 { 2 } fn main() -> u8 { let f = get1; if f() == 1 { f = get2; } f() }"
                ),
                2
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
        fn parameters() {
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
                    "fn a() -> u8 { 123 } fn b() -> u8 { 99 } fn main() -> u8 { let my_fn = if true { a } else { b }; my_fn() }"
                ),
                123
            );
        }

        #[test]
        fn shadowing() {
            assert_eq!(
                run(
                    "fn main() -> u8 { let a = 1; let b = { let old_a = a; let a = 5; a + old_a }; a + b }"
                ),
                7
            );
        }

        #[test]
        fn break_nothing() {
            assert_eq!(
                run(r#"fn main() -> u8 {
                    let count = 0;

                    loop {
                        if count >= 3 {
                            break;
                        }

                        count = count + 1;
                    };

                    count
                }"#),
                3
            );
        }

        #[test]
        fn break_expression() {
            assert_eq!(
                run(r#"fn main() -> u8 {
                    let count = 0;

                    let output = loop {
                        if count >= 3 {
                            break 10;
                        }

                        count = count + 1;
                    };

                    output
                }"#),
                10
            );
        }

        #[test]
        fn tuple() {
            assert_eq!(
                run("fn main() -> u8 { let a = (23, 95, true); a.0 = 5; a.0 + a.1 }"),
                100
            )
        }

        #[test]
        fn trait_impl() {
            assert_eq!(
                run(r#"trait MyTrait {
                        fn some_method() -> Self;
                    }

                    impl MyTrait for u8 {
                        fn some_method() -> Self {
                            10
                        }
                    }

                    fn main() -> u8 {
                        <u8 as MyTrait>::some_method()
                    }"#),
                10
            );
        }

        #[test]
        #[should_panic(expected = "Type")]
        fn trait_impl_mismatch() {
            run(r#"trait MyTrait {
                fn some_method() -> Self;
            }

            impl MyTrait for u8 {
                fn some_method(parameter: bool) -> Self {
                    10
                }
            }

            fn main() -> u8 {
                <u8 as MyTrait>::some_method()
            }"#);
        }

        #[test]
        #[should_panic(expected = "type must implement trait")]
        fn trait_not_implemented() {
            run(r#"trait MyTrait {
                fn some_method() -> Self;
            }

            fn main() -> u8 {
                <u8 as MyTrait>::some_method()
            }"#);
        }

        #[test]
        fn complex_path_usage() {
            assert_eq!(
                run(r#"trait MyTrait {
                        fn some_method() -> Self;
                    }

                    impl MyTrait for u8 {
                        fn some_method() -> Self {
                            10
                        }
                    }

                    fn fallback() -> u8 {
                        3
                    }

                    fn main() -> u8 {
                        let get_num = if true {
                            <u8 as MyTrait>::some_method
                        } else {
                            fallback
                        };

                        get_num()
                    }"#),
                10
            );
        }

        #[test]
        #[should_panic(expected = "cannot generate HIR for function without implementation")]
        fn extern_function_no_implementation() {
            run(r#"extern fn something() -> bool;

            fn main() -> u8 {
                if something() {
                    3
                } else {
                    7
                }
            }"#);
        }
    }
}
