#![recursion_limit = "256"]

mod ctx;
mod ir;
mod lex;
mod stages;
mod util;

use crate::{ctx::Ctx, stages::parse::Parse};

pub use self::lex::Tok;

fn run(source: &str) -> u8 {
    let mut ctx = Ctx::default();
    let mut toks = lex::Lexer::new(source);
    let cst = ir::cst::Program::parse(&mut toks);
    let ast = stages::ast_builder::build_ast(&mut ctx, &cst);
    let hir = stages::hir_builder::lower(&ctx, &ast);
    dbg!(&hir);
    let types = stages::ty::solve(&hir);
    dbg!(&types);
    let thir = ir::hir::Thir::new(hir, types);
    dbg!(&thir);
    let mir = stages::mir_builder::lower(&thir);
    dbg!(&mir);

    let ink = inkwell::context::Context::create();
    let module = stages::codegen::codegen(&ctx, &ink, &mir);

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
    let result = run(
        "fn a() -> u8 { 123 } fn b() -> u8 { 99 } fn main() -> u8 { let func = if true { a } else { b }; func() }",
    );

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
    }
}
