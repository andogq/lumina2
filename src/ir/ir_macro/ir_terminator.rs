#[macro_export(local_inner_macros)]
macro_rules! ir_terminator {
    (return) => {
        $crate::ir::Terminator::Return
    };
}

#[cfg(test)]
mod test {
    use crate::ir::Terminator;

    #[test]
    fn term_return() {
        assert_eq!(ir_terminator!(return), Terminator::Return);
    }
}
