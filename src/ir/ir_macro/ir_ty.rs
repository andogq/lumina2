/// Parse stream of tokens into a type. An instance of [`Ty`] must be provided in the initial
/// set of brackets. This macro will return [`Ty`], which will resolve to the [`Ty`] parsed
/// from the macro.
///
/// [`Ty`]: crate::Ty
/// [`Ty`]: crate::Ty
#[macro_export(local_inner_macros)]
macro_rules! ir_ty {
    /*
     * Primitive types.
     */
    // Type for `u8` primitive.
    (u8) => {
        $crate::tir::Ty::U8
    };
    // Type for `i8` primitive.
    (i8) => {
        $crate::tir::Ty::I8
    };

    /*
     * References.
     */
    // Parses `&<ty>`, where `<ty>` is any type.
    //
    // Detect type starting with `&`. If found, recurse to determine inner type, and report it as a
    // reference.
    (& $($ty:tt)+) => {{
        let ty = ir_ty!($($ty)+);

        $crate::tir::Ty::Ref(::std::boxed::Box::new(ty))
    }};

    /*
     * Arrays.
     */
    // Parses `[<ty>; <count>]`, where `<ty>` is any type, and `<count>` is any expression that
    // results in a `usize`.
    //
    // Detect any type wrapped in `[]`. If found, split the contents at `;` expecting two children,
    // the inner type, and the count.
    ([$($toks:tt)*]) => {
        split_token!([;] without_trailing [ir_ty(cb_array_parts)] $($toks)*)
    };
    // Callback for array parsing, after splitting at semicolon. Expects to be provided two items,
    // a series of tokens for the inner type, and an expression for the length.
    (cb_array_parts [$($ty:tt)+] [$length:expr]) => {{
        let ty = ir_ty!($($ty)+);

        $crate::tir::Ty::Array(::std::boxed::Box::new(ty), $length)
    }};
    (cb_array_parts [$($ty:tt)+]) => {{
        let ty = ir_ty!($($ty)+);

        $crate::tir::Ty::Slice(::std::boxed::Box::new(ty))
    }};
}

#[cfg(test)]
mod test {
    use crate::tir::Ty;

    macro_rules! assert_ty {
            (
                ty => [$($ty:tt)*],
                expected => [$($expected:tt)*] $(,)?
            ) => {
                assert_eq!(
                    ir_ty!($($ty)*),
                    $($expected)*
                );
            };
        }

    mod primitive {
        use super::*;

        #[test]
        fn u8() {
            assert_eq!(ir_ty!(u8), Ty::U8);
        }

        #[test]
        fn i8() {
            assert_eq!(ir_ty!(i8), Ty::I8);
        }
    }

    mod reference {
        use super::*;

        #[test]
        fn ref_primitive() {
            assert_eq!(ir_ty!(&u8), Ty::Ref(Box::new(Ty::U8)));
        }

        #[test]
        fn ref_ref_primitive() {
            // HACK: When using `tt`, the tokeniser will interpret `&&` as boolean `AND`,
            // rather than a reference of a reference. This is mitigated by separating them
            // with a space.
            #[rustfmt::skip]
            assert_eq!(
                ir_ty!(& &u8),
                Ty::Ref(Box::new(Ty::Ref(Box::new(Ty::U8))))
            );
        }

        #[test]
        fn ref_array() {
            assert_eq!(
                ir_ty!(&[u8; 3]),
                Ty::Ref(Box::new(Ty::Array(Box::new(Ty::U8), 3)))
            );
        }
    }

    mod array {
        use super::*;

        #[test]
        fn simple_array() {
            assert_eq!(ir_ty!([u8; 3]), Ty::Array(Box::new(Ty::U8), 3));
        }

        #[test]
        fn nested_array() {
            assert_eq!(
                ir_ty!([[u8; 10]; 3]),
                Ty::Array(Box::new(Ty::Array(Box::new(Ty::U8), 10)), 3)
            );
        }
    }

    mod slice {
        use super::*;

        #[test]
        fn simple_slice() {
            assert_eq!(ir_ty!([u8]), Ty::Slice(Box::new(Ty::U8)));
        }

        #[test]
        fn slice_ref() {
            assert_eq!(
                ir_ty!(&[u8]),
                Ty::Ref(Box::new(Ty::Slice(Box::new(Ty::U8))))
            );
        }
    }
}
