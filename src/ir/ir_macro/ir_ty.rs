/// Parse stream of tokens into a type. An instance of [`TyInfo`] must be provided in the initial
/// set of brackets. This macro will return [`Ty`], which will resolve to the [`TyInfo`] parsed
/// from the macro.
///
/// [`TyInfo`]: crate::TyInfo
/// [`Ty`]: crate::Ty
#[macro_export(local_inner_macros)]
macro_rules! ir_ty {
    /*
     * Primitive types.
     */
    // Type for `u8` primitive.
    ([$tys:expr] u8) => {
        ir_ty!(insert [$tys] $crate::ir::TyInfo::U8)
    };
    // Type for `i8` primitive.
    ([$tys:expr] i8) => {
        ir_ty!(insert [$tys] $crate::ir::TyInfo::I8)
    };

    /*
     * References.
     */
    // Parses `&<ty>`, where `<ty>` is any type.
    //
    // Detect type starting with `&`. If found, recurse to determine inner type, and report it as a
    // reference.
    ([$tys:expr] & $($ty:tt)+) => {{
        let ty = ir_ty!([$tys] $($ty)+);

        ir_ty!(insert [$tys] $crate::ir::TyInfo::Ref(ty))
    }};

    /*
     * Arrays.
     */
    // Parses `[<ty>; <count>]`, where `<ty>` is any type, and `<count>` is any expression that
    // results in a `usize`.
    //
    // Detect any type wrapped in `[]`. If found, split the contents at `;` expecting two children,
    // the inner type, and the count.
    ([$tys:expr] [$($toks:tt)*]) => {
        split_token!([;] without_trailing [ir_ty(cb_array_parts [$tys])] $($toks)*)
    };
    // Callback for array parsing, after splitting at semicolon. Expects to be provided two items,
    // a series of tokens for the inner type, and an expression for the length.
    (cb_array_parts [$tys:expr] [$($ty:tt)+] [$length:expr]) => {{
        let ty = ir_ty!([$tys] $($ty)+);

        ir_ty!(insert [$tys] $crate::ir::TyInfo::Array { ty, length: $length })
    }};


    /*
     * Helpers.
     */
    // Helper to insert `TyInfo` into `tys`.
    (insert [$tys:expr] $($ty:tt)*) => {
        $tys.find_or_insert($($ty)*)
    };
}

#[cfg(test)]
mod test {
    use crate::ir::{TyInfo, Tys};

    macro_rules! assert_ty {
            (
                $({ $(let $ident:ident = $value:expr;)* },)?
                ty => [$($ty:tt)*],
                expected => [$($expected:tt)*] $(,)?
            ) => {
                #[allow(unused_mut)]
                let mut tys = Tys::new();

                $($(
                    let $ident = tys.find_or_insert($value);
                )*)?

                assert_eq!(
                    ir_ty!([tys] $($ty)*),
                    tys.find_or_insert($($expected)*)
                );
            };
        }

    mod primitive {
        use super::*;

        #[test]
        fn u8() {
            assert_ty! {
                ty => [u8],
                expected => [TyInfo::U8],
            };
        }

        #[test]
        fn i8() {
            assert_ty! {
                ty => [i8],
                expected => [TyInfo::I8]
            };
        }
    }

    mod reference {
        use super::*;

        #[test]
        fn ref_primitive() {
            assert_ty! {
                {
                    let inner = TyInfo::U8;
                },
                ty => [&u8],
                expected => [TyInfo::Ref(inner)]
            };
        }

        #[test]
        fn ref_ref_primitive() {
            assert_ty! {
                {
                    let inner = TyInfo::U8;
                    let inner_ref = TyInfo::Ref(inner);
                },
                // HACK: When using `tt`, the tokeniser will interpret `&&` as boolean `AND`,
                // rather than a reference of a reference. This is mitigated by separating them
                // with a space.
                ty => [& &u8],
                expected => [TyInfo::Ref(inner_ref)]
            };
        }

        #[test]
        fn ref_array() {
            assert_ty! {
                {
                    let inner = TyInfo::U8;
                    let array = TyInfo::Array { length: 3, ty: inner };
                },
                ty => [&[u8; 3]],
                expected => [TyInfo::Ref(array)]
            };
        }
    }

    mod array {
        use super::*;

        #[test]
        fn simple_array() {
            assert_ty! {
                {
                    let inner = TyInfo::U8;
                },
                ty => [[u8; 3]],
                expected => [TyInfo::Array { ty: inner, length: 3 }],
            }
        }

        #[test]
        fn nested_array() {
            assert_ty! {
                {
                    let inner = TyInfo::U8;
                    let inner_array = TyInfo::Array { length: 10, ty: inner };
                },
                ty => [[[u8; 10]; 3]],
                expected => [TyInfo::Array { ty: inner_array, length: 3 }],
            }
        }
    }
}
