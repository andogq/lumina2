/// This macro internally uses a number of 'variables' to track state. These variables are in the
/// form `key=[value]`.
///
/// - `local`: The ident of the local the place is derived from, which may or may not be present.
/// - `post`: Projections to be appended to the end of the projection list. This is primarily for
///   'prefix' projections, such as de-referencing (`*`). These projections will be inserted as-is,
///   so the variable should be a well-formed comma separated list.
/// - `projection`: Collection of comma separated [`Projections`] which have been parsed.
/// - `nested`: Temporary storage for in-progress parsing when parsing a nested expression. Will be
///   in the form `[post=[post projections] other tokens]`.
///
/// [`Projections`]: crate::ir::Projection
#[macro_export(local_inner_macros)]
macro_rules! ir_place {
    // Matches a standalone ident. If there is no `local`, it's safe to assume this ident is the
    // local of the place. This rule will *not* match if there is already a `local`.
    (step local=[] post=[$($post:tt)*] projection=[$($projection:tt)*] nested=[$($nested:tt)*] $local:ident $($rest:tt)*) => {
        ir_place!(
            step
            local=[$local]
            post=[$($post)*]
            projection=[$($projection)*]
            nested=[$($nested)*]
            $($rest)*
        )
    };

    // Match `[index]`, for indexing projections. `index` must be an identifier.
    (step local=[$($local:ident)?] post=[$($post:tt)*] projection=[$($projection:tt)*] nested=[$($nested:tt)*] [$index:ident] $($rest:tt)*) => {
        ir_place!(
            step
            local=[$($local)?]
            post=[$($post)*]
            projection=[$($projection)* $crate::ir::Projection::Index($index),]
            nested=[$($nested)*]
            $($rest)*
        )
    };

    // Match `()`, allowing for precedence. This 'pauses' the current parsing, by moving anything
    // in `post` and all remaining tokens into `nested`. This allows the tokens within the brackets
    // to be parsed, before resuming the outer tokens once complete.
    (step local=[$($local:ident)?] post=[$($post:tt)*] projection=[$($projection:tt)*] nested=[$($nested:tt)*] ($($inner:tt)*) $($outer:tt)*) => {
        ir_place!(
            step
            local=[$($local)?]
            post=[]
            projection=[$($projection)*]
            nested=[[post=[$($post)*] $($outer)*] $($nested)*]
            $($inner)*
        )
    };

    // Match `*` (dereference operator). This is a prefix operator, so add it to `post` so that
    // it's appended to the list of projections.
    (step local=[$($local:ident)?] post=[$($post:tt)*] projection=[$($projection:tt)*] nested=[$($nested:tt)*] * $($rest:tt)*) => {
        ir_place!(
            step
            local=[$($local)?]
            post=[$($post)* $crate::ir::Projection::Deref,]
            projection=[$($projection)*]
            nested=[$($nested)*]
            $($rest)*
        )
    };

    // No more projection tokens, however there is at least one nested item. Move nested `post`
    // into top-level `post`, and nested tokens into the top-level macro. This will append any
    // existing `post` tokens to the projection.
    (step local=[$($local:ident)?] post=[$($post:tt)*] projection=[$($projection:tt)*] nested=[[post=[$($nested_post:tt)*] $($rest:tt)*] $($nested:tt)*]) => {
        ir_place!(
            step
            local=[$($local)?]
            post=[$($nested_post)*]
            projection=[$($projection)* $($post)*]
            nested=[$($nested)*]
            $($rest)*
        )
    };

    // End case, no other projection tokens found. Projections within `post` are appended to
    // `projection`, and everything is returned as a `Place` instantiation.
    (step local=[$local:ident] post=[$($post:tt)*] projection=[$($projection:tt)*] nested=[]) => {
        $crate::ir::Place {
            local: $local,
            projection: ::std::vec![$($projection)* $($post)*],
        }
    };

    // Helper for if no other projection rules match. Indicates that the projection does not have
    // any matched rules.
    (step local=[$local:ident] post=[$($post:tt)*] projection=[$($projection:tt)*] nested=[$($nested:tt)*] $($rest:tt)+) => {
        ::std::compile_error!(::std::concat!("unknown projection: ", ::std::stringify!($($rest)+)))
    };

    // Entry point of the macro. All variables start uninitialised.
    ($($tokens:tt)*) => {
        ir_place!(
            step
            local=[]
            post=[]
            projection=[]
            nested=[]
            $($tokens)*
        )
    };
}

#[cfg(test)]
mod test {
    #![allow(clippy::just_underscores_and_digits)]
    use crate::ir::{Local, Place, Projection};

    #[test]
    fn local() {
        let _0 = Local::zero();

        assert_eq!(
            ir_place!(_0),
            Place {
                local: _0,
                projection: vec![]
            }
        );
    }

    #[test]
    fn index_access() {
        let _0 = Local::zero();
        let _1 = Local::of(1);

        assert_eq!(
            ir_place!(_0[_1]),
            Place {
                local: _0,
                projection: vec![Projection::Index(_1)]
            }
        );
    }

    #[test]
    fn deref() {
        let _0 = Local::zero();

        assert_eq!(
            ir_place!(*_0),
            Place {
                local: _0,
                projection: vec![Projection::Deref]
            }
        );
    }

    #[test]
    fn deref_index() {
        let _0 = Local::zero();
        let _1 = Local::of(1);

        assert_eq!(
            ir_place!(*_0[_1]),
            Place {
                local: _0,
                projection: vec![Projection::Index(_1), Projection::Deref],
            }
        );
    }

    #[test]
    fn parens_no_projection() {
        let _0 = Local::zero();

        assert_eq!(
            ir_place!((_0)),
            Place {
                local: _0,
                projection: vec![]
            }
        )
    }

    #[test]
    fn parens_with_deref() {
        let _0 = Local::zero();

        assert_eq!(
            ir_place!((*_0)),
            Place {
                local: _0,
                projection: vec![Projection::Deref]
            }
        )
    }

    #[test]
    fn parens_with_deref_index() {
        let _0 = Local::zero();
        let _1 = Local::of(1);

        assert_eq!(
            ir_place!((*_0)[_1]),
            Place {
                local: _0,
                projection: vec![Projection::Deref, Projection::Index(_1)]
            }
        )
    }

    #[test]
    fn parens_with_deref_index_deref() {
        let _0 = Local::zero();
        let _1 = Local::of(1);

        assert_eq!(
            ir_place!(*(*_0)[_1]),
            Place {
                local: _0,
                projection: vec![Projection::Deref, Projection::Index(_1), Projection::Deref]
            }
        )
    }

    #[test]
    fn complex_parens() {
        let _0 = Local::zero();
        let _1 = Local::of(1);
        let _2 = Local::of(2);

        assert_eq!(
            ir_place!(*(*(*_0)[_1])[_2]),
            Place {
                local: _0,
                projection: vec![
                    Projection::Deref,
                    Projection::Index(_1),
                    Projection::Deref,
                    Projection::Index(_2),
                    Projection::Deref
                ]
            }
        )
    }
}
