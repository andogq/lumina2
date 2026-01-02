/// Helper to implement `From` and `TryFrom` to/from an enum.
#[macro_export]
macro_rules! enum_conversion {
    ([$target:ident] $($variant:ident: $ty:ty),* $(,)?) => {
        $(
            impl From<$ty> for $target {
                fn from(value: $ty) -> Self {
                    Self::$variant(value)
                }
            }

            impl TryFrom<$target> for $ty {
                type Error = $target;

                fn try_from(value: $target) -> Result<Self, $target> {
                    #[allow(unreachable_patterns)]
                    match value {
                        $target::$variant(value) => Ok(value),
                        expression => Err(expression)
                    }
                }
            }
        )*
    };
}
