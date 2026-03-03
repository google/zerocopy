
macro_rules! make_fn_with_spec {
    ($name:ident, $val:expr) => {
        /// @spec
        /// ensures result = $val
        pub fn $name() -> u32 {
            $val
        }
    };
}

make_fn_with_spec!(generated_fn, 42);


/// ```lean, hermes
/// proof
///   sorry
/// ```
pub fn dummy_hermes_padding() {}
