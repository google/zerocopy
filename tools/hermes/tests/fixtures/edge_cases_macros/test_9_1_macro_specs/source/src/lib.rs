
macro_rules! make_fn_with_spec {
    ($name:ident, $val:expr) => {
        /// @spec
        /// ensures:
///   ///   ///   ret = $val
        pub fn $name() -> u32 {
            $val
        }
    };
}

make_fn_with_spec!(generated_fn, 42);


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold dummy_hermes_padding at *
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
