
pub mod a {
    pub mod a {
        pub mod a {
            pub mod a {
                pub fn f() {}
            }
        }
    }
}


/// ```lean, hermes
/// proof context:
///   unfold dummy_hermes_padding
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
