
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
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold dummy_hermes_padding at *
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
