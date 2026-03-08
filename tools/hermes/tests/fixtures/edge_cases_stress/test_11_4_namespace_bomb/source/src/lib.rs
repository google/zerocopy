
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
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding() {}
