
macro_rules! make_struct {
    ($name:ident) => {
        pub struct $name {
            pub f: u32,
        }
    };
}

make_struct!(GeneratedStruct);


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding() {}
