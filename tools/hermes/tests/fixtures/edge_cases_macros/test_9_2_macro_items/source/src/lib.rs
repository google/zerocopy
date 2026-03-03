
macro_rules! make_struct {
    ($name:ident) => {
        pub struct $name {
            pub f: u32,
        }
    };
}

make_struct!(GeneratedStruct);


/// ```lean, hermes
/// proof
///   sorry
/// ```
pub fn dummy_hermes_padding() {}
