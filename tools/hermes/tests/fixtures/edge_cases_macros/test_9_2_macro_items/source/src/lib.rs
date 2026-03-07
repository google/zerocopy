
macro_rules! make_struct {
    ($name:ident) => {
        pub struct $name {
            pub f: u32,
        }
    };
}

make_struct!(GeneratedStruct);


/// ```lean, hermes
/// proof context:
///   unfold dummy_hermes_padding
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
