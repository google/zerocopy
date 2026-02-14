
macro_rules! make_struct {
    ($name:ident) => {
        pub struct $name {
            pub f: u32,
        }
    };
}

make_struct!(GeneratedStruct);
