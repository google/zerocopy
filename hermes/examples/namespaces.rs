pub mod outer {
    pub mod inner {
        /// ```lean, hermes, spec
        /// ```
        pub fn deep_function(x: u32) -> u32 {
            x + 1
        }
    }
}

pub fn call_deep() -> u32 {
    outer::inner::deep_function(42)
}

fn main() {}
