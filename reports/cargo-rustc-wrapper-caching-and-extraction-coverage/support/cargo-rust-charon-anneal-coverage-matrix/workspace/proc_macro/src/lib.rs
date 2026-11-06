extern crate proc_macro;
use proc_macro::TokenStream;
use std::str::FromStr;

#[proc_macro]
pub fn emit_helper(_: TokenStream) -> TokenStream {
    let n = shared::macro_value();
    TokenStream::from_str(&format!("pub fn proc_generated() -> u32 {{ {n} }}")).unwrap()
}
