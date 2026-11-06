extern crate proc_macro;
use proc_macro::TokenStream;

#[proc_macro]
pub fn emit_generated(_input: TokenStream) -> TokenStream {
    let delta = std::env::var("PROC_VALUE").unwrap_or_else(|_| "3".to_owned());
    format!("pub fn macro_generated(x: u32) -> u32 {{ x.wrapping_add({delta}) }}")
        .parse()
        .unwrap()
}
