#![crate_type = "proc-macro"]

extern crate proc_macro;

use proc_macro::TokenStream;

#[proc_macro]
pub fn thing(input: TokenStream) -> TokenStream {
    std::thread::sleep(std::time::Duration::from_secs(5));
    input
}
