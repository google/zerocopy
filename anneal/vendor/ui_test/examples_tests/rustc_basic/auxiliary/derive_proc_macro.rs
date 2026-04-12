//@compile-flags: --emit=link -C prefer-dynamic=no

#![crate_type = "proc-macro"]

extern crate proc_macro;

use proc_macro::TokenStream;

#[proc_macro_derive(Something)]
pub fn noop(_: TokenStream) -> TokenStream {
    std::thread::sleep(std::time::Duration::from_secs(5));
    TokenStream::new()
}
