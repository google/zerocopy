extern crate proc_macro;

use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn passthrough(_: TokenStream, item: TokenStream) -> TokenStream {
    std::thread::sleep(std::time::Duration::from_secs(5));
    item
}
