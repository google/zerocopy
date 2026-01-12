test_normalize! {
    INPUT="tests/ui/not-repeatable.rs"
"
error[E0599]: no method named `quote_into_iter` found for struct `std::net::Ipv4Addr` in the current scope
  --> /git/trybuild/test_suite/tests/ui/not-repeatable.rs:6:13
   |
6  |     let _ = quote! { #(#ip)* };
   |             ^^^^^^^^^^^^^^^^^^ method not found in `std::net::Ipv4Addr`
   |
  ::: /rustlib/src/rust/src/libstd/net/ip.rs:83:1
  ::: /rustlib/src/rust/library/std/src/net/ip.rs:83:1
   |
83 | pub struct Ipv4Addr {
   | -------------------
   | |
   | doesn't satisfy `std::net::Ipv4Addr: quote::to_tokens::ToTokens`
" "
error[E0599]: no method named `quote_into_iter` found for struct `std::net::Ipv4Addr` in the current scope
 --> tests/ui/not-repeatable.rs:6:13
  |
6 |     let _ = quote! { #(#ip)* };
  |             ^^^^^^^^^^^^^^^^^^ method not found in `std::net::Ipv4Addr`
  |
 ::: $RUST/src/libstd/net/ip.rs
 ::: $RUST/std/src/net/ip.rs
  |
  | pub struct Ipv4Addr {
  | -------------------
  | |
  | doesn't satisfy `std::net::Ipv4Addr: quote::to_tokens::ToTokens`
"}
