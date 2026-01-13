test_normalize! {"
error[E0277]: the trait bound `__T: serde::ser::Serialize` is not satisfied
  --> src/main.rs:5:1
   |
5  | serialize_trait_object!(MyTrait);
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ the trait `serde::ser::Serialize` is not implemented for `__T`
   |
   = note: required for `__T` to implement `erased_serde::Serialize`
note: required by a bound in `require_erased_serialize_impl`
  --> /home/david/.cargo/registry/src/index.crates.io-6f17d22bba15001f/erased-serde-0.3.28/src/private.rs:14:17
   |
12 | pub fn require_erased_serialize_impl<T>()
   |        ----------------------------- required by a bound in this function
13 | where
14 |     T: ?Sized + crate::Serialize,
   |                 ^^^^^^^^^^^^^^^^ required by this bound in `require_erased_serialize_impl`
   = note: this error originates in the macro `$crate::__internal_serialize_trait_object` which comes from the expansion of the macro `serialize_trait_object` (in Nightly builds, run with -Z macro-backtrace for more info)
help: consider further restricting this bound
   |
5  | serialize_trait_object!(MyTrait + serde::ser::Serialize);
   |                                 +++++++++++++++++++++++
" "
error[E0277]: the trait bound `__T: serde::ser::Serialize` is not satisfied
 --> src/main.rs:5:1
  |
5 | serialize_trait_object!(MyTrait);
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ the trait `serde::ser::Serialize` is not implemented for `__T`
  |
  = note: required for `__T` to implement `erased_serde::Serialize`
note: required by a bound in `require_erased_serialize_impl`
 --> $CARGO/erased-serde-0.3.28/src/private.rs
  |
  | pub fn require_erased_serialize_impl<T>()
  |        ----------------------------- required by a bound in this function
  | where
  |     T: ?Sized + crate::Serialize,
  |                 ^^^^^^^^^^^^^^^^ required by this bound in `require_erased_serialize_impl`
  = note: this error originates in the macro `$crate::__internal_serialize_trait_object` which comes from the expansion of the macro `serialize_trait_object` (in Nightly builds, run with -Z macro-backtrace for more info)
help: consider further restricting this bound
  |
5 | serialize_trait_object!(MyTrait + serde::ser::Serialize);
  |                                 +++++++++++++++++++++++
"}
