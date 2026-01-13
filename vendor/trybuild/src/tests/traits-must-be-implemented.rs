test_normalize! {"
error[E0599]: the method `anyhow_kind` exists for reference `&Error`, but its trait bounds were not satisfied
   --> src/main.rs:7:13
    |
4   | struct Error;
    | -------------
    | |
    | doesn't satisfy `Error: Into<anyhow::Error>`
    | doesn't satisfy `Error: anyhow::private::kind::TraitKind`
    | doesn't satisfy `Error: std::fmt::Display`
...
7   |     let _ = anyhow!(Error);
    |             ^^^^^^^^^^^^^^ method cannot be called on `&Error` due to unsatisfied trait bounds
    |
    = note: the following trait bounds were not satisfied:
            `Error: Into<anyhow::Error>`
            which is required by `Error: anyhow::private::kind::TraitKind`
            `Error: std::fmt::Display`
            which is required by `&Error: anyhow::private::kind::AdhocKind`
            `&Error: Into<anyhow::Error>`
            which is required by `&Error: anyhow::private::kind::TraitKind`
note: the following traits must be implemented
   --> /rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/convert/mod.rs:274:1
    |
274 | / pub trait Into<T>: Sized {
275 | |     /// Performs the conversion.
276 | |     #[stable(feature = \"rust1\", since = \"1.0.0\")]
277 | |     fn into(self) -> T;
278 | | }
    | |_^
    |
   ::: /rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/fmt/mod.rs:715:1
    |
715 | / pub trait Display {
716 | |     /// Formats the value using the given formatter.
717 | |     ///
718 | |     /// # Examples
...   |
738 | |     fn fmt(&self, f: &mut Formatter<'_>) -> Result;
739 | | }
    | |_^
    = note: this error originates in the macro `anyhow` (in Nightly builds, run with -Z macro-backtrace for more info)
" "
error[E0599]: the method `anyhow_kind` exists for reference `&Error`, but its trait bounds were not satisfied
 --> src/main.rs:7:13
  |
4 | struct Error;
  | -------------
  | |
  | doesn't satisfy `Error: Into<anyhow::Error>`
  | doesn't satisfy `Error: anyhow::private::kind::TraitKind`
  | doesn't satisfy `Error: std::fmt::Display`
...
7 |     let _ = anyhow!(Error);
  |             ^^^^^^^^^^^^^^ method cannot be called on `&Error` due to unsatisfied trait bounds
  |
  = note: the following trait bounds were not satisfied:
          `Error: Into<anyhow::Error>`
          which is required by `Error: anyhow::private::kind::TraitKind`
          `Error: std::fmt::Display`
          which is required by `&Error: anyhow::private::kind::AdhocKind`
          `&Error: Into<anyhow::Error>`
          which is required by `&Error: anyhow::private::kind::TraitKind`
note: the following traits must be implemented
 --> $RUST/core/src/convert/mod.rs
  |
  | / pub trait Into<T>: Sized {
  | |     /// Performs the conversion.
  | |     #[stable(feature = \"rust1\", since = \"1.0.0\")]
  | |     fn into(self) -> T;
  | | }
  | |_^
  |
 ::: $RUST/core/src/fmt/mod.rs
  |
  | / pub trait Display {
  | |     /// Formats the value using the given formatter.
  | |     ///
  | |     /// # Examples
... |
  | |     fn fmt(&self, f: &mut Formatter<'_>) -> Result;
  | | }
  | |_^
  = note: this error originates in the macro `anyhow` (in Nightly builds, run with -Z macro-backtrace for more info)
"}
