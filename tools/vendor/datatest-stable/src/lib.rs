// Copyright (c) The datatest-stable Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

//! `datatest-stable` is a test harness intended to write *file-driven* or *data-driven* tests,
//! where individual test case fixtures are specified as files and not as code.
//!
//! Given:
//!
//! * a test `my_test` that accepts a path, and optionally the contents as input
//! * a directory to look for files (test fixtures) in
//! * a pattern to match files on
//!
//! `datatest-stable` will call the `my_test` function once per matching file in
//! the directory. Directory traversals are recursive.
//!
//! `datatest-stable` works with [cargo nextest](https://nexte.st/), and is part
//! of the [nextest-rs organization](https://github.com/nextest-rs/) on GitHub.
//! With nextest, each test case is represented as a separate test, and is run
//! as a separate process in parallel.
//!
//! # Usage
//!
//! 1. Configure the test target by setting `harness = false` in `Cargo.toml`:
//!
//! ```toml
//! [[test]]
//! name = "<test target name>"
//! harness = false
//! ```
//!
//! 2. Call the `datatest_stable::harness!` macro as:
//!
//!   ```rust,ignore
//!   datatest_stable::harness! {
//!       { test = my_test, root = "path/to/fixtures", pattern = r".*" },
//!   }
//!   ```
//!
//! * `test` - The test function to be executed on each matching input. This function can be one
//!   of:
//!   * `fn(&Path) -> datatest_stable::Result<()>`
//!   * `fn(&Utf8Path) -> datatest_stable::Result<()>` ([`Utf8Path`](camino::Utf8Path) is part of the
//!      [`camino`] library, and is re-exported here for convenience.)
//!   * `fn(&P, String) -> datatest_stable::Result<()>` where `P` is `Path` or `Utf8Path`. If the
//!     extra `String` parameter is specified, the contents of the file will be loaded and passed in
//!     as a string (erroring out if that failed).
//!   * `fn(&P, Vec<u8>) -> datatest_stable::Result<()>` where `P` is `Path` or `Utf8Path`. If the
//!     extra `Vec<u8>` parameter is specified, the contents of the file will be loaded and passed
//!     in as a `Vec<u8>` (erroring out if that failed).
//!
//! * `root` - The path to the root directory where the input files (fixtures)
//!   live. Relative paths are resolved relative to the crate root (the directory where the crate's
//!   `Cargo.toml` is located).
//!
//!   `root` is an arbitrary expression that implements
//!   [`Display`](std::fmt::Display), such as `&str`, or a function call that
//!   returns a [`Utf8PathBuf`](camino::Utf8PathBuf).
//!
//! * `pattern` - a regex used to match against and select each file to be tested. Extended regexes
//!   with lookaround and backtracking are supported via the [`fancy_regex`] crate.
//!
//!   `pattern` is an arbitrary expression that implements [`Display`](std::fmt::Display), such as
//!   `&str`, or a function call that returns a `String`.
//!
//!   `pattern` is optional, and defaults to `r".*"` (match all files).
//!
//! The three parameters can be repeated if you have multiple sets of data-driven tests to be run:
//!
//! ```rust,ignore
//! datatest_stable::harness! {
//!     { test = testfn1, root = root1, pattern = pattern1 },
//!     { test = testfn2, root = root2 },
//! }
//! ```
//!
//! Trailing commas are optional.
//!
//! ## Relative and absolute paths
//!
//! The `pattern` argument is tested against the **relative** path of each file,
//! **excluding** the `root` prefix -- not the absolute path.
//!
//! The `Path` and `Utf8Path` passed into the test functions are created by
//! joining `root` to the relative path of the file.
//!
//! * If `root` is **relative**, the paths passed in are relative to the crate root.
//! * If `root` is **absolute**, the paths passed in are absolute.
//!
//! For uniformity, all relative paths use `/` as the path separator,
//! including on Windows, and all absolute paths use the platform's native
//! separator throughout.
//!
//! ## Examples
//!
//! This is an example test. Use it with `harness = false`.
//!
//! ```rust
//! use datatest_stable::Utf8Path;
//! use std::path::Path;
//!
//! fn my_test(path: &Path) -> datatest_stable::Result<()> {
//!     // ... write test here
//!
//!     Ok(())
//! }
//!
//! fn my_test_utf8(path: &Utf8Path, contents: String) -> datatest_stable::Result<()> {
//!     // ... write test here
//!
//!     Ok(())
//! }
//!
//! datatest_stable::harness! {
//!     { test = my_test, root = "path/to/fixtures" },
//!     {
//!         test = my_test_utf8,
//!         root = "path/to/fixtures",
//!         pattern = r"^.*\.txt$",
//!     },
//! }
//! ```
//!
//! If `path/to/fixtures` contains a file `foo/bar.txt`, then:
//!
//! * The pattern `r"^.*/*"` will match `foo/bar.txt`.
//! * `my_test` and `my_test_utf8` will be called with `"path/to/fixtures/foo/bar.txt"`.
//!
//! ## Embedding directories at compile time
//!
//! With the `include-dir` feature enabled, you can use the
//! [`include_dir`](https://docs.rs/include_dir) crate's [`include_dir!`] macro.
//! This allows you to embed directories into the binary at compile time.
//!
//! This is generally not recommended for rapidly-changing test data, since each
//! change will force a rebuild. But it can be useful for relatively-unchanging
//! data suites distributed separately, e.g. on crates.io.
//!
//! With the `include-dir` feature enabled, you can use:
//!
#![cfg_attr(feature = "include-dir", doc = "```rust")]
#![cfg_attr(not(feature = "include-dir"), doc = "```rust,ignore")]
//! // The `include_dir!` macro is re-exported for convenience.
//! use datatest_stable::include_dir;
//! use std::path::Path;
//!
//! fn my_test(path: &Path, contents: Vec<u8>) -> datatest_stable::Result<()> {
//!     // ... write test here
//!     Ok(())
//! }
//!
//! datatest_stable::harness! {
//!     { test = my_test, root = include_dir!("tests/files"), pattern = r"^.*\.json$" },
//! }
//! ```
//!
//! You can also use directories published as `static` items in upstream crates:
//!
#![cfg_attr(feature = "include-dir", doc = "```rust")]
#![cfg_attr(not(feature = "include-dir"), doc = "```rust,ignore")]
//! use datatest_stable::{include_dir, Utf8Path};
//!
//! // In the upstream crate:
//! pub static FIXTURES: include_dir::Dir<'static> =
//!     include_dir!("$CARGO_MANIFEST_DIR/tests/files");
//!
//! // In your test:
//! fn my_test(path: &Utf8Path, contents: String) -> datatest_stable::Result<()> {
//!     // ... write test here
//!     Ok(())
//! }
//!
//! datatest_stable::harness! {
//!     { test = my_test, root = &FIXTURES },
//! }
//! ```
//!
//! In this case, the passed-in `Path` and `Utf8Path` are always **relative** to
//! the root of the included directory. Like elsewhere in `datatest-stable`,
//! these relative paths always use forward slashes as separators, including on
//! Windows.
//!
//! Because the files don't exist on disk, the test functions must accept their
//! contents as either a `String` or a `Vec<u8>`. If the argument is not
//! provided, the harness will panic at runtime.
//!
//! ## Conditionally embedding directories
//!
//! It is also possible to conditionally include directories at compile time via
//! a feature flag. For example, you might have an internal-only `testing`
//! feature that you turn on locally, but users don't on crates.io. In that
//! case, you can use:
//!
#![cfg_attr(feature = "include-dir", doc = "```rust")]
#![cfg_attr(not(feature = "include-dir"), doc = "```rust,ignore")]
//! use datatest_stable::Utf8Path;
//!
//! // In the library itself:
//! pub mod fixtures {
//!     #[cfg(feature = "testing")]
//!     pub static FIXTURES: &str = "tests/files";
//!
//!     #[cfg(not(feature = "testing"))]
//!     pub static FIXTURES: include_dir::Dir<'static> =
//!         include_dir::include_dir!("$CARGO_MANIFEST_DIR/tests/files");
//! }
//!
//! // In the test:
//! fn my_test(path: &Utf8Path, contents: String) -> datatest_stable::Result<()> {
//!     // ... write test here
//!     Ok(())
//! }
//!
//! datatest_stable::harness! {
//!     { test = my_test, root = &fixtures::FIXTURES, pattern = r"^inputs/.*$" },
//! }
//! ```
//!
//! In this case, note that `path` will be relative to the **crate directory**
//! (e.g. `tests/files/foo/bar.txt`) if `FIXTURES` is a string, and relative to
//! the **include directory** (e.g. `foo/bar.txt`) if `FIXTURES` is a
//! [`Dir`](include_dir::Dir). Your test should be prepared to handle either
//! case.
//!
//! # Features
//!
//! * `include-dir`: Enables the `include_dir!` macro, which allows embedding
//!   directories at compile time. This feature is disabled by default.
//!
//! # Minimum supported Rust version (MSRV)
//!
//! The minimum supported Rust version is **Rust 1.72**. MSRV bumps may be accompanied by a minor
//! version update; at any time, Rust versions from at least the last 6 months are supported.
//!
//! # See also
//!
//! * [`datatest`](https://crates.io/crates/datatest): the original inspiration for this crate, with
//!   more features but targeting nightly Rust.
//! * [Data-driven testing](https://en.wikipedia.org/wiki/Data-driven_testing)

#![warn(missing_docs)]
#![cfg_attr(doc_cfg, feature(doc_cfg))]

mod data_source;
mod macros;
mod runner;

/// The result type for `datatest-stable` tests.
pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

#[doc(hidden)]
pub use self::data_source::{data_source_kinds, DataSource};
/// Not part of the public API, just used for macros.
#[doc(hidden)]
pub use self::runner::{runner, test_kinds, Requirements, TestFn};
/// A re-export of this type from the `camino` crate, since it forms part of function signatures.
#[doc(no_inline)]
pub use camino::Utf8Path;
/// A re-export of `include_dir!` from the `include_dir` crate, for convenience.
#[cfg(feature = "include-dir")]
#[doc(no_inline)]
pub use include_dir::include_dir;
