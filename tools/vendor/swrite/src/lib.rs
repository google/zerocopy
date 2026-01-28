//! [![CI](https://github.com/rusticstuff/swrite/actions/workflows/ci.yml/badge.svg)](https://github.com/rusticstuff/swrite/actions/workflows/ci.yml)
//! [![crates.io](https://img.shields.io/crates/v/swrite.svg)](https://crates.io/crates/swrite)
//! [![docs.rs](https://docs.rs/swrite/badge.svg)](https://docs.rs/swrite)
//! ![Minimum rustc version](https://img.shields.io/badge/rustc-1.30+-lightgray.svg)
//!
//! `swrite` is a tiny Rust crate providing the `swrite!` and `swriteln!` macros as
//! infallible alternatives to `write!` and `writeln!` for Strings. This is safe because
//! writing to a String never returns `Err(_)`.
//!
//! The implementation uses the `SWrite` trait. It is implemented for `String`.
//! With the `osstring` feature is enabled, it is also implemented for `std::ffi::OsString`.
//!
//! Minimum Supported Rust Version (MSRV):
//! - Without the `osstring` feature (default): 1.30.0
//! - With the `osstring` feature: 1.64.0
//!
//! # Usage
//!
//! In `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! swrite = "0.1.0"
//! ```
//!
//! In your Rust code:
//!
//! ```rust
//! use swrite::{SWrite, swrite, swriteln};
//! ```
//!
//! # Examples
//!
//! Using `swrite!` and `swriteln!` with a `String`:
//!
//! ```rust
//! use swrite::{SWrite, swrite, swriteln};
//!
//! let mut s = String::new();
//! swrite!(s, "Hello, {}! ", "world");
//! swriteln!(s, "The answer is {}.", 42);
//!
//! println!("{}", s);
//! ```
//!
//! Output:
//!
//! ```not_rust
//! Hello, world! The answer is 42.
//! ```
//!
//! # License
//!
//! This project is dual-licensed under [Apache 2.0](LICENSE-APACHE) and [MIT](LICENSE-MIT) licenses.

/// Write formatted text to the given `String`.
///
/// # Example
/// ```
/// use swrite::{SWrite, swrite};
/// let mut s = String::new();
/// swrite!(s, "The answer is {}.", 42);
/// ```
#[macro_export]
macro_rules! swrite {
    ($dst:expr, $($arg:tt)*) => {
        $dst.swrite_fmt(format_args!($($arg)*))
    };
}

/// Write formatted text to the given `String`, followed by a newline.
///
/// # Example
/// ```
/// use swrite::{SWrite, swriteln};
/// let mut s = String::new();
/// swriteln!(s, "The answer is {}.", 42);
/// ```
#[macro_export]
macro_rules! swriteln {
    ($dst:expr) => {
        $crate::swrite!($dst, "\n")
    };
    ($dst:expr,) => {
        $crate::swrite!($dst, "\n")
    };
    ($dst:expr, $($arg:tt)*) => {
        $dst.swrite_fmt_nl(format_args!($($arg)*))
    };
}

/// Implementing this trait allows using the `swrite!` and `swriteln!` macros.
pub trait SWrite {
    /// Write formatted text.
    ///
    /// For types implementing `std::fmt::Write` this is usually done with
    /// just a call to `std::fmt::Write::write_fmt` ignoring the result.
    ///
    /// Make sure that `write_fmt()` never returns `Err(_)`.
    fn swrite_fmt(&mut self, fmt: std::fmt::Arguments<'_>);

    /// Write formatted text to the given `String`, followed by a newline.
    ///
    /// For types implementing `std::fmt::Write` this is usually done with
    /// just a call to `std::fmt::Write::write_fmt`, followed by a type-specific
    /// way of appending a newline.
    ///
    /// Make sure that `write_fmt()` never returns `Err(_)`.
    fn swrite_fmt_nl(&mut self, fmt: std::fmt::Arguments<'_>);
}

impl SWrite for String {
    #[inline]
    fn swrite_fmt(&mut self, fmt: std::fmt::Arguments<'_>) {
        // write_fmt() never fails for Strings.
        let _ = std::fmt::Write::write_fmt(self, fmt);
    }

    #[inline]
    fn swrite_fmt_nl(&mut self, fmt: std::fmt::Arguments<'_>) {
        self.swrite_fmt(fmt);
        self.push('\n');
    }
}

#[cfg(feature = "osstring")]
impl SWrite for std::ffi::OsString {
    #[inline]
    fn swrite_fmt(&mut self, fmt: std::fmt::Arguments<'_>) {
        // write_fmt() never fails for OsStrings.
        let _ = std::fmt::Write::write_fmt(self, fmt);
    }

    #[inline]
    fn swrite_fmt_nl(&mut self, fmt: std::fmt::Arguments<'_>) {
        self.swrite_fmt(fmt);
        self.push("\n");
    }
}

#[cfg(all(test, feature = "osstring"))]
mod osstring_tests;
