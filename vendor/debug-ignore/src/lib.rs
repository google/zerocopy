// Copyright (c) The debug-ignore Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! This library contains `DebugIgnore`, a newtype wrapper that causes a field to be skipped while
//! printing out `Debug` output.
//!
//! # Examples
//!
//! ```rust
//! use debug_ignore::DebugIgnore;
//!
//! // Some structs have many fields with large `Debug` implementations.
//! #[derive(Debug)]
//! struct InnerStructWithLotsOfDebugInfo {
//!     field: &'static str,
//!     // ...
//! }
//!
//! #[derive(Debug)]
//! pub struct PublicStruct {
//!     inner: DebugIgnore<InnerStructWithLotsOfDebugInfo>,
//! }
//!
//! impl PublicStruct {
//!     pub fn new() -> Self {
//!         Self {
//!             // DebugIgnore<T> has a `From<T>` impl for the inner type; you can also construct
//!             // one explicitly.
//!             inner: InnerStructWithLotsOfDebugInfo { field: "field", /* ... */ }.into(),
//!         }
//!     }
//! }
//!
//! let x = PublicStruct::new();
//! assert_eq!(format!("{:?}", x), "PublicStruct { inner: ... }");
//!
//! // Fields within inner can still be accessed through the Deref impl.
//! assert_eq!(x.inner.field, "field");
//! ```
//!
//! # Why?
//!
//! Some structs have many fields with large `Debug` implementations. It can be really annoying to
//! go through a ton of usually irrelevant `Debug` output.
//!
//! `DebugIgnore` is a zero-cost, zero-compile-time way to achieve a `Debug` impl that skips over a
//! field.
//!
//! # Optional features
//!
//! `serde`: `serde` support with `#[serde(transparent)]`.
//!
//! # Rust version support
//!
//! The MSRV is **Rust 1.34** though this crate likely builds with older versions. This crate is
//! too trivial to require anything more recent.
//!
//! Optional features may require newer versions of Rust.
//!
//! # Alternatives
//!
//! * Implement `Debug` by hand.
//! * [`derivative`](https://crates.io/crates/derivative) has greater control over the behavior of
//!   `Debug` impls, at the cost of a compile-time proc-macro dependency.

#![no_std]

use core::{
    fmt,
    ops::{Deref, DerefMut},
    str::FromStr,
};

/// A newtype wrapper that causes the field within to be ignored while printing out `Debug` output.
///
/// For more, see the [crate documentation](self).
#[derive(Copy, Clone, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct DebugIgnore<T: ?Sized>(pub T);

/// The point of this struct.
impl<T: ?Sized> fmt::Debug for DebugIgnore<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "...")
    }
}

// ---
// Other trait impls
// ---

impl<T> From<T> for DebugIgnore<T> {
    #[inline]
    fn from(t: T) -> Self {
        Self(t)
    }
}

impl<T: ?Sized> Deref for DebugIgnore<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: ?Sized> DerefMut for DebugIgnore<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: FromStr> FromStr for DebugIgnore<T> {
    type Err = T::Err;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse().map(DebugIgnore)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for DebugIgnore<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: ?Sized, Q: ?Sized> AsRef<Q> for DebugIgnore<T>
where
    T: AsRef<Q>,
{
    #[inline]
    fn as_ref(&self) -> &Q {
        self.0.as_ref()
    }
}
