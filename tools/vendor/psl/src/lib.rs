//! A native Rust library for Mozilla's Public Suffix List

#![no_std]
#![forbid(unsafe_code)]

mod list;

#[cfg(feature = "helpers")]
use core::str;

pub use psl_types::{Domain, Info, List as Psl, Suffix, Type};

/// A static public suffix list
pub struct List;

impl Psl for List {
    #[inline]
    fn find<'a, T>(&self, labels: T) -> Info
    where
        T: Iterator<Item = &'a [u8]>,
    {
        list::lookup(labels)
    }
}

/// Get the public suffix of the domain
#[cfg(feature = "helpers")]
#[inline]
pub fn suffix(name: &[u8]) -> Option<Suffix<'_>> {
    List.suffix(name)
}

/// Get the public suffix of the domain
#[cfg(feature = "helpers")]
#[inline]
pub fn suffix_str(name: &str) -> Option<&str> {
    let bytes = suffix(name.as_bytes())?.trim().as_bytes();
    str::from_utf8(bytes).ok()
}

/// Get the registrable domain
#[cfg(feature = "helpers")]
#[inline]
pub fn domain(name: &[u8]) -> Option<Domain<'_>> {
    List.domain(name)
}

/// Get the registrable domain
#[cfg(feature = "helpers")]
#[inline]
pub fn domain_str(name: &str) -> Option<&str> {
    let bytes = domain(name.as_bytes())?.trim().as_bytes();
    str::from_utf8(bytes).ok()
}
