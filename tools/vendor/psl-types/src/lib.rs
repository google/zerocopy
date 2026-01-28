//! Common types for the public suffix implementation crates
//!
//! The types in this crate assume that the input is valid
//! UTF-8 encoded domain names. If input is potentially invalid,
//! use a higher level crate like the `addr` crate.
//!
//! Some implentations may also assume that the domain name is
//! in lowercase and/or may only support looking up unicode
//! domain names.

#![no_std]
#![forbid(unsafe_code)]

use core::cmp::Ordering;
use core::hash::{Hash, Hasher};

/// A list of all public suffixes
pub trait List {
    /// Finds the suffix information of the given input labels
    ///
    /// *NB:* `labels` must be in reverse order
    fn find<'a, T>(&self, labels: T) -> Info
    where
        T: Iterator<Item = &'a [u8]>;

    /// Get the public suffix of the domain
    #[inline]
    fn suffix<'a>(&self, name: &'a [u8]) -> Option<Suffix<'a>> {
        let mut labels = name.rsplit(|x| *x == b'.');
        let fqdn = if name.ends_with(b".") {
            labels.next();
            true
        } else {
            false
        };
        let Info { mut len, typ } = self.find(labels);
        if fqdn {
            len += 1;
        }
        if len == 0 {
            return None;
        }
        let offset = name.len() - len;
        let bytes = name.get(offset..)?;
        Some(Suffix { bytes, fqdn, typ })
    }

    /// Get the registrable domain
    #[inline]
    fn domain<'a>(&self, name: &'a [u8]) -> Option<Domain<'a>> {
        let suffix = self.suffix(name)?;
        let name_len = name.len();
        let suffix_len = suffix.bytes.len();
        if name_len < suffix_len + 2 {
            return None;
        }
        let offset = name_len - (1 + suffix_len);
        let subdomain = name.get(..offset)?;
        let root_label = subdomain.rsplitn(2, |x| *x == b'.').next()?;
        let registrable_len = root_label.len() + 1 + suffix_len;
        let offset = name_len - registrable_len;
        let bytes = name.get(offset..)?;
        Some(Domain { bytes, suffix })
    }
}

impl<L: List> List for &'_ L {
    #[inline]
    fn find<'a, T>(&self, labels: T) -> Info
    where
        T: Iterator<Item = &'a [u8]>,
    {
        (*self).find(labels)
    }
}

/// Type of suffix
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Type {
    Icann,
    Private,
}

/// Information about the suffix
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Info {
    pub len: usize,
    pub typ: Option<Type>,
}

/// The suffix of a domain name
#[derive(Copy, Clone, Eq, Debug)]
pub struct Suffix<'a> {
    bytes: &'a [u8],
    fqdn: bool,
    typ: Option<Type>,
}

impl<'a> Suffix<'a> {
    /// Builds a new suffix
    #[inline]
    #[must_use]
    #[doc(hidden)]
    pub fn new(bytes: &[u8], typ: Option<Type>) -> Suffix<'_> {
        Suffix {
            bytes,
            typ,
            fqdn: bytes.ends_with(b"."),
        }
    }

    /// The suffix as bytes
    #[inline]
    #[must_use]
    pub const fn as_bytes(&self) -> &'a [u8] {
        self.bytes
    }

    /// Whether or not the suffix is fully qualified (i.e. it ends with a `.`)
    #[inline]
    #[must_use]
    pub const fn is_fqdn(&self) -> bool {
        self.fqdn
    }

    /// Whether this is an `ICANN`, `private` or unknown suffix
    #[inline]
    #[must_use]
    pub const fn typ(&self) -> Option<Type> {
        self.typ
    }

    /// Returns the suffix with a trailing `.` removed
    #[inline]
    #[must_use]
    pub fn trim(mut self) -> Self {
        if self.fqdn {
            self.bytes = &self.bytes[..self.bytes.len() - 1];
            self.fqdn = false;
        }
        self
    }

    /// Whether or not this is a known suffix (i.e. it is explicitly in the public suffix list)
    // Could be const but Isahc needs support for Rust v1.41
    #[inline]
    #[must_use]
    pub fn is_known(&self) -> bool {
        self.typ.is_some()
    }
}

impl PartialEq for Suffix<'_> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.trim().bytes == strip_dot(other.bytes)
    }
}

impl PartialEq<&[u8]> for Suffix<'_> {
    #[inline]
    fn eq(&self, other: &&[u8]) -> bool {
        self.trim().bytes == strip_dot(other)
    }
}

impl PartialEq<&str> for Suffix<'_> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        self.trim().bytes == strip_dot(other.as_bytes())
    }
}

impl Ord for Suffix<'_> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.trim().bytes.cmp(strip_dot(other.bytes))
    }
}

impl PartialOrd for Suffix<'_> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.trim().bytes.cmp(strip_dot(other.bytes)))
    }
}

impl Hash for Suffix<'_> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.trim().bytes.hash(state);
    }
}

/// A registrable domain name
#[derive(Copy, Clone, Eq, Debug)]
pub struct Domain<'a> {
    bytes: &'a [u8],
    suffix: Suffix<'a>,
}

impl<'a> Domain<'a> {
    /// Builds a root domain
    #[inline]
    #[must_use]
    #[doc(hidden)]
    pub const fn new(bytes: &'a [u8], suffix: Suffix<'a>) -> Domain<'a> {
        Domain { bytes, suffix }
    }

    /// The domain name as bytes
    #[inline]
    #[must_use]
    pub const fn as_bytes(&self) -> &'a [u8] {
        self.bytes
    }

    /// The public suffix of this domain name
    #[inline]
    #[must_use]
    pub const fn suffix(&self) -> Suffix<'_> {
        self.suffix
    }

    /// Returns the domain with a trailing `.` removed
    #[inline]
    #[must_use]
    pub fn trim(mut self) -> Self {
        if self.suffix.fqdn {
            self.bytes = &self.bytes[..self.bytes.len() - 1];
            self.suffix = self.suffix.trim();
        }
        self
    }
}

impl PartialEq for Domain<'_> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.trim().bytes == strip_dot(other.bytes)
    }
}

impl PartialEq<&[u8]> for Domain<'_> {
    #[inline]
    fn eq(&self, other: &&[u8]) -> bool {
        self.trim().bytes == strip_dot(other)
    }
}

impl PartialEq<&str> for Domain<'_> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        self.trim().bytes == strip_dot(other.as_bytes())
    }
}

impl Ord for Domain<'_> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.trim().bytes.cmp(strip_dot(other.bytes))
    }
}

impl PartialOrd for Domain<'_> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.trim().bytes.cmp(strip_dot(other.bytes)))
    }
}

impl Hash for Domain<'_> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.trim().bytes.hash(state);
    }
}

#[inline]
fn strip_dot(bytes: &[u8]) -> &[u8] {
    if bytes.ends_with(b".") {
        &bytes[..bytes.len() - 1]
    } else {
        bytes
    }
}

#[cfg(test)]
mod test {
    use super::{Info, List as Psl};

    struct List;

    impl Psl for List {
        fn find<'a, T>(&self, mut labels: T) -> Info
        where
            T: Iterator<Item = &'a [u8]>,
        {
            match labels.next() {
                Some(label) => Info {
                    len: label.len(),
                    typ: None,
                },
                None => Info { len: 0, typ: None },
            }
        }
    }

    #[test]
    fn www_example_com() {
        let domain = List.domain(b"www.example.com").expect("domain name");
        assert_eq!(domain, "example.com");
        assert_eq!(domain.suffix(), "com");
    }

    #[test]
    fn example_com() {
        let domain = List.domain(b"example.com").expect("domain name");
        assert_eq!(domain, "example.com");
        assert_eq!(domain.suffix(), "com");
    }

    #[test]
    fn example_com_() {
        let domain = List.domain(b"example.com.").expect("domain name");
        assert_eq!(domain, "example.com.");
        assert_eq!(domain.suffix(), "com.");
    }

    #[test]
    fn fqdn_comparisons() {
        let domain = List.domain(b"example.com.").expect("domain name");
        assert_eq!(domain, "example.com");
        assert_eq!(domain.suffix(), "com");
    }

    #[test]
    fn non_fqdn_comparisons() {
        let domain = List.domain(b"example.com").expect("domain name");
        assert_eq!(domain, "example.com.");
        assert_eq!(domain.suffix(), "com.");
    }

    #[test]
    fn self_comparisons() {
        let fqdn = List.domain(b"example.com.").expect("domain name");
        let non_fqdn = List.domain(b"example.com").expect("domain name");
        assert_eq!(fqdn, non_fqdn);
        assert_eq!(fqdn.suffix(), non_fqdn.suffix());
    }

    #[test]
    fn btreemap_comparisons() {
        extern crate alloc;
        use alloc::collections::BTreeSet;

        let mut domain = BTreeSet::new();
        let mut suffix = BTreeSet::new();

        let fqdn = List.domain(b"example.com.").expect("domain name");
        domain.insert(fqdn);
        suffix.insert(fqdn.suffix());

        let non_fqdn = List.domain(b"example.com").expect("domain name");
        assert!(domain.contains(&non_fqdn));
        assert!(suffix.contains(&non_fqdn.suffix()));
    }

    #[test]
    fn hashmap_comparisons() {
        extern crate std;
        use std::collections::HashSet;

        let mut domain = HashSet::new();
        let mut suffix = HashSet::new();

        let fqdn = List.domain(b"example.com.").expect("domain name");
        domain.insert(fqdn);
        suffix.insert(fqdn.suffix());

        let non_fqdn = List.domain(b"example.com").expect("domain name");
        assert!(domain.contains(&non_fqdn));
        assert!(suffix.contains(&non_fqdn.suffix()));
    }

    #[test]
    fn com() {
        let domain = List.domain(b"com");
        assert_eq!(domain, None);

        let suffix = List.suffix(b"com").expect("public suffix");
        assert_eq!(suffix, "com");
    }

    #[test]
    fn root() {
        let domain = List.domain(b".");
        assert_eq!(domain, None);

        let suffix = List.suffix(b".").expect("public suffix");
        assert_eq!(suffix, ".");
    }

    #[test]
    fn empty_string() {
        let domain = List.domain(b"");
        assert_eq!(domain, None);

        let suffix = List.suffix(b"");
        assert_eq!(suffix, None);
    }

    #[test]
    #[allow(dead_code)]
    fn accessors_borrow_correctly() {
        fn return_suffix(domain: &str) -> &[u8] {
            let suffix = List.suffix(domain.as_bytes()).unwrap();
            suffix.as_bytes()
        }

        fn return_domain(name: &str) -> &[u8] {
            let domain = List.domain(name.as_bytes()).unwrap();
            domain.as_bytes()
        }
    }
}
