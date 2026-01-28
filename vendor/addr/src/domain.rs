//! Domain name types

use crate::error::{Kind, Result};
use crate::matcher;
use core::fmt;
use psl_types::{List, Type};

/// Holds information about a particular domain name
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Name<'a> {
    full: &'a str,
    suffix: psl_types::Suffix<'a>,
}

impl<'a> Name<'a> {
    pub(crate) fn parse<T: List + ?Sized>(list: &T, name: &'a str) -> Result<Name<'a>> {
        let stripped = if name.ends_with('.') {
            name.get(..name.len() - 1).unwrap_or_default()
        } else {
            name
        };
        if stripped.contains('.') {
            matcher::is_domain_name(stripped)?;
        } else {
            matcher::is_label(stripped, true)?;
        }
        Ok(Self {
            suffix: list.suffix(name.as_bytes()).ok_or(Kind::InvalidDomain)?,
            full: name,
        })
    }

    /// Full domain name as a `str`
    pub const fn as_str(&self) -> &'a str {
        self.full
    }

    fn without_suffix(&self) -> Option<&'a str> {
        let domain_len = self.full.len();
        let suffix_len = self.suffix().len();
        if domain_len == suffix_len {
            return None;
        }
        self.full.get(..domain_len - suffix_len - 1)
    }

    /// The root domain (the registrable part)
    pub fn root(&self) -> Option<&'a str> {
        let offset = self
            .without_suffix()?
            .rfind('.')
            .map(|x| x + 1)
            .unwrap_or_default();
        self.full.get(offset..)
    }

    /// The part before the root domain (aka. subdomain)
    pub fn prefix(&self) -> Option<&'a str> {
        let domain_len = self.full.len();
        let root_len = self.root()?.len();
        if domain_len == root_len {
            return None;
        }
        self.full.get(..domain_len - root_len - 1)
    }

    /// The domain name suffix (extension)
    pub fn suffix(&self) -> &'a str {
        let offset = self.full.len() - self.suffix.as_bytes().len();
        &self.full[offset..]
    }

    /// Whether the suffix of the domain name is in the Public Suffix List
    pub fn has_known_suffix(&self) -> bool {
        self.suffix.is_known()
    }

    /// Whether this an ICANN delegated suffix
    ///
    /// ICANN domains are those delegated by ICANN or part of the IANA root
    /// zone database
    pub fn is_icann(&self) -> bool {
        self.suffix.typ() == Some(Type::Icann)
    }

    /// Whether this is a private party delegated suffix
    ///
    /// PRIVATE domains are amendments submitted by the domain holder, as an
    /// expression of how they operate their domain security policy
    pub fn is_private(&self) -> bool {
        self.suffix.typ() == Some(Type::Private)
    }
}

impl fmt::Display for Name<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.full)
    }
}

impl PartialEq<&str> for Name<'_> {
    fn eq(&self, other: &&str) -> bool {
        self.full == *other
    }
}
