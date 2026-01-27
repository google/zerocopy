//! Email address types

use crate::domain::Name;
use crate::error::{Kind, Result};
use crate::matcher;
#[cfg(feature = "net")]
#[cfg(not(feature = "std"))]
use crate::net::IpAddr;
use core::fmt;
#[cfg(not(any(feature = "net", feature = "std")))]
use core::str::FromStr;
use psl_types::List;
#[cfg(feature = "std")]
use std::net::IpAddr;

/// Holds information about a particular email address
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Address<'a> {
    full: &'a str,
    at_sign: usize,
    host: Host<'a>,
}

impl<'a> Address<'a> {
    pub(crate) fn parse<T: List + ?Sized>(list: &T, address: &'a str) -> Result<Address<'a>> {
        if address.chars().count() > 254 {
            return Err(Kind::EmailTooLong);
        }
        let at_sign = address.rfind('@').ok_or(Kind::NoAtSign)?;
        let local = address.get(..at_sign).ok_or(Kind::NoUserPart)?;
        matcher::is_email_local(local)?;
        let rest = address.get(at_sign + 1..).ok_or(Kind::NoHostPart)?;
        let host = Host::parse(list, rest)?;
        Ok(Self {
            host,
            at_sign,
            full: address,
        })
    }

    /// The full email address as a `str`
    pub const fn as_str(&self) -> &'a str {
        self.full
    }

    /// The host part of the email address
    pub const fn host(&self) -> Host<'a> {
        self.host
    }

    /// The user (local) part of the email address
    pub fn user(&self) -> &'a str {
        &self.full[..self.at_sign]
    }
}

impl fmt::Display for Address<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.full)
    }
}

impl PartialEq<&str> for Address<'_> {
    fn eq(&self, other: &&str) -> bool {
        self.full == *other
    }
}

// A placeholder IP address that can never be constructed
#[cfg(not(any(feature = "net", feature = "std")))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
#[doc(hidden)]
pub enum IpAddr {}

#[cfg(not(any(feature = "net", feature = "std")))]
impl FromStr for IpAddr {
    type Err = Kind;

    fn from_str(_: &str) -> Result<Self> {
        unreachable!()
    }
}

/// Information about the host part of an email address
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Host<'a> {
    Domain(Name<'a>),
    IpAddr(IpAddr),
}

impl<'a> Host<'a> {
    pub(crate) fn parse<T: List + ?Sized>(list: &T, host: &'a str) -> Result<Host<'a>> {
        if host.starts_with('[') && host.ends_with(']') {
            let host_len = host.len();
            if host_len < 3 {
                return Err(Kind::InvalidIpAddr);
            }
            if cfg!(not(any(feature = "net", feature = "std"))) {
                return Err(Kind::NetDisabled);
            }
            let ip_addr = host
                .get(1..host_len - 1)
                .ok_or(Kind::InvalidIpAddr)?
                .parse()?;
            Ok(Host::IpAddr(ip_addr))
        } else {
            Ok(Host::Domain(Name::parse(list, host)?))
        }
    }
}

#[cfg(test)]
mod test {
    use super::Address;
    use psl::List;

    #[test]
    fn parse() {
        // Valid email addresses
        Address::parse(&List, "johndoe@example.com").unwrap();
        Address::parse(&List, "john.doe@example.com").unwrap();
        Address::parse(&List, "john+doe@example.com").unwrap();
        Address::parse(&List, r#""john doe"@example.com"#).unwrap();

        // Invalid email addresses
        Address::parse(&List, "@example.com").unwrap_err();
        Address::parse(&List, r#""@example.com"#).unwrap_err();
        Address::parse(&List, " @example.com").unwrap_err();
    }

    #[test]
    fn user() {
        let email = Address::parse(&List, "johndoe@localhost").unwrap();
        assert_eq!(email.user(), "johndoe");
    }
}
