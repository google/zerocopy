//! Network types
//!
//! This module only exists because `std::net` is not available in
//! `no_std` environments. It requires Rust v1.46.

use crate::error::Kind;
use core::str::FromStr;
use no_std_net as upstream;

/// An IPv4 address
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Ipv4Addr(pub(crate) upstream::Ipv4Addr);

impl Ipv4Addr {
    /// Returns the four eight-bit integers that make up this address.
    pub const fn octets(&self) -> [u8; 4] {
        self.0.octets()
    }
}

/// An IPv6 address
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Ipv6Addr(pub(crate) upstream::Ipv6Addr);

impl Ipv6Addr {
    /// Returns the sixteen eight-bit integers the IPv6 address consists of.
    pub const fn octets(&self) -> [u8; 16] {
        self.0.octets()
    }
}

/// An IP address
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum IpAddr {
    V4(Ipv4Addr),
    V6(Ipv6Addr),
}

impl FromStr for IpAddr {
    type Err = Kind;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.parse::<upstream::IpAddr>() {
            Ok(ip_addr) => match ip_addr {
                upstream::IpAddr::V4(ip_addr) => Ok(IpAddr::V4(Ipv4Addr(ip_addr))),
                upstream::IpAddr::V6(ip_addr) => Ok(IpAddr::V6(Ipv6Addr(ip_addr))),
            },
            Err(_) => Err(Kind::InvalidIpAddr),
        }
    }
}
