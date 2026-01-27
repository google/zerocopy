#[cfg(feature = "net")]
use crate::net;
use crate::parser::{DnsName, DomainName, EmailAddress};
use crate::{dns, domain, email};
#[cfg(feature = "net")]
use no_std_net as upstream;
#[cfg(feature = "psl")]
use psl::List;
use serde::de::{Error, Unexpected};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

impl Serialize for domain::Name<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

#[cfg(feature = "psl")]
impl<'de> Deserialize<'de> for domain::Name<'de> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let input = <&str>::deserialize(deserializer)?;
        List.parse_domain_name(input).map_err(|_| {
            let invalid = Unexpected::Str(input);
            Error::invalid_value(invalid, &"a domain name")
        })
    }
}

impl Serialize for dns::Name<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

#[cfg(feature = "psl")]
impl<'de> Deserialize<'de> for dns::Name<'de> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let input = <&str>::deserialize(deserializer)?;
        List.parse_dns_name(input).map_err(|_| {
            let invalid = Unexpected::Str(input);
            Error::invalid_value(invalid, &"a DNS name")
        })
    }
}

impl Serialize for email::Address<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

#[cfg(feature = "psl")]
impl<'de> Deserialize<'de> for email::Address<'de> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let input = <&str>::deserialize(deserializer)?;
        List.parse_email_address(input).map_err(|_| {
            let invalid = Unexpected::Str(input);
            Error::invalid_value(invalid, &"an email address")
        })
    }
}

impl Serialize for email::Host<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use email::Host;
        match self {
            Host::Domain(domain) => domain.serialize(serializer),
            Host::IpAddr(ip_addr) => ip_addr.serialize(serializer),
        }
    }
}

impl<'de> Deserialize<'de> for email::Host<'de> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let input = <&str>::deserialize(deserializer)?;
        email::Host::parse(&List, input).map_err(|_| {
            let invalid = Unexpected::Str(input);
            Error::invalid_value(invalid, &"an email host")
        })
    }
}

#[cfg(feature = "net")]
impl Serialize for net::Ipv4Addr {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

#[cfg(feature = "net")]
impl<'de> Deserialize<'de> for net::Ipv4Addr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let ip_addr = upstream::Ipv4Addr::deserialize(deserializer)?;
        Ok(Self(ip_addr))
    }
}

#[cfg(feature = "net")]
impl Serialize for net::Ipv6Addr {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

#[cfg(feature = "net")]
impl<'de> Deserialize<'de> for net::Ipv6Addr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let ip_addr = upstream::Ipv6Addr::deserialize(deserializer)?;
        Ok(Self(ip_addr))
    }
}

#[cfg(feature = "net")]
impl Serialize for net::IpAddr {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use net::IpAddr;
        match self {
            IpAddr::V4(ip_addr) => ip_addr.serialize(serializer),
            IpAddr::V6(ip_addr) => ip_addr.serialize(serializer),
        }
    }
}

#[cfg(feature = "net")]
impl<'de> Deserialize<'de> for net::IpAddr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        use upstream::IpAddr;
        match IpAddr::deserialize(deserializer)? {
            IpAddr::V4(ip_addr) => Ok(net::IpAddr::V4(net::Ipv4Addr(ip_addr))),
            IpAddr::V6(ip_addr) => Ok(net::IpAddr::V6(net::Ipv6Addr(ip_addr))),
        }
    }
}
