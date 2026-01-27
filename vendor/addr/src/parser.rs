//! Parser traits

use crate::{dns, domain, email, Result};
use psl_types::List;

/// Parses a domain using the list
pub trait DomainName {
    /// This method tries to stick to restrictions usually imposed by domain registries
    /// when registering domain names. If your input can potentially include additional
    /// characters allowed in DNS labels, like underscores, use `parse_dns_name` instead.
    fn parse_domain_name<'a>(&self, name: &'a str) -> Result<'a, domain::Name<'a>>;
}

impl<T> DomainName for T
where
    T: List,
{
    fn parse_domain_name<'a>(&self, name: &'a str) -> Result<'a, domain::Name<'a>> {
        domain::Name::parse(self, name).map_err(|kind| kind.error_with(name))
    }
}

/// Parses any arbitrary string that can be used as a key in a DNS database
pub trait DnsName {
    /// This method allows additional characters, like underscores, typically allowed
    /// in DNS labels but are not usually allowed by domain registries. For that
    /// use `parse_domain_name` instead.
    fn parse_dns_name<'a>(&self, name: &'a str) -> Result<'a, dns::Name<'a>>;
}

impl<T> DnsName for T
where
    T: List,
{
    fn parse_dns_name<'a>(&self, name: &'a str) -> Result<'a, dns::Name<'a>> {
        dns::Name::parse(self, name).map_err(|kind| kind.error_with(name))
    }
}

/// Parses an email address using the list
pub trait EmailAddress {
    fn parse_email_address<'a>(&self, name: &'a str) -> Result<'a, email::Address<'a>>;
}

impl<T> EmailAddress for T
where
    T: List,
{
    /// By default email addresses with IP address host part are not supported.
    /// If you need support for that, enable the `net` feature.
    fn parse_email_address<'a>(&self, name: &'a str) -> Result<'a, email::Address<'a>> {
        email::Address::parse(self, name).map_err(|kind| kind.error_with(name))
    }
}
