//! The errors returned by this crate

use core::fmt;

pub(crate) type Result<T> = core::result::Result<T, Kind>;

/// Information about the error and its input
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Error<'a> {
    kind: Kind,
    input: &'a str,
}

impl<'a> Error<'a> {
    /// The kind of error this is
    pub const fn kind(&self) -> Kind {
        self.kind
    }

    /// The input that resulted in this error
    pub const fn input(&self) -> &'a str {
        self.input
    }
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            Kind::NameTooLong => write!(f, "'{}' is too long", self.input),
            Kind::NetDisabled => write!(f, "'{}'; can't parse email addresses containing IP addresses when `net` feature is disabled", self.input),
            Kind::EmptyLabel => write!(f, "'{}' contains an empty label", self.input),
            Kind::EmailLocalTooLong => {
                write!(f, "the user local part in '{}' is too long", self.input)
            }
            Kind::EmailTooLong => write!(f, "'{}' is too long for an email address", self.input),
            Kind::EmptyName => write!(f, "name is empty"),
            Kind::IllegalCharacter => write!(f, "'{}' contains an illegal character", self.input),
            Kind::InvalidDomain => write!(f, "'{}' is not a valid domain name", self.input),
            Kind::InvalidIpAddr => write!(f, "'{}' contains an invalid IP address", self.input),
            Kind::LabelEndNotAlnum => {
                write!(
                    f,
                    "'{}' has a label that does not end with an alphanumeric character",
                    self.input
                )
            }
            Kind::LabelStartNotAlnum => {
                write!(
                    f,
                    "'{}' has a label that does not start with an alphanumeric character",
                    self.input
                )
            }
            Kind::LabelTooLong => write!(f, "'{}' has a label that is too long", self.input),
            Kind::NoAtSign => write!(f, "'{}' does not have an @ sign", self.input),
            Kind::NoHostPart => write!(f, "'{}' does not have a host part", self.input),
            Kind::NoUserPart => write!(f, "'{}' does not have a user local part", self.input),
            Kind::NumericTld => write!(f, "'{}' has a numeric TLD", self.input),
            Kind::QuoteUnclosed => write!(f, "'{}' has an unclosed quotation mark", self.input),
            Kind::TooManyLabels => write!(f, "'{}' contains too many labels", self.input),
        }
    }
}

#[cfg(feature = "std")]
impl<'a> std::error::Error for Error<'a> {}

/// Description of the error
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
#[non_exhaustive]
pub enum Kind {
    NameTooLong,
    NetDisabled,
    EmptyLabel,
    EmailLocalTooLong,
    EmailTooLong,
    EmptyName,
    IllegalCharacter,
    InvalidDomain,
    InvalidIpAddr,
    LabelEndNotAlnum,
    LabelStartNotAlnum,
    LabelTooLong,
    NoAtSign,
    NoHostPart,
    NoUserPart,
    NumericTld,
    QuoteUnclosed,
    TooManyLabels,
}

impl Kind {
    pub(crate) const fn error_with(self, input: &str) -> Error<'_> {
        Error { kind: self, input }
    }
}

#[cfg(feature = "std")]
impl From<std::net::AddrParseError> for Kind {
    fn from(_: std::net::AddrParseError) -> Self {
        Self::InvalidIpAddr
    }
}
