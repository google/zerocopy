//! Error that occurred at some stage of parsing

use core::fmt;

use crate::error::{ParseFromDescription, TryFromParsed};

/// An error that occurred at some stage of parsing.
#[cfg_attr(__time_03_docs, doc(cfg(feature = "parsing")))]
#[allow(variant_size_differences)]
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Parse {
    #[allow(clippy::missing_docs_in_private_items)]
    TryFromParsed(TryFromParsed),
    #[allow(clippy::missing_docs_in_private_items)]
    ParseFromDescription(ParseFromDescription),
    /// The input should have ended, but there were characters remaining.
    #[non_exhaustive]
    UnexpectedTrailingCharacters,
}

impl fmt::Display for Parse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TryFromParsed(err) => err.fmt(f),
            Self::ParseFromDescription(err) => err.fmt(f),
            Self::UnexpectedTrailingCharacters => f.write_str("unexpected trailing characters"),
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(__time_03_docs, doc(cfg(feature = "std")))]
impl std::error::Error for Parse {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::TryFromParsed(err) => Some(err),
            Self::ParseFromDescription(err) => Some(err),
            Self::UnexpectedTrailingCharacters => None,
        }
    }
}

impl From<TryFromParsed> for Parse {
    fn from(err: TryFromParsed) -> Self {
        Self::TryFromParsed(err)
    }
}

impl From<ParseFromDescription> for Parse {
    fn from(err: ParseFromDescription) -> Self {
        Self::ParseFromDescription(err)
    }
}

impl From<Parse> for crate::Error {
    fn from(err: Parse) -> Self {
        match err {
            Parse::TryFromParsed(err) => Self::TryFromParsed(err),
            Parse::ParseFromDescription(err) => Self::ParseFromDescription(err),
            Parse::UnexpectedTrailingCharacters => Self::UnexpectedTrailingCharacters,
        }
    }
}

#[cfg(feature = "serde-human-readable")]
impl Parse {
    /// Obtain an error type for the deserializer.
    pub(crate) fn to_invalid_serde_value<'a, D: serde::Deserializer<'a>>(self) -> D::Error {
        #[cfg(not(feature = "std"))]
        use alloc::format;

        use serde::de::Error;

        match self {
            Self::TryFromParsed(TryFromParsed::InsufficientInformation) => unreachable!(
                "The deserializing format contains all information needed to construct a `Time`."
            ),
            Self::TryFromParsed(TryFromParsed::ComponentRange(err)) => {
                err.to_invalid_serde_value::<D>()
            }
            Self::ParseFromDescription(ParseFromDescription::InvalidLiteral) => {
                D::Error::invalid_value(serde::de::Unexpected::Other("literal"), &"valid format")
            }
            Self::ParseFromDescription(ParseFromDescription::InvalidComponent(component)) => {
                D::Error::invalid_value(
                    serde::de::Unexpected::Other(component),
                    &&*format!("valid {}", component),
                )
            }
            Self::UnexpectedTrailingCharacters => D::Error::invalid_value(
                serde::de::Unexpected::Other("literal"),
                &"no extraneous characters",
            ),
        }
    }
}
