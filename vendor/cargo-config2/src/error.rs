// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::{ffi::OsString, fmt, io};

macro_rules! format_err {
    ($($tt:tt)*) => {
        crate::Error::new(format!($($tt)*))
    };
}

macro_rules! bail {
    ($($tt:tt)*) => {
        return Err(format_err!($($tt)*))
    };
}

pub(crate) type Result<T, E = Error> = core::result::Result<T, E>;

/// An error that occurred during loading or resolving the Cargo configuration.
#[derive(Debug)]
pub struct Error(ErrorKind);

// Hiding error variants from a library's public error type to prevent
// dependency updates from becoming breaking changes.
// We can add `is_*` methods that indicate the kind of error if needed, but
// don't expose dependencies' types directly in the public API.
#[derive(Debug)]
pub(crate) enum ErrorKind {
    Io(io::Error),

    CfgExprParse(crate::cfg_expr::error::ParseError),

    Other(Box<str>),
    WithContext(Box<str>, Option<Box<dyn std::error::Error + Send + Sync>>),
}

impl Error {
    pub(crate) fn new(e: impl Into<ErrorKind>) -> Self {
        Self(e.into())
    }

    pub(crate) fn env_not_unicode(name: &str, var: OsString) -> Self {
        Self(ErrorKind::WithContext(
            format!("failed to parse environment variable `{name}`").into_boxed_str(),
            Some(Box::new(std::env::VarError::NotUnicode(var))),
        ))
    }
    pub(crate) fn env_not_unicode_redacted(name: &str) -> Self {
        Self(ErrorKind::WithContext(
            format!("failed to parse environment variable `{name}`").into_boxed_str(),
            Some("environment variable was not valid unicode: [REDACTED]".into()),
        ))
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            ErrorKind::Io(e) => fmt::Display::fmt(e, f),
            ErrorKind::CfgExprParse(e) => fmt::Display::fmt(e, f),
            ErrorKind::Other(e) | ErrorKind::WithContext(e, ..) => fmt::Display::fmt(e, f),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.0 {
            ErrorKind::Io(e) => e.source(),
            ErrorKind::CfgExprParse(e) => e.source(),
            ErrorKind::Other(_) => None,
            ErrorKind::WithContext(_, e) => Some(&**e.as_ref()?),
        }
    }
}

// TODO: consider removing this in the next breaking release
impl From<Error> for io::Error {
    fn from(e: Error) -> Self {
        match e.0 {
            ErrorKind::Io(e) => e,
            ErrorKind::CfgExprParse(e) => Self::other(e),
            ErrorKind::Other(e) | ErrorKind::WithContext(e, None) => Self::other(e.into_string()),
            ErrorKind::WithContext(msg, Some(source)) => {
                let kind = if let Some(e) = source.downcast_ref::<io::Error>() {
                    e.kind()
                } else if source.downcast_ref::<toml::de::Error>().is_some() {
                    io::ErrorKind::InvalidData
                } else {
                    io::ErrorKind::Other
                };
                Self::new(kind, Error(ErrorKind::WithContext(msg, Some(source))))
            }
        }
    }
}

impl From<String> for ErrorKind {
    fn from(s: String) -> Self {
        Self::Other(s.into_boxed_str())
    }
}
impl From<crate::cfg_expr::error::ParseError> for ErrorKind {
    fn from(e: crate::cfg_expr::error::ParseError) -> Self {
        Self::CfgExprParse(e)
    }
}

// Note: Do not implement From<ThirdPartyErrorType> to prevent dependency
// updates from becoming breaking changes.
// Implementing `From<StdErrorType>` should also be avoided whenever possible,
// as it would be a breaking change to remove the implementation if the
// conversion is no longer needed due to changes in the internal implementation.
// TODO: consider removing them in the next breaking release
impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Self(ErrorKind::Io(e))
    }
}
// TODO: this is no longer used in our code; remove in the next breaking release
impl From<std::env::VarError> for Error {
    fn from(e: std::env::VarError) -> Self {
        Self(ErrorKind::Other(e.to_string().into_boxed_str()))
    }
}

// Inspired by anyhow::Context.
pub(crate) trait Context<T, E> {
    fn context<C>(self, context: C) -> Result<T, Error>
    where
        C: fmt::Display;
    fn with_context<C, F>(self, context: F) -> Result<T, Error>
    where
        C: fmt::Display,
        F: FnOnce() -> C;
}
impl<T, E> Context<T, E> for Result<T, E>
where
    E: std::error::Error + Send + Sync + 'static,
{
    fn context<C>(self, context: C) -> Result<T, Error>
    where
        C: fmt::Display,
    {
        match self {
            Ok(ok) => Ok(ok),
            Err(e) => Err(Error(ErrorKind::WithContext(
                context.to_string().into_boxed_str(),
                Some(Box::new(e)),
            ))),
        }
    }
    fn with_context<C, F>(self, context: F) -> Result<T, Error>
    where
        C: fmt::Display,
        F: FnOnce() -> C,
    {
        match self {
            Ok(ok) => Ok(ok),
            Err(e) => Err(Error(ErrorKind::WithContext(
                context().to_string().into_boxed_str(),
                Some(Box::new(e)),
            ))),
        }
    }
}
impl<T> Context<T, core::convert::Infallible> for Option<T> {
    fn context<C>(self, context: C) -> Result<T, Error>
    where
        C: fmt::Display,
    {
        match self {
            Some(ok) => Ok(ok),
            None => Err(Error(ErrorKind::WithContext(context.to_string().into_boxed_str(), None))),
        }
    }
    fn with_context<C, F>(self, context: F) -> Result<T, Error>
    where
        C: fmt::Display,
        F: FnOnce() -> C,
    {
        match self {
            Some(ok) => Ok(ok),
            None => {
                Err(Error(ErrorKind::WithContext(context().to_string().into_boxed_str(), None)))
            }
        }
    }
}
