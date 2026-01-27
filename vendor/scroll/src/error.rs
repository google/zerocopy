use core::fmt::{self, Display};
use core::{error, result};
#[cfg(feature = "std")]
use std::io;

#[derive(Debug)]
/// A custom Scroll error
pub enum Error {
    /// The type you tried to read was too big
    TooBig {
        size: usize,
        len: usize,
    },
    /// The requested offset to read/write at is invalid
    BadOffset(usize),
    BadInput {
        size: usize,
        msg: &'static str,
    },
    /// A custom Scroll error for reporting messages to clients.
    /// For no-std, use [`Error::BadInput`] with a static string.
    #[cfg(feature = "std")]
    Custom(String),
    /// Returned when IO based errors are encountered
    #[cfg(feature = "std")]
    IO(io::Error),
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match self {
            Error::TooBig { .. } => "TooBig",
            Error::BadOffset(_) => "BadOffset",
            Error::BadInput { .. } => "BadInput",
            #[cfg(feature = "std")]
            Error::Custom(_) => "Custom",
            #[cfg(feature = "std")]
            Error::IO(_) => "IO",
        }
    }
    fn cause(&self) -> Option<&dyn error::Error> {
        match self {
            Error::TooBig { .. } => None,
            Error::BadOffset(_) => None,
            Error::BadInput { .. } => None,
            #[cfg(feature = "std")]
            Error::Custom(_) => None,
            #[cfg(feature = "std")]
            Error::IO(io) => io.source(),
        }
    }
}

#[cfg(feature = "std")]
impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::IO(err)
    }
}

impl Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::TooBig { size, len } => {
                write!(fmt, "type is too big ({size}) for {len}")
            }
            Error::BadOffset(offset) => {
                write!(fmt, "bad offset {offset}")
            }
            Error::BadInput { msg, size } => {
                write!(fmt, "bad input {msg} ({size})")
            }
            #[cfg(feature = "std")]
            Error::Custom(msg) => {
                write!(fmt, "{msg}")
            }
            #[cfg(feature = "std")]
            Error::IO(err) => {
                write!(fmt, "{err}")
            }
        }
    }
}

pub type Result<T> = result::Result<T, Error>;
