//! Re-exports of std traits or local reimplementations if std is not available
#[cfg(feature = "std")]
pub use std::io::{Error, ErrorKind, Read, Write};
