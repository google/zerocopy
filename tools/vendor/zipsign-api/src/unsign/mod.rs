//! Functions to remove signatures from a file

#[cfg(feature = "unsign-tar")]
mod tar;
#[cfg(feature = "unsign-zip")]
mod zip;

#[cfg(feature = "unsign-tar")]
pub use self::tar::{UnsignTarError, copy_and_unsign_tar};
#[cfg(feature = "unsign-zip")]
pub use self::zip::{UnsignZipError, copy_and_unsign_zip};
