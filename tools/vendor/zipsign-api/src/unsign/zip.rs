#![cfg_attr(docsrs, doc(cfg(feature = "unsign-zip")))]

use std::io::{Read, Seek, Write};

use crate::sign_unsign_zip::{CopyZipError, copy_zip};

crate::Error! {
    /// An error returned by [`copy_and_unsign_zip()`]
    pub struct UnsignZipError(Error) {
        #[error("could not copy ZIP data")]
        Copy(#[source] CopyZipError),
    }
}

/// Copy a signed `.zip` file without the signatures
pub fn copy_and_unsign_zip<I, O>(input: &mut I, output: &mut O) -> Result<(), UnsignZipError>
where
    I: ?Sized + Read + Seek,
    O: ?Sized + Read + Seek + Write,
{
    copy_zip(input, output).map_err(Error::Copy)?;
    Ok(())
}
