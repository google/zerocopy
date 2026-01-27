#![cfg_attr(docsrs, doc(cfg(feature = "unsign-tar")))]

use std::io::{Read, Seek, Write, copy};

use crate::verify_unsign_tar::{
    TarFindDataStartAndLenError, TarReadSignaturesError, tar_find_data_start_and_len,
    tar_read_signatures,
};

crate::Error! {
    /// An error returned by [`copy_and_unsign_tar()`]
    pub struct UnsignTarError(Error) {
        #[error("could not copy data")]
        Copy(#[source] std::io::Error),
        #[error("could not find read signatures in .tar.gz file")]
        FindDataStartAndLen(#[source] TarFindDataStartAndLenError),
        #[error("could not find read signatures in .tar.gz file")]
        ReadSignatures(#[source] TarReadSignaturesError),
        #[error("could not seek inside the input")]
        Seek(#[source] std::io::Error),
    }
}

/// Copy a signed `.tar.gz` file without the signatures
pub fn copy_and_unsign_tar<I, O>(input: &mut I, output: &mut O) -> Result<(), UnsignTarError>
where
    I: ?Sized + Seek + Read,
    O: ?Sized + Seek + Write,
{
    // seek to start of base64 encoded signatures
    let (data_start, data_len) =
        tar_find_data_start_and_len(input).map_err(Error::FindDataStartAndLen)?;

    // read base64 encoded signatures
    let _ = tar_read_signatures(data_start, data_len, input).map_err(Error::ReadSignatures)?;

    // copy data
    input.rewind().map_err(Error::Seek)?;
    let _ = copy(&mut input.take(data_start), output).map_err(Error::Copy)?;

    Ok(())
}
