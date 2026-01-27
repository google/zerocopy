#![cfg_attr(docsrs, doc(cfg(feature = "verify-tar")))]

use std::io::{Read, Seek};

use super::{NoMatch, find_match};
use crate::verify_unsign_tar::{
    TarFindDataStartAndLenError, TarReadSignaturesError, tar_find_data_start_and_len,
    tar_read_signatures,
};
use crate::{Prehash, VerifyingKey};

crate::Error! {
    /// An error returned by [`verify_tar()`]
    pub struct VerifyTarError(Error) {
        #[error("could not find read signatures in .tar.gz file")]
        FindDataStartAndLen(#[source] TarFindDataStartAndLenError),
        #[error("no matching key/signature pair found")]
        NoMatch(NoMatch),
        #[error("could not read input")]
        Read(#[source] std::io::Error),
        #[error("could not find read signatures in .tar.gz file")]
        ReadSignatures(#[source] TarReadSignaturesError),
        #[error("could not seek inside the input")]
        Seek(#[source] std::io::Error),
    }
}

/// Find the index of the first [`VerifyingKey`] that matches the a signature in a signed `.tar.gz`
/// file
pub fn verify_tar<I>(
    input: &mut I,
    keys: &[VerifyingKey],
    context: Option<&[u8]>,
) -> Result<usize, VerifyTarError>
where
    I: ?Sized + Read + Seek,
{
    // seek to start of base64 encoded signatures
    let (data_start, data_len) =
        tar_find_data_start_and_len(input).map_err(Error::FindDataStartAndLen)?;

    // read base64 encoded signatures
    let signatures =
        tar_read_signatures(data_start, data_len, input).map_err(Error::ReadSignatures)?;

    // pre-hash file
    input.rewind().map_err(Error::Seek)?;
    let prehashed_message = Prehash::calculate(&mut input.take(data_start)).map_err(Error::Read)?;

    // find match
    let (key_idx, _) =
        find_match(keys, &signatures, &prehashed_message, context).map_err(Error::NoMatch)?;
    Ok(key_idx)
}
