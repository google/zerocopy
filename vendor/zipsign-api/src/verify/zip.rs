#![cfg_attr(docsrs, doc(cfg(feature = "verify-zip")))]

use std::io::{Read, Seek};

use super::{NoMatch, ReadSignaturesError, VerifyingKey, find_match, read_signatures};
use crate::{Prehash, Signature};

crate::Error! {
    /// An error returned by [`verify_zip()`]
    pub struct VerifyZipError(Error) {
        #[error("could not read input")]
        InputRead(#[source] std::io::Error),
        #[error("no matching key/signature pair found")]
        NoMatch(NoMatch),
        #[error("could not read signatures from input")]
        ReadSignaturesError(#[source] ReadSignaturesError),
    }
}

/// Find the index of the first [`VerifyingKey`] that matches the a signature in a signed `.zip`
/// file
pub fn verify_zip<R>(
    signed_file: &mut R,
    keys: &[VerifyingKey],
    context: Option<&[u8]>,
) -> Result<usize, VerifyZipError>
where
    R: ?Sized + Read + Seek,
{
    let (prehashed_message, signatures) = read_zip(signed_file)?;
    let (key_idx, _) =
        find_match(keys, &signatures, &prehashed_message, context).map_err(Error::NoMatch)?;
    Ok(key_idx)
}

fn read_zip<R>(signed_file: &mut R) -> Result<(Prehash, Vec<Signature>), VerifyZipError>
where
    R: ?Sized + Read + Seek,
{
    let signatures = read_signatures(signed_file).map_err(Error::ReadSignaturesError)?;
    let prehashed_message = Prehash::calculate(signed_file).map_err(Error::InputRead)?;
    Ok((prehashed_message, signatures))
}
