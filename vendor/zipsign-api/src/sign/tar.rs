#![cfg_attr(docsrs, doc(cfg(feature = "sign-tar")))]

use std::io::{Read, Seek, Write, copy};

use base64::Engine;
use base64::prelude::BASE64_STANDARD;
use ed25519_dalek::SIGNATURE_LENGTH;

use super::{GatherSignatureDataError, gather_signature_data};
use crate::constants::{
    BUF_LIMIT, GZIP_END, GZIP_EXTRA, GZIP_START, HEADER_SIZE, SignatureCountLeInt,
};
use crate::{Prehash, SigningKey};

crate::Error! {
    /// An error returned by [`copy_and_sign_tar()`]
    pub struct SignTarError(Error) {
        #[error("could not copy input to output")]
        Copy(#[source] std::io::Error),
        #[error("could not read input")]
        InputRead(#[source] std::io::Error),
        #[error("could not seek in input")]
        InputSeek(#[source] std::io::Error),
        #[error("could not seek in output")]
        OutputSeek(#[source] std::io::Error),
        #[error("could not write output")]
        OutputWrite(#[source] std::io::Error),
        #[error("could not sign pre-hashed message")]
        Sign(#[source] GatherSignatureDataError),
        #[error("too many keys")]
        TooManyKeys,
    }
}

/// Copy a `.tar.gz` file and sign its content
pub fn copy_and_sign_tar<I, O>(
    input: &mut I,
    output: &mut O,
    keys: &[SigningKey],
    context: Option<&[u8]>,
) -> Result<(), SignTarError>
where
    I: ?Sized + Seek + Read,
    O: ?Sized + Seek + Write,
{
    if keys.len() > SignatureCountLeInt::MAX as usize {
        return Err(Error::TooManyKeys.into());
    }
    let signature_bytes = SIGNATURE_LENGTH * keys.len() + HEADER_SIZE;
    if (signature_bytes.saturating_add(2) / 3).saturating_mul(4) > BUF_LIMIT {
        return Err(Error::TooManyKeys.into());
    }

    // gather signature
    let prehashed_message = Prehash::calculate(input).map_err(Error::InputRead)?;
    let buf = gather_signature_data(keys, &prehashed_message, context).map_err(Error::Sign)?;
    let buf = BASE64_STANDARD.encode(buf);
    if buf.len() > BUF_LIMIT {
        return Err(Error::TooManyKeys.into());
    }

    // copy input
    input.rewind().map_err(Error::InputSeek)?;
    let _: u64 = copy(input, output).map_err(Error::Copy)?;

    // write signature
    let start = output.stream_position().map_err(Error::OutputSeek)?;
    let mut start_buf = [0u8; 16];
    write!(&mut start_buf[..], "{start:016x}").unwrap();

    let mut tail = Vec::with_capacity(GZIP_EXTRA + buf.len());
    tail.extend(GZIP_START);
    tail.extend(buf.into_bytes()); // GZIP comment
    tail.extend(start_buf); // GZIP comment
    tail.extend(GZIP_END);
    output.write_all(&tail).map_err(Error::OutputWrite)?;

    Ok(())
}
