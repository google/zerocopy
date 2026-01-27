use std::io::{Read, Seek, SeekFrom};
use std::mem::size_of;

use base64::Engine;
use base64::prelude::BASE64_STANDARD;
use ed25519_dalek::{SIGNATURE_LENGTH, Signature, SignatureError};

use crate::constants::{
    BUF_LIMIT, GZIP_END, GZIP_START, HEADER_SIZE, MAGIC_HEADER, SignatureCountLeInt,
};

#[derive(Debug, thiserror::Error)]
pub(crate) enum TarFindDataStartAndLenError {
    #[error("the expected last GZIP block was missing or corrupted")]
    Gzip,
    #[error("could not read input")]
    Read(#[source] std::io::Error),
    #[error("could not seek inside the input")]
    Seek(#[source] std::io::Error),
    #[error("too many signatures in input")]
    TooManySignatures,
}

pub(crate) fn tar_find_data_start_and_len<I>(
    input: &mut I,
) -> Result<(u64, usize), TarFindDataStartAndLenError>
where
    I: ?Sized + Read + Seek,
{
    let mut tail = [0; u64::BITS as usize / 4 + GZIP_END.len()];
    let data_end = input
        .seek(SeekFrom::End(-(tail.len() as i64)))
        .map_err(TarFindDataStartAndLenError::Seek)?;

    input
        .read_exact(&mut tail)
        .map_err(TarFindDataStartAndLenError::Read)?;
    if tail[u64::BITS as usize / 4..] != *GZIP_END {
        return Err(TarFindDataStartAndLenError::Gzip);
    }
    let Ok(gzip_start) = std::str::from_utf8(&tail[..16]) else {
        return Err(TarFindDataStartAndLenError::Gzip);
    };
    let Ok(gzip_start) = u64::from_str_radix(gzip_start, 16) else {
        return Err(TarFindDataStartAndLenError::Gzip);
    };
    let Some(data_start) = gzip_start.checked_add(10) else {
        return Err(TarFindDataStartAndLenError::Gzip);
    };
    let Some(data_len) = data_end.checked_sub(data_start) else {
        return Err(TarFindDataStartAndLenError::Gzip);
    };
    let Ok(data_len) = usize::try_from(data_len) else {
        return Err(TarFindDataStartAndLenError::Gzip);
    };
    if data_len > BUF_LIMIT {
        return Err(TarFindDataStartAndLenError::TooManySignatures);
    }

    Ok((gzip_start, data_len + GZIP_START.len()))
}

#[derive(Debug, thiserror::Error)]
pub(crate) enum TarReadSignaturesError {
    #[error("the input contained invalid base64 encoded data")]
    Base64,
    #[error("the input contained no signatures")]
    Empty,
    #[error("the expected last GZIP block was missing or corrupted")]
    Gzip,
    #[error("the encoded length did not fit the expected length")]
    LengthMismatch,
    #[error("the expected magic header was missing or corrupted")]
    MagicHeader,
    #[error("could not read input")]
    Read(#[source] std::io::Error),
    #[error("the input contained an illegal signature at index #{1}")]
    Signature(#[source] SignatureError, usize),
}

pub(crate) fn tar_read_signatures<I>(
    data_start: u64,
    data_len: usize,
    input: &mut I,
) -> Result<Vec<Signature>, TarReadSignaturesError>
where
    I: ?Sized + Read + Seek,
{
    let _: u64 = input
        .seek(SeekFrom::Start(data_start))
        .map_err(TarReadSignaturesError::Read)?;

    let mut data = vec![0; data_len];
    input
        .read_exact(&mut data)
        .map_err(TarReadSignaturesError::Read)?;

    if data[..GZIP_START.len()] != *GZIP_START {
        return Err(TarReadSignaturesError::Gzip);
    }
    let Ok(data) = BASE64_STANDARD.decode(&data[GZIP_START.len()..]) else {
        return Err(TarReadSignaturesError::Base64);
    };
    if data.len() < HEADER_SIZE {
        return Err(TarReadSignaturesError::MagicHeader);
    }
    if data[..MAGIC_HEADER.len()] != *MAGIC_HEADER {
        return Err(TarReadSignaturesError::MagicHeader);
    }

    let signature_count = data[MAGIC_HEADER.len()..][..size_of::<SignatureCountLeInt>()]
        .try_into()
        .unwrap();
    let signature_count = SignatureCountLeInt::from_le_bytes(signature_count) as usize;
    if signature_count == 0 {
        return Err(TarReadSignaturesError::Empty);
    }
    if data.len() != HEADER_SIZE + signature_count * SIGNATURE_LENGTH {
        return Err(TarReadSignaturesError::LengthMismatch);
    }

    let signatures = data[HEADER_SIZE..]
        .chunks_exact(SIGNATURE_LENGTH)
        .enumerate()
        .map(|(idx, bytes)| {
            Signature::from_slice(bytes).map_err(|err| TarReadSignaturesError::Signature(err, idx))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(signatures)
}
