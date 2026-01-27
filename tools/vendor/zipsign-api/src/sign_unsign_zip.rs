use std::io::{BufReader, BufWriter, Read, Seek, Write};

use zip::result::ZipError;
use zip::{ZipArchive, ZipWriter};

#[derive(Debug, thiserror::Error)]
pub(crate) enum CopyZipError {
    #[error("could not read input ZIP")]
    InputZip(#[source] ZipError),
    #[error("could not read file #{1} inside input ZIP")]
    InputZipIndex(#[source] ZipError, usize),
    #[error("could not write to output")]
    OutputWrite(#[source] std::io::Error),
    #[error("could not write ZIP file #{1} to output")]
    OutputZip(#[source] ZipError, usize),
    #[error("could not finish writing output ZIP")]
    OutputZipFinish(#[source] ZipError),
}

pub(crate) fn copy_zip<I, O>(input: &mut I, output: &mut O) -> Result<(), CopyZipError>
where
    I: ?Sized + Seek + Read,
    O: ?Sized + Seek + Write,
{
    let mut input = ZipArchive::new(BufReader::new(input)).map_err(CopyZipError::InputZip)?;
    let mut output = ZipWriter::new(BufWriter::new(output));

    output.set_raw_comment(input.comment().into());
    for idx in 0..input.len() {
        let file = input
            .by_index_raw(idx)
            .map_err(|err| CopyZipError::InputZipIndex(err, idx))?;
        output
            .raw_copy_file(file)
            .map_err(|err| CopyZipError::OutputZip(err, idx))?;
    }
    output
        .finish()
        .map_err(CopyZipError::OutputZipFinish)?
        .flush()
        .map_err(CopyZipError::OutputWrite)?;

    Ok(())
}
