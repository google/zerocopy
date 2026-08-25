// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Text-file boundary for canonical repository inputs.
//!
//! `.gitattributes` records LF in Git's index and asks new checkouts to write
//! LF, but adding that attribute does not rewrite a file which is already in a
//! Windows worktree. Normalize only well-formed CRLF while reading the
//! checkout. The source-level parsers still receive and require one canonical
//! LF spelling, and a bare carriage return remains an error rather than being
//! silently reinterpreted.

use std::{
    fs::{self, File},
    io::{self, Read},
    path::Path,
};

/// Reads one repository-owned text file into its canonical LF representation.
pub(crate) fn read(path: &Path) -> io::Result<String> {
    normalize(fs::read_to_string(path)?)
}

/// Reads canonical repository text from an already-open file.
///
/// Callers which also rely on file identity use this entry point so the bytes
/// and identity come from the same operating-system handle rather than two
/// path lookups with a rename window between them.
pub(crate) fn read_open(file: &File) -> io::Result<String> {
    let mut reader = file;
    let mut source = String::new();
    reader.read_to_string(&mut source)?;
    normalize(source)
}

fn normalize(source: String) -> io::Result<String> {
    if !source.contains('\r') {
        return Ok(source);
    }

    let mut normalized = String::with_capacity(source.len());
    let mut characters = source.chars();
    while let Some(character) = characters.next() {
        if character != '\r' {
            normalized.push(character);
            continue;
        }
        if characters.next() != Some('\n') {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "repository text contains a bare carriage return",
            ));
        }
        normalized.push('\n');
    }
    Ok(normalized)
}

#[cfg(test)]
mod tests {
    use std::{
        fs, process,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::{normalize, read, read_open};

    #[test]
    fn preserves_lf_and_normalizes_only_well_formed_crlf() {
        assert_eq!(normalize("one\ntwo\n".to_owned()).unwrap(), "one\ntwo\n");
        assert_eq!(normalize("one\r\ntwo\r\n".to_owned()).unwrap(), "one\ntwo\n");

        for source in ["one\rtwo\n", "one\r\r\ntwo\n", "one\n\r"] {
            let error = normalize(source.to_owned()).unwrap_err();
            assert_eq!(error.kind(), std::io::ErrorKind::InvalidData);
            assert!(error.to_string().contains("bare carriage return"));
        }
    }

    #[test]
    fn repository_read_applies_normalization_at_the_file_boundary() {
        static NEXT_FILE: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_FILE.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir()
            .join(format!("zerocopy-repository-text-test-{}-{unique}.txt", process::id()));

        fs::write(&path, "one\r\ntwo\r\n").unwrap();
        assert_eq!(read(&path).unwrap(), "one\ntwo\n");

        fs::write(&path, "one\rtwo\n").unwrap();
        let error = read(&path).unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::InvalidData);

        fs::remove_file(path).unwrap();
    }

    #[test]
    fn open_file_read_applies_the_same_normalization() {
        static NEXT_FILE: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_FILE.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir()
            .join(format!("zerocopy-open-text-test-{}-{unique}.txt", process::id()));
        fs::write(&path, "one\r\ntwo\r\n").unwrap();

        let file = fs::File::open(&path).unwrap();
        assert_eq!(read_open(&file).unwrap(), "one\ntwo\n");
        drop(file);

        fs::remove_file(path).unwrap();
    }
}
