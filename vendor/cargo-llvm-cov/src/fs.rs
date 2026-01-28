// SPDX-License-Identifier: Apache-2.0 OR MIT

pub(crate) use std::fs::Metadata;
use std::{ffi::OsStr, io, path::Path};

pub(crate) use fs_err::{File, create_dir_all, read_dir, write};

/// Removes a file from the filesystem **if exists**. (Similar to `rm -f`)
pub(crate) fn remove_file(path: impl AsRef<Path>) -> io::Result<()> {
    match fs_err::remove_file(path.as_ref()) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(()),
        res => res,
    }
}

/// Removes a directory at this path **if exists**. (Similar to `rm -rf`)
pub(crate) fn remove_dir_all(path: impl AsRef<Path>) -> io::Result<()> {
    match fs_err::remove_dir_all(path.as_ref()) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(()),
        res => res,
    }
}

/// `a.tar.gz` -> `a` (Note: normal file_stem returns `a.tar`)
pub(crate) fn file_stem_recursive(path: &Path) -> Option<&OsStr> {
    let mut file_name = path.file_name()?;
    while let Some(stem) = Path::new(file_name).file_stem() {
        if file_name == stem {
            break;
        }
        file_name = stem;
    }
    Some(file_name)
}
