// Copyright (c) The camino-tempfile Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use camino::Utf8PathBuf;
use std::{error, fmt, io};

#[derive(Debug)]
struct Utf8PathError {
    path: Utf8PathBuf,
    err: io::Error,
}

impl fmt::Display for Utf8PathError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at path {}", self.err, self.path)
    }
}

impl error::Error for Utf8PathError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        self.err.source()
    }
}

pub(crate) trait IoResultExt<T> {
    fn with_err_path<F, P>(self, path: F) -> Self
    where
        F: FnOnce() -> P,
        P: Into<Utf8PathBuf>;
}

impl<T> IoResultExt<T> for Result<T, io::Error> {
    fn with_err_path<F, P>(self, path: F) -> Self
    where
        F: FnOnce() -> P,
        P: Into<Utf8PathBuf>,
    {
        self.map_err(|e| {
            io::Error::new(
                e.kind(),
                Utf8PathError {
                    path: path().into(),
                    err: e,
                },
            )
        })
    }
}
