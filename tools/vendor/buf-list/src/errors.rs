// Copyright (c) 2018 the linkerd2-proxy authors
// Copyright (c) The buf-list Contributors
// SPDX-License-Identifier: Apache-2.0

//! Error types returned by buf-list.

use std::{error, fmt};

/// An error returned if `read_exact` was called on a [`Cursor`](crate::Cursor) that doesn't have
/// enough bytes remaining.
///
/// This is private because `read_exact_impl` returns an `io::Error`.
#[derive(Debug)]
pub(crate) struct ReadExactError {
    pub(crate) remaining: u64,
    pub(crate) buf_len: usize,
}

impl error::Error for ReadExactError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

impl fmt::Display for ReadExactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Cursor had {} bytes remaining but buffer was {} bytes long",
            self.remaining, self.buf_len
        )
    }
}
