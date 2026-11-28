// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Tests: Installation directory repair and resolution retries.

use std::{io, path::PathBuf};

use super::*;

#[test]
fn resolve_installation_dir_retries_once_on_already_exists_toctou() {
    use std::cell::Cell;

    let calls = Cell::new(0usize);
    let recovered = resolve_installation_dir_with(|| {
        let n = calls.get();
        calls.set(n + 1);
        if n == 0 {
            Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "Path exists but is not a directory",
            ))
        } else {
            Ok(PathBuf::from("/cache/recovered-bundle"))
        }
    })
    .expect("single AlreadyExists TOCTOU recovers on retry");
    assert_eq!(recovered, PathBuf::from("/cache/recovered-bundle"));
    assert_eq!(calls.get(), 2);

    let non_dir_calls = Cell::new(0usize);
    let non_dir_err = resolve_installation_dir_with(|| {
        non_dir_calls.set(non_dir_calls.get() + 1);
        Err(io::Error::new(io::ErrorKind::AlreadyExists, "Path exists but is not a directory"))
    })
    .expect_err("persistent non-directory must still fail closed");
    assert_eq!(non_dir_err.kind(), io::ErrorKind::AlreadyExists);
    assert_eq!(non_dir_calls.get(), 2);

    let not_found_calls = Cell::new(0usize);
    let not_found_err = resolve_installation_dir_with(|| {
        not_found_calls.set(not_found_calls.get() + 1);
        Err(io::Error::new(io::ErrorKind::NotFound, "Managed directory does not exist"))
    })
    .expect_err("NotFound must propagate immediately without retrying");
    assert_eq!(not_found_err.kind(), io::ErrorKind::NotFound);
    assert_eq!(not_found_calls.get(), 1);
}
