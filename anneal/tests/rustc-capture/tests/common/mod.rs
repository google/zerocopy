// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Thin compatibility shim forwarding to [`anneal_testkit::toolchain`].

use std::path::PathBuf;

#[allow(dead_code)]
pub fn sysroot() -> PathBuf {
    anneal_testkit::default_rust_sysroot().expect("resolve pinned compiler sysroot")
}

#[allow(dead_code)]
pub fn lean() -> PathBuf {
    anneal_testkit::default_lean_path().expect("resolve pinned Lean executable")
}
