// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{fs, os::unix::fs::symlink};

use super::validate_artifact_dir_chain;

#[test]
fn validate_artifact_dir_chain_rejects_root_intermediate_and_leaf_symlinks() {
    let tmp = tempfile::tempdir().unwrap();
    let real_root = tmp.path().join("real_art");
    let outside = tmp.path().join("outside");
    fs::create_dir_all(real_root.join("authored")).unwrap();
    fs::create_dir_all(&outside).unwrap();
    fs::write(real_root.join("authored/Spec.lean"), b"-- ok\n").unwrap();
    fs::write(outside.join("Spec.lean"), b"-- outside\n").unwrap();

    assert!(validate_artifact_dir_chain(&real_root, "authored/Spec.lean").is_ok());

    // Symlinked root directory.
    let sym_root = tmp.path().join("sym_art");
    symlink(&real_root, &sym_root).unwrap();
    assert!(validate_artifact_dir_chain(&sym_root, "authored/Spec.lean").is_err());

    // Symlinked intermediate directory.
    let escaped_art = tmp.path().join("escaped_art");
    fs::create_dir_all(&escaped_art).unwrap();
    symlink(&outside, escaped_art.join("authored")).unwrap();
    assert!(validate_artifact_dir_chain(&escaped_art, "authored/Spec.lean").is_err());

    // Symlinked leaf file.
    symlink(outside.join("Spec.lean"), real_root.join("authored/Link.lean")).unwrap();
    assert!(validate_artifact_dir_chain(&real_root, "authored/Link.lean").is_err());
}
