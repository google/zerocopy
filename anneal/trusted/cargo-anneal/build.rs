// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Generates `$OUT_DIR/bundled_resources.rs` deterministically from the
//! canonical workspace sources (or from `packaged/bundled_resources.rs` inside
//! an unpacked `.crate` archive).

#[allow(dead_code)]
#[path = "src/trusted_bundle.rs"]
mod trusted_bundle;

use std::{env, fs, path::Path};

fn ensure_safe_directive_path(path: &Path) -> &str {
    let s = path
        .to_str()
        .unwrap_or_else(|| panic!("non-UTF-8 path in build script: {}", path.display()));
    assert!(
        !s.bytes().any(|b| b < 0x20 || b == 0x7f),
        "control character forbidden in Cargo rerun-if-changed path: {s:?}"
    );
    s
}

fn emit_rerun_if_changed(path: &Path) {
    println!("cargo:rerun-if-changed={}", ensure_safe_directive_path(path));
}

fn write_if_changed(dest: &Path, content: &str) {
    if let Ok(existing) = fs::read(dest)
        && existing == content.as_bytes()
    {
        return;
    }
    fs::write(dest, content.as_bytes())
        .unwrap_or_else(|e| panic!("failed to write {}: {e}", dest.display()));
}

fn main() {
    let manifest_dir = env::var_os("CARGO_MANIFEST_DIR")
        .map(std::path::PathBuf::from)
        .expect("CARGO_MANIFEST_DIR must be set");
    let out_dir =
        env::var_os("OUT_DIR").map(std::path::PathBuf::from).expect("OUT_DIR must be set");

    let plan = trusted_bundle::resolve_build_script_bundle(&manifest_dir)
        .unwrap_or_else(|e| panic!("{e}"));
    for path in &plan.rerun_if_changed {
        emit_rerun_if_changed(path);
    }
    write_if_changed(&out_dir.join("bundled_resources.rs"), &plan.rendered_source);
}
