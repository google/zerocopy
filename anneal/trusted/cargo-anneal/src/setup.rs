// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Toolchain installation via `exocrate` (`cargo anneal setup`).
//!
//! Manages the versioned omnibus archive containing:
//! - `bin/anneal-rustc-capture`, the standalone MIR capture driver;
//! - `lean/`, the pinned Lean toolchain;
//! - `rust/`, the pinned Rust toolchain (`rustc`, `rust-std`, and `rustc-dev`);
//!   and
//! - `share/anneal/`, the `trusted/lean/` foundation metadata.

use std::path::PathBuf;

exocrate::config! {
    const CONFIG: Config = Config {
        rel_dir_path: [".anneal", "toolchain"],
        versioned_files: &["../Cargo.toml"],
    };
}

exocrate::parse_remote_archive! {
    const REMOTE_ARCHIVE: RemoteArchive = "Cargo.toml";
}

/// Installs or resolves the Anneal toolchain archive in the user-global cache.
///
/// Uses `local_archive` when set, falling back to the remote archive recorded
/// in `[[package.metadata.exocrate]]` for the current platform.
pub fn install(local_archive: Option<PathBuf>) -> Result<PathBuf, String> {
    let source = match local_archive {
        Some(path) => exocrate::Source::Local(path),
        None => exocrate::Source::Remote(REMOTE_ARCHIVE),
    };
    CONFIG
        .resolve_installation_dir_or_install(
            exocrate::Location::UserGlobal,
            source,
        )
        .map(|(dir, _)| dir)
        .map_err(|e| format!("failed to install Anneal toolchain: {e}"))
}

#[cfg(test)]
mod tests {
    use std::process::Command;

    use super::*;

    #[test]
    fn resolves_and_executes_installed_exocrate_toolchain() {
        let root = CONFIG
            .resolve_installation_dir(exocrate::Location::UserGlobal)
            .expect("Anneal toolchain must be installed before running tests");

        assert!(
            root.join("share/anneal/trusted/lean/foundation-lock.json")
                .is_file(),
            "expected bundled foundation-lock.json inside share/anneal"
        );

        let lean_out = Command::new(root.join("lean/bin/lean"))
            .arg("--version")
            .output()
            .expect("failed to execute bundled lean --version");
        assert!(
            lean_out.status.success(),
            "bundled lean --version failed: {lean_out:?}"
        );
        let lean_stdout = String::from_utf8_lossy(&lean_out.stdout);
        assert!(
            lean_stdout.contains("4.34.1"),
            "expected Lean 4.34.1, got: {lean_stdout}"
        );

        for rel_bin in ["rust/bin/rustc", "bin/anneal-rustc-capture"] {
            let out = Command::new(root.join(rel_bin))
                .arg("--version")
                .output()
                .unwrap_or_else(|e| panic!("failed to execute {rel_bin}: {e}"));
            assert!(out.status.success(), "{rel_bin} --version failed: {out:?}");
        }
    }
}
