// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Shared helpers for `anneal-rustc-capture` integration tests.

use std::path::PathBuf;
use std::process::Command;

pub fn sysroot() -> PathBuf {
    let raw = ["ANNEAL_SYSROOT", "ANNEAL_TEST_RUST_SYSROOT"]
        .into_iter()
        .find_map(|name| {
            std::env::var_os(name)
                .filter(|v| !v.is_empty())
                .map(PathBuf::from)
        })
        .or_else(|| {
            std::env::var_os("ANNEAL_TEST_INSTALL_ROOT")
                .filter(|v| !v.is_empty())
                .map(|root| PathBuf::from(root).join("rust"))
        })
        .unwrap_or_else(|| {
            let output = Command::new("rustup")
                .args(["run", "nightly-2026-05-31", "rustc", "--print", "sysroot"])
                .output()
                .expect("set ANNEAL_SYSROOT or install rustup nightly-2026-05-31");
            assert!(
                output.status.success(),
                "cannot find pinned compiler sysroot; set ANNEAL_SYSROOT:\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
            PathBuf::from(
                String::from_utf8(output.stdout)
                    .expect("rustc sysroot must be UTF-8")
                    .trim(),
            )
        });
    std::fs::canonicalize(&raw)
        .unwrap_or_else(|e| panic!("cannot resolve Rust sysroot {}: {e}", raw.display()))
}

#[allow(dead_code)]
fn find_installed_lean(toolchain_parent: &std::path::Path) -> Option<PathBuf> {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(toolchain_parent)
        .ok()?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .collect();
    entries.sort();
    entries
        .into_iter()
        .map(|dir| dir.join("lean/bin/lean"))
        .find(|candidate| candidate.is_file())
}

#[allow(dead_code)]
pub fn lean() -> PathBuf {
    if let Some(explicit) = std::env::var_os("ANNEAL_LEAN").filter(|v| !v.is_empty()) {
        let path = PathBuf::from(explicit);
        return std::fs::canonicalize(&path)
            .unwrap_or_else(|e| panic!("cannot resolve ANNEAL_LEAN {}: {e}", path.display()));
    }
    if let Some(root) = std::env::var_os("ANNEAL_TEST_INSTALL_ROOT").filter(|v| !v.is_empty()) {
        let candidate = PathBuf::from(root).join("lean/bin/lean");
        if candidate.is_file() {
            return std::fs::canonicalize(&candidate).unwrap();
        }
    }
    if let Some(xdg) = std::env::var_os("XDG_CACHE_HOME").filter(|v| !v.is_empty())
        && let Some(found) = find_installed_lean(&PathBuf::from(xdg).join("anneal/toolchain"))
    {
        return std::fs::canonicalize(&found).unwrap();
    }
    if let Some(home) = std::env::var_os("HOME").filter(|v| !v.is_empty()) {
        let home = PathBuf::from(home);
        for rel in [
            ".cache/anneal/toolchain",
            "Library/Caches/anneal/toolchain",
            "anneal/toolchain",
        ] {
            if let Some(found) = find_installed_lean(&home.join(rel)) {
                return std::fs::canonicalize(&found).unwrap();
            }
        }
        let elan = home.join(".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean");
        if elan.is_file() {
            return std::fs::canonicalize(&elan).unwrap();
        }
    }
    panic!("cannot find pinned Lean 4.34.1 executable; set ANNEAL_LEAN or install via elan/setup");
}
