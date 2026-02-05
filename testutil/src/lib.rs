// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![deny(unexpected_cfgs)]

#[derive(Debug)]
pub enum ToolchainVersion {
    /// The version listed as our MSRV (ie, the `package.rust-version` key in
    /// `Cargo.toml`).
    PinnedMsrv,
    /// The stable version pinned in CI.
    PinnedStable,
    /// The nightly version pinned in CI
    PinnedNightly,
}

impl ToolchainVersion {
    /// Attempts to determine whether the current toolchain version matches one
    /// of the versions pinned in CI and if so, which one.
    pub fn extract_from_env() -> Option<ToolchainVersion> {
        if cfg!(__ZEROCOPY_INTERNAL_USE_ONLY_TOOLCHAIN = "msrv") {
            Some(ToolchainVersion::PinnedMsrv)
        } else if cfg!(__ZEROCOPY_INTERNAL_USE_ONLY_TOOLCHAIN = "stable") {
            Some(ToolchainVersion::PinnedStable)
        } else if cfg!(__ZEROCOPY_INTERNAL_USE_ONLY_TOOLCHAIN = "nightly") {
            Some(ToolchainVersion::PinnedNightly)
        } else {
            None
        }
    }

    /// Gets the name of the directory in which to store source files and
    /// expected output for UI tests for this toolchain version.
    ///
    /// UI tests depend on the exact error messages emitted by rustc, but those
    /// error messages are not stable, and sometimes change between Rust
    /// versions. Thus, we maintain one set of UI tests for each Rust version
    /// that we test in CI, and we pin to specific versions in CI (a specific
    /// MSRV, a specific stable version, and a specific date of the nightly
    /// compiler). Updating those pinned versions may also require updating
    /// these tests.
    /// - `tests/ui-nightly` - Contains the source of truth for our UI test
    ///   source files (`.rs`), and contains `.err` and `.out` files for nightly
    /// - `tests/ui-stable` - Contains symlinks to the `.rs` files in
    ///   `tests/ui-nightly`, and contains `.err` and `.out` files for stable
    /// - `tests/ui-msrv` - Contains symlinks to the `.rs` files in
    ///   `tests/ui-nightly`, and contains `.err` and `.out` files for MSRV
    pub fn get_ui_source_files_dirname(&self) -> &'static str {
        match self {
            ToolchainVersion::PinnedMsrv => "ui-msrv",
            ToolchainVersion::PinnedStable => "ui-stable",
            ToolchainVersion::PinnedNightly => "ui-nightly",
        }
    }
}

/// Sets `-Wwarnings` in `RUSTFLAGS`.
pub fn set_rustflags_w_warnings() {
    use parking_lot::Mutex;

    static ENV_MTX: Mutex<()> = parking_lot::const_mutex(());

    // Make sure we don't read/write the environment concurrently.
    // `env::set_var` should be `unsafe` to prevent this, but isn't. [1]
    //
    // [1] https://github.com/rust-lang/rust/issues/27970
    let guard = ENV_MTX.lock();

    let mut rustflags = std::env::var_os("RUSTFLAGS").unwrap_or_default();
    rustflags.push(" -Wwarnings");
    std::env::set_var("RUSTFLAGS", rustflags);

    std::mem::drop(guard);
}
