// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use cargo_metadata::MetadataCommand;
use rustc_version::{Channel, Version};
use std::error::Error;

struct PinnedVersions {
    msrv: String,
    stable: String,
    nightly: String,
}

impl PinnedVersions {
    /// Attempts to extract pinned toolchain versions based on the current
    /// working directory.
    ///
    /// `extract_from_pwd` expects to be called from a directory which is a
    /// child of a Cargo workspace. It extracts the pinned versions from the
    /// metadata of the root package.
    fn extract_from_pwd() -> Result<PinnedVersions, Box<dyn Error>> {
        let meta = MetadataCommand::new().exec()?;
        // NOTE(joshlf): In theory `meta.root_package()` should work instead of
        // this manual search, but for some reason it breaks when called from
        // zerocopy-derive's tests. This works as a workaround, and it's just
        // test code, so I didn't bother investigating.
        let pkg = meta
            .workspace_packages()
            .into_iter()
            .find(|pkg| pkg.name == "zerocopy")
            .ok_or("no `zerocopy` package found; are we in a workspace?")?;
        let msrv = pkg
            .rust_version
            .as_ref()
            .ok_or("failed to find msrv: no `rust-version` key present")?
            .to_string();
        let extract = |version_name, key| -> Result<String, String> {
            let value = pkg.metadata.pointer(&format!("/ci/{key}")).ok_or_else(|| {
                format!("failed to find {version_name}: no `metadata.ci.{key}` key present")
            })?;
            value.as_str().map(str::to_string).ok_or_else(|| format!("failed to find {version_name}: key `metadata.ci.{key}` (contents: {value:?}) failed to parse as JSON string"))
        };
        let stable = extract("stable", "pinned-stable")?;
        let nightly = extract("nightly", "pinned-nightly")?;
        Ok(PinnedVersions { msrv, stable, nightly })
    }
}

#[derive(Debug)]
pub enum ToolchainVersion {
    /// The version listed as our MSRV (ie, the `package.rust-version` key in
    /// `Cargo.toml`).
    PinnedMsrv,
    /// The stable version pinned in CI.
    PinnedStable,
    /// The nightly version pinned in CI
    PinnedNightly,
    /// A stable version other than the one pinned in CI.
    OtherStable,
    /// A nightly version other than the one pinned in CI.
    OtherNightly,
}

impl ToolchainVersion {
    /// Attempts to determine whether the current toolchain version matches one
    /// of the versions pinned in CI and if so, which one.
    pub fn extract_from_pwd() -> Result<ToolchainVersion, Box<dyn Error>> {
        let pinned_versions = PinnedVersions::extract_from_pwd()?;
        let current = rustc_version::version_meta()?;

        let s = match current.channel {
            Channel::Dev | Channel::Beta => {
                return Err(format!("unsupported channel: {:?}", current.channel).into())
            }
            Channel::Nightly => {
                format!(
                    "nightly-{}",
                    current.commit_date.as_ref().ok_or("nightly channel missing commit date")?
                )
            }
            Channel::Stable => {
                let Version { major, minor, patch, .. } = current.semver;
                format!("{major}.{minor}.{patch}")
            }
        };

        // Due to a quirk of how Rust nightly versions are encoded and published
        // [1], the version as understood by rustup uses a date one day ahead of
        // the version as encoded in the `rustc` binary itself.
        // `pinned_versions` encodes the former notion of the date (as it is
        // meant to be passed as the `+<toolchain>` selector syntax understood
        // by rustup), while `current` encodes the latter notion of the date (as
        // it is extracted from `rustc`). Without this adjustment, toolchain
        // versions that should be considered equal would not be.
        //
        // [1] https://github.com/rust-lang/rust/issues/51533
        let pinned_nightly_adjusted = {
            let desc = time::macros::format_description!("nightly-[year]-[month]-[day]");
            let date = time::Date::parse(&pinned_versions.nightly, &desc).map_err(|_| {
                format!("failed to parse nightly version: {}", pinned_versions.nightly)
            })?;
            let adjusted = date - time::Duration::DAY;
            adjusted.format(&desc).unwrap()
        };

        Ok(match s {
            s if s == pinned_versions.msrv => ToolchainVersion::PinnedMsrv,
            s if s == pinned_versions.stable => ToolchainVersion::PinnedStable,
            s if s == pinned_nightly_adjusted => ToolchainVersion::PinnedNightly,
            _ if current.channel == Channel::Stable => ToolchainVersion::OtherStable,
            _ if current.channel == Channel::Nightly => ToolchainVersion::OtherNightly,
            _ => {
                return Err(format!(
                    "current toolchain ({current:?}) doesn't match any known version"
                )
                .into())
            }
        })
    }

    /// Gets the name of the directory in which to store source files and
    /// expected output for UI tests for this toolchain version.
    ///
    /// For toolchain versions which are not pinned in CI, prints a warning to
    /// `stderr` which will be captured by the test harness and only printed on
    /// test failure.
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
    pub fn get_ui_source_files_dirname_and_maybe_print_warning(&self) -> &'static str {
        if matches!(self, ToolchainVersion::OtherStable | ToolchainVersion::OtherNightly) {
            // This will be eaten by the test harness and only displayed on
            // failure.
            eprintln!("warning: current toolchain does not match any toolchain pinned in CI; this may cause spurious test failure");
        }

        match self {
            ToolchainVersion::PinnedMsrv => "ui-msrv",
            ToolchainVersion::PinnedStable | ToolchainVersion::OtherStable => "ui-stable",
            ToolchainVersion::PinnedNightly | ToolchainVersion::OtherNightly => "ui-nightly",
        }
    }
}
