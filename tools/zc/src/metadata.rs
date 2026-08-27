// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Typed access to metadata in Zerocopy's package manifest.
//!
//! This module reads Zerocopy's manifest directly instead of invoking `cargo
//! metadata`. One of its consumers is `cargo-zerocopy`, which must choose a
//! toolchain before it invokes Cargo. Running Cargo to make that choice would
//! make bootstrapping depend on the ambient toolchain and introduce a nested
//! Cargo invocation into the wrapper's own setup path.
//!
//! `zerocopy/build.rs` also reads `[package.metadata.build-rs]`, but it parses
//! that table as text. Its literal header and line-format requirements are a
//! separate cross-file contract. Successfully reading the TOML here does not
//! prove that `build.rs` can read differently formatted TOML.

use std::{
    collections::BTreeMap,
    fs, io,
    path::{Path, PathBuf},
};

use serde::Deserialize;
use thiserror::Error;

/// The toolchain information stored in the Zerocopy package manifest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ToolchainMetadata {
    /// The crate's minimum supported Rust version (`package.rust-version`).
    pub rust_version: String,
    /// The stable toolchain used by CI (`package.metadata.ci.pinned-stable`).
    pub pinned_stable: String,
    /// The nightly toolchain used by CI (`package.metadata.ci.pinned-nightly`).
    pub pinned_nightly: String,
    /// Version cfg names and their first supported Rust versions.
    ///
    /// `zerocopy/build.rs` reads the same table without a TOML parser. Keep its
    /// documented text format intact when changing these entries; this map is
    /// only the structured view of that separate contract.
    pub build_rs: BTreeMap<String, String>,
    // This is intentionally private: consumers may ask whether the manifest
    // owns a workspace, but cannot manufacture metadata which claims that
    // topology without parsing the manifest.
    defines_workspace: bool,
}

impl ToolchainMetadata {
    /// Reads toolchain metadata from the Zerocopy manifest at `path`.
    ///
    /// Errors retain the path supplied by the caller. This matters when a
    /// validation command reads manifests from more than one worktree.
    pub fn read(path: impl AsRef<Path>) -> Result<Self, ReadMetadataError> {
        let path = path.as_ref();
        let source = fs::read_to_string(path)
            .map_err(|source| ReadMetadataError::Read { path: path.to_path_buf(), source })?;
        Self::parse(path, &source)
    }

    pub(crate) fn parse(path: &Path, source: &str) -> Result<Self, ReadMetadataError> {
        let manifest: Manifest = toml::from_str(source)
            .map_err(|source| ReadMetadataError::Parse { path: path.to_path_buf(), source })?;

        // `execution::build_operations` deliberately uses one native
        // `cargo test` invocation in place of separate dev-profile build and
        // test passes for ordinary libraries. A selected test profile can
        // change that build, while Cargo always forces tests and their
        // dependencies to unwind even if the dev profile requests abort.
        // Reject both differences before inventory or execution can rely on
        // consolidation. Other dev settings remain supported: a consolidated
        // ordinary library's integration tests compile its normal artifact
        // with those settings, while the executor retains an explicit build
        // for proc macros and ordinary selections without an enabled
        // integration target. The executor separately rejects corresponding
        // runner-owned inputs in CI; keep both halves coordinated.
        if manifest.profile.contains_key("test") {
            return Err(ReadMetadataError::TestProfile { path: path.to_path_buf() });
        }
        if manifest
            .profile
            .get("dev")
            .and_then(toml::Value::as_table)
            .and_then(|dev| dev.get("panic"))
            .is_some_and(|panic| panic.as_str() != Some("unwind"))
        {
            return Err(ReadMetadataError::DevPanicProfile { path: path.to_path_buf() });
        }

        Ok(Self {
            rust_version: manifest.package.rust_version,
            pinned_stable: manifest.package.metadata.ci.pinned_stable,
            pinned_nightly: manifest.package.metadata.ci.pinned_nightly,
            build_rs: manifest.package.metadata.build_rs,
            defines_workspace: manifest.workspace.is_some(),
        })
    }

    /// Reports whether this package manifest also defines a Cargo workspace.
    ///
    /// Inventory uses this before trusting the sibling `Cargo.lock`. Keeping
    /// the fact in the same typed parse as compiler metadata prevents a future
    /// workspace move from silently changing which lockfile Cargo reads.
    pub(crate) fn defines_workspace(&self) -> bool {
        self.defines_workspace
    }
}

/// An error reading toolchain metadata from a Zerocopy manifest.
#[derive(Debug, Error)]
pub enum ReadMetadataError {
    /// The manifest could not be read.
    #[error("failed to read Zerocopy manifest `{path}`: {source}")]
    Read {
        /// The path passed to [`ToolchainMetadata::read`].
        path: PathBuf,
        /// The underlying file-system error.
        #[source]
        source: io::Error,
    },
    /// The manifest did not contain well-typed toolchain metadata.
    #[error("failed to parse toolchain metadata from `{path}`: {source}")]
    Parse {
        /// The path passed to [`ToolchainMetadata::read`].
        path: PathBuf,
        /// The TOML syntax or deserialization error.
        #[source]
        source: toml::de::Error,
    },
    /// The workspace root declared a test profile which breaks CI's
    /// build/test consolidation assumption.
    #[error(
        "Cargo test profile in `{path}` is unsupported: consolidated ordinary-library CI requires Cargo's built-in test profile"
    )]
    TestProfile {
        /// The manifest which declared the profile.
        path: PathBuf,
    },
    /// The workspace root selected a dev panic strategy which Cargo does not
    /// preserve while compiling tests and their dependencies.
    #[error(
        "Cargo dev panic profile in `{path}` is unsupported: consolidated CI requires the unwind panic strategy"
    )]
    DevPanicProfile {
        /// The manifest which declared the profile.
        path: PathBuf,
    },
}

#[derive(Deserialize)]
struct Manifest {
    workspace: Option<toml::Table>,
    package: Package,
    // Cargo accepts table headers, dotted keys, quoted keys, and inline tables
    // for the same logical profile map. Deserialize the map instead of
    // searching source text so all equivalent spellings reach one check.
    #[serde(default)]
    profile: BTreeMap<String, toml::Value>,
}

#[derive(Deserialize)]
struct Package {
    #[serde(rename = "rust-version")]
    rust_version: String,
    metadata: PackageMetadata,
}

#[derive(Deserialize)]
struct PackageMetadata {
    #[serde(rename = "build-rs")]
    build_rs: BTreeMap<String, String>,
    ci: CiMetadata,
}

#[derive(Deserialize)]
struct CiMetadata {
    #[serde(rename = "pinned-stable")]
    pinned_stable: String,
    #[serde(rename = "pinned-nightly")]
    pinned_nightly: String,
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::{ReadMetadataError, ToolchainMetadata};

    #[test]
    fn reads_the_toolchain_contract() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("testdata/toolchains.toml");
        let metadata = ToolchainMetadata::read(path).unwrap();

        assert_eq!(metadata.rust_version, "1.56.0");
        assert_eq!(metadata.pinned_stable, "1.93.1");
        assert_eq!(metadata.pinned_nightly, "nightly-2026-01-25");
        assert!(metadata.defines_workspace());
        assert_eq!(
            metadata.build_rs,
            [
                ("no-zerocopy-example-1-60-0".to_owned(), "1.60.0".to_owned()),
                ("no-zerocopy-example-1-81-0".to_owned(), "1.81.0".to_owned()),
            ]
            .into_iter()
            .collect()
        );
    }

    #[test]
    fn reports_the_manifest_path_for_invalid_metadata() {
        let path = Path::new("some-worktree/zerocopy/Cargo.toml");
        let error = ToolchainMetadata::parse(
            path,
            r#"
                [package]
                rust-version = "1.56.0"

                [package.metadata.build-rs]
                no-zerocopy-example-1-60-0 = "1.60.0"

                [package.metadata.ci]
                pinned-stable = "1.93.1"
            "#,
        )
        .unwrap_err();

        match &error {
            ReadMetadataError::Parse { path: error_path, source } => {
                assert_eq!(error_path, path);
                assert!(source.to_string().contains("pinned-nightly"));
            }
            ReadMetadataError::Read { .. }
            | ReadMetadataError::TestProfile { .. }
            | ReadMetadataError::DevPanicProfile { .. } => {
                panic!("expected a parse error")
            }
        }
        assert!(error.to_string().contains(&path.display().to_string()));
    }

    #[test]
    fn reports_the_manifest_path_for_io_errors() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("testdata/this-file-intentionally-does-not-exist.toml");
        let error = ToolchainMetadata::read(&path).unwrap_err();

        match &error {
            ReadMetadataError::Read { path: error_path, .. } => assert_eq!(error_path, &path),
            ReadMetadataError::Parse { .. }
            | ReadMetadataError::TestProfile { .. }
            | ReadMetadataError::DevPanicProfile { .. } => {
                panic!("expected a read error")
            }
        }
        assert!(error.to_string().contains(&path.display().to_string()));
    }

    #[test]
    fn rejects_every_test_profile_toml_spelling() {
        let path = Path::new("some-worktree/zerocopy/Cargo.toml");
        let base = include_str!("../testdata/toolchains.toml");

        for declaration in [
            "[profile.test]\nopt-level = 1\n",
            "[profile.\"test\"]\nopt-level = 1\n",
            "[\"profile\".test]\nopt-level = 1\n",
            "profile.test.opt-level = 1\n",
            "profile = { test = { opt-level = 1 } }\n",
            "[profile.test.package.zerocopy]\nopt-level = 1\n",
            "[profile.test.build-override]\nopt-level = 1\n",
        ] {
            let source = format!("{declaration}\n{base}");
            let error = ToolchainMetadata::parse(path, &source).unwrap_err();
            assert!(
                matches!(error, ReadMetadataError::TestProfile { path: ref error_path } if error_path == path),
                "declaration {declaration:?} produced {error}"
            );
        }

        // Profiles which cannot be selected by the consolidated native
        // command do not affect its dev/test equivalence.
        let source = format!("[profile.release]\nopt-level = 1\n\n{base}");
        ToolchainMetadata::parse(path, &source).unwrap();
    }

    #[test]
    fn rejects_every_non_unwind_dev_panic_toml_spelling() {
        let path = Path::new("some-worktree/zerocopy/Cargo.toml");
        let base = include_str!("../testdata/toolchains.toml");

        for declaration in [
            "[profile.dev]\npanic = \"abort\"\n",
            "[profile.\"dev\"]\npanic = \"abort\"\n",
            "[\"profile\".dev]\npanic = \"abort\"\n",
            "profile.dev.panic = \"abort\"\n",
            "profile = { dev = { panic = \"abort\" } }\n",
        ] {
            let source = format!("{declaration}\n{base}");
            let error = ToolchainMetadata::parse(path, &source).unwrap_err();
            assert!(
                matches!(error, ReadMetadataError::DevPanicProfile { path: ref error_path } if error_path == path),
                "declaration {declaration:?} produced {error}"
            );
        }

        // Cargo preserves ordinary dev settings for a library artifact built
        // by integration tests, and proc-macro cells retain an explicit build.
        // An explicit unwind strategy also matches Cargo's forced test value.
        for declaration in [
            "[profile.dev]\nopt-level = 1\n",
            "[profile.dev]\npanic = \"unwind\"\n",
            "[profile.dev.package.zerocopy]\nopt-level = 1\n",
            "[profile.dev.build-override]\nopt-level = 1\n",
        ] {
            let source = format!("{declaration}\n{base}");
            ToolchainMetadata::parse(path, &source).unwrap();
        }
    }
}
