// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Live repository inventory for the CI control plane.
//!
//! [`Policy`](crate::policy::Policy) records deliberate coverage choices;
//! Cargo metadata records what the repository actually contains. This module
//! keeps those roles separate. In particular, it does not reimplement Cargo's
//! package, feature, or target discovery from TOML. It asks Cargo once, turns
//! the answer into deterministic typed collections, and checks every policy
//! reference against that answer.
//!
//! There are four deliberately independent cross-file contracts here:
//!
//! * `ci/zc.toml` names packages, feature profiles, compilation targets, and
//!   toolchain sources. Its package paths and profile choices must agree with
//!   Cargo metadata. The planner may consume only a validated inventory.
//! * `zerocopy/Cargo.toml` owns feature edges and compiler versions. The stable
//!   feature set is the closure of the aggregate feature named by policy. The
//!   nightly set is its complement, so neither set is copied into another
//!   configuration file.
//! * `zerocopy/build.rs` parses `[package.metadata.build-rs]` as text rather
//!   than TOML. This module checks the narrower textual grammar before a
//!   harmless formatting edit can make that build script panic in CI.
//! * `ci/rust-target-support.toml` records the exact target/version pairs
//!   selected by the policy and manifest. This offline evidence keeps planning
//!   network-free; its typed refresh command verifies changed stable/nightly
//!   pins against rustup before rewriting the catalog.
//!
//! The frozen files named by `Policy::baselines` remain independent evidence
//! of the old workflow's behavior. Inventory checks that every file exists,
//! but does not generate or bless one. Likewise, permissions, secrets,
//! runners, action references, and publication remain hand-reviewed workflow
//! concerns; none belongs in this unprivileged repository inventory.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    error::Error,
    ffi::OsString,
    fmt,
    fmt::Write as _,
    fs, io,
    io::Write as _,
    path::{Component, Path, PathBuf},
    process::Command,
};

use cargo_metadata::{CargoOpt, MetadataCommand, PackageId, Resolve, TargetKind};
use thiserror::Error;

use crate::{
    identifier::{self, IdentifierError},
    metadata::{ReadMetadataError, ToolchainMetadata},
    policy::{FeatureProfile, Policy, ReadPolicyError, TargetMode, ToolchainSource},
    repository_file::{self, OpenRepositoryFileError, OpenedRepositoryFile},
};

const PRIMARY_PACKAGE_ID: &str = "zerocopy";

// This checked-in file records only the target/version pairs selected by
// policy. Inventory cannot ask every compiler directly: doing so would make
// the unprivileged plan job download all of the historical build-rs toolchains
// before it could emit a matrix. Keep this path and the refresh instructions
// in the file coordinated. Version-keying makes a toolchain roll fail until
// its compact support evidence is deliberately refreshed.
const RUST_TARGET_SUPPORT_PATH: &str = "ci/rust-target-support.toml";
const RUST_TARGET_SUPPORT_SCHEMA_VERSION: u32 = 1;

// The refresh command owns the canonical text before the schema. Keeping this
// prose with its renderer prevents a successful roll from discarding the
// cross-file maintenance guidance embedded in the checked-in evidence.
const RUST_TARGET_SUPPORT_PREAMBLE: &str = r#"# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# This is independent, offline evidence for the Rust target/version pairs on
# which CI currently relies. `ci/zc.toml` owns targets, target sets, and their
# toolchain scopes; `zerocopy/Cargo.toml` owns the exact compiler versions.
# `tools/zc/src/inventory.rs` resolves both files, then requires this support
# map to contain exactly their selected pairs. A target, scope, or compiler
# version change therefore fails planning until this file is reviewed too.
#
# Do not infer support from a target-looking name. The stable/nightly roller
# invokes the typed `refresh-rust-target-support` tool after changing a pin.
# For other policy or toolchain changes, install every affected exact version,
# inspect the authoritative list, then update this compact file deliberately:
#
#   rustup target list --toolchain VERSION
#
# After updating all affected rows, install every cataloged compiler and run:
#
#   ./tools/cargo.sh test --locked --offline -p zc \
#     inventory::tests::target_support_evidence_matches_rustup -- \
#     --ignored --exact
#
# Every target below must appear in that output. Keep the toolchain tables and
# each target array sorted lexicographically, and list only the union of targets
# selected on that version by ordinary, Miri, and semver scopes. Do not copy
# Rust's complete target catalog here: it would obscure the small set of
# assumptions reviewers need to check.
# This preamble and the tables are renderer-owned canonical text; update the
# renderer in `tools/zc/src/inventory.rs` when changing these instructions.
#
"#;

// The ordinary executor runs inside the x86_64 Linux CI image named by
// `.github/workflows/ci.yml`. That image can execute its native 64-bit target
// and the 32-bit x86 userspace installed by `gcc-multilib` in
// `.github/ci-image/Dockerfile`, but no other configured target. Keep this
// allow-list coordinated with those two files, the producer and consumer
// audits in `planned_adapter/{image,matrix}.rs`, and
// `execution::build_operations`. A future native-capable runner must update
// this independent check before changing a policy mode can enable execution.
const NATIVE_EXECUTION_TARGETS: [&str; 2] = ["i686-unknown-linux-gnu", "x86_64-unknown-linux-gnu"];

// `TargetMode::Thumb` names one current exception rather than a general target
// family: its test dependencies do not compile, so the executor checks only
// the library. Keep this identity coordinated with that enum's documentation
// and the thumb branches in `execution::build_operations`.
const THUMB_EXECUTION_TARGET: &str = "thumbv6m-none-eabi";

// `testutil` is a workspace package so Cargo can resolve one shared lockfile,
// but it is test support rather than an independently published CI subject.
// Every other workspace package must appear in `ci/zc.toml`. Keep this one
// explicit exception coordinated with `zerocopy/Cargo.toml`'s workspace and
// dev-dependency declarations. A newly added package then fails inventory
// instead of silently receiving no matrix coverage.
const SUPPORT_PACKAGES: [(&str, &str); 1] = [("testutil", "zerocopy/testutil/Cargo.toml")];

/// Cargo's deterministic description of one workspace package.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CargoPackage {
    name: String,
    manifest: PathBuf,
    rust_version: Option<String>,
    // Cargo reports the package default and each target's effective edition.
    // Retain all of them: an explicit per-target override can require a newer
    // compiler than the package default, and even an otherwise unused target
    // must still be understood while Cargo loads the manifest.
    editions: BTreeSet<String>,
    features: BTreeMap<String, BTreeSet<String>>,
    dependencies: BTreeMap<String, Dependency>,
    // Keep package identity separate from the renamed dependency keys above.
    // CI commands compile dev, build, optional, and target-specific path
    // dependencies under different cells; MSRV validation conservatively
    // follows every local workspace edge rather than reimplementing Cargo's
    // feature and target resolver.
    workspace_dependencies: BTreeSet<PathBuf>,
    targets: BTreeSet<CargoTarget>,
}

impl CargoPackage {
    /// Returns the Cargo package name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the manifest path relative to the repository root.
    pub fn manifest(&self) -> &Path {
        &self.manifest
    }

    /// Returns the package's `rust-version`, if it declares one.
    pub fn rust_version(&self) -> Option<&str> {
        self.rust_version.as_deref()
    }

    /// Returns Cargo's complete local feature graph.
    pub fn features(&self) -> &BTreeMap<String, BTreeSet<String>> {
        &self.features
    }

    /// Returns every Cargo target belonging to this package.
    pub fn targets(&self) -> &BTreeSet<CargoTarget> {
        &self.targets
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Dependency {
    optional: bool,
}

/// One Cargo target discovered from a workspace manifest.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CargoTarget {
    package: String,
    name: String,
    kinds: BTreeSet<String>,
    crate_types: BTreeSet<String>,
    source: PathBuf,
    required_features: BTreeSet<String>,
    test: bool,
    doctest: bool,
    doc: bool,
}

impl CargoTarget {
    /// Returns the package which owns this target.
    pub fn package(&self) -> &str {
        &self.package
    }

    /// Returns the Cargo target name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the target kinds reported by Cargo.
    pub fn kinds(&self) -> &BTreeSet<String> {
        &self.kinds
    }

    /// Returns the artifact crate types reported by Cargo.
    pub fn crate_types(&self) -> &BTreeSet<String> {
        &self.crate_types
    }

    /// Returns the target's source path relative to the repository root.
    pub fn source(&self) -> &Path {
        &self.source
    }

    /// Returns the Cargo features required to build this target.
    pub fn required_features(&self) -> &BTreeSet<String> {
        &self.required_features
    }

    /// Returns whether `cargo test` tests this target by default.
    pub fn is_tested(&self) -> bool {
        self.test
    }

    /// Returns whether Cargo runs documentation tests for this target.
    pub fn has_doctests(&self) -> bool {
        self.doctest
    }

    /// Returns whether `cargo doc` documents this target.
    pub fn is_documented(&self) -> bool {
        self.doc
    }
}

/// Feature and target facts for one policy package.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackageInventory {
    cargo: CargoPackage,
    stable_features: BTreeSet<String>,
    nightly_features: BTreeSet<String>,
    default_features: BTreeSet<String>,
}

impl PackageInventory {
    /// Returns Cargo's package description.
    pub fn cargo(&self) -> &CargoPackage {
        &self.cargo
    }

    /// Returns the stable aggregate feature's local closure.
    pub fn stable_features(&self) -> &BTreeSet<String> {
        &self.stable_features
    }

    /// Returns features outside the stable aggregate closure.
    pub fn nightly_features(&self) -> &BTreeSet<String> {
        &self.nightly_features
    }

    /// Returns the local closure of Cargo's `default` feature.
    pub fn default_features(&self) -> &BTreeSet<String> {
        &self.default_features
    }
}

/// Repository facts which have passed every inventory check.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepositoryInventory {
    workspace_packages: BTreeMap<PathBuf, CargoPackage>,
    policy_packages: BTreeMap<String, PackageInventory>,
    cargo_targets: BTreeSet<CargoTarget>,
    toolchain_versions: BTreeMap<String, String>,
}

impl RepositoryInventory {
    /// Collects and validates live facts rooted at `repository_root`.
    pub fn audit(repository_root: impl AsRef<Path>, policy: &Policy) -> Result<Self, AuditError> {
        let collected =
            CollectedRepository::collect(repository_root, policy).map_err(AuditError::Collect)?;
        collected.validate(policy).map_err(AuditError::Invalid)
    }

    /// Returns all Cargo workspace packages, keyed by manifest path.
    pub fn workspace_packages(&self) -> &BTreeMap<PathBuf, CargoPackage> {
        &self.workspace_packages
    }

    /// Returns validated packages, keyed by policy identifier.
    pub fn policy_packages(&self) -> &BTreeMap<String, PackageInventory> {
        &self.policy_packages
    }

    /// Returns every target reported for every workspace package.
    pub fn cargo_targets(&self) -> &BTreeSet<CargoTarget> {
        &self.cargo_targets
    }

    /// Returns exact compiler descriptors, keyed by policy toolchain ID.
    pub fn toolchain_versions(&self) -> &BTreeMap<String, String> {
        &self.toolchain_versions
    }
}

/// A collection failure or an aggregated validation failure.
#[derive(Debug, Error)]
pub enum AuditError {
    /// Live repository facts could not be collected.
    #[error(transparent)]
    Collect(#[from] CollectError),
    /// Facts were collected but violated one or more contracts.
    #[error(transparent)]
    Invalid(#[from] InventoryErrors),
}

/// Failure while refreshing support evidence after a pinned-toolchain roll.
#[derive(Debug, Error)]
pub enum RefreshTargetSupportError {
    /// A fixed repository input failed containment or identity checks.
    #[error(transparent)]
    Repository(#[from] CollectError),
    /// The checked-in CI policy could not be read or validated.
    #[error(transparent)]
    Policy(#[from] ReadPolicyError),
    /// The post-edit Zerocopy manifest could not be read.
    #[error(transparent)]
    Metadata(#[from] ReadMetadataError),
    /// Existing support evidence could not be read.
    #[error("failed to read Rust target-support evidence `{path}`: {source}")]
    Read {
        /// Checked-in evidence path.
        path: PathBuf,
        /// File-system diagnostic.
        #[source]
        source: io::Error,
    },
    /// Existing support evidence was not valid TOML.
    #[error("failed to parse Rust target-support evidence `{path}`: {source}")]
    Parse {
        /// Checked-in evidence path.
        path: PathBuf,
        /// TOML diagnostic.
        #[source]
        source: Box<toml::de::Error>,
    },
    /// The command was asked to roll a pin it does not own.
    #[error("unsupported pinned toolchain `{0}`; expected `stable` or `nightly`")]
    UnsupportedPin(String),
    /// A supplied pre- or post-roll pin was not an exact compiler descriptor.
    #[error("{pin} toolchain version `{version}` is not an exact pinned compiler descriptor")]
    InvalidPinVersion {
        /// Stable or nightly metadata field.
        pin: String,
        /// Invalid exact descriptor.
        version: String,
    },
    /// The writable catalog path redirected to another file.
    #[error(
        "Rust target-support path `{configured}` redirects to `{resolved}`; replace it with a regular file at the configured path"
    )]
    RedirectedCatalog {
        /// Fixed checked-in path.
        configured: PathBuf,
        /// Resolved destination.
        resolved: PathBuf,
    },
    /// The existing catalog did not describe the state before this roll.
    #[error("refusing to refresh target support because unrelated evidence already drifted:\n{0}")]
    ExistingDrift(InventoryErrors),
    /// rustup could not inspect the changed exact compiler.
    #[error("failed to run `{command}`: {source}")]
    RustupIo {
        /// Human-readable command.
        command: String,
        /// Process-launch diagnostic.
        #[source]
        source: io::Error,
    },
    /// rustup rejected the changed exact compiler.
    #[error("`{command}` failed with {status}:\n{stderr}")]
    RustupFailed {
        /// Human-readable command.
        command: String,
        /// Exit status.
        status: std::process::ExitStatus,
        /// Captured standard error.
        stderr: String,
    },
    /// rustup emitted non-UTF-8 target data.
    #[error("`{command}` produced non-UTF-8 output: {source}")]
    RustupUtf8 {
        /// Human-readable command.
        command: String,
        /// UTF-8 diagnostic.
        #[source]
        source: std::string::FromUtf8Error,
    },
    /// rustup output did not match its strict target-list protocol.
    #[error("`{command}` returned malformed target list line {line}: {message}")]
    MalformedRustupOutput {
        /// Human-readable command.
        command: String,
        /// One-based output line, or zero for an empty list.
        line: usize,
        /// Protocol violation.
        message: String,
    },
    /// One or more selected targets are unavailable on the changed compiler.
    #[error(
        "Rust `{version}` does not distribute selected target(s): {targets}",
        targets = .targets.join(", ")
    )]
    UnsupportedTargets {
        /// Exact post-roll compiler version.
        version: String,
        /// Missing selected target names.
        targets: Vec<String>,
    },
    /// A temporary catalog could not be written or atomically installed.
    #[error("failed to atomically rewrite Rust target-support evidence `{path}`: {source}")]
    Write {
        /// Checked-in evidence path.
        path: PathBuf,
        /// File-system diagnostic.
        #[source]
        source: io::Error,
    },
}

/// A failure collecting live Cargo or file-system facts.
#[derive(Debug, Error)]
pub enum CollectError {
    /// The repository root could not be canonicalized.
    #[error("failed to resolve repository root `{path}`: {source}")]
    RepositoryRoot {
        /// The path supplied to the collector.
        path: PathBuf,
        /// The underlying file-system error.
        #[source]
        source: io::Error,
    },
    /// Policy did not contain the package which owns toolchain metadata.
    #[error("CI policy must contain a `{PRIMARY_PACKAGE_ID}` package")]
    MissingPrimaryPackage,
    /// Cargo metadata could not describe the primary workspace.
    #[error("failed to collect Cargo metadata from `{manifest}`: {source}")]
    CargoMetadata {
        /// The manifest passed to Cargo.
        manifest: PathBuf,
        /// Cargo metadata's diagnostic.
        #[source]
        source: cargo_metadata::Error,
    },
    /// Cargo omitted the dependency graph requested by inventory collection.
    #[error("Cargo metadata omitted its resolved dependency graph")]
    MissingDependencyGraph,
    /// Cargo's resolved graph named a package absent from package metadata.
    #[error("Cargo dependency graph refers to package `{package}` absent from package metadata")]
    MissingResolvedPackage {
        /// Opaque Cargo package identity missing from `metadata.packages`.
        package: String,
    },
    /// Cargo selected a target directory outside the collector's fixed contract.
    #[error(
        "Cargo metadata selected target directory `{found}` instead of audited directory `{expected}`"
    )]
    UnexpectedCargoTargetDirectory {
        /// Fixed output directory supplied to the metadata command.
        expected: PathBuf,
        /// Directory Cargo reported after applying all of its inputs.
        found: PathBuf,
    },
    /// The primary package manifest stopped defining the audited workspace.
    #[error(
        "primary manifest `{path}` must define `[workspace]` so its directory owns the lockfile audited before Cargo runs"
    )]
    PrimaryManifestNotWorkspaceRoot {
        /// Canonical primary manifest which must remain the workspace root.
        path: PathBuf,
    },
    /// Cargo's workspace lockfile was absent or not a regular file.
    #[error("Cargo lockfile `{path}` must exist as a regular repository file before Cargo runs")]
    InvalidCargoLockfile {
        /// Fixed lockfile path beside the primary workspace manifest.
        path: PathBuf,
    },
    /// Cargo's workspace lockfile was not valid TOML with a format version.
    #[error("failed to parse Cargo lockfile `{path}`: {source}")]
    CargoLockfile {
        /// Canonical lockfile path.
        path: PathBuf,
        /// The TOML parser's diagnostic.
        #[source]
        source: Box<toml::de::Error>,
    },
    /// Cargo's workspace lockfile uses a format whose floor is not modeled.
    #[error(
        "Cargo lockfile `{path}` uses unsupported format version {version}; extend the audited Cargo compatibility table before accepting it"
    )]
    UnsupportedCargoLockfileVersion {
        /// Canonical lockfile path.
        path: PathBuf,
        /// Unrecognized top-level lockfile version.
        version: u32,
    },
    /// Cargo's lockfile predates an unambiguous top-level format marker.
    #[error(
        "Cargo lockfile `{path}` has no format version; V1 and V2 are indistinguishable without one, so regenerate or deliberately extend the audited compatibility model"
    )]
    AmbiguousCargoLockfileVersion {
        /// Canonical lockfile path.
        path: PathBuf,
    },
    /// A repository path resolved outside this repository.
    #[error(
        "repository path `{path}` resolves to `{resolved}`, outside repository `{repository_root}`"
    )]
    PathOutsideRepository {
        /// The repository root used for collection.
        repository_root: PathBuf,
        /// The spelling reported by Cargo or selected by repository policy.
        path: PathBuf,
        /// The physical path after following symbolic links.
        resolved: PathBuf,
    },
    /// A repository path could not be resolved or inspected.
    #[error("failed to resolve repository path `{path}`: {source}")]
    RepositoryPath {
        /// The spelling reported by Cargo or selected by repository policy.
        path: PathBuf,
        /// The underlying file-system error.
        #[source]
        source: io::Error,
    },
    /// A repository file changed between containment and identity checks.
    #[error(
        "repository file `{path}` changed while it was opened: first resolved to `{first}`, then to `{second}`"
    )]
    RepositoryFileChangedDuringOpen {
        /// Configured repository path.
        path: PathBuf,
        /// Canonical destination checked before opening.
        first: PathBuf,
        /// Canonical destination checked after opening.
        second: PathBuf,
    },
    /// A required repository input was not a regular file.
    #[error("repository input `{path}` is not a regular file")]
    RepositoryPathNotFile {
        /// Canonical path to the non-file object.
        path: PathBuf,
    },
    /// Cargo's checked-in configuration was not valid TOML.
    #[error("failed to parse Cargo configuration `{path}`: {source}")]
    CargoConfiguration {
        /// Canonical checked-in Cargo configuration path.
        path: PathBuf,
        /// The TOML parser's diagnostic.
        #[source]
        source: Box<toml::de::Error>,
    },
    /// Cargo's checked-in source replacement was missing or ambiguous.
    #[error("invalid Cargo source configuration in `{path}`: {message}")]
    InvalidCargoSourceConfiguration {
        /// Canonical checked-in Cargo configuration path.
        path: PathBuf,
        /// Exact unsupported or inconsistent source contract.
        message: String,
    },
    /// Cargo's checked-in environment could alter unmodeled build behavior.
    #[error("invalid Cargo environment configuration in `{path}`: {message}")]
    InvalidCargoEnvironmentConfiguration {
        /// Canonical checked-in Cargo configuration path.
        path: PathBuf,
        /// Exact unsupported or inconsistent environment contract.
        message: String,
    },
    /// Cargo's legacy extensionless configuration could override the audited file.
    #[error(
        "legacy Cargo configuration `{path}` exists; remove it so Cargo and CI inventory both use `{preferred}`"
    )]
    LegacyCargoConfiguration {
        /// Legacy path which Cargo gives precedence when both spellings exist.
        path: PathBuf,
        /// Checked-in configuration spelling audited by this collector.
        preferred: PathBuf,
    },
    /// A repository ancestor contained another configuration Cargo would merge.
    #[error(
        "Cargo would merge unsupported ancestor configuration `{path}` with audited configuration `{audited}`"
    )]
    UnexpectedCargoConfiguration {
        /// Additional repository-owned configuration entry.
        path: PathBuf,
        /// Sole Cargo configuration modeled by inventory.
        audited: PathBuf,
    },
    /// A package-source link could make generated Cargo output visible as input.
    #[error(
        "package source symlink `{path}` resolves to `{resolved}`, which contains Cargo target directory `{target}`"
    )]
    CargoTargetSourceAlias {
        /// Symbolic link encountered while walking package source.
        path: PathBuf,
        /// Canonical directory selected by the link.
        resolved: PathBuf,
        /// Generated directory which must not hide behind a source alias.
        target: PathBuf,
    },
    /// A local dependency was absent from the classified workspace inventory.
    #[error(
        "workspace package `{package}` has local dependency `{dependency}` at unclassified manifest `{manifest}`"
    )]
    UnclassifiedLocalDependency {
        /// Package which declares the dependency.
        package: String,
        /// Cargo dependency name before any local rename.
        dependency: String,
        /// Repository-relative dependency manifest.
        manifest: PathBuf,
    },
    /// A repository file could not be read.
    #[error("failed to read `{path}`: {source}")]
    Read {
        /// The path being read.
        path: PathBuf,
        /// The underlying file-system error.
        #[source]
        source: io::Error,
    },
    /// Structured Zerocopy toolchain metadata could not be read.
    #[error(transparent)]
    ToolchainMetadata(#[from] ReadMetadataError),
    /// The checked-in Rust target-support evidence was not valid TOML.
    #[error("failed to parse Rust target-support evidence `{path}`: {source}")]
    RustTargetSupport {
        /// Canonical support-file path.
        path: PathBuf,
        /// The TOML parser's diagnostic.
        #[source]
        source: Box<toml::de::Error>,
    },
}

/// Reviewed evidence for the target/version pairs on which CI relies.
///
/// This deliberately stores only selected pairs, not eleven opaque copies of
/// Rust's complete target list. Semantic validation requires its version keys
/// and target sets to agree exactly with the live policy. The typed refresh
/// command verifies changed pins against rustup before rewriting this compact
/// evidence; ordinary validation remains deliberately offline.
#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct RustTargetSupport {
    schema_version: u32,
    toolchains: Vec<RustTargetSupportEntry>,
}

#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct RustTargetSupportEntry {
    version: String,
    targets: Vec<String>,
}

/// Cargo-owned facts for any package in the complete resolved graph.
///
/// Workspace packages retain their richer [`CargoPackage`] representation and
/// remain the only packages exposed by [`RepositoryInventory`]. This parallel
/// record exists because registry packages still constrain every compiler that
/// reaches them, while `PackageId` is the only collision-free identity for two
/// versions or sources of the same package name.
#[derive(Clone, Debug, Eq, PartialEq)]
struct ResolvedPackage {
    name: String,
    version: String,
    manifest: PathBuf,
    rust_version: Option<String>,
    editions: BTreeSet<String>,
    dependencies: BTreeSet<PackageId>,
}

/// One checked-in Cargo.lock serialization format with a known Cargo floor.
///
/// Cargo's own `ResolveVersion` documentation is the authority for this
/// intentionally closed table. V2 was introduced in Cargo 1.38, but both V1
/// and V2 omit a version marker and therefore cannot be distinguished from
/// their header alone; inventory rejects that ambiguous legacy spelling. V3
/// was introduced in Cargo 1.47 and V4 in Cargo 1.78. A future lockfile format
/// must fail collection until its reader floor is reviewed and added here;
/// guessing would let old compatibility jobs reach bytes they cannot parse.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CargoLockfileVersion {
    V3,
    V4,
}

impl CargoLockfileVersion {
    fn parse(version: u32) -> Option<Self> {
        match version {
            3 => Some(Self::V3),
            4 => Some(Self::V4),
            _ => None,
        }
    }

    fn display(self) -> &'static str {
        match self {
            Self::V3 => "V3",
            Self::V4 => "V4",
        }
    }

    fn minimum_cargo_version(self) -> RustVersion {
        match self {
            Self::V3 => RustVersion::new(1, 47, 0),
            Self::V4 => RustVersion::new(1, 78, 0),
        }
    }
}

/// Live facts kept separate from semantic validation for mutation tests.
#[derive(Clone, Debug)]
pub struct CollectedRepository {
    repository_root: PathBuf,
    packages: BTreeMap<PathBuf, CargoPackage>,
    workspace_package_ids: BTreeMap<PathBuf, PackageId>,
    resolved_packages: BTreeMap<PackageId, ResolvedPackage>,
    conventional_sources: BTreeSet<PathBuf>,
    existing_files: BTreeMap<PathBuf, bool>,
    primary_manifest_source: String,
    toolchain_metadata: ToolchainMetadata,
    rust_target_support: RustTargetSupport,
    cargo_lockfile_version: CargoLockfileVersion,
}

impl CollectedRepository {
    /// Collects Cargo metadata and repository file facts without interpreting
    /// policy semantics.
    ///
    /// Cargo is run with `--locked --offline --all-features`. Inventory must
    /// never update a lockfile or turn a validation command into network
    /// access. Full resolution is required to identify dependencies redirected
    /// to workspace packages by Cargo's patch and replacement mechanisms.
    pub fn collect(
        repository_root: impl AsRef<Path>,
        policy: &Policy,
    ) -> Result<Self, CollectError> {
        let supplied_root = repository_root.as_ref();
        let repository_root = supplied_root.canonicalize().map_err(|source| {
            CollectError::RepositoryRoot { path: supplied_root.to_path_buf(), source }
        })?;

        // Zerocopy is the root package which owns CI compiler metadata. If a
        // future repository split changes that fact, failing here forces a
        // deliberate collector migration rather than selecting another
        // manifest by map order.
        let primary =
            policy.packages().get(PRIMARY_PACKAGE_ID).ok_or(CollectError::MissingPrimaryPackage)?;
        // Policy paths are syntactically repository-relative, but a checked-in
        // symlink can still escape the checkout. Open the primary manifest
        // through the shared retained-handle boundary, then derive every local
        // parse from those exact bytes instead of reopening the checked path.
        // Cargo itself still requires a path; pass it the canonical spelling
        // selected by the same boundary.
        let primary_manifest_file =
            open_inventory_file(&repository_root, primary.manifest().as_path())?;
        let primary_manifest = primary_manifest_file.path().to_path_buf();
        let primary_manifest_source = primary_manifest_file
            .read_to_string()
            .map_err(|source| CollectError::Read { path: primary_manifest.clone(), source })?;
        let cargo_directory =
            primary_manifest.parent().expect("a repository-relative manifest always has a parent");
        // Keep Cargo's audited configuration open through the metadata
        // subprocess. This does not turn Cargo's path-based reads into an
        // atomic filesystem snapshot, but it prevents identity reuse and
        // keeps our complete parsed input alive for the whole observation.
        let _cargo_configuration_file =
            validate_cargo_source_configuration(&repository_root, cargo_directory)?;
        let toolchain_metadata =
            ToolchainMetadata::parse(&primary_manifest, &primary_manifest_source)?;
        // Target-support evidence is a fixed CI input, not a policy-selected
        // path. Read it through the same retained-handle containment boundary
        // as the primary manifest. Its exact version keys are checked only
        // after toolchain metadata and policy have been reconciled below.
        let rust_target_support_file =
            open_inventory_file(&repository_root, Path::new(RUST_TARGET_SUPPORT_PATH))?;
        let rust_target_support_source =
            rust_target_support_file.read_to_string().map_err(|source| CollectError::Read {
                path: rust_target_support_file.path().to_path_buf(),
                source,
            })?;
        let rust_target_support =
            toml::from_str(&rust_target_support_source).map_err(|source| {
                CollectError::RustTargetSupport {
                    path: rust_target_support_file.path().to_path_buf(),
                    source: Box::new(source),
                }
            })?;
        // `--locked` reads the lockfile before metadata gives us Cargo's
        // workspace root. Require the primary manifest to keep owning the
        // workspace so this preflight cannot silently validate the wrong
        // `Cargo.lock` after a repository-layout change.
        if !toolchain_metadata.defines_workspace() {
            return Err(CollectError::PrimaryManifestNotWorkspaceRoot {
                path: primary_manifest.clone(),
            });
        }
        // Keep the exact checked lockfile open through Cargo's metadata read,
        // just like the manifest and configuration above. Its format version
        // is a separate compatibility input: every semantic toolchain in CI
        // supplies both rustc and the same-version Cargo binary.
        let (_cargo_lockfile_file, cargo_lockfile_version) =
            validate_cargo_lockfile(&repository_root, cargo_directory)?;

        let command = cargo_metadata_command(
            &primary_manifest,
            cargo_directory,
            &toolchain_metadata.pinned_stable,
        );
        let metadata = command.exec().map_err(|source| CollectError::CargoMetadata {
            manifest: primary_manifest.clone(),
            source,
        })?;
        let cargo_target_directory = cargo_directory.join("target");
        if metadata.target_directory.as_std_path() != cargo_target_directory {
            return Err(CollectError::UnexpectedCargoTargetDirectory {
                expected: cargo_target_directory,
                found: metadata.target_directory.into_std_path_buf(),
            });
        }

        // Cargo metadata contains each crate entry point but not the module,
        // `include!`, or macro input files rustc may read beneath a package
        // directory. Inspect every resolved package tree before trusting the
        // metadata paths so a checked-in module symlink cannot import bytes
        // from outside the checkout. The Cargo target directory is generated,
        // runner-local output rather than package source; its ordinary root
        // entry is deliberately excluded from this walk.
        let package_directories = metadata
            .packages
            .iter()
            .map(|package| {
                package
                    .manifest_path
                    .as_std_path()
                    .parent()
                    .expect("Cargo package manifests always have a parent directory")
                    .to_path_buf()
            })
            .collect::<BTreeSet<_>>();
        validate_package_source_symlink_containment(
            &repository_root,
            &package_directories,
            &cargo_target_directory,
        )?;

        // Cargo reports dependency paths independently from workspace package
        // records. Resolve the complete workspace manifest set first so the
        // package pass below can turn each local dependency into an exact,
        // rename-independent package identity. A new local package must join
        // the classified workspace instead of silently falling out of MSRV
        // validation.
        let workspace_manifests_by_id = metadata
            .workspace_packages()
            .into_iter()
            .map(|package| {
                relative_path(&repository_root, package.manifest_path.as_std_path())
                    .map(|manifest| (package.id.clone(), manifest))
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let workspace_manifests =
            workspace_manifests_by_id.values().cloned().collect::<BTreeSet<_>>();
        let workspace_package_ids = workspace_manifests_by_id
            .iter()
            .map(|(id, manifest)| (manifest.clone(), id.clone()))
            .collect::<BTreeMap<_, _>>();
        let resolve = metadata.resolve.as_ref().ok_or(CollectError::MissingDependencyGraph)?;
        let mut resolved_workspace_dependencies =
            resolved_workspace_dependencies(&workspace_manifests_by_id, resolve);

        // `Metadata::workspace_packages` is intentionally insufficient here:
        // Cargo compiles registry and Git packages in the resolved closure too,
        // and their `rust-version` declarations can reject an otherwise valid
        // workspace MSRV job. Retain every PackageId edge from the one locked,
        // offline, all-features resolution. PackageId, rather than name and
        // version, distinguishes equal versions obtained from different
        // sources and is also the exact identity used by `Resolve`.
        let metadata_package_ids =
            metadata.packages.iter().map(|package| package.id.clone()).collect::<BTreeSet<_>>();
        for node in &resolve.nodes {
            if !metadata_package_ids.contains(&node.id) {
                return Err(CollectError::MissingResolvedPackage { package: node.id.to_string() });
            }
            for dependency in &node.deps {
                if !metadata_package_ids.contains(&dependency.pkg) {
                    return Err(CollectError::MissingResolvedPackage {
                        package: dependency.pkg.to_string(),
                    });
                }
            }
        }
        let dependencies_by_id = resolve
            .nodes
            .iter()
            .map(|node| {
                (
                    node.id.clone(),
                    node.deps.iter().map(|dependency| dependency.pkg.clone()).collect(),
                )
            })
            .collect::<BTreeMap<_, BTreeSet<_>>>();
        let mut resolved_packages = BTreeMap::new();
        for package in &metadata.packages {
            // The checked source replacement is repository-contained before
            // Cargo runs. Check Cargo's concrete answer as well so an ambient
            // override or a symbolic link below the vendor root cannot turn a
            // resolved manifest or target into an approved host-local input.
            let manifest = relative_path(&repository_root, package.manifest_path.as_std_path())?;
            for target in &package.targets {
                relative_path(&repository_root, target.src_path.as_std_path())?;
            }
            resolved_packages.insert(
                package.id.clone(),
                ResolvedPackage {
                    name: package.name.to_string(),
                    version: package.version.to_string(),
                    manifest,
                    rust_version: package.rust_version.as_ref().map(ToString::to_string),
                    editions: cargo_package_editions(package),
                    dependencies: dependencies_by_id.get(&package.id).cloned().unwrap_or_default(),
                },
            );
        }

        let mut packages = BTreeMap::new();
        for package in metadata.workspace_packages() {
            let manifest = relative_path(&repository_root, package.manifest_path.as_std_path())?;
            let mut dependencies = BTreeMap::<String, Dependency>::new();
            // Cargo's resolved PackageId edges include dependencies redirected
            // by `[patch]` or `[replace]`, whose declaration has no `path`.
            // Union the declaration paths below: they deliberately retain all
            // optional, target-specific, and dependency-kind edges even if a
            // particular unified resolution does not activate one of them.
            let mut workspace_dependencies =
                resolved_workspace_dependencies.remove(&package.id).unwrap_or_default();
            for dependency in &package.dependencies {
                let key = dependency.rename.as_ref().unwrap_or(&dependency.name).clone();
                dependencies
                    .entry(key)
                    .and_modify(|known| known.optional |= dependency.optional)
                    .or_insert(Dependency { optional: dependency.optional });
                if let Some(directory) = &dependency.path {
                    let dependency_manifest = directory.join("Cargo.toml");
                    let dependency_manifest =
                        relative_path(&repository_root, dependency_manifest.as_std_path())?;
                    if !workspace_manifests.contains(&dependency_manifest) {
                        return Err(CollectError::UnclassifiedLocalDependency {
                            package: package.name.to_string(),
                            dependency: dependency.name.clone(),
                            manifest: dependency_manifest,
                        });
                    }
                    workspace_dependencies.insert(dependency_manifest);
                }
            }

            let mut targets = BTreeSet::new();
            for target in &package.targets {
                let source = relative_path(&repository_root, target.src_path.as_std_path())?;
                let kinds = target.kind.iter().map(target_kind_name).collect();
                let crate_types = target.crate_types.iter().map(ToString::to_string).collect();
                targets.insert(CargoTarget {
                    package: package.name.to_string(),
                    name: target.name.clone(),
                    kinds,
                    crate_types,
                    source,
                    required_features: target.required_features.iter().cloned().collect(),
                    test: target.test,
                    doctest: target.doctest,
                    doc: target.doc,
                });
            }

            let cargo_package = CargoPackage {
                name: package.name.to_string(),
                manifest: manifest.clone(),
                rust_version: package.rust_version.as_ref().map(ToString::to_string),
                editions: cargo_package_editions(package),
                features: package
                    .features
                    .iter()
                    .map(|(name, members)| {
                        (name.clone(), members.iter().cloned().collect::<BTreeSet<_>>())
                    })
                    .collect(),
                dependencies,
                workspace_dependencies,
                targets,
            };
            packages.insert(manifest, cargo_package);
        }

        let mut conventional_sources = BTreeSet::new();
        for package in packages.values() {
            let package_directory =
                package.manifest.parent().expect("Cargo.toml always has a parent directory");
            discover_conventional_sources(
                &repository_root,
                package_directory,
                &mut conventional_sources,
            )?;
        }

        let mut existing_files = BTreeMap::new();
        for path in baseline_paths(policy) {
            // RepoPath rejects absolute paths and parent components, but those
            // syntax checks cannot detect a checked-in symbolic link. Resolve
            // every configured baseline before treating it as present so the
            // inventory cannot approve a file outside this checkout.
            let exists =
                repository_regular_file_exists(&repository_root, &repository_root.join(path))?;
            existing_files.insert(path.to_path_buf(), exists);
        }
        for package in packages.values() {
            existing_files.insert(
                package.manifest.clone(),
                repository_root.join(&package.manifest).is_file(),
            );
            for target in &package.targets {
                existing_files
                    .insert(target.source.clone(), repository_root.join(&target.source).is_file());
            }
        }

        Ok(Self {
            repository_root,
            packages,
            workspace_package_ids,
            resolved_packages,
            conventional_sources,
            existing_files,
            primary_manifest_source,
            toolchain_metadata,
            rust_target_support,
            cargo_lockfile_version,
        })
    }

    /// Checks all independent repository contracts in one deterministic pass.
    pub fn validate(&self, policy: &Policy) -> Result<RepositoryInventory, InventoryErrors> {
        let mut errors = ErrorSink::default();

        validate_baseline_paths(policy, &self.existing_files, &mut errors);
        validate_conventional_sources(
            &self.packages,
            &self.conventional_sources,
            &self.existing_files,
            &mut errors,
        );
        validate_workspace_package_classification(policy, &self.packages, &mut errors);
        validate_cargo_target_classification(&self.packages, &mut errors);

        let mut policy_packages = BTreeMap::new();
        for (id, package_policy) in policy.packages() {
            let manifest = package_policy.manifest().as_path();
            let location = format!("packages.{}", id.as_str());
            let Some(package) = self.packages.get(manifest) else {
                errors.push(
                    format!("{location}.manifest"),
                    format!(
                        "`{}` is not a package in Cargo's primary workspace",
                        manifest.display()
                    ),
                );
                continue;
            };

            if package.name != id.as_str() {
                errors.push(
                    format!("{location}.id"),
                    format!(
                        "policy ID `{}` must equal Cargo package name `{}`",
                        id.as_str(),
                        package.name
                    ),
                );
            }

            let analysis = analyze_features(package, policy, &location, &mut errors);
            validate_profiles(package, package_policy, policy, &location, &mut errors);
            validate_target_feature_references(package, &location, &mut errors);
            policy_packages.insert(
                id.as_str().to_owned(),
                PackageInventory {
                    cargo: package.clone(),
                    stable_features: analysis.stable,
                    nightly_features: analysis.nightly,
                    default_features: analysis.default,
                },
            );
        }

        validate_non_nightly_all_feature_scopes(policy, &policy_packages, &mut errors);
        validate_policy_targets(policy, &mut errors);
        let build_rs_versions = validate_build_rs_contract(
            &self.primary_manifest_source,
            &self.toolchain_metadata.build_rs,
            &mut errors,
        );
        let toolchain_versions = validate_toolchains(policy, self, &build_rs_versions, &mut errors);
        validate_rust_target_support(
            policy,
            &toolchain_versions,
            &self.rust_target_support,
            &mut errors,
        );

        if !errors.is_empty() {
            return Err(errors.finish());
        }

        let cargo_targets =
            self.packages.values().flat_map(|package| package.targets.iter().cloned()).collect();
        Ok(RepositoryInventory {
            workspace_packages: self.packages.clone(),
            policy_packages,
            cargo_targets,
            toolchain_versions,
        })
    }

    /// Returns the canonical repository root used for collection.
    pub fn repository_root(&self) -> &Path {
        &self.repository_root
    }
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct CargoConfiguration {
    // Cargo exports these values to compiler and build-script processes, not
    // merely to metadata source discovery. Retain the complete map so the
    // preflight below can require the one reviewed local-development marker
    // and reject every behavior-bearing addition explicitly.
    #[serde(default, rename = "env")]
    environment: BTreeMap<String, toml::Value>,
    #[serde(default)]
    source: BTreeMap<String, CargoSourceConfiguration>,
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct CargoSourceConfiguration {
    #[serde(rename = "replace-with")]
    replace_with: Option<String>,
    directory: Option<PathBuf>,
}

/// Validates the Cargo configuration and directory source loaded by metadata.
///
/// Cargo searches for `.cargo/config.toml` from its current directory, not from
/// `--manifest-path`; [`cargo_metadata_command`] therefore runs in the primary
/// package directory. Cargo also resolves a relative path in that discovered
/// configuration against the parent of `.cargo`, which is `cargo_directory`
/// here, rather than against `.cargo` itself or the canonical destination of a
/// symbolic-link configuration file. Reproduce exactly those lookup semantics
/// while checking physical destinations before Cargo can read either input.
///
/// The repository contract redirects `crates-io` through one or more named
/// `replace-with` entries to a directory source. Following the names instead of
/// hard-coding `vendor` keeps a reviewed in-repository rename valid. Validate
/// every other configured source chain too: a future Git dependency can name
/// its own replacement, and Cargo may read that source before metadata exists
/// for the post-invocation containment check. A missing entry, cycle, or
/// ambiguous entry therefore fails closed rather than falling back to
/// runner-local Cargo state.
fn validate_cargo_source_configuration(
    repository_root: &Path,
    cargo_directory: &Path,
) -> Result<OpenedRepositoryFile, CollectError> {
    let configured_path = cargo_directory.join(".cargo/config.toml");
    let legacy_path = cargo_directory.join(".cargo/config");
    // Cargo still recognizes the old extensionless spelling and gives it
    // precedence when both files exist. Inspect the directory entry without
    // following it so a broken or escaping symlink cannot silently select an
    // unaudited configuration before Cargo runs.
    match fs::symlink_metadata(&legacy_path) {
        Ok(_) => {
            return Err(CollectError::LegacyCargoConfiguration {
                path: legacy_path,
                preferred: configured_path,
            });
        }
        Err(source) if source.kind() == io::ErrorKind::NotFound => {}
        Err(source) => return Err(CollectError::RepositoryPath { path: legacy_path, source }),
    }

    // Cargo begins at its current directory and merges configuration from
    // every ancestor. Inventory deliberately models one checked-in file
    // instead of attempting to reproduce those merge rules. Reject either
    // spelling in every repository-owned ancestor so a future root-level or
    // intermediate configuration cannot add unmodeled sources, environment,
    // build flags, aliases, or target-directory behavior before metadata.
    // Host configuration above `repository_root` is outside this repository
    // audit and is constrained separately at the process boundary.
    for ancestor in cargo_directory.ancestors().skip(1) {
        if !ancestor.starts_with(repository_root) {
            break;
        }
        for path in [ancestor.join(".cargo/config"), ancestor.join(".cargo/config.toml")] {
            match fs::symlink_metadata(&path) {
                Ok(_) => {
                    return Err(CollectError::UnexpectedCargoConfiguration {
                        path,
                        audited: configured_path,
                    });
                }
                Err(source) if source.kind() == io::ErrorKind::NotFound => {}
                Err(source) => return Err(CollectError::RepositoryPath { path, source }),
            }
        }
    }
    // Keep validation and parsing on one retained object. In particular, do
    // not resolve this path and later reopen its mutable directory entry: that
    // would let an ordinary concurrent replacement supply different Cargo
    // behavior after containment was approved.
    let configured = configured_path
        .strip_prefix(repository_root)
        .expect("the fixed Cargo configuration is below the canonical repository root");
    let config_file = open_inventory_file(repository_root, configured)?;
    let config_path = config_file.path().to_path_buf();
    let source = config_file
        .read_to_string()
        .map_err(|source| CollectError::Read { path: config_path.clone(), source })?;
    let configuration: CargoConfiguration = toml::from_str(&source).map_err(|source| {
        CollectError::CargoConfiguration { path: config_path.clone(), source: Box::new(source) }
    })?;

    let invalid = |message| CollectError::InvalidCargoSourceConfiguration {
        path: config_path.clone(),
        message,
    };
    let invalid_environment = |message| CollectError::InvalidCargoEnvironmentConfiguration {
        path: config_path.clone(),
        message,
    };
    let expected_environment =
        BTreeMap::from([("__ZEROCOPY_LOCAL_DEV".to_owned(), toml::Value::String("1".to_owned()))]);
    if configuration.environment != expected_environment {
        return Err(invalid_environment(format!(
            "expected exactly `__ZEROCOPY_LOCAL_DEV = \"1\"`; found {}",
            display_toml_map(&configuration.environment)
        )));
    }
    let source_names = std::iter::once("crates-io".to_owned())
        .chain(configuration.source.keys().cloned())
        .collect::<BTreeSet<_>>();
    for initial_source_name in source_names {
        let mut source_name = initial_source_name.clone();
        let mut visited = BTreeSet::new();
        let configured_directory = loop {
            if !visited.insert(source_name.clone()) {
                return Err(invalid(format!(
                    "source replacement from `{initial_source_name}` cycles at `{source_name}`"
                )));
            }
            let Some(configured_source) = configuration.source.get(&source_name) else {
                return Err(invalid(format!(
                    "source `{source_name}` referenced from `{initial_source_name}` is absent from the checked-in configuration"
                )));
            };
            match (&configured_source.replace_with, &configured_source.directory) {
                (Some(_), Some(_)) => {
                    return Err(invalid(format!(
                        "source `{source_name}` declares both `replace-with` and `directory`"
                    )));
                }
                (Some(replacement), None) => source_name = replacement.clone(),
                (None, Some(directory)) if directory.as_os_str().is_empty() => {
                    return Err(invalid(format!(
                        "directory source `{source_name}` has an empty path"
                    )));
                }
                (None, Some(directory)) => {
                    let uses_nonlocal_spelling = directory.is_absolute()
                        || directory.components().any(|component| {
                            matches!(
                                component,
                                Component::Prefix(_)
                                    | Component::RootDir
                                    | Component::ParentDir
                                    | Component::CurDir
                            )
                        })
                        || directory
                            .components()
                            .next()
                            .is_some_and(|component| component.as_os_str() == "~");
                    if uses_nonlocal_spelling {
                        return Err(invalid(format!(
                            "directory source `{source_name}` must use a relative path without home, current-directory, or parent components"
                        )));
                    }
                    break directory;
                }
                (None, None) => {
                    return Err(invalid(format!(
                        "source `{source_name}` has neither `replace-with` nor `directory`"
                    )));
                }
            }
        };

        // The lexical check above keeps this repository input portable and
        // avoids Cargo's home-relative path semantics. Canonical containment
        // remains necessary because an apparently local directory or one of
        // its ancestors can still be a symbolic link outside the checkout.
        let configured_directory = cargo_directory.join(configured_directory);
        let resolved_directory = resolve_repository_path(repository_root, &configured_directory)?;
        let metadata = fs::metadata(&resolved_directory).map_err(|source| {
            CollectError::RepositoryPath { path: resolved_directory.clone(), source }
        })?;
        if !metadata.is_dir() {
            return Err(invalid(format!(
                "directory source `{source_name}` resolves to non-directory `{}`",
                resolved_directory.display()
            )));
        }
    }
    Ok(config_file)
}

#[derive(serde::Deserialize)]
struct CargoLockfileHeader {
    version: Option<u32>,
}

/// Opens and validates the lockfile Cargo will read while honoring `--locked`.
///
/// [`CollectedRepository::collect`] first proves that the primary manifest
/// defines the workspace. Cargo therefore selects the sibling `Cargo.lock`,
/// rather than an ancestor workspace's lockfile. Consume the exact retained
/// handle whose containment and file kind were checked, then return it so the
/// caller can keep that identity alive through Cargo's own path-based read.
/// The parsed format is later checked against every semantic CI toolchain.
fn validate_cargo_lockfile(
    repository_root: &Path,
    cargo_directory: &Path,
) -> Result<(OpenedRepositoryFile, CargoLockfileVersion), CollectError> {
    let path = cargo_directory.join("Cargo.lock");
    let configured = path
        .strip_prefix(repository_root)
        .expect("the audited Cargo workspace is below the canonical repository root");
    let lockfile = match open_inventory_file(repository_root, configured) {
        Ok(lockfile) => lockfile,
        Err(CollectError::RepositoryPathNotFile { .. }) => {
            return Err(CollectError::InvalidCargoLockfile { path });
        }
        Err(CollectError::RepositoryPath { source, .. })
            if source.kind() == io::ErrorKind::NotFound =>
        {
            return Err(CollectError::InvalidCargoLockfile { path });
        }
        Err(error) => return Err(error),
    };
    let path = lockfile.path().to_path_buf();
    let source = lockfile
        .read_to_string()
        .map_err(|source| CollectError::Read { path: path.clone(), source })?;
    let header: CargoLockfileHeader = toml::from_str(&source).map_err(|source| {
        CollectError::CargoLockfile { path: path.clone(), source: Box::new(source) }
    })?;
    let Some(raw_version) = header.version else {
        return Err(CollectError::AmbiguousCargoLockfileVersion { path });
    };
    let version = CargoLockfileVersion::parse(raw_version)
        .ok_or(CollectError::UnsupportedCargoLockfileVersion { path, version: raw_version })?;
    Ok((lockfile, version))
}

fn display_toml_map(values: &BTreeMap<String, toml::Value>) -> String {
    if values.is_empty() {
        return "no entries".to_owned();
    }
    values.iter().map(|(key, value)| format!("`{key} = {value}`")).collect::<Vec<_>>().join(", ")
}

/// Requires every symbolic link reachable from a package tree to stay local.
///
/// Cargo metadata reports manifests and target entry points, but rustc follows
/// module paths and macro inputs which metadata does not enumerate. Walk every
/// resolved workspace and vendored package directory without descending
/// through the ordinary root entry for Cargo's generated target directory.
/// Internal directory links are followed so an escaping link nested beneath
/// their destination cannot hide behind the first safe hop. That includes an
/// explicit source-tree link into a target subdirectory: unlike the ordinary
/// output-tree entry, such a link can be an input rustc actually follows and
/// therefore must not create an audit exemption. Canonical-directory
/// deduplication prevents internal link cycles.
fn validate_package_source_symlink_containment(
    repository_root: &Path,
    package_directories: &BTreeSet<PathBuf>,
    cargo_target_directory: &Path,
) -> Result<(), CollectError> {
    let mut pending = package_directories.iter().cloned().collect::<Vec<_>>();
    // Reverse once because `pop` then visits the sorted roots in ascending
    // order. Directory entries are handled the same way below, keeping the
    // first collection diagnostic deterministic across filesystems.
    pending.reverse();
    let mut visited = BTreeSet::new();

    while let Some(directory) = pending.pop() {
        if directory == cargo_target_directory {
            continue;
        }
        let directory = resolve_repository_path(repository_root, &directory)?;
        if !visited.insert(directory.clone()) {
            continue;
        }

        let mut entries = fs::read_dir(&directory)
            .map_err(|source| CollectError::RepositoryPath { path: directory.clone(), source })?
            .map(|entry| {
                entry.map(|entry| entry.path()).map_err(|source| CollectError::RepositoryPath {
                    path: directory.clone(),
                    source,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        entries.sort();
        entries.reverse();

        for path in entries {
            if path == cargo_target_directory {
                continue;
            }
            let metadata = fs::symlink_metadata(&path)
                .map_err(|source| CollectError::RepositoryPath { path: path.clone(), source })?;
            if metadata.file_type().is_symlink() {
                let resolved = resolve_repository_path(repository_root, &path)?;
                if resolved.is_dir() && cargo_target_directory.starts_with(&resolved) {
                    // Revisiting an already-walked package ancestor would be
                    // suppressed by canonical-directory deduplication, while
                    // entering the target root would otherwise inherit its
                    // ordinary output-tree exemption. Reject both aliases
                    // explicitly. A link to a target subdirectory remains
                    // walkable and is audited like any other source input.
                    return Err(CollectError::CargoTargetSourceAlias {
                        path,
                        resolved,
                        target: cargo_target_directory.to_path_buf(),
                    });
                }
                if resolved.is_dir() {
                    pending.push(resolved);
                }
            } else if metadata.is_dir() {
                pending.push(path);
            }
        }
    }
    Ok(())
}

fn cargo_metadata_command(
    primary_manifest: &Path,
    cargo_directory: &Path,
    pinned_stable: &str,
) -> MetadataCommand {
    let mut command = MetadataCommand::new();
    command
        // Setting the executable keeps an ambient `CARGO` override from
        // replacing Cargo with a project wrapper or unrelated binary. The
        // ordinary `cargo` spelling still lets rustup select the pinned
        // toolchain below.
        .cargo_path("cargo")
        .manifest_path(primary_manifest)
        // Cargo discovers `.cargo/config.toml` from its working directory,
        // not from `--manifest-path`. Run beside the primary manifest so
        // Zerocopy's checked-in vendored-source configuration is active.
        .current_dir(cargo_directory)
        // Inventory must mean the same thing when called from an MSRV,
        // nightly, or externally overridden shell. This value comes directly
        // from the resolved primary manifest before Cargo is invoked.
        .env("RUSTUP_TOOLCHAIN", pinned_stable)
        // Cargo sees `--offline` only after the rustup proxy selects a
        // toolchain. Without this separate rustup setting, a clean checkout
        // can attempt a network download before Cargo has a chance to enforce
        // its offline contract. Fail immediately if the pinned toolchain has
        // not been installed by the repository bootstrap instead.
        .env("RUSTUP_AUTO_INSTALL", "0")
        // `CARGO_TARGET_DIR` otherwise comes from the caller and is reflected
        // back through metadata. The source-containment walk deliberately
        // skips generated Cargo output; letting an ambient value point that
        // exemption at `src` would hide the exact package tree being audited.
        // Pin the ordinary workspace-local directory and separately require
        // Cargo's reported value to match before using it as an exclusion.
        .env("CARGO_TARGET_DIR", cargo_directory.join("target"))
        // A complete PackageId graph is the only Cargo-owned identity for a
        // registry dependency or one redirected to a local package by
        // `[patch]` or `[replace]`. Resolve every feature so optional edges are
        // represented too. The graph intentionally covers every target because
        // no `--filter-platform` is supplied. This conservative superset avoids
        // reimplementing Cargo's feature and target resolver while remaining
        // locked and offline.
        .features(CargoOpt::AllFeatures)
        .other_options(vec!["--locked".to_owned(), "--offline".to_owned()]);
    command
}

/// Extracts Cargo-resolved edges whose two endpoints are workspace members.
///
/// `PackageId` is intentionally the join key. Dependency names are local
/// aliases and declaration paths are absent when Cargo redirects a registry
/// dependency through `[patch]` or `[replace]`. The caller unions these edges
/// with declaration paths to retain deliberately conservative coverage of all
/// dependency kinds, targets, and optional features.
fn resolved_workspace_dependencies(
    workspace_manifests: &BTreeMap<PackageId, PathBuf>,
    resolve: &Resolve,
) -> BTreeMap<PackageId, BTreeSet<PathBuf>> {
    let mut dependencies = workspace_manifests
        .keys()
        .cloned()
        .map(|id| (id, BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    for node in &resolve.nodes {
        let Some(package_dependencies) = dependencies.get_mut(&node.id) else {
            continue;
        };
        for dependency in &node.deps {
            if let Some(manifest) = workspace_manifests.get(&dependency.pkg) {
                package_dependencies.insert(manifest.clone());
            }
        }
    }
    dependencies
}

fn validate_workspace_package_classification(
    policy: &Policy,
    packages: &BTreeMap<PathBuf, CargoPackage>,
    errors: &mut ErrorSink,
) {
    let policy_manifests = policy
        .packages()
        .values()
        .map(|package| package.manifest().as_path().to_path_buf())
        .collect::<BTreeSet<_>>();
    validate_workspace_package_classification_from_manifests(&policy_manifests, packages, errors);
}

fn validate_workspace_package_classification_from_manifests(
    policy_manifests: &BTreeSet<PathBuf>,
    packages: &BTreeMap<PathBuf, CargoPackage>,
    errors: &mut ErrorSink,
) {
    let support = SUPPORT_PACKAGES
        .into_iter()
        .map(|(name, manifest)| (PathBuf::from(manifest), name))
        .collect::<BTreeMap<_, _>>();

    // Policy packages receive matrix coverage; support packages exist only so
    // that Cargo can share a workspace lockfile. Treating one manifest as both
    // would make its target rules depend on which check happened first.
    for (manifest, name) in &support {
        if policy_manifests.contains(manifest) {
            errors.push(
                "cargo.packages",
                format!(
                    "support package `{name}` at `{}` must not also appear in CI policy",
                    manifest.display()
                ),
            );
        }
        match packages.get(manifest) {
            Some(package) if package.name == *name => {}
            Some(package) => errors.push(
                "cargo.packages",
                format!(
                    "support manifest `{}` now names package `{}` instead of `{name}`",
                    manifest.display(),
                    package.name
                ),
            ),
            None => errors.push(
                "cargo.packages",
                format!(
                    "support-package classification `{name}` at `{}` is stale",
                    manifest.display()
                ),
            ),
        }
    }

    for (manifest, package) in packages {
        if policy_manifests.contains(manifest) || support.contains_key(manifest) {
            continue;
        }
        errors.push(
            "cargo.packages",
            format!(
                "workspace package `{}` at `{}` has no CI policy or explicit support-package classification",
                package.name,
                manifest.display()
            ),
        );
    }
}

fn relative_path(repository_root: &Path, path: &Path) -> Result<PathBuf, CollectError> {
    let resolved = resolve_repository_path(repository_root, path)?;
    let relative = resolved.strip_prefix(repository_root).map_err(|_| {
        CollectError::PathOutsideRepository {
            repository_root: repository_root.to_path_buf(),
            path: path.to_path_buf(),
            resolved: resolved.clone(),
        }
    })?;
    if relative.as_os_str().is_empty()
        || relative.components().any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(CollectError::PathOutsideRepository {
            repository_root: repository_root.to_path_buf(),
            path: path.to_path_buf(),
            resolved,
        });
    }
    Ok(relative.to_path_buf())
}

/// Opens a repository-owned inventory input without separating containment
/// checks from the handle which supplies its bytes.
fn open_inventory_file(
    repository_root: &Path,
    configured: &Path,
) -> Result<OpenedRepositoryFile, CollectError> {
    repository_file::open(repository_root, configured).map_err(|error| match error {
        OpenRepositoryFileError::Path { path, source }
        | OpenRepositoryFileError::Identity { path, source } => {
            CollectError::RepositoryPath { path, source }
        }
        OpenRepositoryFileError::ChangedDuringOpen { path, first, second } => {
            CollectError::RepositoryFileChangedDuringOpen { path, first, second }
        }
        OpenRepositoryFileError::OutsideRepository { path, resolved, repository_root } => {
            CollectError::PathOutsideRepository { path, resolved, repository_root }
        }
        OpenRepositoryFileError::NotFile { path } => CollectError::RepositoryPathNotFile { path },
    })
}

fn cargo_package_editions(package: &cargo_metadata::Package) -> BTreeSet<String> {
    // `Package::edition` is Cargo's normalized default, including the implicit
    // 2015 fallback. A target may override that default, and old Cargo must
    // understand every such declaration while it loads the manifest even if a
    // particular CI command does not eventually compile the target.
    std::iter::once(package.edition.to_string())
        .chain(package.targets.iter().map(|target| target.edition.to_string()))
        .collect()
}

/// Follows symbolic links and keeps a repository-owned path inside its checkout.
///
/// Policy path syntax rules prevent explicit `..` and absolute paths. Cargo also
/// normally reports paths below the workspace. Neither fact constrains the
/// destination of a symbolic link, so every repository path which will be
/// trusted must cross this physical containment check.
fn resolve_repository_path(repository_root: &Path, path: &Path) -> Result<PathBuf, CollectError> {
    let resolved = path
        .canonicalize()
        .map_err(|source| CollectError::RepositoryPath { path: path.to_path_buf(), source })?;
    if !resolved.starts_with(repository_root) {
        return Err(CollectError::PathOutsideRepository {
            repository_root: repository_root.to_path_buf(),
            path: path.to_path_buf(),
            resolved,
        });
    }
    Ok(resolved)
}

/// Reports whether a configured repository input is a regular file.
///
/// A missing baseline is a semantic policy error, not a collection failure. It
/// must therefore remain `false` so validation can aggregate it with unrelated
/// repository mistakes. The initial probe cannot distinguish an absent path
/// from a path beneath a missing or broken-link ancestor; both remain `false`
/// and fail later as a missing configured input. Other file-system failures are
/// different. In particular, a permission error or a broken final-component
/// symbolic link stops collection with its original cause rather than being
/// reported as merely missing.
fn repository_regular_file_exists(
    repository_root: &Path,
    path: &Path,
) -> Result<bool, CollectError> {
    match fs::symlink_metadata(path) {
        Ok(_) => {}
        Err(source) if source.kind() == io::ErrorKind::NotFound => return Ok(false),
        Err(source) => {
            return Err(CollectError::RepositoryPath { path: path.to_path_buf(), source });
        }
    }

    // `symlink_metadata` deliberately inspected the configured directory entry
    // without following its final link. Now follow the complete path and reject
    // any destination outside the checkout before asking what kind of file it
    // is. This also catches an escape through a symbolic-link ancestor.
    let resolved = resolve_repository_path(repository_root, path)?;
    let metadata = fs::metadata(&resolved)
        .map_err(|source| CollectError::RepositoryPath { path: resolved.clone(), source })?;
    Ok(metadata.is_file())
}

fn target_kind_name(kind: &TargetKind) -> String {
    match kind {
        TargetKind::Bench => "bench",
        TargetKind::Bin => "bin",
        TargetKind::CustomBuild => "custom-build",
        TargetKind::CDyLib => "cdylib",
        TargetKind::DyLib => "dylib",
        TargetKind::Example => "example",
        TargetKind::Lib => "lib",
        TargetKind::ProcMacro => "proc-macro",
        TargetKind::RLib => "rlib",
        TargetKind::StaticLib => "staticlib",
        TargetKind::Test => "test",
        TargetKind::Unknown(name) => name.as_str(),
        kind => return kind.to_string(),
    }
    .to_owned()
}

fn discover_conventional_sources(
    repository_root: &Path,
    package_directory: &Path,
    discovered: &mut BTreeSet<PathBuf>,
) -> Result<(), CollectError> {
    let package_root = repository_root.join(package_directory);
    for relative in ["src/lib.rs", "src/main.rs"] {
        let path = package_root.join(relative);
        if path.is_file() {
            discovered.insert(package_directory.join(relative));
        }
    }

    // Cargo's automatic target discovery examines `.rs` files directly in
    // each conventional directory, plus `*/main.rs`. Do not recurse farther:
    // files such as `tests/ui/fail.rs` and bench support modules are not
    // independent Cargo targets.
    for directory in ["src/bin", "examples", "tests", "benches"] {
        let absolute = package_root.join(directory);
        let entries = match fs::read_dir(&absolute) {
            Ok(entries) => entries,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(source) => return Err(CollectError::Read { path: absolute, source }),
        };
        for entry in entries {
            let entry =
                entry.map_err(|source| CollectError::Read { path: absolute.clone(), source })?;
            let file_type = entry
                .file_type()
                .map_err(|source| CollectError::Read { path: entry.path(), source })?;
            let path = entry.path();
            if file_type.is_file() && path.extension().is_some_and(|extension| extension == "rs") {
                discovered.insert(relative_path(repository_root, &path)?);
            } else if file_type.is_dir() {
                let main = path.join("main.rs");
                if main.is_file() {
                    discovered.insert(relative_path(repository_root, &main)?);
                }
            }
        }
    }
    Ok(())
}

fn baseline_paths(policy: &Policy) -> Vec<&Path> {
    let baselines = policy.baselines();
    vec![
        baselines.manifest().as_path(),
        baselines.build_reduced().as_path(),
        baselines.build_full().as_path(),
        baselines.miri_reduced().as_path(),
        baselines.miri_full().as_path(),
        baselines.logical_obligations().as_path(),
        baselines.standalone_obligations().as_path(),
        baselines.command_goldens().as_path(),
    ]
}

fn validate_baseline_paths(
    policy: &Policy,
    existing_files: &BTreeMap<PathBuf, bool>,
    errors: &mut ErrorSink,
) {
    for path in baseline_paths(policy) {
        if !existing_files.get(path).copied().unwrap_or(false) {
            errors.push(
                "baselines",
                format!("configured baseline `{}` does not exist", path.display()),
            );
        }
    }
}

fn validate_conventional_sources(
    packages: &BTreeMap<PathBuf, CargoPackage>,
    conventional_sources: &BTreeSet<PathBuf>,
    existing_files: &BTreeMap<PathBuf, bool>,
    errors: &mut ErrorSink,
) {
    let metadata_sources: BTreeSet<_> = packages
        .values()
        .flat_map(|package| package.targets.iter().map(|target| target.source.clone()))
        .collect();
    for source in conventional_sources.difference(&metadata_sources) {
        errors.push(
            "cargo.targets",
            format!(
                "conventional Cargo target `{}` was not reported by Cargo metadata",
                source.display()
            ),
        );
    }
    for source in &metadata_sources {
        if !existing_files.get(source).copied().unwrap_or(false) {
            errors.push(
                "cargo.targets",
                format!("Cargo target source `{}` does not exist", source.display()),
            );
        }
    }
}

/// Checks the complete target shapes that the current executors understand.
///
/// Cargo metadata makes adding a target easy, but that does not establish how
/// CI should run it. Keep this allow-list coordinated with the build executor
/// and with `zerocopy/tests/codegen.rs`. A target which no rule recognizes must
/// fail here until its execution and coverage semantics are explicit.
fn validate_cargo_target_classification(
    packages: &BTreeMap<PathBuf, CargoPackage>,
    errors: &mut ErrorSink,
) {
    for (manifest, package) in packages {
        let package_directory =
            manifest.parent().expect("Cargo.toml always has a parent directory");
        let support_name = SUPPORT_PACKAGES.iter().find_map(|(name, support_manifest)| {
            (manifest == Path::new(support_manifest)).then_some(*name)
        });

        for target in &package.targets {
            let location = format!("cargo.targets.{}.{}", package.name, target.name);
            if target.package != package.name {
                errors.push(
                    &location,
                    format!(
                        "target reports package `{}` but belongs to package `{}`",
                        target.package, package.name
                    ),
                );
            }

            if let Some(support_name) = support_name
                .filter(|_| !has_only_kind(target, "lib") && !has_only_kind(target, "custom-build"))
            {
                errors.push(
                    &location,
                    format!(
                        "support package `{support_name}` may contain only its library and structural build script"
                    ),
                );
                continue;
            }

            if has_only_kind(target, "lib") {
                validate_target_crate_types(
                    target,
                    &["lib"],
                    "ordinary library",
                    &location,
                    errors,
                );
                validate_library_target(package_directory, package, target, &location, errors);
            } else if has_only_kind(target, "proc-macro") {
                validate_target_crate_types(
                    target,
                    &["proc-macro"],
                    "procedural macro library",
                    &location,
                    errors,
                );
                validate_library_target(package_directory, package, target, &location, errors);
            } else if has_only_kind(target, "test") {
                validate_target_crate_types(
                    target,
                    &["bin"],
                    "integration test",
                    &location,
                    errors,
                );
                validate_integration_test_target(
                    manifest,
                    package_directory,
                    package,
                    target,
                    &location,
                    errors,
                );
            } else if has_only_kind(target, "bench") {
                validate_target_crate_types(target, &["bin"], "codegen bench", &location, errors);
                validate_codegen_bench_target(
                    manifest,
                    package_directory,
                    package,
                    target,
                    &location,
                    errors,
                );
            } else if has_only_kind(target, "custom-build") {
                validate_target_crate_types(
                    target,
                    &["bin"],
                    "custom-build target",
                    &location,
                    errors,
                );
                validate_custom_build_target(package_directory, target, &location, errors);
            } else {
                errors.push(
                    &location,
                    format!(
                        "Cargo target kind(s) {} need an explicit CI classification",
                        display_set(&target.kinds)
                    ),
                );
            }
        }
    }
}

fn has_only_kind(target: &CargoTarget, kind: &str) -> bool {
    target.kinds.len() == 1 && target.kinds.contains(kind)
}

fn display_set(values: &BTreeSet<String>) -> String {
    format!("[{}]", values.iter().map(|value| format!("`{value}`")).collect::<Vec<_>>().join(", "))
}

fn validate_target_crate_types(
    target: &CargoTarget,
    expected: &[&str],
    classification: &str,
    location: &str,
    errors: &mut ErrorSink,
) {
    let expected = expected.iter().map(|crate_type| (*crate_type).to_owned()).collect();
    if target.crate_types != expected {
        errors.push(
            location,
            format!(
                "{classification} must use Cargo crate type(s) {}; found {}",
                display_set(&expected),
                display_set(&target.crate_types)
            ),
        );
    }
}

fn validate_library_target(
    package_directory: &Path,
    package: &CargoPackage,
    target: &CargoTarget,
    location: &str,
    errors: &mut ErrorSink,
) {
    let expected_name = package.name.replace('-', "_");
    if target.name != expected_name {
        errors.push(
            location,
            format!(
                "ordinary library target must be named `{expected_name}` for package `{}`",
                package.name
            ),
        );
    }
    let expected_source = package_directory.join("src/lib.rs");
    if target.source != expected_source {
        errors.push(
            location,
            format!(
                "ordinary library target must use `{}`; found `{}`",
                expected_source.display(),
                target.source.display()
            ),
        );
    }
    validate_target_flags(target, true, true, true, "ordinary library", location, errors);
}

fn validate_integration_test_target(
    manifest: &Path,
    package_directory: &Path,
    package: &CargoPackage,
    target: &CargoTarget,
    location: &str,
    errors: &mut ErrorSink,
) {
    let direct_source = package_directory.join("tests").join(format!("{}.rs", target.name));
    let directory_source = package_directory.join("tests").join(&target.name).join("main.rs");
    if target.source != direct_source && target.source != directory_source {
        errors.push(
            location,
            format!(
                "integration test `{}` must use `{}` or `{}`; found `{}`",
                target.name,
                direct_source.display(),
                directory_source.display(),
                target.source.display()
            ),
        );
    }

    // `codegen` is run by its dedicated workflow after LLVM tooling is set up.
    // Keep this identity coordinated with `zerocopy/Cargo.toml`'s explicit
    // `[[test]]` entry and `.github/workflows/ci.yml`'s codegen job. No other
    // integration test may silently opt out of ordinary `cargo test` runs.
    let is_standalone_codegen = manifest == Path::new("zerocopy/Cargo.toml")
        && package.name == "zerocopy"
        && target.package == "zerocopy"
        && target.name == "codegen"
        && target.source == Path::new("zerocopy/tests/codegen.rs");
    validate_target_flags(
        target,
        !is_standalone_codegen,
        false,
        false,
        if is_standalone_codegen { "standalone codegen test" } else { "integration test" },
        location,
        errors,
    );
}

fn validate_codegen_bench_target(
    manifest: &Path,
    package_directory: &Path,
    package: &CargoPackage,
    target: &CargoTarget,
    location: &str,
    errors: &mut ErrorSink,
) {
    if manifest != Path::new("zerocopy/Cargo.toml") || package.name != "zerocopy" {
        errors.push(
            location,
            "only direct `zerocopy` benches are classified; this bench needs an explicit CI classification",
        );
    }

    // The codegen test enumerates every direct `benches/*.rs` file and passes
    // its stem to `cargo asm --bench`. Keep all three spellings identical or a
    // bench could exist in Cargo metadata without being exercised by codegen.
    let expected_source = package_directory.join("benches").join(format!("{}.rs", target.name));
    if target.source != expected_source {
        errors.push(
            location,
            format!(
                "codegen bench `{}` must be the direct file `{}`; found `{}`",
                target.name,
                expected_source.display(),
                target.source.display()
            ),
        );
    }
    validate_target_flags(target, false, false, false, "codegen bench", location, errors);
}

fn validate_custom_build_target(
    package_directory: &Path,
    target: &CargoTarget,
    location: &str,
    errors: &mut ErrorSink,
) {
    if target.name != "build-script-build" {
        errors.push(location, "custom-build target must be named `build-script-build`");
    }
    let expected_source = package_directory.join("build.rs");
    if target.source != expected_source {
        errors.push(
            location,
            format!(
                "custom-build target must use `{}`; found `{}`",
                expected_source.display(),
                target.source.display()
            ),
        );
    }
    validate_target_flags(target, false, false, false, "custom-build target", location, errors);
}

fn validate_target_flags(
    target: &CargoTarget,
    test: bool,
    doctest: bool,
    doc: bool,
    classification: &str,
    location: &str,
    errors: &mut ErrorSink,
) {
    if (target.test, target.doctest, target.doc) != (test, doctest, doc) {
        errors.push(
            location,
            format!(
                "{classification} must set test={test}, doctest={doctest}, and doc={doc}; found test={}, doctest={}, and doc={}",
                target.test, target.doctest, target.doc
            ),
        );
    }
}

#[derive(Default)]
struct FeatureAnalysis {
    stable: BTreeSet<String>,
    nightly: BTreeSet<String>,
    default: BTreeSet<String>,
}

fn analyze_features(
    package: &CargoPackage,
    policy: &Policy,
    location: &str,
    errors: &mut ErrorSink,
) -> FeatureAnalysis {
    if package.features.is_empty() {
        return FeatureAnalysis::default();
    }

    let root = policy.features().stable_feature_root().as_str();
    if !package.features.contains_key(root) {
        errors.push(
            format!("{location}.features"),
            format!("Cargo feature graph does not contain stable aggregate `{root}`"),
        );
        return FeatureAnalysis::default();
    }

    let stable = feature_closure(package, [root], location, errors);
    let default = if package.features.contains_key("default") {
        feature_closure(package, ["default"], location, errors)
    } else {
        BTreeSet::new()
    };
    let nightly = package
        .features
        .keys()
        .filter(|name| name.as_str() != "default" && !stable.contains(*name))
        .cloned()
        .collect::<BTreeSet<_>>();

    let default_nightly = default.intersection(&nightly).cloned().collect::<Vec<_>>();
    if !default_nightly.is_empty() {
        errors.push(
            format!("{location}.features.default"),
            format!(
                "default features include nightly-only feature(s): {}",
                default_nightly.join(", ")
            ),
        );
    }

    FeatureAnalysis { stable, nightly, default }
}

fn feature_closure<'a>(
    package: &CargoPackage,
    roots: impl IntoIterator<Item = &'a str>,
    location: &str,
    errors: &mut ErrorSink,
) -> BTreeSet<String> {
    let mut enabled = BTreeSet::new();
    let mut pending = roots.into_iter().map(str::to_owned).collect::<VecDeque<_>>();

    while let Some(feature) = pending.pop_front() {
        if !enabled.insert(feature.clone()) {
            continue;
        }
        let Some(members) = package.features.get(&feature) else {
            errors.push(
                format!("{location}.features.{feature}"),
                "feature closure refers to an unknown local feature",
            );
            continue;
        };

        for member in members {
            match parse_feature_member(member) {
                FeatureMember::Local(name) => {
                    if package.features.contains_key(name) {
                        pending.push_back(name.to_owned());
                    } else {
                        errors.push(
                            format!("{location}.features.{feature}"),
                            format!("member `{member}` names no local feature"),
                        );
                    }
                }
                FeatureMember::Dependency(name) => {
                    if !is_optional_dependency(package, name) {
                        errors.push(
                            format!("{location}.features.{feature}"),
                            format!("member `{member}` names no optional dependency"),
                        );
                    }
                }
                FeatureMember::StrongDependencyFeature(name) => {
                    let Some(dependency) = package.dependencies.get(name) else {
                        errors.push(
                            format!("{location}.features.{feature}"),
                            format!("member `{member}` names no dependency"),
                        );
                        continue;
                    };
                    // Cargo's `dependency/feature` form strongly activates an
                    // optional dependency. That activation also enables a
                    // package-local feature with the dependency's name when
                    // Cargo metadata contains one, so its descendants belong
                    // in the stable closure too. `dependency?/feature` below
                    // deliberately does not perform this activation.
                    if dependency.optional && package.features.contains_key(name) {
                        pending.push_back(name.to_owned());
                    }
                }
                FeatureMember::WeakDependencyFeature(name) => {
                    if !package.dependencies.contains_key(name) {
                        errors.push(
                            format!("{location}.features.{feature}"),
                            format!("member `{member}` names no dependency"),
                        );
                    }
                }
            }
        }
    }
    enabled
}

fn is_optional_dependency(package: &CargoPackage, name: &str) -> bool {
    package.dependencies.get(name).is_some_and(|dependency| dependency.optional)
}

enum FeatureMember<'a> {
    Local(&'a str),
    Dependency(&'a str),
    StrongDependencyFeature(&'a str),
    WeakDependencyFeature(&'a str),
}

fn parse_feature_member(member: &str) -> FeatureMember<'_> {
    if let Some(name) = member.strip_prefix("dep:") {
        FeatureMember::Dependency(name)
    } else if let Some((name, _feature)) = member.split_once("?/") {
        FeatureMember::WeakDependencyFeature(name)
    } else if let Some((name, _feature)) = member.split_once('/') {
        FeatureMember::StrongDependencyFeature(name)
    } else {
        FeatureMember::Local(member)
    }
}

fn validate_profiles(
    package: &CargoPackage,
    package_policy: &crate::policy::Package,
    policy: &Policy,
    location: &str,
    errors: &mut ErrorSink,
) {
    let has_features = !package.features.is_empty();
    let has_default = package.features.contains_key("default");
    let mut required = BTreeSet::from([FeatureProfile::Default]);
    if has_features {
        required.insert(FeatureProfile::StableAggregate);
        required.insert(FeatureProfile::All);
    }
    if has_default {
        required.insert(FeatureProfile::NoDefault);
    }

    let selected = package_policy
        .profiles()
        .iter()
        .filter_map(|id| policy.features().profiles().get(id.as_str()).copied())
        .collect::<BTreeSet<_>>();
    for missing in required.difference(&selected) {
        errors.push(
            format!("{location}.profiles"),
            format!("Cargo feature graph requires a `{}` profile", profile_name(*missing)),
        );
    }
    for stale in selected.difference(&required) {
        let reason = if *stale == FeatureProfile::NoDefault && !has_default {
            "Cargo has no `default` feature, so this profile is currently identical to `default`"
        } else {
            "this profile has no package-local feature behavior"
        };
        errors.push(
            format!("{location}.profiles"),
            format!("profile `{}` is invalid: {reason}", profile_name(*stale)),
        );
    }
}

fn profile_name(profile: FeatureProfile) -> &'static str {
    match profile {
        FeatureProfile::Default => "default",
        FeatureProfile::NoDefault => "no-default",
        FeatureProfile::StableAggregate => "stable-aggregate",
        FeatureProfile::All => "all",
    }
}

/// Keeps Cargo's all-features selection on a compiler which can accept it.
///
/// `ci/zc.toml` deliberately stores profile semantics separately from package
/// feature graphs and toolchain sources. Policy validation can therefore prove
/// that all three references exist, but only live inventory knows whether
/// Cargo's stable aggregate has a nonempty nightly-only complement. The planner
/// later translates [`FeatureProfile::All`] directly to `--all-features`; once
/// that happens, a stable, MSRV, or build-rs compiler cannot decline just the
/// nightly-only members. Reject that cross-file combination before planning.
///
/// An `all` selection remains valid on a non-nightly compiler when the
/// complement is empty. This matters for packages whose complete feature graph
/// works on stable and avoids treating a profile spelling as inherently tied to
/// nightly rather than checking the Cargo semantics it currently denotes.
fn validate_non_nightly_all_feature_scopes(
    policy: &Policy,
    packages: &BTreeMap<String, PackageInventory>,
    errors: &mut ErrorSink,
) {
    for (toolchain_id, toolchain) in policy.toolchains() {
        if toolchain.source() == ToolchainSource::PinnedNightly {
            continue;
        }
        for (scope_index, scope) in toolchain.scopes().iter().enumerate() {
            for profile_id in scope.profiles() {
                if policy.features().profiles().get(profile_id.as_str())
                    != Some(&FeatureProfile::All)
                {
                    continue;
                }
                for package_id in scope.packages() {
                    let Some(package) = packages.get(package_id.as_str()) else {
                        // Policy reference validation owns unknown package IDs.
                        continue;
                    };
                    if package.nightly_features.is_empty() {
                        continue;
                    }
                    errors.push(
                        format!(
                            "toolchains.{}.scopes[{scope_index}].profiles",
                            toolchain_id.as_str()
                        ),
                        format!(
                            "non-nightly toolchain selects all-features profile `{}` for package `{}`, whose nightly-only feature(s) are {}",
                            profile_id.as_str(),
                            package_id.as_str(),
                            display_set(&package.nightly_features)
                        ),
                    );
                }
            }
        }
    }
}

fn validate_target_feature_references(
    package: &CargoPackage,
    location: &str,
    errors: &mut ErrorSink,
) {
    for target in &package.targets {
        for feature in &target.required_features {
            if !package.features.contains_key(feature) {
                errors.push(
                    format!("{location}.targets.{}", target.name),
                    format!("required feature `{feature}` is absent from Cargo metadata"),
                );
            }
        }
    }
}

/// Returns the union of all targets selected on each exact Rust version.
///
/// Ordinary, Miri, and semver selections are intentionally combined here and
/// nowhere else. Validation and the roller's rewrite must agree about both
/// collisions (two policy toolchains resolving to one version) and retained
/// versions after one pin changes.
fn selected_targets_by_version(
    policy: &Policy,
    toolchain_versions: &BTreeMap<String, String>,
) -> BTreeMap<String, BTreeSet<String>> {
    let mut selected = toolchain_versions
        .values()
        .map(|version| (version.clone(), BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    let mut add_target_set = |toolchain_id: &str, target_set: &crate::policy::Id| {
        let (Some(version), Some(targets)) =
            (toolchain_versions.get(toolchain_id), policy.target_sets().get(target_set.as_str()))
        else {
            return;
        };
        selected
            .entry(version.clone())
            .or_default()
            .extend(targets.iter().map(|target| target.as_str().to_owned()));
    };

    for (toolchain_id, toolchain) in policy.toolchains() {
        for scope in toolchain.scopes() {
            add_target_set(toolchain_id.as_str(), scope.target_set());
        }
    }
    let miri = policy.miri();
    for scope in miri.scopes() {
        add_target_set(miri.toolchain().as_str(), scope.target_set());
    }
    let semver = policy.semver();
    add_target_set(semver.toolchain().as_str(), semver.target_set());
    selected
}

/// Reconciles offline target-support evidence with every selected CI cell.
///
/// `rustc --print target-list` and `rustup target list` are authoritative only
/// after their exact compiler has been installed. Asking for all selected
/// compilers here would make planning download the MSRV and every historical
/// build-rs compiler before matrix fan-out. Instead,
/// `ci/rust-target-support.toml` records the small set of target/version pairs
/// on which policy currently relies. Exact equality makes any target, scope,
/// or compiler-version change fail until that evidence is reviewed. The typed
/// stable/nightly refresh command checks a changed compiler's real rustup list
/// before replacing this checked-in evidence.
fn validate_rust_target_support(
    policy: &Policy,
    toolchain_versions: &BTreeMap<String, String>,
    support: &RustTargetSupport,
    errors: &mut ErrorSink,
) {
    if support.schema_version != RUST_TARGET_SUPPORT_SCHEMA_VERSION {
        errors.push(
            format!("{RUST_TARGET_SUPPORT_PATH}.schema_version"),
            format!(
                "unsupported schema version {}; expected {RUST_TARGET_SUPPORT_SCHEMA_VERSION}",
                support.schema_version
            ),
        );
    }

    if support.toolchains.windows(2).any(|pair| pair[0].version >= pair[1].version) {
        errors.push(
            format!("{RUST_TARGET_SUPPORT_PATH}.toolchains"),
            "compiler versions must be strictly sorted and unique",
        );
    }

    let mut supported = BTreeMap::<String, BTreeSet<String>>::new();
    for (index, entry) in support.toolchains.iter().enumerate() {
        let location = format!("{RUST_TARGET_SUPPORT_PATH}.toolchains[{index}]");
        if entry.version.is_empty() {
            errors.push(format!("{location}.version"), "compiler version must not be empty");
        }
        if entry.targets.is_empty() {
            errors.push(format!("{location}.targets"), "target support set must not be empty");
        }
        if entry.targets.windows(2).any(|pair| pair[0] >= pair[1]) {
            errors.push(
                format!("{location}.targets"),
                "target names must be strictly sorted and unique",
            );
        }
        for target in &entry.targets {
            match identifier::validate(target) {
                Err(IdentifierError::TooLong { bytes }) => errors.push(
                    format!("{location}.targets"),
                    format!(
                        "target identifier `{target}` is {bytes} bytes; maximum is {} bytes",
                        identifier::MAX_ID_BYTES
                    ),
                ),
                Err(IdentifierError::InvalidSyntax) => errors.push(
                    format!("{location}.targets"),
                    format!("`{target}` is not a canonical CI identifier"),
                ),
                Ok(()) if !is_rust_target_name(target) => errors.push(
                    format!("{location}.targets"),
                    format!("`{target}` is not a canonical Rust target name"),
                ),
                Ok(()) => {}
            }
        }
        if supported
            .insert(entry.version.clone(), entry.targets.iter().cloned().collect())
            .is_some()
        {
            errors.push(
                format!("{location}.version"),
                format!("compiler version `{}` is declared more than once", entry.version),
            );
        }
    }

    let expected_versions = toolchain_versions.values().cloned().collect::<BTreeSet<_>>();
    for version in &expected_versions {
        if !supported.contains_key(version) {
            errors.push(
                format!("{RUST_TARGET_SUPPORT_PATH}.toolchains"),
                format!("selected Rust version `{version}` has no target-support evidence"),
            );
        }
    }
    for version in supported.keys() {
        if !expected_versions.contains(version) {
            errors.push(
                format!("{RUST_TARGET_SUPPORT_PATH}.toolchains.{version}"),
                "target-support evidence does not correspond to a selected Rust version",
            );
        }
    }

    let expected = selected_targets_by_version(policy, toolchain_versions);
    for (toolchain_id, toolchain) in policy.toolchains() {
        let Some(version) = toolchain_versions.get(toolchain_id.as_str()) else {
            continue;
        };
        validate_scopes_target_support(
            policy,
            toolchain_id.as_str(),
            version,
            toolchain.scopes(),
            &format!("toolchains.{}.scopes", toolchain_id.as_str()),
            &supported,
            errors,
        );
    }

    let miri = policy.miri();
    if let Some(version) = toolchain_versions.get(miri.toolchain().as_str()) {
        validate_scopes_target_support(
            policy,
            miri.toolchain().as_str(),
            version,
            miri.scopes(),
            "miri.scopes",
            &supported,
            errors,
        );
    }

    let semver = policy.semver();
    if let (Some(version), Some(targets)) = (
        toolchain_versions.get(semver.toolchain().as_str()),
        policy.target_sets().get(semver.target_set().as_str()),
    ) {
        validate_selected_target_support(
            semver.toolchain().as_str(),
            version,
            targets,
            "semver.target_set",
            &supported,
            errors,
        );
    }

    // Require equality, not merely a superset. Otherwise a removed scope could
    // leave stale evidence which later makes reintroducing that target look as
    // though its compiler support had just been reviewed.
    for (version, targets) in &supported {
        let Some(expected_targets) = expected.get(version) else {
            continue;
        };
        for target in targets.difference(expected_targets) {
            errors.push(
                format!("{RUST_TARGET_SUPPORT_PATH}.toolchains.{version}.targets"),
                format!(
                    "target `{target}` is not selected on Rust version `{version}` by current policy"
                ),
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn validate_scopes_target_support(
    policy: &Policy,
    toolchain_id: &str,
    version: &str,
    scopes: &[crate::policy::Scope],
    location: &str,
    supported: &BTreeMap<String, BTreeSet<String>>,
    errors: &mut ErrorSink,
) {
    for (index, scope) in scopes.iter().enumerate() {
        let Some(targets) = policy.target_sets().get(scope.target_set().as_str()) else {
            // Policy reference validation owns unknown target-set IDs.
            continue;
        };
        validate_selected_target_support(
            toolchain_id,
            version,
            targets,
            &format!("{location}[{index}].target_set"),
            supported,
            errors,
        );
    }
}

#[allow(clippy::too_many_arguments)]
fn validate_selected_target_support(
    toolchain_id: &str,
    version: &str,
    targets: &BTreeSet<crate::policy::Id>,
    location: &str,
    supported: &BTreeMap<String, BTreeSet<String>>,
    errors: &mut ErrorSink,
) {
    let available = supported.get(version);
    for target in targets {
        if available.is_some_and(|available| !available.contains(target.as_str())) {
            errors.push(
                location,
                format!(
                    "target `{}` lacks reviewed support on toolchain `{toolchain_id}` (Rust `{version}`) in `{RUST_TARGET_SUPPORT_PATH}`",
                    target.as_str()
                ),
            );
        }
    }
}

/// Refreshes checked-in support after the manifest's stable or nightly pin
/// has already been edited.
///
/// `old_version` is intentionally supplied by the caller. The roller captures
/// it before editing the manifest; this function reads the post-edit manifest
/// and reconstructs the pre-edit state. Exact pre-state validation prevents a
/// roll from blessing unrelated catalog drift. The replacement is derived
/// from complete target unions rather than editing one row, so both an old
/// version retained by another toolchain and a new version which collides with
/// another toolchain are handled without special cases.
pub fn refresh_rust_target_support(
    repository_root: impl AsRef<Path>,
    pin: &str,
    old_version: &str,
) -> Result<(), RefreshTargetSupportError> {
    let repository_root = repository_root.as_ref().canonicalize().map_err(|source| {
        CollectError::RepositoryRoot { path: repository_root.as_ref().to_path_buf(), source }
    })?;
    let policy_file = open_inventory_file(&repository_root, Path::new("ci/zc.toml"))?;
    let policy_source = policy_file
        .read_to_string()
        .map_err(|source| CollectError::Read { path: policy_file.path().to_owned(), source })?;
    let policy = Policy::parse(&policy_source).map_err(|source| ReadPolicyError::Policy {
        path: policy_file.path().to_owned(),
        source,
    })?;

    let manifest_file = open_inventory_file(&repository_root, Path::new("zerocopy/Cargo.toml"))?;
    let manifest_source = manifest_file
        .read_to_string()
        .map_err(|source| CollectError::Read { path: manifest_file.path().to_owned(), source })?;
    let metadata = ToolchainMetadata::parse(manifest_file.path(), &manifest_source)?;

    let path = repository_root.join(RUST_TARGET_SUPPORT_PATH);
    let support_file = open_inventory_file(&repository_root, Path::new(RUST_TARGET_SUPPORT_PATH))?;
    if support_file.path() != path {
        return Err(RefreshTargetSupportError::RedirectedCatalog {
            configured: path,
            resolved: support_file.path().to_owned(),
        });
    }
    let source = support_file.read_to_string().map_err(|source| {
        RefreshTargetSupportError::Read { path: support_file.path().to_owned(), source }
    })?;
    let support = toml::from_str(&source).map_err(|source| RefreshTargetSupportError::Parse {
        path: support_file.path().to_owned(),
        source: Box::new(source),
    })?;

    // Reject drift before asking rustup anything. Besides producing the most
    // useful failure, this prevents a malformed pre-state from triggering an
    // unnecessary toolchain lookup or download attempt.
    let (new_version, refreshed) =
        planned_rust_target_support(&policy, &metadata, &support, pin, old_version)?;
    let command = format!("rustup target list --toolchain {new_version}");
    let output = Command::new("rustup")
        .args(["target", "list", "--toolchain", &new_version])
        .env("RUSTUP_AUTO_INSTALL", "0")
        .env_remove("RUSTUP_TOOLCHAIN")
        .output()
        .map_err(|source| RefreshTargetSupportError::RustupIo {
            command: command.clone(),
            source,
        })?;
    if !output.status.success() {
        return Err(RefreshTargetSupportError::RustupFailed {
            command,
            status: output.status,
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        });
    }
    let stdout = String::from_utf8(output.stdout).map_err(|source| {
        RefreshTargetSupportError::RustupUtf8 { command: command.clone(), source }
    })?;
    let available = parse_rustup_target_list(&command, &stdout)?;

    validate_refreshed_targets(&new_version, &refreshed, &available)?;
    atomic_replace(
        &path,
        &support_file,
        &[
            (&policy_file, repository_root.join("ci/zc.toml")),
            (&manifest_file, repository_root.join("zerocopy/Cargo.toml")),
            (&support_file, path.clone()),
        ],
        render_rust_target_support(&refreshed).as_bytes(),
    )
    .map_err(|source| RefreshTargetSupportError::Write { path, source })
}

fn parse_rustup_target_list(
    command: &str,
    stdout: &str,
) -> Result<BTreeSet<String>, RefreshTargetSupportError> {
    let mut targets = BTreeSet::new();
    for (index, line) in stdout.lines().enumerate() {
        let parts = line.split_whitespace().collect::<Vec<_>>();
        if !matches!(parts.as_slice(), [_] | [_, "(installed)"]) {
            return Err(RefreshTargetSupportError::MalformedRustupOutput {
                command: command.to_owned(),
                line: index + 1,
                message: format!("expected `TARGET` or `TARGET (installed)`, found `{line}`"),
            });
        }
        let target = parts[0];
        let canonical =
            if parts.len() == 1 { target.to_owned() } else { format!("{target} (installed)") };
        if line != canonical {
            return Err(RefreshTargetSupportError::MalformedRustupOutput {
                command: command.to_owned(),
                line: index + 1,
                message: format!("noncanonical spacing in `{line}`"),
            });
        }
        if identifier::validate(target).is_err() || !is_rust_target_name(target) {
            return Err(RefreshTargetSupportError::MalformedRustupOutput {
                command: command.to_owned(),
                line: index + 1,
                message: format!("`{target}` is not a canonical Rust target name"),
            });
        }
        if !targets.insert(target.to_owned()) {
            return Err(RefreshTargetSupportError::MalformedRustupOutput {
                command: command.to_owned(),
                line: index + 1,
                message: format!("target `{target}` appears more than once"),
            });
        }
    }
    if targets.is_empty() {
        return Err(RefreshTargetSupportError::MalformedRustupOutput {
            command: command.to_owned(),
            line: 0,
            message: "target list is empty".to_owned(),
        });
    }
    Ok(targets)
}

fn pinned_version<'a>(
    metadata: &'a ToolchainMetadata,
    pin: &str,
) -> Result<&'a str, RefreshTargetSupportError> {
    match pin {
        "stable" => Ok(&metadata.pinned_stable),
        "nightly" => Ok(&metadata.pinned_nightly),
        _ => Err(RefreshTargetSupportError::UnsupportedPin(pin.to_owned())),
    }
}

fn set_pinned_version(
    metadata: &mut ToolchainMetadata,
    pin: &str,
    version: String,
) -> Result<(), RefreshTargetSupportError> {
    match pin {
        "stable" => metadata.pinned_stable = version,
        "nightly" => metadata.pinned_nightly = version,
        _ => return Err(RefreshTargetSupportError::UnsupportedPin(pin.to_owned())),
    }
    Ok(())
}

#[cfg(test)]
fn refreshed_rust_target_support(
    policy: &Policy,
    post_metadata: &ToolchainMetadata,
    support: &RustTargetSupport,
    pin: &str,
    old_version: &str,
    available: &BTreeSet<String>,
) -> Result<RustTargetSupport, RefreshTargetSupportError> {
    let (new_version, refreshed) =
        planned_rust_target_support(policy, post_metadata, support, pin, old_version)?;
    validate_refreshed_targets(&new_version, &refreshed, available)?;
    Ok(refreshed)
}

fn planned_rust_target_support(
    policy: &Policy,
    post_metadata: &ToolchainMetadata,
    support: &RustTargetSupport,
    pin: &str,
    old_version: &str,
) -> Result<(String, RustTargetSupport), RefreshTargetSupportError> {
    let new_version = pinned_version(post_metadata, pin)?.to_owned();
    validate_refresh_pin(pin, old_version)?;
    validate_refresh_pin(pin, &new_version)?;
    let mut pre_metadata = post_metadata.clone();
    set_pinned_version(&mut pre_metadata, pin, old_version.to_owned())?;

    let pre_versions = resolved_toolchain_versions(policy, &pre_metadata);
    let mut errors = ErrorSink::default();
    validate_rust_target_support(policy, &pre_versions, support, &mut errors);
    if !errors.is_empty() {
        return Err(RefreshTargetSupportError::ExistingDrift(errors.finish()));
    }

    let post_versions = resolved_toolchain_versions(policy, post_metadata);
    let selected = selected_targets_by_version(policy, &post_versions);
    Ok((new_version, target_support_from_selected(selected)))
}

fn validate_refresh_pin(pin: &str, version: &str) -> Result<(), RefreshTargetSupportError> {
    let valid = match pin {
        "stable" => parse_exact_rust_version(version).is_some(),
        "nightly" => is_pinned_nightly(version),
        _ => return Err(RefreshTargetSupportError::UnsupportedPin(pin.to_owned())),
    };
    if !valid {
        return Err(RefreshTargetSupportError::InvalidPinVersion {
            pin: pin.to_owned(),
            version: version.to_owned(),
        });
    }
    Ok(())
}

fn validate_refreshed_targets(
    new_version: &str,
    refreshed: &RustTargetSupport,
    available: &BTreeSet<String>,
) -> Result<(), RefreshTargetSupportError> {
    let required = refreshed
        .toolchains
        .iter()
        .find(|entry| entry.version == new_version)
        .map(|entry| entry.targets.iter().cloned().collect::<BTreeSet<_>>())
        .unwrap_or_default();
    let unsupported = required.difference(available).cloned().collect::<Vec<_>>();
    if !unsupported.is_empty() {
        return Err(RefreshTargetSupportError::UnsupportedTargets {
            version: new_version.to_owned(),
            targets: unsupported,
        });
    }
    Ok(())
}

fn target_support_from_selected(selected: BTreeMap<String, BTreeSet<String>>) -> RustTargetSupport {
    RustTargetSupport {
        schema_version: RUST_TARGET_SUPPORT_SCHEMA_VERSION,
        toolchains: selected
            .into_iter()
            .map(|(version, targets)| RustTargetSupportEntry {
                version,
                targets: targets.into_iter().collect(),
            })
            .collect(),
    }
}

fn render_rust_target_support(support: &RustTargetSupport) -> String {
    let mut rendered = RUST_TARGET_SUPPORT_PREAMBLE.to_owned();
    writeln!(rendered, "schema_version = {}", support.schema_version).unwrap();
    for entry in &support.toolchains {
        writeln!(rendered, "\n[[toolchains]]").unwrap();
        writeln!(rendered, "version = {:?}", entry.version).unwrap();
        if entry.targets.len() == 1 {
            writeln!(rendered, "targets = [{:?}]", entry.targets[0]).unwrap();
            continue;
        }
        writeln!(rendered, "targets = [").unwrap();
        for target in &entry.targets {
            writeln!(rendered, "    {target:?},").unwrap();
        }
        writeln!(rendered, "]").unwrap();
    }
    rendered
}

/// Replaces `path` only after a complete sibling temporary file is durable.
///
/// The scheduled roller runs on Linux, where renaming over an existing file is
/// atomic. Platforms without replacement rename semantics fail without first
/// deleting the checked-in catalog; they cannot expose a partially written
/// support contract.
fn atomic_replace(
    path: &Path,
    original: &OpenedRepositoryFile,
    inputs: &[(&OpenedRepositoryFile, PathBuf)],
    contents: &[u8],
) -> io::Result<()> {
    let parent = path.parent().ok_or_else(|| io::Error::other("path has no parent directory"))?;
    let file_name = path.file_name().ok_or_else(|| io::Error::other("path has no file name"))?;
    let permissions = original.permissions()?;
    let (temporary, mut file) = (0..100)
        .find_map(|nonce| {
            let mut temporary_name = OsString::from(".");
            temporary_name.push(file_name);
            temporary_name.push(format!(".tmp-{}-{nonce}", std::process::id()));
            let temporary = parent.join(temporary_name);
            match fs::OpenOptions::new().write(true).create_new(true).open(&temporary) {
                Ok(file) => Some(Ok((temporary, file))),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => None,
                Err(error) => Some(Err(error)),
            }
        })
        .transpose()?
        .ok_or_else(|| {
            io::Error::new(io::ErrorKind::AlreadyExists, "no temporary name available")
        })?;

    let result = (|| {
        file.set_permissions(permissions)?;
        file.write_all(contents)?;
        file.sync_all()?;
        drop(file);
        for (input, configured) in inputs {
            if !input.is_still_named_by(configured)? {
                return Err(io::Error::other(format!(
                    "repository input `{}` changed after its retained read",
                    configured.display()
                )));
            }
        }
        fs::rename(&temporary, path)?;
        // The scheduled roller runs on Linux. Syncing the parent makes the
        // replacement rename durable there, rather than merely making the
        // temporary file's contents durable before a crash.
        #[cfg(unix)]
        fs::File::open(parent)?.sync_all()?;
        Ok(())
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    result
}

fn validate_policy_targets(policy: &Policy, errors: &mut ErrorSink) {
    let semver = policy.semver();
    let selected =
        policy.target_sets().get(semver.target_set().as_str()).cloned().unwrap_or_default();
    for (id, target) in policy.targets() {
        let name = id.as_str();
        if !is_rust_target_name(name) {
            errors.push(
                format!("targets.{name}.id"),
                "Rust target name must have at least two nonempty `-`-separated components",
            );
        }

        // `mode` changes commands, not just labels: native runs test binaries,
        // cross compiles tests and the library, and thumb checks only library
        // code. Keep this independent allow-list between policy and executor
        // so a one-word policy edit cannot make the x86_64 Linux job execute a
        // foreign binary or silently weaken one of the two native targets.
        let expected_mode = if NATIVE_EXECUTION_TARGETS.contains(&name) {
            TargetMode::Native
        } else if name == THUMB_EXECUTION_TARGET {
            TargetMode::Thumb
        } else {
            TargetMode::Cross
        };
        if target.mode() != expected_mode {
            errors.push(
                format!("targets.{name}.mode"),
                format!(
                    "target must use `{}` mode for the current x86_64 Linux executor; found `{}`",
                    target_mode_name(expected_mode),
                    target_mode_name(target.mode())
                ),
            );
        }

        let is_selected = selected.contains(name);
        let is_waived = semver.waivers().contains_key(name);
        match (target.semver_eligible(), is_selected, is_waived) {
            (true, true, false) | (true, false, true) | (false, false, false) => {}
            (true, true, true) => errors.push(
                format!("targets.{name}.semver"),
                "semver-eligible target is both selected and waived; choose exactly one",
            ),
            (true, false, false) => errors.push(
                format!("targets.{name}.semver"),
                "semver-eligible target must be selected or explicitly waived",
            ),
            (false, _, _) => errors.push(
                format!("targets.{name}.semver"),
                "semver-inapplicable target must be neither selected nor waived",
            ),
        }
    }
}

fn target_mode_name(mode: TargetMode) -> &'static str {
    match mode {
        TargetMode::Native => "native",
        TargetMode::Cross => "cross",
        TargetMode::Thumb => "thumb",
    }
}

fn is_rust_target_name(name: &str) -> bool {
    // Policy IDs already restrict the character set to lowercase ASCII,
    // digits, `_`, `-`, and `.`. Rust has built-in two-component targets such
    // as `avr-none` and dotted components such as `thumbv8m.base`; do not
    // impose the conventional but inaccurate three-component "triple" shape.
    let mut components = name.split('-');
    let Some(first) = components.next() else {
        return false;
    };
    let Some(second) = components.next() else {
        return false;
    };
    !first.is_empty() && !second.is_empty() && components.all(|component| !component.is_empty())
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RustVersion {
    major: u64,
    minor: u64,
    patch: u64,
}

impl RustVersion {
    const fn new(major: u64, minor: u64, patch: u64) -> Self {
        Self { major, minor, patch }
    }
}

impl fmt::Display for RustVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

fn parse_exact_rust_version(value: &str) -> Option<RustVersion> {
    let mut components = value.split('.');
    let major = components.next()?.parse().ok()?;
    let minor = components.next()?.parse().ok()?;
    let patch = components.next()?.parse().ok()?;
    if components.next().is_some() {
        return None;
    }
    let version = RustVersion { major, minor, patch };
    (version.to_string() == value).then_some(version)
}

/// A Rust edition whose compiler floor has been deliberately reviewed.
///
/// These release floors come from the Rust Edition Guide: Rust 2015 is the
/// language baseline, while editions 2018, 2021, and 2024 shipped in Rust
/// 1.31, 1.56, and 1.85 respectively. Keep this closed rather than inferring a
/// year-to-version formula; future editions must fail inventory until their
/// actual release floor is known.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RustEdition {
    E2015,
    E2018,
    E2021,
    E2024,
}

impl RustEdition {
    fn parse(value: &str) -> Option<Self> {
        match value {
            "2015" => Some(Self::E2015),
            "2018" => Some(Self::E2018),
            "2021" => Some(Self::E2021),
            "2024" => Some(Self::E2024),
            _ => None,
        }
    }

    fn year(self) -> &'static str {
        match self {
            Self::E2015 => "2015",
            Self::E2018 => "2018",
            Self::E2021 => "2021",
            Self::E2024 => "2024",
        }
    }

    fn compiler_floor(self) -> RustVersion {
        match self {
            Self::E2015 => RustVersion::new(1, 0, 0),
            Self::E2018 => RustVersion::new(1, 31, 0),
            Self::E2021 => RustVersion::new(1, 56, 0),
            Self::E2024 => RustVersion::new(1, 85, 0),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CompilerFloorSource {
    DeclaredRustVersion,
    Edition(RustEdition),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PackageCompilerFloor {
    version: RustVersion,
    source: CompilerFloorSource,
}

/// Derives the strongest compiler floor expressed by one Cargo package.
///
/// `rust-version` is optional, but edition syntax is not backwards compatible
/// with arbitrarily old compilers. Cargo metadata supplies the normalized
/// package default and every target override, so absence of `rust-version`
/// must not mean absence of a floor. Unknown editions fail closed here before
/// a future Cargo update can silently add unmodeled compatibility requirements.
fn package_compiler_floor(
    rust_version: Option<&str>,
    editions: &BTreeSet<String>,
    rust_version_location: &str,
    edition_location: &str,
    package_context: Option<&str>,
    errors: &mut ErrorSink,
) -> Option<PackageCompilerFloor> {
    let mut floor = None;
    if let Some(value) = rust_version {
        match parse_exact_rust_version(value) {
            Some(version) => {
                floor = Some(PackageCompilerFloor {
                    version,
                    source: CompilerFloorSource::DeclaredRustVersion,
                });
            }
            None => {
                let message = package_context.map_or_else(
                    || format!("declared MSRV `{value}` is not an exact Rust version"),
                    |context| {
                        format!(
                            "dependency {context} declares MSRV `{value}`, which is not an exact Rust version"
                        )
                    },
                );
                errors.push(rust_version_location, message);
            }
        }
    }

    if editions.is_empty() {
        errors.push(edition_location, "Cargo metadata reported no Rust edition for this package");
    }
    for value in editions {
        let Some(edition) = RustEdition::parse(value) else {
            let context = package_context
                .map(|context| format!(" for dependency {context}"))
                .unwrap_or_default();
            errors.push(
                edition_location,
                format!(
                    "Cargo metadata{context} reports unsupported Rust edition `{value}`; extend the audited edition compatibility table before accepting it"
                ),
            );
            continue;
        };
        let candidate = PackageCompilerFloor {
            version: edition.compiler_floor(),
            source: CompilerFloorSource::Edition(edition),
        };
        if floor.is_none_or(|known| candidate.version > known.version) {
            floor = Some(candidate);
        }
    }
    floor
}

fn validate_toolchain_package_floor(
    location: impl Into<String>,
    toolchain: &str,
    version: RustVersion,
    package: &str,
    floor: PackageCompilerFloor,
    errors: &mut ErrorSink,
) {
    if version >= floor.version {
        return;
    }
    let requirement = match floor.source {
        CompilerFloorSource::DeclaredRustVersion => format!("MSRV `{}`", floor.version),
        CompilerFloorSource::Edition(edition) => {
            format!("Rust {} edition floor `{}`", edition.year(), floor.version)
        }
    };
    errors.push(
        location,
        format!(
            "toolchain `{toolchain}` Rust version `{version}` is older than package `{package}` {requirement}"
        ),
    );
}

fn validate_build_rs_contract(
    source: &str,
    expected: &BTreeMap<String, String>,
    errors: &mut ErrorSink,
) -> BTreeMap<String, RustVersion> {
    const HEADER: &str = "[package.metadata.build-rs]";
    let lines = source.lines().collect::<Vec<_>>();
    let literal_occurrences = source.matches(HEADER).count();
    let headers = lines
        .iter()
        .enumerate()
        .filter_map(|(index, line)| (*line == HEADER).then_some(index))
        .collect::<Vec<_>>();
    if literal_occurrences != 1 || headers.len() != 1 {
        errors.push(
            "zerocopy/Cargo.toml.package.metadata.build-rs",
            format!(
                "expected `{HEADER}` exactly once as a complete line; found {literal_occurrences} literal occurrence(s) and {} complete header line(s)",
                headers.len()
            ),
        );
        return BTreeMap::new();
    }

    let start = headers[0] + 1;
    let end =
        lines[start..].iter().position(|line| line.starts_with('[')).map(|offset| start + offset);
    let Some(end) = end else {
        errors.push(
            "zerocopy/Cargo.toml.package.metadata.build-rs",
            "the build-rs table must be followed by another unindented TOML table",
        );
        return BTreeMap::new();
    };

    let mut parsed = BTreeMap::new();
    let mut cfg_names = BTreeMap::<String, String>::new();
    for (offset, line) in lines[start..end].iter().enumerate() {
        let line_number = start + offset + 1;
        let before_comment = line.split('#').next().unwrap_or("");
        let content = before_comment.trim();
        if content.is_empty() {
            continue;
        }
        if line.trim_start().starts_with('[') {
            errors.push(
                format!("zerocopy/Cargo.toml:{line_number}"),
                "TOML table headers after build-rs must start in column one",
            );
            continue;
        }

        let words = content.split_whitespace().collect::<Vec<_>>();
        if words.len() != 3 || words.get(1) != Some(&"=") {
            errors.push(
                format!("zerocopy/Cargo.toml:{line_number}"),
                "expected exactly `name = \"1.2.3\"` before any comment",
            );
            continue;
        }
        let name = words[0];
        let quoted = words[2];
        let Some(value) = quoted.strip_prefix('"').and_then(|value| value.strip_suffix('"')) else {
            errors.push(
                format!("zerocopy/Cargo.toml:{line_number}"),
                "build-rs version must be one double-quoted `major.minor.patch` value",
            );
            continue;
        };
        let Some(version) = parse_exact_rust_version(value) else {
            errors.push(
                format!("zerocopy/Cargo.toml:{line_number}"),
                format!("`{value}` is not an exact `major.minor.patch` Rust version"),
            );
            continue;
        };
        if !name
            .bytes()
            .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-')
        {
            errors.push(
                format!("zerocopy/Cargo.toml:{line_number}"),
                format!(
                    "build-rs key `{name}` may contain only lowercase letters, digits, and dashes"
                ),
            );
        }
        let suffix = format!("-{}-{}-{}", version.major, version.minor, version.patch);
        if !name.starts_with("no-zerocopy-") || !name.ends_with(&suffix) {
            errors.push(
                format!("zerocopy/Cargo.toml:{line_number}"),
                format!("key `{name}` must start with `no-zerocopy-` and end with `{suffix}`"),
            );
        }
        if parsed.insert(name.to_owned(), version).is_some() {
            errors.push(
                format!("zerocopy/Cargo.toml:{line_number}"),
                format!("duplicate build-rs key `{name}`"),
            );
        }
        let cfg_name = name.replace('-', "_");
        if let Some(previous) = cfg_names.insert(cfg_name.clone(), name.to_owned()) {
            errors.push(
                format!("zerocopy/Cargo.toml:{line_number}"),
                format!("keys `{previous}` and `{name}` both become cfg name `{cfg_name}`"),
            );
        }
    }

    let parsed_text = parsed
        .iter()
        .map(|(name, version)| (name.clone(), version.to_string()))
        .collect::<BTreeMap<_, _>>();
    for (name, value) in expected {
        match parsed_text.get(name) {
            None => errors.push(
                "zerocopy/Cargo.toml.package.metadata.build-rs",
                format!("TOML key `{name}` was not parsed by the build.rs text grammar"),
            ),
            Some(parsed_value) if parsed_value != value => errors.push(
                "zerocopy/Cargo.toml.package.metadata.build-rs",
                format!(
                    "TOML gives `{name}` version `{value}`, but text parsing gives `{parsed_value}`"
                ),
            ),
            Some(_) => {}
        }
    }
    for name in parsed_text.keys() {
        if !expected.contains_key(name) {
            errors.push(
                "zerocopy/Cargo.toml.package.metadata.build-rs",
                format!("text parser found `{name}`, but structured TOML did not"),
            );
        }
    }
    parsed
}

fn resolved_toolchain_version<'a>(
    id: &str,
    source: ToolchainSource,
    metadata: &'a ToolchainMetadata,
) -> Option<&'a str> {
    match source {
        ToolchainSource::ManifestRustVersion => Some(&metadata.rust_version),
        ToolchainSource::PinnedStable => Some(&metadata.pinned_stable),
        ToolchainSource::PinnedNightly => Some(&metadata.pinned_nightly),
        ToolchainSource::BuildRs => metadata.build_rs.get(id),
    }
    .map(String::as_str)
}

/// Resolves policy toolchain IDs through the manifest-owned version sources.
///
/// Inventory validation and the target-support refresh command deliberately
/// share this function. Otherwise a new source variant or renamed metadata
/// field could make the roller update a different catalog from the one the
/// planner later validates.
fn resolved_toolchain_versions(
    policy: &Policy,
    metadata: &ToolchainMetadata,
) -> BTreeMap<String, String> {
    policy
        .toolchains()
        .iter()
        .filter_map(|(id, toolchain)| {
            resolved_toolchain_version(id.as_str(), toolchain.source(), metadata)
                .map(|version| (id.as_str().to_owned(), version.to_owned()))
        })
        .collect()
}

fn validate_toolchains(
    policy: &Policy,
    collected: &CollectedRepository,
    build_rs: &BTreeMap<String, RustVersion>,
    errors: &mut ErrorSink,
) -> BTreeMap<String, String> {
    let packages = &collected.packages;
    let workspace_package_ids = &collected.workspace_package_ids;
    let resolved_packages = &collected.resolved_packages;
    let metadata = &collected.toolchain_metadata;
    let primary_manifest =
        policy.packages().get(PRIMARY_PACKAGE_ID).map(|package| package.manifest().as_path());
    let primary_package = primary_manifest.and_then(|manifest| packages.get(manifest));
    match primary_package.and_then(CargoPackage::rust_version) {
        Some(version) if version == metadata.rust_version => {}
        Some(version) => errors.push(
            "toolchains.msrv",
            format!(
                "Cargo metadata reports rust-version `{version}`, but manifest metadata reports `{}`",
                metadata.rust_version
            ),
        ),
        None => errors.push(
            "toolchains.msrv",
            "primary Cargo package must declare an exact rust-version",
        ),
    }

    let msrv = parse_exact_rust_version(&metadata.rust_version);
    if msrv.is_none() {
        errors.push(
            "toolchains.msrv",
            format!("`{}` is not an exact Rust version", metadata.rust_version),
        );
    }
    let pinned_stable = parse_exact_rust_version(&metadata.pinned_stable);
    if pinned_stable.is_none() {
        errors.push(
            "toolchains.stable",
            format!("`{}` is not an exact stable Rust version", metadata.pinned_stable),
        );
    }
    // A dated nightly descriptor has no sound ordering against a semantic Rust
    // release number. Its exact date shape is the strongest local check; the
    // bootstrap and execution paths separately prove that the pin is usable.
    if !is_pinned_nightly(&metadata.pinned_nightly) {
        errors.push(
            "toolchains.nightly",
            format!("`{}` must have exact form `nightly-YYYY-MM-DD`", metadata.pinned_nightly),
        );
    }

    let policy_build_rs = policy
        .toolchains()
        .iter()
        .filter(|(_, toolchain)| toolchain.source() == ToolchainSource::BuildRs)
        .map(|(id, _)| id.as_str().to_owned())
        .collect::<BTreeSet<_>>();
    let manifest_build_rs = metadata.build_rs.keys().cloned().collect::<BTreeSet<_>>();
    for missing in manifest_build_rs.difference(&policy_build_rs) {
        errors.push(
            "toolchains",
            format!("build-rs metadata key `{missing}` has no policy toolchain"),
        );
    }
    for stale in policy_build_rs.difference(&manifest_build_rs) {
        errors.push(
            format!("toolchains.{stale}"),
            "build-rs policy toolchain has no matching manifest metadata key",
        );
    }

    let versions = resolved_toolchain_versions(policy, metadata);
    let mut semantic_versions = BTreeMap::new();
    for (id, toolchain) in policy.toolchains() {
        let (required_id, semantic_version) = match toolchain.source() {
            ToolchainSource::ManifestRustVersion => ("msrv", msrv),
            ToolchainSource::PinnedStable => ("stable", pinned_stable),
            ToolchainSource::PinnedNightly => ("nightly", None),
            ToolchainSource::BuildRs => (id.as_str(), build_rs.get(id.as_str()).copied()),
        };
        if resolved_toolchain_version(id.as_str(), toolchain.source(), metadata).is_none() {
            continue;
        }
        if id.as_str() != required_id {
            errors.push(
                format!("toolchains.{}.id", id.as_str()),
                format!(
                    "source `{}` requires exact policy ID `{required_id}`",
                    toolchain_source_name(toolchain.source())
                ),
            );
        }
        if toolchain.source() == ToolchainSource::BuildRs && !build_rs.contains_key(id.as_str()) {
            // The text-contract validator owns the more specific diagnostic.
            continue;
        }
        if let Some(version) = semantic_version {
            semantic_versions.insert(id.as_str().to_owned(), version);
        }
    }

    validate_toolchain_lockfile_compatibility(
        collected.cargo_lockfile_version,
        &semantic_versions,
        errors,
    );
    validate_scoped_package_compiler_floors(
        policy,
        packages,
        workspace_package_ids,
        resolved_packages,
        &semantic_versions,
        errors,
    );
    versions
}

/// Checks the Cargo binary paired with every semantically versioned compiler.
///
/// Rust release toolchains ship matching rustc and Cargo release numbers. CI
/// invokes that toolchain's Cargo, which must parse `Cargo.lock` before rustc
/// can enforce any package MSRV. Dated nightlies are deliberately absent from
/// `semantic_versions`; their date has no exact ordering against a Cargo
/// release, while unknown future lock formats already fail collection.
fn validate_toolchain_lockfile_compatibility(
    lockfile: CargoLockfileVersion,
    semantic_versions: &BTreeMap<String, RustVersion>,
    errors: &mut ErrorSink,
) {
    let floor = lockfile.minimum_cargo_version();
    for (toolchain, version) in semantic_versions {
        if *version < floor {
            errors.push(
                format!("toolchains.{toolchain}"),
                format!(
                    "toolchain `{toolchain}` Cargo version `{version}` cannot read Cargo.lock format {}; that format requires Cargo `{floor}` or newer",
                    lockfile.display()
                ),
            );
        }
    }
}

/// Checks each semantic compiler against its complete resolved closure.
///
/// A package can declare an MSRV independently of the primary Zerocopy crate,
/// and its edition imposes a floor even when `rust-version` is absent. Cargo
/// can also compile local and non-workspace normal, dev, build, optional, and
/// target-specific dependencies while executing a selected package's CI
/// commands. Begin with policy scope roots and conservatively traverse both
/// every declared workspace edge and Cargo's complete resolved PackageId
/// graph. This avoids both silent guaranteed failures and a second, incomplete
/// implementation of Cargo's selection rules. Dated nightly pins are absent
/// from `semantic_versions` because a nightly date has no sound ordering
/// against a stable Rust release.
fn validate_scoped_package_compiler_floors(
    policy: &Policy,
    packages: &BTreeMap<PathBuf, CargoPackage>,
    workspace_package_ids: &BTreeMap<PathBuf, PackageId>,
    resolved_packages: &BTreeMap<PackageId, ResolvedPackage>,
    semantic_versions: &BTreeMap<String, RustVersion>,
    errors: &mut ErrorSink,
) {
    let mut package_floors = BTreeMap::new();
    let workspace_ids = workspace_package_ids.values().cloned().collect::<BTreeSet<_>>();
    let policy_ids_by_manifest = policy
        .packages()
        .iter()
        .map(|(id, package)| (package.manifest().as_path(), id.as_str()))
        .collect::<BTreeMap<_, _>>();
    for (manifest, package) in packages {
        let location = policy_ids_by_manifest.get(manifest.as_path()).map_or_else(
            || format!("workspace_packages.{}", package.name),
            |id| format!("packages.{id}"),
        );
        let Some(floor) = package_compiler_floor(
            package.rust_version(),
            &package.editions,
            &format!("{location}.rust-version"),
            &format!("{location}.edition"),
            None,
            errors,
        ) else {
            continue;
        };
        let Some(package_id) = workspace_package_ids.get(manifest) else {
            // Workspace classification and collection own this inconsistency.
            continue;
        };
        package_floors.insert(package_id.clone(), (package.name.clone(), floor));
    }
    for (package_id, package) in resolved_packages {
        if workspace_ids.contains(package_id) {
            // Mutation tests intentionally edit the richer CargoPackage facts.
            // In production both records originate in the same Cargo response,
            // but keeping one authority here prevents a stale duplicate from
            // masking a workspace-manifest error.
            continue;
        }
        let location = format!("resolved_packages.{package_id}");
        let context =
            format!("`{} {}` at `{}`", package.name, package.version, package.manifest.display());
        let Some(floor) = package_compiler_floor(
            package.rust_version.as_deref(),
            &package.editions,
            &format!("{location}.rust-version"),
            &format!("{location}.edition"),
            Some(&context),
            errors,
        ) else {
            continue;
        };
        package_floors
            .insert(package_id.clone(), (format!("{}@{}", package.name, package.version), floor));
    }

    for (toolchain_id, toolchain) in policy.toolchains() {
        let Some(version) = semantic_versions.get(toolchain_id.as_str()).copied() else {
            continue;
        };
        // Initialize every directly selected root before traversing. A package
        // may appear in multiple disjoint profile/target scopes, and workspace
        // dependency cycles are legal (notably through dev dependencies), so
        // the visited set both deduplicates comparisons and bounds traversal.
        let selected_roots = toolchain
            .scopes()
            .iter()
            .flat_map(|scope| scope.packages())
            .filter_map(|id| policy.packages().get(id))
            .map(|package| package.manifest().as_path().to_path_buf())
            .collect::<BTreeSet<_>>();
        // Declaration paths retain local dependency edges which are optional,
        // target-specific, or otherwise absent from this unified resolution.
        // Translating that deliberately broad workspace closure to PackageIds
        // gives Cargo's resolved graph every possible local entry point.
        let selected_workspace = workspace_dependency_closure(&selected_roots, packages);
        let selected_roots = selected_workspace
            .iter()
            .filter_map(|manifest| workspace_package_ids.get(manifest).cloned())
            .collect::<BTreeSet<_>>();
        // Collection requests one locked, offline `--all-features` resolution
        // without a platform filter. Its graph is consequently a conservative
        // superset of any individual CI profile and target. Exact per-cell
        // reachability would require several Cargo resolutions and would make
        // inventory depend on reimplementing the planner's selection rules.
        let selected_packages = resolved_dependency_closure(&selected_roots, resolved_packages);
        for package_id in selected_packages {
            let Some((package, floor)) = package_floors.get(&package_id) else {
                continue;
            };
            validate_toolchain_package_floor(
                format!("toolchains.{}.scopes", toolchain_id.as_str()),
                toolchain_id.as_str(),
                version,
                package,
                *floor,
                errors,
            );
        }
    }
}

fn resolved_dependency_closure(
    roots: &BTreeSet<PackageId>,
    packages: &BTreeMap<PackageId, ResolvedPackage>,
) -> BTreeSet<PackageId> {
    let mut closure = roots.clone();
    let mut pending = roots.iter().cloned().collect::<VecDeque<_>>();
    while let Some(package_id) = pending.pop_front() {
        let Some(package) = packages.get(&package_id) else {
            continue;
        };
        for dependency in &package.dependencies {
            if closure.insert(dependency.clone()) {
                pending.push_back(dependency.clone());
            }
        }
    }
    closure
}

fn workspace_dependency_closure(
    roots: &BTreeSet<PathBuf>,
    packages: &BTreeMap<PathBuf, CargoPackage>,
) -> BTreeSet<PathBuf> {
    let mut closure = roots.clone();
    let mut pending = roots.iter().cloned().collect::<VecDeque<_>>();
    while let Some(manifest) = pending.pop_front() {
        let Some(package) = packages.get(&manifest) else {
            continue;
        };
        for dependency in &package.workspace_dependencies {
            if closure.insert(dependency.clone()) {
                pending.push_back(dependency.clone());
            }
        }
    }
    closure
}

fn toolchain_source_name(source: ToolchainSource) -> &'static str {
    match source {
        ToolchainSource::ManifestRustVersion => "manifest-rust-version",
        ToolchainSource::PinnedStable => "pinned-stable",
        ToolchainSource::PinnedNightly => "pinned-nightly",
        ToolchainSource::BuildRs => "build-rs",
    }
}

fn is_pinned_nightly(value: &str) -> bool {
    let Some(date) = value.strip_prefix("nightly-") else {
        return false;
    };
    if date.len() != 10 {
        return false;
    }
    let bytes = date.as_bytes();
    if bytes.get(4) != Some(&b'-') || bytes.get(7) != Some(&b'-') {
        return false;
    }
    if bytes
        .iter()
        .enumerate()
        .any(|(index, byte)| index != 4 && index != 7 && !byte.is_ascii_digit())
    {
        return false;
    }
    let Ok(year) = date[0..4].parse::<u32>() else {
        return false;
    };
    let Ok(month) = date[5..7].parse::<u32>() else {
        return false;
    };
    let Ok(day) = date[8..10].parse::<u32>() else {
        return false;
    };
    let leap = year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
    let days = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if leap => 29,
        2 => 28,
        _ => return false,
    };
    (1..=days).contains(&day)
}

/// All semantic inventory errors found in one pass.
#[derive(Debug)]
pub struct InventoryErrors(Vec<InventoryError>);

impl InventoryErrors {
    /// Returns individual errors in deterministic reporting order.
    pub fn errors(&self) -> &[InventoryError] {
        &self.0
    }
}

impl fmt::Display for InventoryErrors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "repository inventory has {} error(s):", self.0.len())?;
        for error in &self.0 {
            writeln!(f, "- {}: {}", error.location, error.message)?;
        }
        Ok(())
    }
}

impl Error for InventoryErrors {}

/// One actionable repository inventory error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InventoryError {
    location: String,
    message: String,
}

impl InventoryError {
    /// Returns the policy field or repository path associated with the error.
    pub fn location(&self) -> &str {
        &self.location
    }

    /// Returns a plain-language repair diagnostic.
    pub fn message(&self) -> &str {
        &self.message
    }
}

#[derive(Default)]
struct ErrorSink(Vec<InventoryError>);

impl ErrorSink {
    fn push(&mut self, location: impl Into<String>, message: impl Into<String>) {
        self.0.push(InventoryError { location: location.into(), message: message.into() });
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn finish(mut self) -> InventoryErrors {
        self.0.sort_by(|left, right| {
            (&left.location, &left.message).cmp(&(&right.location, &right.message))
        });
        self.0.dedup();
        InventoryErrors(self.0)
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{BTreeMap, BTreeSet},
        path::{Path, PathBuf},
        process::Command,
    };

    use super::{
        cargo_metadata_command, cargo_package_editions, feature_closure, is_pinned_nightly,
        is_rust_target_name, package_compiler_floor, parse_exact_rust_version, relative_path,
        repository_regular_file_exists, resolved_dependency_closure,
        resolved_workspace_dependencies, validate_build_rs_contract, validate_cargo_lockfile,
        validate_cargo_source_configuration, validate_cargo_target_classification,
        validate_package_source_symlink_containment, validate_policy_targets,
        validate_rust_target_support, validate_toolchain_lockfile_compatibility,
        validate_toolchain_package_floor, validate_toolchain_version_floor,
        validate_workspace_package_classification_from_manifests, workspace_dependency_closure,
        CargoLockfileVersion, CargoPackage, CargoTarget, CollectError, CompilerFloorSource,
        Dependency, ErrorSink, PackageCompilerFloor, ResolvedPackage, RustEdition,
        RustTargetSupport, RustTargetSupportEntry,
    };
    use crate::{metadata::ToolchainMetadata, policy::ToolchainSource};

    fn feature_package(root_members: &[&str]) -> CargoPackage {
        CargoPackage {
            name: "example".to_owned(),
            manifest: "example/Cargo.toml".into(),
            rust_version: Some("1.56.0".to_owned()),
            editions: ["2021".to_owned()].into_iter().collect(),
            features: [(
                "stable".to_owned(),
                root_members.iter().map(|member| (*member).to_owned()).collect(),
            )]
            .into_iter()
            .collect(),
            dependencies: BTreeMap::new(),
            workspace_dependencies: BTreeSet::new(),
            targets: Default::default(),
        }
    }

    fn add_feature(package: &mut CargoPackage, name: &str, members: &[&str]) {
        package
            .features
            .insert(name.to_owned(), members.iter().map(|member| (*member).to_owned()).collect());
    }

    fn add_optional_dependency(package: &mut CargoPackage, name: &str) {
        package.dependencies.insert(name.to_owned(), Dependency { optional: true });
    }

    fn dependency_package(
        name: &str,
        manifest: &str,
        workspace_dependencies: &[&str],
    ) -> CargoPackage {
        CargoPackage {
            name: name.to_owned(),
            manifest: manifest.into(),
            rust_version: None,
            editions: ["2015".to_owned()].into_iter().collect(),
            features: BTreeMap::new(),
            dependencies: BTreeMap::new(),
            workspace_dependencies: workspace_dependencies.iter().map(PathBuf::from).collect(),
            targets: BTreeSet::new(),
        }
    }

    fn assert_feature_closure(package: &CargoPackage, expected: &[&str]) {
        let mut errors = ErrorSink::default();
        let closure = feature_closure(package, ["stable"], "packages.example", &mut errors);
        assert!(errors.is_empty(), "{}", errors.finish());
        assert_eq!(closure, expected.iter().map(|name| (*name).to_owned()).collect());
    }

    #[test]
    fn dep_edge_does_not_enable_an_explicit_same_name_feature() {
        let mut package = feature_package(&["dep:shared"]);
        add_optional_dependency(&mut package, "shared");
        add_feature(&mut package, "shared", &["leaf"]);
        add_feature(&mut package, "leaf", &[]);

        assert_feature_closure(&package, &["stable"]);
    }

    #[test]
    fn strong_dependency_edge_enables_an_explicit_same_name_feature() {
        let mut package = feature_package(&["shared/feature"]);
        add_optional_dependency(&mut package, "shared");
        add_feature(&mut package, "shared", &["leaf"]);
        add_feature(&mut package, "leaf", &[]);

        assert_feature_closure(&package, &["leaf", "shared", "stable"]);
    }

    #[test]
    fn weak_dependency_edge_does_not_enable_an_explicit_same_name_feature() {
        let mut package = feature_package(&["shared?/feature"]);
        add_optional_dependency(&mut package, "shared");
        add_feature(&mut package, "shared", &["leaf"]);
        add_feature(&mut package, "leaf", &[]);

        assert_feature_closure(&package, &["stable"]);
    }

    #[test]
    fn strong_nonoptional_dependency_edge_does_not_enable_a_local_feature() {
        let mut package = feature_package(&["shared/feature"]);
        package.dependencies.insert("shared".to_owned(), Dependency { optional: false });
        add_feature(&mut package, "shared", &["leaf"]);
        add_feature(&mut package, "leaf", &[]);

        assert_feature_closure(&package, &["stable"]);
    }

    #[test]
    fn accepts_two_component_and_dotted_rust_target_names() {
        for target in
            ["avr-none", "wasm32-wasip1", "thumbv8m.base-none-eabi", "x86_64-unknown-linux-gnu"]
        {
            assert!(is_rust_target_name(target), "{target}");
        }
        for target in ["single", "-leading", "trailing-", "empty--component"] {
            assert!(!is_rust_target_name(target), "{target}");
        }
    }

    #[test]
    fn policy_target_modes_match_the_current_execution_host() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let source = std::fs::read_to_string(root.join("ci/zc.toml")).unwrap();

        for (target, expected, replacement) in [
            ("i686-unknown-linux-gnu", "native", "cross"),
            ("x86_64-unknown-linux-gnu", "native", "thumb"),
            ("x86_64-pc-windows-msvc", "cross", "native"),
            ("thumbv6m-none-eabi", "thumb", "cross"),
        ] {
            let expected_declaration = format!("id = {target:?}\nmode = {expected:?}");
            let invalid_declaration = format!("id = {target:?}\nmode = {replacement:?}");
            assert_eq!(source.matches(&expected_declaration).count(), 1, "{target}");
            let policy = crate::policy::Policy::parse(&source.replacen(
                &expected_declaration,
                &invalid_declaration,
                1,
            ))
            .unwrap();
            let mut errors = ErrorSink::default();
            validate_policy_targets(&policy, &mut errors);
            let errors = errors.finish();

            assert!(
                errors.errors().iter().any(|error| {
                    error.location() == format!("targets.{target}.mode")
                        && error.message().contains(&format!("must use `{expected}` mode"))
                }),
                "{target}: {errors}"
            );
        }
    }

    fn live_target_support_inputs() -> (crate::policy::Policy, ToolchainMetadata, RustTargetSupport)
    {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy = crate::policy::Policy::read(root.join("ci/zc.toml")).unwrap();
        let metadata = ToolchainMetadata::read(root.join("zerocopy/Cargo.toml")).unwrap();
        let support = toml::from_str(
            &std::fs::read_to_string(root.join("ci/rust-target-support.toml")).unwrap(),
        )
        .unwrap();
        (policy, metadata, support)
    }

    fn target_support_errors(
        policy: &crate::policy::Policy,
        metadata: &ToolchainMetadata,
        support: &RustTargetSupport,
    ) -> super::InventoryErrors {
        let versions = super::resolved_toolchain_versions(policy, metadata);
        let mut errors = ErrorSink::default();
        validate_rust_target_support(policy, &versions, support, &mut errors);
        errors.finish()
    }

    #[test]
    #[ignore = "requires every exact CI toolchain to be installed"]
    fn target_support_evidence_matches_rustup() {
        let (policy, metadata, support) = live_target_support_inputs();
        let errors = target_support_errors(&policy, &metadata, &support);
        assert!(errors.errors().is_empty(), "{errors}");

        for entry in &support.toolchains {
            let output = Command::new("rustup")
                .args(["target", "list", "--toolchain", &entry.version])
                .env("RUSTUP_AUTO_INSTALL", "0")
                .env_remove("RUSTUP_TOOLCHAIN")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "rustup could not inspect {}:\n{}",
                entry.version,
                String::from_utf8_lossy(&output.stderr)
            );
            let stdout = String::from_utf8(output.stdout).unwrap();
            let available = super::parse_rustup_target_list("rustup target list", &stdout).unwrap();
            for target in &entry.targets {
                assert!(
                    available.contains(target.as_str()),
                    "Rust {} does not distribute target {}",
                    entry.version,
                    target
                );
            }
        }
    }

    #[test]
    fn policy_rejects_a_well_formed_but_unsupported_rust_target() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let source = std::fs::read_to_string(root.join("ci/zc.toml")).unwrap();
        let typo = source.replace("arm-unknown-linux-gnueabi", "arm-unknown-linux-gnueabii");
        assert_ne!(source, typo);
        let policy = crate::policy::Policy::parse(&typo).unwrap();
        let metadata = ToolchainMetadata::read(root.join("zerocopy/Cargo.toml")).unwrap();
        let support: RustTargetSupport = toml::from_str(
            &std::fs::read_to_string(root.join("ci/rust-target-support.toml")).unwrap(),
        )
        .unwrap();
        let errors = target_support_errors(&policy, &metadata, &support);
        assert!(
            errors.errors().iter().any(|error| {
                error.location().starts_with("toolchains.")
                    && error
                        .message()
                        .contains("target `arm-unknown-linux-gnueabii` lacks reviewed support")
            }),
            "{errors}"
        );
    }

    #[test]
    fn target_support_rejects_missing_and_stale_versions() {
        let (policy, metadata, support) = live_target_support_inputs();

        let mut missing = support.clone();
        missing.toolchains.retain(|entry| entry.version != "1.93.1");
        let errors = target_support_errors(&policy, &metadata, &missing);
        assert!(
            errors.errors().iter().any(|error| {
                error.location() == "ci/rust-target-support.toml.toolchains"
                    && error
                        .message()
                        .contains("selected Rust version `1.93.1` has no target-support evidence")
            }),
            "{errors}"
        );

        let mut stale = support;
        stale.toolchains.push(RustTargetSupportEntry {
            version: "999.0.0".to_owned(),
            targets: vec!["x86_64-unknown-linux-gnu".to_owned()],
        });
        let errors = target_support_errors(&policy, &metadata, &stale);
        assert!(
            errors.errors().iter().any(|error| {
                error.location() == "ci/rust-target-support.toml.toolchains.999.0.0"
                    && error.message().contains("does not correspond to a selected Rust version")
            }),
            "{errors}"
        );
    }

    #[test]
    fn target_support_rejects_missing_and_stale_targets() {
        let (policy, metadata, support) = live_target_support_inputs();

        let mut missing = support.clone();
        let stable = missing.toolchains.iter_mut().find(|entry| entry.version == "1.93.1").unwrap();
        stable.targets.retain(|target| target != "aarch64-unknown-linux-gnu");
        let errors = target_support_errors(&policy, &metadata, &missing);
        assert!(
            errors.errors().iter().any(|error| {
                error.message().contains(
                    "target `aarch64-unknown-linux-gnu` lacks reviewed support on toolchain `stable`",
                )
            }),
            "{errors}"
        );

        let mut stale = support;
        let stable = stale.toolchains.iter_mut().find(|entry| entry.version == "1.93.1").unwrap();
        stable.targets.push("wasm32-unknown-unknown".to_owned());
        stable.targets.sort();
        let errors = target_support_errors(&policy, &metadata, &stale);
        assert!(
            errors.errors().iter().any(|error| {
                error.location() == "ci/rust-target-support.toml.toolchains.1.93.1.targets"
                    && error.message().contains(
                        "target `wasm32-unknown-unknown` is not selected on Rust version `1.93.1`",
                    )
            }),
            "{errors}"
        );
    }

    #[test]
    fn target_support_rejects_duplicate_versions_and_noncanonical_target_rows() {
        let (policy, metadata, mut support) = live_target_support_inputs();
        let mut repeated_target = support.clone();
        let stable =
            repeated_target.toolchains.iter_mut().find(|entry| entry.version == "1.93.1").unwrap();
        stable.targets.insert(1, stable.targets[0].clone());
        let errors = target_support_errors(&policy, &metadata, &repeated_target);
        assert!(
            errors.errors().iter().any(|error| error
                .message()
                .contains("target names must be strictly sorted and unique")),
            "{errors}"
        );

        let duplicate =
            support.toolchains.iter_mut().find(|entry| entry.version == "1.93.1").unwrap();
        duplicate.targets.swap(0, 1);
        let duplicate = duplicate.clone();
        support.toolchains.push(duplicate);

        let errors = target_support_errors(&policy, &metadata, &support);
        assert!(
            errors.errors().iter().any(|error| error
                .message()
                .contains("target names must be strictly sorted and unique")),
            "{errors}"
        );
        assert!(
            errors.errors().iter().any(|error| error
                .message()
                .contains("compiler version `1.93.1` is declared more than once")),
            "{errors}"
        );
    }

    #[test]
    fn target_support_rejects_unsorted_toolchain_rows() {
        let (policy, metadata, mut support) = live_target_support_inputs();
        support.toolchains.swap(0, 1);

        let errors = target_support_errors(&policy, &metadata, &support);
        assert!(
            errors.errors().iter().any(|error| {
                error.location() == "ci/rust-target-support.toml.toolchains"
                    && error
                        .message()
                        .contains("compiler versions must be strictly sorted and unique")
            }),
            "{errors}"
        );
    }

    #[test]
    fn target_support_rejects_an_unknown_schema_version() {
        let (policy, metadata, mut support) = live_target_support_inputs();
        support.schema_version += 1;

        let errors = target_support_errors(&policy, &metadata, &support);
        assert!(
            errors.errors().iter().any(|error| {
                error.location() == "ci/rust-target-support.toml.schema_version"
                    && error.message().contains("unsupported schema version")
            }),
            "{errors}"
        );
    }

    #[test]
    fn target_support_applies_the_shared_identifier_contract_before_shape() {
        let (policy, metadata, support) = live_target_support_inputs();
        for (target, diagnostic) in [
            ("UPPERCASE".to_owned(), "not a canonical CI identifier"),
            ("a".repeat(257), "257 bytes; maximum is 256 bytes"),
        ] {
            let mut mutated = support.clone();
            mutated.toolchains[0].targets.push(target);
            mutated.toolchains[0].targets.sort();
            let errors = target_support_errors(&policy, &metadata, &mutated);
            assert!(
                errors.errors().iter().any(|error| error.message().contains(diagnostic)),
                "{errors}"
            );
        }
    }

    #[test]
    fn rustup_target_list_parser_rejects_malformed_or_ambiguous_rows() {
        let parsed = super::parse_rustup_target_list(
            "rustup target list",
            "aarch64-unknown-linux-gnu\nx86_64-unknown-linux-gnu (installed)\n",
        )
        .unwrap();
        assert_eq!(
            parsed,
            ["aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"]
                .into_iter()
                .map(str::to_owned)
                .collect()
        );

        for malformed in [
            "",
            "\n",
            "x86_64-unknown-linux-gnu\nx86_64-unknown-linux-gnu\n",
            "x86_64-unknown-linux-gnu (default)\n",
            "x86_64-unknown-linux-gnu  (installed)\n",
            "UPPERCASE-unknown-linux-gnu\n",
        ] {
            assert!(
                super::parse_rustup_target_list("rustup target list", malformed).is_err(),
                "accepted {malformed:?}"
            );
        }
    }

    fn all_policy_targets(policy: &crate::policy::Policy) -> BTreeSet<String> {
        policy.targets().keys().map(|target| target.as_str().to_owned()).collect()
    }

    fn support_for(
        policy: &crate::policy::Policy,
        metadata: &ToolchainMetadata,
    ) -> RustTargetSupport {
        let versions = super::resolved_toolchain_versions(policy, metadata);
        super::target_support_from_selected(super::selected_targets_by_version(policy, &versions))
    }

    #[test]
    fn target_support_refreshes_an_ordinary_roll() {
        let (policy, pre_metadata, support) = live_target_support_inputs();
        let mut post_metadata = pre_metadata.clone();
        post_metadata.pinned_stable = "1.94.0".to_owned();

        let refreshed = super::refreshed_rust_target_support(
            &policy,
            &post_metadata,
            &support,
            "stable",
            &pre_metadata.pinned_stable,
            &all_policy_targets(&policy),
        )
        .unwrap();

        assert_eq!(refreshed, support_for(&policy, &post_metadata));
        assert!(refreshed.toolchains.iter().any(|entry| entry.version == "1.94.0"));
        assert!(!refreshed.toolchains.iter().any(|entry| entry.version == "1.93.1"));
    }

    #[test]
    fn target_support_refresh_retains_an_old_version_used_elsewhere() {
        let (policy, mut pre_metadata, _) = live_target_support_inputs();
        // A historical build-rs scope already selects 1.89.0. Model stable
        // starting on that same version, then rolling away from it.
        pre_metadata.pinned_stable = "1.89.0".to_owned();
        let support = support_for(&policy, &pre_metadata);
        let mut post_metadata = pre_metadata.clone();
        post_metadata.pinned_stable = "1.94.0".to_owned();

        let refreshed = super::refreshed_rust_target_support(
            &policy,
            &post_metadata,
            &support,
            "stable",
            "1.89.0",
            &all_policy_targets(&policy),
        )
        .unwrap();

        assert_eq!(refreshed, support_for(&policy, &post_metadata));
        assert!(refreshed.toolchains.iter().any(|entry| entry.version == "1.89.0"));
    }

    #[test]
    fn target_support_refresh_unions_an_existing_new_version_collision() {
        let (policy, pre_metadata, support) = live_target_support_inputs();
        let mut post_metadata = pre_metadata.clone();
        // Rolling stable onto this historical build-rs compiler must merge
        // both selections into one version row, not overwrite either one.
        post_metadata.pinned_stable = "1.89.0".to_owned();

        let refreshed = super::refreshed_rust_target_support(
            &policy,
            &post_metadata,
            &support,
            "stable",
            &pre_metadata.pinned_stable,
            &all_policy_targets(&policy),
        )
        .unwrap();

        assert_eq!(refreshed, support_for(&policy, &post_metadata));
        assert_eq!(
            refreshed.toolchains.iter().filter(|entry| entry.version == "1.89.0").count(),
            1
        );
    }

    #[test]
    fn target_support_refresh_rejects_an_unsupported_new_target() {
        let (policy, pre_metadata, support) = live_target_support_inputs();
        let mut post_metadata = pre_metadata.clone();
        post_metadata.pinned_stable = "1.94.0".to_owned();
        let versions = super::resolved_toolchain_versions(&policy, &post_metadata);
        let mut available =
            super::selected_targets_by_version(&policy, &versions)["1.94.0"].clone();
        let missing = available.pop_first().unwrap();

        let error = super::refreshed_rust_target_support(
            &policy,
            &post_metadata,
            &support,
            "stable",
            &pre_metadata.pinned_stable,
            &available,
        )
        .unwrap_err();
        assert!(matches!(
            error,
            super::RefreshTargetSupportError::UnsupportedTargets { version, targets }
                if version == "1.94.0" && targets == [missing]
        ));
    }

    #[test]
    fn target_support_refresh_rejects_unrelated_existing_drift() {
        let (policy, pre_metadata, mut support) = live_target_support_inputs();
        support.toolchains[0].targets.pop();
        let mut post_metadata = pre_metadata.clone();
        post_metadata.pinned_nightly = "nightly-2026-08-26".to_owned();

        let error = super::refreshed_rust_target_support(
            &policy,
            &post_metadata,
            &support,
            "nightly",
            &pre_metadata.pinned_nightly,
            &all_policy_targets(&policy),
        )
        .unwrap_err();
        assert!(matches!(error, super::RefreshTargetSupportError::ExistingDrift(_)));
    }

    #[test]
    fn target_support_catalog_and_roller_use_the_canonical_refresh_contract() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let (policy, pre_metadata, support) = live_target_support_inputs();
        let source = std::fs::read_to_string(root.join("ci/rust-target-support.toml")).unwrap();
        assert_eq!(super::render_rust_target_support(&support), source);

        let workflow = std::fs::read_to_string(
            root.join(".github/workflows/roll-pinned-toolchain-versions.yml"),
        )
        .unwrap();
        for coordinated_line in [
            "./zerocopy/cargo.sh --version \"$VERSION_NAME\"",
            "--bin refresh-rust-target-support --",
            "--old-version \"$OLD_VERSION\"",
        ] {
            assert_eq!(workflow.matches(coordinated_line).count(), 1, "{coordinated_line}");
        }

        // Simulate the post-manifest state consumed by that workflow call.
        let mut post_metadata = pre_metadata.clone();
        post_metadata.pinned_nightly = "nightly-2026-08-26".to_owned();
        let refreshed = super::refreshed_rust_target_support(
            &policy,
            &post_metadata,
            &support,
            "nightly",
            &pre_metadata.pinned_nightly,
            &all_policy_targets(&policy),
        )
        .unwrap();
        assert_eq!(refreshed, support_for(&policy, &post_metadata));
    }

    #[cfg(unix)]
    #[test]
    fn atomic_target_support_replacement_preserves_mode_and_detects_replacement() {
        use std::os::unix::fs::PermissionsExt as _;

        let unique = format!(
            "zc-target-support-atomic-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        );
        let temporary = std::env::temp_dir().join(unique);
        let repository = temporary.join("repository");
        let configured = repository.join("ci/rust-target-support.toml");
        std::fs::create_dir_all(configured.parent().unwrap()).unwrap();
        std::fs::write(&configured, "old\n").unwrap();
        std::fs::set_permissions(&configured, std::fs::Permissions::from_mode(0o640)).unwrap();
        let repository = repository.canonicalize().unwrap();

        let retained =
            crate::repository_file::open(&repository, Path::new("ci/rust-target-support.toml"))
                .unwrap();
        let stale = configured
            .parent()
            .unwrap()
            .join(format!(".rust-target-support.toml.tmp-{}-0", std::process::id()));
        std::fs::write(&stale, "stale\n").unwrap();
        super::atomic_replace(&configured, &retained, &[(&retained, configured.clone())], b"new\n")
            .unwrap();
        assert_eq!(std::fs::read_to_string(&configured).unwrap(), "new\n");
        assert_eq!(std::fs::metadata(&configured).unwrap().permissions().mode() & 0o777, 0o640);
        assert_eq!(std::fs::read_to_string(&stale).unwrap(), "stale\n");
        std::fs::remove_file(stale).unwrap();

        let retained =
            crate::repository_file::open(&repository, Path::new("ci/rust-target-support.toml"))
                .unwrap();
        let policy = repository.join("ci/zc.toml");
        std::fs::write(&policy, "policy\n").unwrap();
        let retained_policy =
            crate::repository_file::open(&repository, Path::new("ci/zc.toml")).unwrap();
        std::fs::rename(&policy, repository.join("ci/displaced-policy.toml")).unwrap();
        std::fs::write(&policy, "replacement policy\n").unwrap();
        assert!(super::atomic_replace(
            &configured,
            &retained,
            &[(&retained_policy, policy), (&retained, configured.clone()),],
            b"must-not-land\n",
        )
        .is_err());
        assert_eq!(std::fs::read_to_string(&configured).unwrap(), "new\n");

        let retained =
            crate::repository_file::open(&repository, Path::new("ci/rust-target-support.toml"))
                .unwrap();
        let displaced = repository.join("ci/displaced.toml");
        std::fs::rename(&configured, &displaced).unwrap();
        std::fs::write(&configured, "replacement\n").unwrap();
        assert!(super::atomic_replace(
            &configured,
            &retained,
            &[(&retained, configured.clone())],
            b"must-not-land\n",
        )
        .is_err());
        assert_eq!(std::fs::read_to_string(&configured).unwrap(), "replacement\n");
        assert_eq!(
            std::fs::read_dir(configured.parent().unwrap())
                .unwrap()
                .filter_map(Result::ok)
                .filter(|entry| entry.file_name().to_string_lossy().contains(".tmp-"))
                .count(),
            0
        );

        std::fs::remove_dir_all(temporary).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn target_support_refresh_rejects_an_in_repository_catalog_redirect() {
        use std::os::unix::fs::symlink;

        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let unique = format!(
            "zc-target-support-redirect-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        );
        let temporary = std::env::temp_dir().join(unique);
        let repository = temporary.join("repository");
        std::fs::create_dir_all(repository.join("ci")).unwrap();
        std::fs::create_dir_all(repository.join("zerocopy")).unwrap();
        std::fs::copy(root.join("ci/zc.toml"), repository.join("ci/zc.toml")).unwrap();
        std::fs::copy(root.join("zerocopy/Cargo.toml"), repository.join("zerocopy/Cargo.toml"))
            .unwrap();
        std::fs::copy(
            root.join("ci/rust-target-support.toml"),
            repository.join("ci/redirected.toml"),
        )
        .unwrap();
        symlink("redirected.toml", repository.join("ci/rust-target-support.toml")).unwrap();

        let error =
            super::refresh_rust_target_support(&repository, "stable", "1.93.1").unwrap_err();
        assert!(matches!(error, super::RefreshTargetSupportError::RedirectedCatalog { .. }));

        std::fs::remove_dir_all(temporary).unwrap();
    }

    #[test]
    fn plain_edge_follows_cargos_implicit_optional_dependency_feature() {
        let mut package = feature_package(&["shared"]);
        add_optional_dependency(&mut package, "shared");
        // This is the feature entry Cargo metadata synthesizes for an optional
        // dependency when no `dep:shared` edge suppresses it.
        add_feature(&mut package, "shared", &["dep:shared"]);

        assert_feature_closure(&package, &["shared", "stable"]);
    }

    #[test]
    fn plain_edge_follows_an_explicit_same_name_local_feature() {
        let mut package = feature_package(&["shared"]);
        add_optional_dependency(&mut package, "shared");
        add_feature(&mut package, "shared", &["leaf"]);
        add_feature(&mut package, "leaf", &[]);

        assert_feature_closure(&package, &["leaf", "shared", "stable"]);
    }

    #[test]
    fn feature_closure_aggregates_bad_edges() {
        let mut package = feature_package(&[]);
        package.features.insert(
            "broken".to_owned(),
            [
                "missing-local".to_owned(),
                "dep:missing-dep".to_owned(),
                "other/feature".to_owned(),
                "weak-other?/feature".to_owned(),
            ]
            .into_iter()
            .collect(),
        );
        let mut errors = ErrorSink::default();
        feature_closure(&package, ["broken"], "packages.example", &mut errors);

        assert_eq!(errors.0.len(), 4);
        assert!(errors.0.iter().all(|error| error.location.contains("broken")));
    }

    fn cargo_target(
        package: &str,
        name: &str,
        kinds: &[&str],
        source: &str,
        flags: (bool, bool, bool),
    ) -> CargoTarget {
        let crate_type = match kinds {
            ["lib"] => "lib",
            ["proc-macro"] => "proc-macro",
            _ => "bin",
        };
        CargoTarget {
            package: package.to_owned(),
            name: name.to_owned(),
            kinds: kinds.iter().map(|kind| (*kind).to_owned()).collect(),
            crate_types: [crate_type.to_owned()].into_iter().collect(),
            source: source.into(),
            required_features: BTreeSet::new(),
            test: flags.0,
            doctest: flags.1,
            doc: flags.2,
        }
    }

    fn target_classification_errors(
        manifest: &str,
        package_name: &str,
        target: CargoTarget,
    ) -> super::InventoryErrors {
        let package = CargoPackage {
            name: package_name.to_owned(),
            manifest: manifest.into(),
            rust_version: None,
            editions: ["2015".to_owned()].into_iter().collect(),
            features: BTreeMap::new(),
            dependencies: BTreeMap::new(),
            workspace_dependencies: BTreeSet::new(),
            targets: [target].into_iter().collect(),
        };
        let packages = [(PathBuf::from(manifest), package)].into_iter().collect();
        let mut errors = ErrorSink::default();
        validate_cargo_target_classification(&packages, &mut errors);
        errors.finish()
    }

    #[test]
    fn accepts_each_current_cargo_target_classification() {
        let cases = [
            (
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "zerocopy",
                    &["lib"],
                    "zerocopy/src/lib.rs",
                    (true, true, true),
                ),
            ),
            (
                "zerocopy/zerocopy-derive/Cargo.toml",
                "zerocopy-derive",
                cargo_target(
                    "zerocopy-derive",
                    "zerocopy_derive",
                    &["proc-macro"],
                    "zerocopy/zerocopy-derive/src/lib.rs",
                    (true, true, true),
                ),
            ),
            (
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "include",
                    &["test"],
                    "zerocopy/tests/include.rs",
                    (true, false, false),
                ),
            ),
            (
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "codegen",
                    &["test"],
                    "zerocopy/tests/codegen.rs",
                    (false, false, false),
                ),
            ),
            (
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "read_from_bytes",
                    &["bench"],
                    "zerocopy/benches/read_from_bytes.rs",
                    (false, false, false),
                ),
            ),
            (
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "build-script-build",
                    &["custom-build"],
                    "zerocopy/build.rs",
                    (false, false, false),
                ),
            ),
            (
                "zerocopy/testutil/Cargo.toml",
                "testutil",
                cargo_target(
                    "testutil",
                    "testutil",
                    &["lib"],
                    "zerocopy/testutil/src/lib.rs",
                    (true, true, true),
                ),
            ),
        ];

        for (manifest, package, target) in cases {
            let errors = target_classification_errors(manifest, package, target);
            assert!(errors.errors().is_empty(), "{errors}");
        }
    }

    #[test]
    fn target_classification_rejects_extra_artifact_crate_types() {
        let mut target = cargo_target(
            "zerocopy",
            "zerocopy",
            &["lib"],
            "zerocopy/src/lib.rs",
            (true, true, true),
        );
        target.crate_types.insert("cdylib".to_owned());

        let errors = target_classification_errors("zerocopy/Cargo.toml", "zerocopy", target);
        assert_eq!(errors.errors().len(), 1, "{errors}");
        assert!(
            errors.errors()[0].message().contains(
                "ordinary library must use Cargo crate type(s) [`lib`]; found [`cdylib`, `lib`]"
            ),
            "{errors}"
        );
    }

    #[test]
    fn target_classification_rejects_single_shape_mutations() {
        let cases = [
            (
                "library name",
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "renamed",
                    &["lib"],
                    "zerocopy/src/lib.rs",
                    (true, true, true),
                ),
                "ordinary library target must be named",
            ),
            (
                "library source",
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "zerocopy",
                    &["lib"],
                    "zerocopy/src/other.rs",
                    (true, true, true),
                ),
                "ordinary library target must use",
            ),
            (
                "library flags",
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "zerocopy",
                    &["lib"],
                    "zerocopy/src/lib.rs",
                    (false, true, true),
                ),
                "ordinary library must set test=true",
            ),
            (
                "integration-test source",
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "include",
                    &["test"],
                    "zerocopy/src/include.rs",
                    (true, false, false),
                ),
                "integration test `include` must use",
            ),
            (
                "integration-test flags",
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "include",
                    &["test"],
                    "zerocopy/tests/include.rs",
                    (true, false, true),
                ),
                "integration test must set test=true",
            ),
            (
                "non-exact codegen exception",
                "zerocopy/zerocopy-derive/Cargo.toml",
                "zerocopy-derive",
                cargo_target(
                    "zerocopy-derive",
                    "codegen",
                    &["test"],
                    "zerocopy/zerocopy-derive/tests/codegen.rs",
                    (false, false, false),
                ),
                "integration test must set test=true",
            ),
            (
                "bench package",
                "zerocopy/zerocopy-derive/Cargo.toml",
                "zerocopy-derive",
                cargo_target(
                    "zerocopy-derive",
                    "measure",
                    &["bench"],
                    "zerocopy/zerocopy-derive/benches/measure.rs",
                    (false, false, false),
                ),
                "only direct `zerocopy` benches are classified",
            ),
            (
                "bench name and source",
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "renamed",
                    &["bench"],
                    "zerocopy/benches/measure.rs",
                    (false, false, false),
                ),
                "codegen bench `renamed` must be the direct file",
            ),
            (
                "bench flags",
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "measure",
                    &["bench"],
                    "zerocopy/benches/measure.rs",
                    (true, false, false),
                ),
                "codegen bench must set test=false",
            ),
            (
                "support test",
                "zerocopy/testutil/Cargo.toml",
                "testutil",
                cargo_target(
                    "testutil",
                    "integration",
                    &["test"],
                    "zerocopy/testutil/tests/integration.rs",
                    (true, false, false),
                ),
                "support package `testutil` may contain only",
            ),
            (
                "support bench",
                "zerocopy/testutil/Cargo.toml",
                "testutil",
                cargo_target(
                    "testutil",
                    "measure",
                    &["bench"],
                    "zerocopy/testutil/benches/measure.rs",
                    (false, false, false),
                ),
                "support package `testutil` may contain only",
            ),
            (
                "support example",
                "zerocopy/testutil/Cargo.toml",
                "testutil",
                cargo_target(
                    "testutil",
                    "demo",
                    &["example"],
                    "zerocopy/testutil/examples/demo.rs",
                    (false, false, false),
                ),
                "support package `testutil` may contain only",
            ),
            (
                "custom-build name",
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "builder",
                    &["custom-build"],
                    "zerocopy/build.rs",
                    (false, false, false),
                ),
                "custom-build target must be named",
            ),
            (
                "custom-build source",
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "build-script-build",
                    &["custom-build"],
                    "zerocopy/src/build.rs",
                    (false, false, false),
                ),
                "custom-build target must use",
            ),
            (
                "custom-build flags",
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "build-script-build",
                    &["custom-build"],
                    "zerocopy/build.rs",
                    (true, false, false),
                ),
                "custom-build target must set test=false",
            ),
            (
                "binary",
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "tool",
                    &["bin"],
                    "zerocopy/src/bin/tool.rs",
                    (true, false, true),
                ),
                "need an explicit CI classification",
            ),
            (
                "example",
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "demo",
                    &["example"],
                    "zerocopy/examples/demo.rs",
                    (false, false, false),
                ),
                "need an explicit CI classification",
            ),
            (
                "unclassified kind combination",
                "zerocopy/Cargo.toml",
                "zerocopy",
                cargo_target(
                    "zerocopy",
                    "zerocopy",
                    &["lib", "rlib"],
                    "zerocopy/src/lib.rs",
                    (true, true, true),
                ),
                "need an explicit CI classification",
            ),
        ];

        for (case, manifest, package, target, expected) in cases {
            let errors = target_classification_errors(manifest, package, target);
            assert_eq!(errors.errors().len(), 1, "{case}: {errors}");
            assert!(errors.errors()[0].message().contains(expected), "{case}: {errors}");
        }
    }

    #[test]
    fn support_package_cannot_also_be_a_policy_package() {
        let manifest = PathBuf::from("zerocopy/testutil/Cargo.toml");
        let package = CargoPackage {
            name: "testutil".to_owned(),
            manifest: manifest.clone(),
            rust_version: None,
            editions: ["2018".to_owned()].into_iter().collect(),
            features: BTreeMap::new(),
            dependencies: BTreeMap::new(),
            workspace_dependencies: BTreeSet::new(),
            targets: BTreeSet::new(),
        };
        let mut errors = ErrorSink::default();
        validate_workspace_package_classification_from_manifests(
            &[manifest.clone()].into_iter().collect(),
            &[(manifest, package)].into_iter().collect(),
            &mut errors,
        );

        let errors = errors.finish();
        assert_eq!(errors.errors().len(), 1, "{errors}");
        assert_eq!(
            errors.errors()[0].message(),
            "support package `testutil` at `zerocopy/testutil/Cargo.toml` must not also appear in CI policy"
        );
    }

    #[test]
    fn cargo_metadata_ignores_ambient_cargo_toolchain_and_target_overrides() {
        let manifest = Path::new("/checkout/zerocopy/Cargo.toml");
        let directory = Path::new("/checkout/zerocopy");
        let command = cargo_metadata_command(manifest, directory, "1.93.1").cargo_command();

        assert_eq!(command.get_program(), "cargo");
        assert_eq!(command.get_current_dir(), Some(directory));
        assert_eq!(
            command.get_args().map(|argument| argument.to_str().unwrap()).collect::<Vec<_>>(),
            [
                "metadata",
                "--format-version",
                "1",
                "--all-features",
                "--manifest-path",
                "/checkout/zerocopy/Cargo.toml",
                "--locked",
                "--offline",
            ]
        );
        assert_eq!(
            command
                .get_envs()
                .map(|(key, value)| (key.to_str().unwrap(), value.unwrap().to_str().unwrap()))
                .collect::<Vec<_>>(),
            [
                ("CARGO_TARGET_DIR", "/checkout/zerocopy/target"),
                ("RUSTUP_AUTO_INSTALL", "0"),
                ("RUSTUP_TOOLCHAIN", "1.93.1"),
            ]
        );
    }

    #[test]
    fn resolved_workspace_dependencies_include_patched_packages() {
        let root = cargo_metadata::PackageId { repr: "root".to_owned() };
        let patched = cargo_metadata::PackageId { repr: "patched".to_owned() };
        let unrelated = cargo_metadata::PackageId { repr: "unrelated".to_owned() };
        let workspace_manifests = [
            (root.clone(), PathBuf::from("root/Cargo.toml")),
            (patched.clone(), PathBuf::from("patched/Cargo.toml")),
            (unrelated.clone(), PathBuf::from("unrelated/Cargo.toml")),
        ]
        .into_iter()
        .collect();
        let resolve: cargo_metadata::Resolve = serde_json::from_value(serde_json::json!({
            "nodes": [
                {
                    "id": "root",
                    "dependencies": ["patched"],
                    "deps": [{ "name": "renamed-patched", "pkg": "patched" }],
                    "features": [],
                },
                { "id": "patched", "dependencies": [], "deps": [], "features": [] },
                { "id": "unrelated", "dependencies": [], "deps": [], "features": [] },
            ],
            "root": "root",
        }))
        .unwrap();

        // A registry dependency redirected through `[patch]` has no
        // declaration `path`. Its resolved PackageId edge is therefore the
        // only reliable link to the workspace member, including after rename.
        let dependencies = resolved_workspace_dependencies(&workspace_manifests, &resolve);
        assert_eq!(
            dependencies[&root],
            [PathBuf::from("patched/Cargo.toml")].into_iter().collect()
        );
        assert!(dependencies[&patched].is_empty());
        assert!(dependencies[&unrelated].is_empty());
    }

    #[test]
    fn workspace_dependency_closure_handles_multiple_hops_and_cycles() {
        let root = PathBuf::from("root/Cargo.toml");
        let middle = PathBuf::from("middle/Cargo.toml");
        let leaf = PathBuf::from("leaf/Cargo.toml");
        let disconnected = PathBuf::from("disconnected/Cargo.toml");
        let packages = [
            (root.clone(), dependency_package("root", "root/Cargo.toml", &["middle/Cargo.toml"])),
            (
                middle.clone(),
                dependency_package("middle", "middle/Cargo.toml", &["leaf/Cargo.toml"]),
            ),
            (leaf.clone(), dependency_package("leaf", "leaf/Cargo.toml", &["root/Cargo.toml"])),
            (
                disconnected.clone(),
                dependency_package("disconnected", "disconnected/Cargo.toml", &[]),
            ),
        ]
        .into_iter()
        .collect();

        let roots = [root.clone()].into_iter().collect();
        assert_eq!(
            workspace_dependency_closure(&roots, &packages),
            [root, middle, leaf].into_iter().collect()
        );
    }

    #[test]
    fn resolved_dependency_closure_handles_multiple_hops_and_cycles() {
        let root = cargo_metadata::PackageId { repr: "root".to_owned() };
        let middle = cargo_metadata::PackageId { repr: "middle".to_owned() };
        let leaf = cargo_metadata::PackageId { repr: "leaf".to_owned() };
        let disconnected = cargo_metadata::PackageId { repr: "disconnected".to_owned() };
        let resolved = [
            (
                root.clone(),
                ResolvedPackage {
                    name: "root".to_owned(),
                    version: "0.0.0".to_owned(),
                    manifest: "root/Cargo.toml".into(),
                    rust_version: None,
                    editions: ["2015".to_owned()].into_iter().collect(),
                    dependencies: [middle.clone()].into_iter().collect(),
                },
            ),
            (
                middle.clone(),
                ResolvedPackage {
                    name: "middle".to_owned(),
                    version: "0.0.0".to_owned(),
                    manifest: "middle/Cargo.toml".into(),
                    rust_version: None,
                    editions: ["2015".to_owned()].into_iter().collect(),
                    dependencies: [leaf.clone()].into_iter().collect(),
                },
            ),
            (
                leaf.clone(),
                ResolvedPackage {
                    name: "leaf".to_owned(),
                    version: "0.0.0".to_owned(),
                    manifest: "leaf/Cargo.toml".into(),
                    rust_version: None,
                    editions: ["2015".to_owned()].into_iter().collect(),
                    dependencies: [root.clone()].into_iter().collect(),
                },
            ),
            (
                disconnected.clone(),
                ResolvedPackage {
                    name: "disconnected".to_owned(),
                    version: "0.0.0".to_owned(),
                    manifest: "disconnected/Cargo.toml".into(),
                    rust_version: None,
                    editions: ["2015".to_owned()].into_iter().collect(),
                    dependencies: BTreeSet::new(),
                },
            ),
        ]
        .into_iter()
        .collect();

        let roots = [root.clone()].into_iter().collect();
        assert_eq!(
            resolved_dependency_closure(&roots, &resolved),
            [root, middle, leaf].into_iter().collect()
        );
    }

    #[cfg(unix)]
    #[test]
    fn cargo_source_symlink_cannot_escape_the_repository() {
        use std::{
            fs,
            os::unix::fs::symlink,
            process,
            sync::atomic::{AtomicU64, Ordering},
        };

        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary = std::env::temp_dir()
            .join(format!("zerocopy-cargo-path-test-{}-{unique}", process::id()));
        let repository = temporary.join("repository");
        let outside = temporary.join("outside.rs");
        fs::create_dir_all(repository.join("src")).unwrap();
        fs::write(&outside, "external\n").unwrap();
        let source = repository.join("src/lib.rs");
        symlink(&outside, &source).unwrap();
        let repository = repository.canonicalize().unwrap();

        let error = relative_path(&repository, &source).unwrap_err();
        assert!(matches!(error, CollectError::PathOutsideRepository { .. }));

        fs::remove_dir_all(temporary).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn cargo_configuration_contains_every_source_path_and_fails_closed() {
        use std::{
            fs,
            os::unix::fs::symlink,
            process,
            sync::atomic::{AtomicU64, Ordering},
        };

        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary = std::env::temp_dir()
            .join(format!("zerocopy-cargo-configuration-test-{}-{unique}", process::id()));
        let repository = temporary.join("repository");
        let cargo_directory = repository.join("zerocopy");
        let cargo_configuration = cargo_directory.join(".cargo/config.toml");
        let internal_vendor = cargo_directory.join("internal-vendor");
        let configured_vendor = cargo_directory.join("vendor");
        let outside = temporary.join("outside");
        let configuration =
            |sources: &str| format!("[env]\n__ZEROCOPY_LOCAL_DEV = \"1\"\n\n{sources}");
        let valid_sources = "[source.crates-io]\nreplace-with = \"vendored\"\n\
                             [source.vendored]\ndirectory = \"vendor\"\n";
        fs::create_dir_all(cargo_configuration.parent().unwrap()).unwrap();
        fs::create_dir_all(&internal_vendor).unwrap();
        fs::create_dir_all(&outside).unwrap();
        fs::write(&cargo_configuration, configuration(valid_sources)).unwrap();
        let repository = repository.canonicalize().unwrap();

        // Cargo resolves `directory = "vendor"` against the parent of
        // `.cargo`, and a symlink which remains in the checkout is safe.
        symlink(&internal_vendor, &configured_vendor).unwrap();
        validate_cargo_source_configuration(&repository, &cargo_directory).unwrap();

        // Cargo merges both supported configuration spellings from every
        // ancestor of its current directory. No repository ancestor may add a
        // second, unmodeled input beside the one audited above. Inspect the
        // directory entry itself so even a broken link fails closed.
        let ancestor_cargo_directory = repository.join(".cargo");
        fs::create_dir_all(&ancestor_cargo_directory).unwrap();
        for name in ["config", "config.toml"] {
            let ancestor_configuration = ancestor_cargo_directory.join(name);
            fs::write(&ancestor_configuration, "[build]\nrustflags = ['-Aall']\n").unwrap();
            let error =
                validate_cargo_source_configuration(&repository, &cargo_directory).unwrap_err();
            assert!(matches!(error, CollectError::UnexpectedCargoConfiguration { .. }));
            fs::remove_file(ancestor_configuration).unwrap();
        }
        let broken_ancestor_configuration = ancestor_cargo_directory.join("config.toml");
        symlink("missing-config", &broken_ancestor_configuration).unwrap();
        let error = validate_cargo_source_configuration(&repository, &cargo_directory).unwrap_err();
        assert!(matches!(error, CollectError::UnexpectedCargoConfiguration { .. }));
        fs::remove_file(broken_ancestor_configuration).unwrap();

        // Cargo exports this table to compilers and build scripts. Only the
        // repository's exact local-development marker is reviewed; absence,
        // a changed value or type, and an additional flag must all fail before
        // Cargo can apply the unmodeled environment.
        for environment in [
            "",
            "[env]\n__ZEROCOPY_LOCAL_DEV = \"0\"\n",
            "[env]\n__ZEROCOPY_LOCAL_DEV = 1\n",
            "[env]\n__ZEROCOPY_LOCAL_DEV = \"1\"\nRUSTFLAGS = \"-Ctarget-cpu=native\"\n",
        ] {
            fs::write(&cargo_configuration, format!("{environment}\n{valid_sources}")).unwrap();
            let error =
                validate_cargo_source_configuration(&repository, &cargo_directory).unwrap_err();
            assert!(matches!(error, CollectError::InvalidCargoEnvironmentConfiguration { .. }));
        }
        fs::write(&cargo_configuration, configuration(valid_sources)).unwrap();

        // A future Git dependency can add another source replacement which is
        // independent of crates.io. Check every declared chain before Cargo,
        // rather than validating only the one used by today's lockfile.
        fs::write(
            &cargo_configuration,
            configuration(
                "[source.crates-io]\nreplace-with = \"vendored\"\n\
                 [source.vendored]\ndirectory = \"vendor\"\n\
                 [source.future-git]\ndirectory = \"../outside\"\n",
            ),
        )
        .unwrap();
        let error = validate_cargo_source_configuration(&repository, &cargo_directory).unwrap_err();
        assert!(matches!(error, CollectError::InvalidCargoSourceConfiguration { .. }));
        fs::write(&cargo_configuration, configuration(valid_sources)).unwrap();

        // The same spelling must fail when its physical destination leaves
        // the checkout, and a regular file cannot stand in for a directory
        // source even though it remains contained.
        fs::remove_file(&configured_vendor).unwrap();
        symlink(&outside, &configured_vendor).unwrap();
        let error = validate_cargo_source_configuration(&repository, &cargo_directory).unwrap_err();
        assert!(matches!(error, CollectError::PathOutsideRepository { .. }));
        fs::remove_file(&configured_vendor).unwrap();
        fs::write(&configured_vendor, "not a directory\n").unwrap();
        let error = validate_cargo_source_configuration(&repository, &cargo_directory).unwrap_err();
        assert!(matches!(error, CollectError::InvalidCargoSourceConfiguration { .. }));
        fs::remove_file(&configured_vendor).unwrap();

        for directory in ["../outside", outside.to_str().unwrap()] {
            fs::write(
                &cargo_configuration,
                configuration(&format!(
                    "[source.crates-io]\nreplace-with = \"vendored\"\n\
                     [source.vendored]\ndirectory = {directory:?}\n"
                )),
            )
            .unwrap();
            let error =
                validate_cargo_source_configuration(&repository, &cargo_directory).unwrap_err();
            assert!(matches!(error, CollectError::InvalidCargoSourceConfiguration { .. }));
        }

        fs::write(
            &cargo_configuration,
            configuration(
                "[source.crates-io]\nreplace-with = \"loop\"\n\
                 [source.loop]\nreplace-with = \"crates-io\"\n",
            ),
        )
        .unwrap();
        let error = validate_cargo_source_configuration(&repository, &cargo_directory).unwrap_err();
        assert!(matches!(error, CollectError::InvalidCargoSourceConfiguration { .. }));

        // Inventory supports exactly the checked-in directory replacement
        // contract. Ignoring a Cargo `registry`, `git`, or `local-registry`
        // key here would let the preflight validate a different source than
        // Cargo actually selects, so deserialization rejects unknown keys.
        fs::write(
            &cargo_configuration,
            configuration("[source.crates-io]\nregistry = \"https://example.invalid/index\"\n"),
        )
        .unwrap();
        let error = validate_cargo_source_configuration(&repository, &cargo_directory).unwrap_err();
        assert!(matches!(error, CollectError::CargoConfiguration { .. }));

        fs::write(
            &cargo_configuration,
            format!("include = \"../../outside-config.toml\"\n\n{}", configuration(valid_sources)),
        )
        .unwrap();
        let error = validate_cargo_source_configuration(&repository, &cargo_directory).unwrap_err();
        assert!(matches!(error, CollectError::CargoConfiguration { .. }));

        // Cargo gives the legacy extensionless name precedence over
        // `config.toml`. Reject any directory entry, including a broken link,
        // before it can make the preflight inspect a different file from Cargo.
        let legacy_configuration = cargo_directory.join(".cargo/config");
        fs::write(&legacy_configuration, "[source.crates-io]\ndirectory = \"vendor\"\n").unwrap();
        let error = validate_cargo_source_configuration(&repository, &cargo_directory).unwrap_err();
        assert!(matches!(error, CollectError::LegacyCargoConfiguration { .. }));
        fs::remove_file(&legacy_configuration).unwrap();
        symlink("missing-config", &legacy_configuration).unwrap();
        let error = validate_cargo_source_configuration(&repository, &cargo_directory).unwrap_err();
        assert!(matches!(error, CollectError::LegacyCargoConfiguration { .. }));
        fs::remove_file(&legacy_configuration).unwrap();

        // Configuration containment is independent from directory-source
        // containment: neither checked-in entry point may be a host-local link.
        let outside_configuration = temporary.join("outside-config.toml");
        fs::write(&outside_configuration, "[source.crates-io]\ndirectory = \"vendor\"\n").unwrap();
        fs::remove_file(&cargo_configuration).unwrap();
        symlink(&outside_configuration, &cargo_configuration).unwrap();
        let error = validate_cargo_source_configuration(&repository, &cargo_directory).unwrap_err();
        assert!(matches!(error, CollectError::PathOutsideRepository { .. }));

        fs::remove_dir_all(temporary).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn cargo_lockfile_format_and_identity_are_validated_before_cargo_runs() {
        use std::{
            fs,
            os::unix::fs::symlink,
            process,
            sync::atomic::{AtomicU64, Ordering},
        };

        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary = std::env::temp_dir()
            .join(format!("zerocopy-cargo-lock-test-{}-{unique}", process::id()));
        let repository = temporary.join("repository");
        let cargo_directory = repository.join("zerocopy");
        let lockfile = cargo_directory.join("Cargo.lock");
        let outside_lockfile = temporary.join("outside-Cargo.lock");
        fs::create_dir_all(&cargo_directory).unwrap();
        fs::write(&lockfile, "version = 4\n").unwrap();
        fs::write(&outside_lockfile, "version = 4\n").unwrap();
        let repository = repository.canonicalize().unwrap();

        let (_, version) = validate_cargo_lockfile(&repository, &cargo_directory).unwrap();
        assert_eq!(version, CargoLockfileVersion::V4);

        // V5 remains unstable and has no reviewed stable reader floor. A
        // future default bump must stop here until that fact is updated.
        fs::write(&lockfile, "version = 5\n").unwrap();
        let error = validate_cargo_lockfile(&repository, &cargo_directory).unwrap_err();
        assert!(matches!(error, CollectError::UnsupportedCargoLockfileVersion { version: 5, .. }));

        // V1 and V2 share the absent marker, so the header alone cannot prove
        // which Cargo floor applies. Reject that ambiguous legacy shape rather
        // than silently making the compatibility audit too weak or too strict.
        fs::write(&lockfile, "[[package]]\nname = \"example\"\nversion = \"0.0.0\"\n").unwrap();
        let error = validate_cargo_lockfile(&repository, &cargo_directory).unwrap_err();
        assert!(matches!(error, CollectError::AmbiguousCargoLockfileVersion { .. }));

        fs::write(&lockfile, "version = 3\n").unwrap();
        let (_, version) = validate_cargo_lockfile(&repository, &cargo_directory).unwrap();
        assert_eq!(version, CargoLockfileVersion::V3);

        fs::remove_file(&lockfile).unwrap();
        symlink(&outside_lockfile, &lockfile).unwrap();
        let error = validate_cargo_lockfile(&repository, &cargo_directory).unwrap_err();
        assert!(matches!(error, CollectError::PathOutsideRepository { .. }));

        fs::remove_file(&lockfile).unwrap();
        fs::create_dir(&lockfile).unwrap();
        let error = validate_cargo_lockfile(&repository, &cargo_directory).unwrap_err();
        assert!(matches!(error, CollectError::InvalidCargoLockfile { .. }));

        fs::remove_dir_all(temporary).unwrap();
    }

    #[test]
    fn repository_file_probe_distinguishes_missing_paths_and_non_files() {
        use std::{
            fs, process,
            sync::atomic::{AtomicU64, Ordering},
        };

        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary = std::env::temp_dir()
            .join(format!("zerocopy-repository-file-kind-test-{}-{unique}", process::id()));
        let repository = temporary.join("repository");
        let directory = repository.join("baseline-directory");
        fs::create_dir_all(&directory).unwrap();
        let repository = repository.canonicalize().unwrap();

        // A missing baseline remains a semantic validation error, represented
        // by `false`, so it can be reported with other independent mistakes.
        assert!(
            !repository_regular_file_exists(&repository, &repository.join("missing.tsv")).unwrap()
        );
        // A directory is present in the file system, but cannot satisfy a
        // baseline contract which will later be read as a regular file.
        assert!(!repository_regular_file_exists(&repository, &directory).unwrap());

        fs::remove_dir_all(temporary).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn configured_file_symlinks_must_remain_inside_the_repository() {
        use std::{
            fs,
            os::unix::fs::symlink,
            process,
            sync::atomic::{AtomicU64, Ordering},
        };

        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary = std::env::temp_dir()
            .join(format!("zerocopy-configured-file-path-test-{}-{unique}", process::id()));
        let repository = temporary.join("repository");
        let baselines = repository.join("baselines");
        let outside_directory = temporary.join("outside");
        fs::create_dir_all(&baselines).unwrap();
        fs::create_dir_all(&outside_directory).unwrap();

        let inside = baselines.join("inside.tsv");
        let outside = outside_directory.join("outside.tsv");
        fs::write(&inside, "inside\n").unwrap();
        fs::write(&outside, "outside\n").unwrap();
        let inside_link = baselines.join("inside-link.tsv");
        let outside_link = baselines.join("outside-link.tsv");
        let outside_ancestor = baselines.join("outside-directory");
        symlink(&inside, &inside_link).unwrap();
        symlink(&outside, &outside_link).unwrap();
        symlink(&outside_directory, &outside_ancestor).unwrap();
        let repository = repository.canonicalize().unwrap();

        // Symbolic links are not forbidden categorically. A link to another
        // checked-in file remains a repository-owned input.
        assert!(repository_regular_file_exists(&repository, &inside_link).unwrap());

        // Both a final-component link and a link in an ancestor must cross the
        // same physical containment boundary before either can count as a
        // present baseline.
        for escaped in [outside_link, outside_ancestor.join("outside.tsv")] {
            let error = repository_regular_file_exists(&repository, &escaped).unwrap_err();
            assert!(matches!(error, CollectError::PathOutsideRepository { .. }));
        }

        fs::remove_dir_all(temporary).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn package_source_trees_reject_nested_escaping_symlinks() {
        use std::{
            fs,
            os::unix::fs::symlink,
            process,
            sync::atomic::{AtomicU64, Ordering},
        };

        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary = std::env::temp_dir()
            .join(format!("zerocopy-package-source-tree-test-{}-{unique}", process::id()));
        let repository = temporary.join("repository");
        let package = repository.join("package");
        let source = package.join("src");
        let shared = repository.join("shared-source");
        let cargo_target = package.join("target");
        let outside = temporary.join("outside.rs");
        fs::create_dir_all(&source).unwrap();
        fs::create_dir_all(&shared).unwrap();
        fs::create_dir_all(&cargo_target).unwrap();
        fs::write(shared.join("inside.rs"), "inside\n").unwrap();
        fs::write(&outside, "outside\n").unwrap();
        symlink(&shared, source.join("shared")).unwrap();

        // Generated output is not package source. An escaping symlink left by
        // a local compiler below Cargo's exact target directory must not make
        // an otherwise clean checkout fail its repository-source audit.
        symlink(&outside, cargo_target.join("generated-link.rs")).unwrap();
        let repository = repository.canonicalize().unwrap();
        let package_directories = BTreeSet::from([package.clone()]);
        validate_package_source_symlink_containment(
            &repository,
            &package_directories,
            &cargo_target,
        )
        .unwrap();

        // Reaching the generated directory through a package-source alias
        // cannot inherit the ordinary `target` entry's exemption. Reject both
        // the direct spelling and an alias of its already-visited package
        // ancestor; canonical-directory deduplication would otherwise hide the
        // generated escaping link in either case.
        for (name, destination) in
            [("target-alias", cargo_target.as_path()), ("package-alias", package.as_path())]
        {
            let alias = source.join(name);
            symlink(destination, &alias).unwrap();
            let error = validate_package_source_symlink_containment(
                &repository,
                &package_directories,
                &cargo_target,
            )
            .unwrap_err();
            assert!(matches!(error, CollectError::CargoTargetSourceAlias { .. }));
            fs::remove_file(alias).unwrap();
        }

        // Follow an internal directory link rather than approving only its
        // first safe hop. Rustc can discover the nested file as a module or
        // macro input even though Cargo metadata reports neither path.
        symlink(&outside, shared.join("escape.rs")).unwrap();
        let error = validate_package_source_symlink_containment(
            &repository,
            &package_directories,
            &cargo_target,
        )
        .unwrap_err();
        assert!(matches!(error, CollectError::PathOutsideRepository { .. }));

        fs::remove_dir_all(temporary).unwrap();
    }

    #[test]
    fn validates_exact_stable_and_nightly_versions() {
        assert!(parse_exact_rust_version("1.93.1").is_some());
        assert!(parse_exact_rust_version("1.093.1").is_none());
        assert!(parse_exact_rust_version("1.93").is_none());
        assert!(parse_exact_rust_version("1.93.1-beta").is_none());

        assert!(is_pinned_nightly("nightly-2024-02-29"));
        assert!(!is_pinned_nightly("nightly-2023-02-29"));
        assert!(!is_pinned_nightly("nightly-2026-13-01"));
        assert!(!is_pinned_nightly("2026-01-25"));
    }

    #[test]
    fn cargo_metadata_normalizes_two_component_rust_versions() {
        let package: cargo_metadata::Package = serde_json::from_value(serde_json::json!({
            "name": "example",
            "version": "0.0.0",
            "id": "path+file:///example#0.0.0",
            "source": null,
            "dependencies": [],
            "targets": [],
            "features": {},
            "manifest_path": "/example/Cargo.toml",
            "rust_version": "1.56",
        }))
        .unwrap();

        // Cargo accepts a two-component manifest declaration, while
        // cargo_metadata exposes it as a semantic Version. Collection stores
        // that normalized display form, so the control plane can retain its
        // deliberately strict exact-version grammar for all stored facts.
        let normalized = package.rust_version.unwrap().to_string();
        assert_eq!(normalized, "1.56.0");
        assert!(parse_exact_rust_version(&normalized).is_some());
        assert!(parse_exact_rust_version("1.56").is_none());
    }

    #[test]
    fn semantic_toolchain_versions_must_not_predate_the_msrv() {
        let floor = PackageCompilerFloor {
            version: parse_exact_rust_version("1.60.0").unwrap(),
            source: CompilerFloorSource::DeclaredRustVersion,
        };
        let mut errors = ErrorSink::default();

        validate_toolchain_package_floor(
            "toolchains.older",
            "older",
            parse_exact_rust_version("1.59.9").unwrap(),
            "zerocopy",
            floor,
            &mut errors,
        );
        validate_toolchain_package_floor(
            "toolchains.equal",
            "equal",
            parse_exact_rust_version("1.60.0").unwrap(),
            "zerocopy",
            floor,
            &mut errors,
        );
        validate_toolchain_package_floor(
            "toolchains.newer",
            "newer",
            parse_exact_rust_version("1.61.0").unwrap(),
            "zerocopy",
            floor,
            &mut errors,
        );

        let errors = errors.finish();
        assert_eq!(errors.errors().len(), 1, "{errors}");
        assert_eq!(errors.errors()[0].location(), "toolchains.older");
        assert_eq!(
            errors.errors()[0].message(),
            "toolchain `older` Rust version `1.59.9` is older than package `zerocopy` MSRV `1.60.0`"
        );
    }

    #[test]
    fn package_compiler_floors_cover_every_known_edition() {
        let cases = [
            ("2015", "1.0.0", RustEdition::E2015),
            ("2018", "1.31.0", RustEdition::E2018),
            ("2021", "1.56.0", RustEdition::E2021),
            ("2024", "1.85.0", RustEdition::E2024),
        ];
        for (edition, expected, source) in cases {
            let editions = [edition.to_owned()].into_iter().collect();
            let mut errors = ErrorSink::default();
            let floor = package_compiler_floor(
                None,
                &editions,
                "packages.example.rust-version",
                "packages.example.edition",
                None,
                &mut errors,
            )
            .unwrap();
            assert!(errors.is_empty(), "edition {edition} unexpectedly failed");
            assert_eq!(floor.version.to_string(), expected);
            assert_eq!(floor.source, CompilerFloorSource::Edition(source));
        }
    }

    #[test]
    fn target_edition_override_raises_an_implicit_package_floor() {
        let package: cargo_metadata::Package = serde_json::from_value(serde_json::json!({
            "name": "example",
            "version": "0.0.0",
            "id": "path+file:///example#0.0.0",
            "source": null,
            "dependencies": [],
            "targets": [{
                "name": "example",
                "kind": ["lib"],
                "crate_types": ["lib"],
                "required-features": [],
                "src_path": "/example/src/lib.rs",
                "edition": "2024",
                "doctest": true,
                "test": true,
                "doc": true,
            }],
            "features": {},
            "manifest_path": "/example/Cargo.toml",
            "edition": "2018",
            "rust_version": null,
        }))
        .unwrap();
        let editions = cargo_package_editions(&package);
        assert_eq!(editions, ["2018".to_owned(), "2024".to_owned()].into_iter().collect());

        let mut errors = ErrorSink::default();
        let floor = package_compiler_floor(
            None,
            &editions,
            "packages.example.rust-version",
            "packages.example.edition",
            None,
            &mut errors,
        )
        .unwrap();
        assert!(errors.is_empty());
        assert_eq!(floor.version.to_string(), "1.85.0");
        assert_eq!(floor.source, CompilerFloorSource::Edition(RustEdition::E2024));

        let mut errors = ErrorSink::default();
        validate_toolchain_package_floor(
            "toolchains.msrv",
            "msrv",
            parse_exact_rust_version("1.56.0").unwrap(),
            "example",
            floor,
            &mut errors,
        );
        validate_toolchain_package_floor(
            "toolchains.edition-2024",
            "edition-2024",
            parse_exact_rust_version("1.85.0").unwrap(),
            "example",
            floor,
            &mut errors,
        );
        let errors = errors.finish();
        assert_eq!(errors.errors().len(), 1, "{errors}");
        assert_eq!(errors.errors()[0].location(), "toolchains.msrv");
        assert!(errors.errors()[0].message().contains("Rust 2024 edition floor `1.85.0`"));
    }

    #[test]
    fn package_compiler_floor_fails_closed_on_a_future_edition() {
        let editions = ["2027".to_owned()].into_iter().collect();
        let mut errors = ErrorSink::default();
        let floor = package_compiler_floor(
            None,
            &editions,
            "packages.example.rust-version",
            "packages.example.edition",
            None,
            &mut errors,
        );

        assert!(floor.is_none());
        let errors = errors.finish();
        assert_eq!(errors.errors().len(), 1, "{errors}");
        assert_eq!(errors.errors()[0].location(), "packages.example.edition");
        assert!(errors.errors()[0].message().contains("unsupported Rust edition `2027`"));
    }

    #[test]
    fn lockfile_formats_constrain_each_semantic_cargo_version() {
        let versions = [
            ("pre-v3".to_owned(), parse_exact_rust_version("1.46.0").unwrap()),
            ("msrv".to_owned(), parse_exact_rust_version("1.56.0").unwrap()),
        ]
        .into_iter()
        .collect();
        let mut errors = ErrorSink::default();
        validate_toolchain_lockfile_compatibility(CargoLockfileVersion::V3, &versions, &mut errors);
        let errors = errors.finish();
        assert_eq!(errors.errors().len(), 1, "{errors}");
        assert_eq!(errors.errors()[0].location(), "toolchains.pre-v3");

        let versions = [
            ("msrv".to_owned(), parse_exact_rust_version("1.56.0").unwrap()),
            ("v4".to_owned(), parse_exact_rust_version("1.78.0").unwrap()),
        ]
        .into_iter()
        .collect();
        let mut errors = ErrorSink::default();
        validate_toolchain_lockfile_compatibility(CargoLockfileVersion::V4, &versions, &mut errors);
        let errors = errors.finish();
        assert_eq!(errors.errors().len(), 1, "{errors}");
        assert_eq!(errors.errors()[0].location(), "toolchains.msrv");
        assert!(errors.errors()[0].message().contains("format V4"));
        assert!(errors.errors()[0].message().contains("Cargo `1.78.0` or newer"));
    }

    #[test]
    fn accepts_the_build_rs_text_contract() {
        let source = include_str!("../testdata/inventory-build-rs-valid.toml");
        let expected = [
            ("no-zerocopy-alpha-1-60-0".to_owned(), "1.60.0".to_owned()),
            ("no-zerocopy-beta-1-81-0".to_owned(), "1.81.0".to_owned()),
        ]
        .into_iter()
        .collect();
        let mut errors = ErrorSink::default();
        let parsed = validate_build_rs_contract(source, &expected, &mut errors);

        assert!(errors.is_empty());
        assert_eq!(parsed.len(), 2);
    }

    #[test]
    fn build_rs_contract_reports_independent_mutations() {
        let source = include_str!("../testdata/inventory-build-rs-invalid.toml");
        let expected = [
            ("no-zerocopy-alpha-1-60-0".to_owned(), "1.60.0".to_owned()),
            ("no-zerocopy-missing-1-70-0".to_owned(), "1.70.0".to_owned()),
        ]
        .into_iter()
        .collect();
        let mut errors = ErrorSink::default();
        validate_build_rs_contract(source, &expected, &mut errors);
        let errors = errors.finish();

        assert!(errors.errors().len() >= 4, "{errors}");
        assert!(errors.to_string().contains("not an exact"));
        assert!(errors.to_string().contains("was not parsed"));
    }

    #[test]
    fn live_repository_collects_and_validates() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy = crate::policy::Policy::read(root.join("ci/zc.toml")).unwrap();
        let inventory = super::RepositoryInventory::audit(&root, &policy).unwrap();

        let zerocopy = &inventory.policy_packages()["zerocopy"];
        assert_eq!(
            zerocopy.nightly_features(),
            &["float-nightly", "simd-nightly"].into_iter().map(str::to_owned).collect()
        );
        assert!(zerocopy.stable_features().contains("zerocopy-derive"));
        assert!(inventory.policy_packages().contains_key("zerocopy-derive"));
        assert!(inventory.workspace_packages().len() >= 3);
        assert!(inventory
            .cargo_targets()
            .iter()
            .any(|target| target.name() == "ui" && target.package() == "zerocopy"));
    }

    #[test]
    fn non_nightly_all_features_requires_an_empty_nightly_complement() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy_path = root.join("ci/zc.toml");
        let policy_source = std::fs::read_to_string(&policy_path).unwrap();
        let stable_scope = "[[toolchains]]\n\
                            id = \"stable\"\n\
                            source = \"pinned-stable\"\n\n\
                            [[toolchains.scopes]]\n\
                            packages = [\"zerocopy\"]\n\
                            profiles = [\"default\"]\n\
                            target_set = \"without-wasm\"";
        let invalid_scope =
            stable_scope.replace("profiles = [\"default\"]", "profiles = [\"default\", \"all\"]");
        assert_eq!(policy_source.matches(stable_scope).count(), 1);
        let policy =
            crate::policy::Policy::parse(&policy_source.replacen(stable_scope, &invalid_scope, 1))
                .unwrap();
        let mut collected = super::CollectedRepository::collect(&root, &policy).unwrap();

        let errors = collected.validate(&policy).unwrap_err();
        assert!(
            errors.errors().iter().any(|error| {
                error.location() == "toolchains.stable.scopes[0].profiles"
                    && error.message().contains(
                        "non-nightly toolchain selects all-features profile `all` for package `zerocopy`",
                    )
            }),
            "{errors}"
        );

        // The restriction is semantic, not a hard-coded profile/toolchain
        // pairing: a package whose full graph is stable may use the same `all`
        // profile on stable. Model that state by removing exactly today's two
        // nightly-only leaves from the collected Cargo feature graph.
        let zerocopy = collected.packages.get_mut(Path::new("zerocopy/Cargo.toml")).unwrap();
        assert!(zerocopy.features.remove("float-nightly").is_some());
        assert!(zerocopy.features.remove("simd-nightly").is_some());
        collected.validate(&policy).unwrap();
    }

    #[test]
    fn repository_validation_rejects_non_nightly_toolchains_below_the_msrv() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy = crate::policy::Policy::read(root.join("ci/zc.toml")).unwrap();
        let mut collected = super::CollectedRepository::collect(&root, &policy).unwrap();

        // This mutation models one incomplete MSRV bump. Cargo metadata and the
        // directly parsed manifest metadata agree on the new floor, but an old
        // pinned stable compiler and one retained build-rs boundary cannot
        // compile the package anymore. Validation must make both stale inputs
        // visible before planning expands them into jobs.
        const RAISED_MSRV: &str = "1.58.0";
        collected.packages.get_mut(Path::new("zerocopy/Cargo.toml")).unwrap().rust_version =
            Some(RAISED_MSRV.to_owned());
        collected.toolchain_metadata.rust_version = RAISED_MSRV.to_owned();
        collected.toolchain_metadata.pinned_stable = "1.55.0".to_owned();

        let diagnostic = collected.validate(&policy).unwrap_err().to_string();
        assert!(
            diagnostic.contains(
                "toolchains.stable.scopes: toolchain `stable` Rust version `1.55.0` is older than package `zerocopy` MSRV `1.58.0`"
            ),
            "{diagnostic}"
        );
        assert!(
            diagnostic.contains(
                "toolchain `no-zerocopy-panic-in-const-and-vec-try-reserve-1-57-0` Rust version `1.57.0` is older than package `zerocopy` MSRV `1.58.0`"
            ),
            "{diagnostic}"
        );
    }

    #[test]
    fn repository_validation_rejects_cargo_versions_below_the_lockfile_floor() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy = crate::policy::Policy::read(root.join("ci/zc.toml")).unwrap();
        let mut collected = super::CollectedRepository::collect(&root, &policy).unwrap();

        // The checked-in V3 lockfile remains readable by today's Rust 1.56
        // MSRV toolchain. Model only a future V4 format bump: Cargo 1.56 must
        // then fail inventory, while Cargo 1.78 is exactly new enough.
        collected.cargo_lockfile_version = CargoLockfileVersion::V4;
        let errors = collected.validate(&policy).unwrap_err();
        let diagnostic = errors.to_string();
        assert!(
            errors.errors().iter().any(|error| {
                error.location() == "toolchains.msrv"
                    && error.message().contains("Cargo version `1.56.0`")
                    && error.message().contains("format V4")
            }),
            "{diagnostic}"
        );
        assert!(
            !errors.errors().iter().any(|error| {
                error.location() == "toolchains.no-zerocopy-diagnostic-on-unimplemented-1-78-0"
                    && error.message().contains("Cargo.lock")
            }),
            "{diagnostic}"
        );
    }

    #[test]
    fn repository_validation_uses_an_edition_floor_without_rust_version() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy = crate::policy::Policy::read(root.join("ci/zc.toml")).unwrap();
        let mut collected = super::CollectedRepository::collect(&root, &policy).unwrap();

        // Zerocopy Derive intentionally has no independent `rust-version`.
        // A future edition bump still raises its compiler floor and therefore
        // must invalidate every older semantic toolchain which can reach it.
        let derive =
            collected.packages.get_mut(Path::new("zerocopy/zerocopy-derive/Cargo.toml")).unwrap();
        assert!(derive.rust_version.is_none());
        derive.editions = ["2024".to_owned()].into_iter().collect();

        let errors = collected.validate(&policy).unwrap_err();
        let diagnostic = errors.to_string();
        assert!(
            errors.errors().iter().any(|error| {
                error.location() == "toolchains.msrv.scopes"
                    && error.message().contains("package `zerocopy-derive`")
                    && error.message().contains("Rust 2024 edition floor `1.85.0`")
            }),
            "{diagnostic}"
        );
        assert!(
            !errors.errors().iter().any(|error| {
                error.location() == "toolchains.no-zerocopy-aarch64-simd-be-1-87-0.scopes"
                    && error.message().contains("zerocopy-derive")
            }),
            "{diagnostic}"
        );
    }

    #[test]
    fn repository_validation_uses_transitive_workspace_dependency_msrvs() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy = crate::policy::Policy::read(root.join("ci/zc.toml")).unwrap();
        let mut collected = super::CollectedRepository::collect(&root, &policy).unwrap();

        // Zerocopy Derive currently has no independent MSRV. Model a future
        // declaration above every configured compiler. Stable and MSRV select
        // it directly; each build-rs toolchain selects Zerocopy, whose optional
        // derive dependency can also be compiled by its feature profiles.
        collected
            .packages
            .get_mut(Path::new("zerocopy/zerocopy-derive/Cargo.toml"))
            .unwrap()
            .rust_version = Some("999.0.0".to_owned());

        let errors = collected.validate(&policy).unwrap_err();
        let diagnostic = errors.to_string();
        let semantic_toolchains = policy
            .toolchains()
            .iter()
            .filter(|(_, toolchain)| toolchain.source() != ToolchainSource::PinnedNightly)
            .map(|(id, _)| id.as_str())
            .collect::<BTreeSet<_>>();
        assert_eq!(errors.errors().len(), semantic_toolchains.len(), "{diagnostic}");
        for toolchain in semantic_toolchains {
            assert!(
                errors.errors().iter().any(|error| {
                    error.location() == format!("toolchains.{toolchain}.scopes")
                        && error.message().contains("package `zerocopy-derive` MSRV `999.0.0`")
                }),
                "{diagnostic}"
            );
        }
        assert!(!diagnostic.contains("toolchain `nightly`"), "{diagnostic}");
    }

    #[test]
    fn repository_validation_uses_non_workspace_dependency_msrvs() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy = crate::policy::Policy::read(root.join("ci/zc.toml")).unwrap();
        let mut collected = super::CollectedRepository::collect(&root, &policy).unwrap();
        let workspace_ids =
            collected.workspace_package_ids.values().cloned().collect::<BTreeSet<_>>();

        // `rustversion` is a registry dev dependency, not an independently
        // classified workspace package. Raising its declared floor models an
        // upstream release which remains lockfile-valid but can no longer be
        // compiled by any of the repository's semantic compatibility jobs.
        let dependency = collected
            .resolved_packages
            .iter_mut()
            .find(|(id, package)| package.name == "rustversion" && !workspace_ids.contains(*id))
            .map(|(_, package)| package)
            .expect("the complete Cargo graph contains the rustversion dev dependency");
        let dependency_label = format!("{}@{}", dependency.name, dependency.version);
        dependency.rust_version = Some("999.0.0".to_owned());

        let errors = collected.validate(&policy).unwrap_err();
        let diagnostic = errors.to_string();
        let semantic_toolchains = policy
            .toolchains()
            .iter()
            .filter(|(_, toolchain)| toolchain.source() != ToolchainSource::PinnedNightly)
            .map(|(id, _)| id.as_str())
            .collect::<BTreeSet<_>>();
        assert_eq!(errors.errors().len(), semantic_toolchains.len(), "{diagnostic}");
        for toolchain in semantic_toolchains {
            assert!(
                errors.errors().iter().any(|error| {
                    error.location() == format!("toolchains.{toolchain}.scopes")
                        && error
                            .message()
                            .contains(&format!("package `{dependency_label}` MSRV `999.0.0`"))
                }),
                "{diagnostic}"
            );
        }
        assert!(!diagnostic.contains("toolchain `nightly`"), "{diagnostic}");
    }

    #[test]
    fn repository_validation_uses_non_workspace_dependency_editions() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy = crate::policy::Policy::read(root.join("ci/zc.toml")).unwrap();
        let mut collected = super::CollectedRepository::collect(&root, &policy).unwrap();
        let workspace_ids =
            collected.workspace_package_ids.values().cloned().collect::<BTreeSet<_>>();

        let dependency = collected
            .resolved_packages
            .iter_mut()
            .find(|(id, package)| package.name == "rustversion" && !workspace_ids.contains(*id))
            .map(|(_, package)| package)
            .expect("the complete Cargo graph contains the rustversion dev dependency");
        let dependency_label = format!("{}@{}", dependency.name, dependency.version);
        dependency.rust_version = None;
        dependency.editions = ["2024".to_owned()].into_iter().collect();

        let errors = collected.validate(&policy).unwrap_err();
        let diagnostic = errors.to_string();
        assert!(
            errors.errors().iter().any(|error| {
                error.location() == "toolchains.msrv.scopes"
                    && error.message().contains(&format!("package `{dependency_label}`"))
                    && error.message().contains("Rust 2024 edition floor `1.85.0`")
            }),
            "{diagnostic}"
        );
        assert!(!diagnostic.contains("toolchain `nightly`"), "{diagnostic}");
    }

    #[test]
    fn repository_validation_includes_test_support_dependency_msrvs() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy = crate::policy::Policy::read(root.join("ci/zc.toml")).unwrap();
        let mut collected = super::CollectedRepository::collect(&root, &policy).unwrap();

        // `testutil` is deliberately absent from CI policy because it is not
        // an independent matrix subject. It is nevertheless a dev dependency
        // compiled by test-bearing cells for both policy packages, so a future
        // explicit floor must constrain every semantic compiler which can
        // reach it.
        collected
            .packages
            .get_mut(Path::new("zerocopy/testutil/Cargo.toml"))
            .unwrap()
            .rust_version = Some("999.0.0".to_owned());

        let errors = collected.validate(&policy).unwrap_err();
        let diagnostic = errors.to_string();
        let semantic_toolchain_count = policy
            .toolchains()
            .values()
            .filter(|toolchain| toolchain.source() != ToolchainSource::PinnedNightly)
            .count();
        assert_eq!(errors.errors().len(), semantic_toolchain_count, "{diagnostic}");
        assert!(
            errors.errors().iter().all(|error| {
                error.location().starts_with("toolchains.")
                    && error.message().contains("package `testutil` MSRV `999.0.0`")
            }),
            "{diagnostic}"
        );
        assert!(!diagnostic.contains("toolchain `nightly`"), "{diagnostic}");
    }

    #[test]
    fn validation_aggregates_independent_repository_mutations() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy = crate::policy::Policy::read(root.join("ci/zc.toml")).unwrap();
        let mut collected = super::CollectedRepository::collect(&root, &policy).unwrap();

        let zerocopy = collected.packages.get_mut(Path::new("zerocopy/Cargo.toml")).unwrap();
        zerocopy.features.insert("default".to_owned(), BTreeSet::new());
        collected.toolchain_metadata.pinned_stable = "moving-stable".to_owned();
        let baseline = policy.baselines().manifest().as_path().to_path_buf();
        collected.existing_files.insert(baseline, false);

        let errors = collected.validate(&policy).unwrap_err();
        let diagnostic = errors.to_string();
        assert!(errors.errors().len() >= 3, "{diagnostic}");
        assert!(diagnostic.contains("no-default"));
        assert!(diagnostic.contains("moving-stable"));
        assert!(diagnostic.contains("does not exist"));
    }
}
