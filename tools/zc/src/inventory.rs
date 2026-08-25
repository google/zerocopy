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
//! There are three deliberately independent cross-file contracts here:
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
//!
//! The frozen files named by `Policy::baselines` remain independent evidence
//! of the old workflow's behavior. Inventory checks that every file exists,
//! but does not generate or bless one. Likewise, permissions, secrets,
//! runners, action references, and publication remain hand-reviewed workflow
//! concerns; none belongs in this unprivileged repository inventory.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    error::Error,
    fmt, fs, io,
    path::{Component, Path, PathBuf},
};

use cargo_metadata::{CargoOpt, MetadataCommand, PackageId, Resolve, TargetKind};
use thiserror::Error;

use crate::{
    metadata::{ReadMetadataError, ToolchainMetadata},
    policy::{FeatureProfile, Policy, TargetMode, ToolchainSource},
};

const PRIMARY_PACKAGE_ID: &str = "zerocopy";

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
    // Retain Cargo's structured package metadata so validation can select the
    // docs.rs command contract from the exact policy-owned Zerocopy package.
    // Raw metadata is deliberately not exposed from the checked inventory.
    metadata: serde_json::Value,
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
    zerocopy_docs_rs_rustdoc_args: Vec<String>,
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

    /// Returns the ordered docs.rs Rustdoc arguments owned by Zerocopy.
    ///
    /// These are read from the canonical package selected by
    /// `ci/zc.toml`, not from a package-name search or another workspace
    /// member which happens to declare similar metadata. Inventory validation
    /// has already rejected missing, empty, non-string, control-bearing, or
    /// whitespace-bearing arguments.
    pub fn zerocopy_docs_rs_rustdoc_args(&self) -> &[String] {
        &self.zerocopy_docs_rs_rustdoc_args
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
    dependencies: BTreeSet<PackageId>,
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
        let configured_primary_manifest = repository_root.join(primary.manifest().as_path());
        // Policy paths are syntactically repository-relative, but a checked-in
        // symlink can still escape the checkout. Resolve the primary manifest
        // before giving it to Cargo, then use that same checked path for every
        // later read.
        let primary_manifest =
            resolve_repository_path(&repository_root, &configured_primary_manifest)?;
        let cargo_directory =
            primary_manifest.parent().expect("a repository-relative manifest always has a parent");
        validate_cargo_source_configuration(&repository_root, cargo_directory)?;
        let toolchain_metadata = ToolchainMetadata::read(&primary_manifest)?;
        // `--locked` reads the lockfile before metadata gives us Cargo's
        // workspace root. Require the primary manifest to keep owning the
        // workspace so this preflight cannot silently validate the wrong
        // `Cargo.lock` after a repository-layout change.
        if !toolchain_metadata.defines_workspace() {
            return Err(CollectError::PrimaryManifestNotWorkspaceRoot {
                path: primary_manifest.clone(),
            });
        }
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
                metadata: package.metadata.clone(),
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

        let primary_manifest_source = fs::read_to_string(&primary_manifest)
            .map_err(|source| CollectError::Read { path: primary_manifest.clone(), source })?;

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
        let zerocopy_docs_rs_rustdoc_args =
            validate_zerocopy_docs_rs_rustdoc_args(policy, &self.packages, &mut errors);

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
        let toolchain_versions = validate_toolchains(
            policy,
            &self.packages,
            &self.workspace_package_ids,
            &self.resolved_packages,
            &self.toolchain_metadata,
            &build_rs_versions,
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
            zerocopy_docs_rs_rustdoc_args,
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
) -> Result<(), CollectError> {
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
    let config_path = resolve_repository_path(repository_root, &configured_path)?;
    let source = fs::read_to_string(&config_path)
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
    Ok(())
}

/// Validates the lockfile Cargo will read while honoring `--locked`.
///
/// [`CollectedRepository::collect`] first proves that the primary manifest
/// defines the workspace. Cargo therefore selects the sibling `Cargo.lock`,
/// rather than an ancestor workspace's lockfile. Check physical containment
/// and file kind before invoking Cargo so `--locked` cannot read through an
/// escaping symbolic link during the operation intended to establish trust.
fn validate_cargo_lockfile(
    repository_root: &Path,
    cargo_directory: &Path,
) -> Result<(), CollectError> {
    let path = cargo_directory.join("Cargo.lock");
    if !repository_regular_file_exists(repository_root, &path)? {
        return Err(CollectError::InvalidCargoLockfile { path });
    }
    Ok(())
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

/// Extracts the docs.rs Rustdoc arguments from the one package which owns the
/// Zerocopy CI contract.
///
/// Cargo exposes arbitrary TOML package metadata as JSON. Treating a missing
/// key, `null`, a scalar, or an object as an empty argument list would silently
/// weaken the nightly documentation command. This parser accepts exactly an
/// ordered, nonempty array of nonempty, whitespace-free strings and preserves
/// the declared order verbatim. The whitespace restriction is load-bearing:
/// the current workflow joins these elements into `RUSTDOCFLAGS`, whose parser
/// cannot preserve an argument-internal space.
fn validate_zerocopy_docs_rs_rustdoc_args(
    policy: &Policy,
    packages: &BTreeMap<PathBuf, CargoPackage>,
    errors: &mut ErrorSink,
) -> Vec<String> {
    let Some(configured) = policy.packages().get(PRIMARY_PACKAGE_ID) else {
        errors.push(
            "packages.zerocopy",
            "canonical Zerocopy package is absent, so docs.rs arguments have no owner",
        );
        return Vec::new();
    };
    let manifest = configured.manifest().as_path();
    let location = format!("{}.package.metadata.docs.rs.rustdoc-args", manifest.display());
    let Some(package) = packages.get(manifest) else {
        errors.push(
            &location,
            format!(
                "canonical Zerocopy manifest `{}` is absent from Cargo metadata",
                manifest.display()
            ),
        );
        return Vec::new();
    };
    if package.name != PRIMARY_PACKAGE_ID || package.manifest != manifest {
        errors.push(
            &location,
            format!(
                "metadata owner must be package `{PRIMARY_PACKAGE_ID}` at `{}`, found package `{}` at `{}`",
                manifest.display(),
                package.name,
                package.manifest.display()
            ),
        );
        return Vec::new();
    }

    let Some(package_metadata) = package.metadata.as_object() else {
        errors.push(&location, "package metadata must be a JSON object");
        return Vec::new();
    };
    let Some(docs) = package_metadata.get("docs").and_then(serde_json::Value::as_object) else {
        errors.push(&location, "`package.metadata.docs` must be a table");
        return Vec::new();
    };
    let Some(docs_rs) = docs.get("rs").and_then(serde_json::Value::as_object) else {
        errors.push(&location, "`package.metadata.docs.rs` must be a table");
        return Vec::new();
    };
    let Some(arguments) = docs_rs.get("rustdoc-args").and_then(serde_json::Value::as_array) else {
        errors.push(&location, "`rustdoc-args` must be an array of strings");
        return Vec::new();
    };
    if arguments.is_empty() {
        errors.push(&location, "`rustdoc-args` must not be empty");
        return Vec::new();
    }

    let mut parsed = Vec::with_capacity(arguments.len());
    for (index, argument) in arguments.iter().enumerate() {
        let argument_location = format!("{location}[{index}]");
        let Some(argument) = argument.as_str() else {
            errors.push(argument_location, "Rustdoc argument must be a string");
            continue;
        };
        if argument.is_empty() {
            errors.push(argument_location, "Rustdoc argument must not be empty");
            continue;
        }
        if argument.chars().any(char::is_control) {
            errors.push(argument_location, "Rustdoc argument must not contain control characters");
            continue;
        }
        if argument.chars().any(char::is_whitespace) {
            errors.push(
                argument_location,
                "Rustdoc argument must not contain whitespace because RUSTDOCFLAGS cannot preserve that argument boundary",
            );
            continue;
        }
        parsed.push(argument.to_owned());
    }
    parsed
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

/// Rejects a semantically versioned CI toolchain which Cargo cannot use.
///
/// Cargo refuses to build a package with a compiler older than its declared
/// `rust-version`. Keeping this comparison next to the exact-version parser
/// prevents a syntactically valid policy from expanding into guaranteed-failing
/// CI cells after the package MSRV changes.
fn validate_toolchain_version_floor(
    location: impl Into<String>,
    toolchain: &str,
    version: RustVersion,
    package: &str,
    msrv: RustVersion,
    errors: &mut ErrorSink,
) {
    if version < msrv {
        errors.push(
            location,
            format!(
                "toolchain `{toolchain}` Rust version `{version}` is older than package `{package}` MSRV `{msrv}`"
            ),
        );
    }
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

fn validate_toolchains(
    policy: &Policy,
    packages: &BTreeMap<PathBuf, CargoPackage>,
    workspace_package_ids: &BTreeMap<PathBuf, PackageId>,
    resolved_packages: &BTreeMap<PackageId, ResolvedPackage>,
    metadata: &ToolchainMetadata,
    build_rs: &BTreeMap<String, RustVersion>,
    errors: &mut ErrorSink,
) -> BTreeMap<String, String> {
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

    let mut versions = BTreeMap::new();
    let mut semantic_versions = BTreeMap::new();
    for (id, toolchain) in policy.toolchains() {
        let (expected_id, semantic_version) = match toolchain.source() {
            ToolchainSource::ManifestRustVersion => {
                (Some(("msrv", metadata.rust_version.as_str())), msrv)
            }
            ToolchainSource::PinnedStable => {
                (Some(("stable", metadata.pinned_stable.as_str())), pinned_stable)
            }
            ToolchainSource::PinnedNightly => {
                (Some(("nightly", metadata.pinned_nightly.as_str())), None)
            }
            ToolchainSource::BuildRs => (
                metadata.build_rs.get(id.as_str()).map(|version| (id.as_str(), version.as_str())),
                build_rs.get(id.as_str()).copied(),
            ),
        };
        let Some((required_id, version)) = expected_id else {
            continue;
        };
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
        versions.insert(id.as_str().to_owned(), version.to_owned());
        if let Some(version) = semantic_version {
            semantic_versions.insert(id.as_str().to_owned(), version);
        }
    }

    validate_scoped_package_msrvs(
        policy,
        packages,
        workspace_package_ids,
        resolved_packages,
        &semantic_versions,
        errors,
    );
    versions
}

/// Checks each semantic compiler against its complete resolved closure.
///
/// A package can declare an MSRV independently of the primary Zerocopy crate.
/// Cargo can also compile local and non-workspace normal, dev, build, optional,
/// and target-specific dependencies while executing a selected package's CI
/// commands. Begin with policy scope roots and conservatively traverse both
/// every declared workspace edge and Cargo's complete resolved PackageId
/// graph. This avoids both silent guaranteed failures and a second, incomplete
/// implementation of Cargo's selection rules. Dated nightly pins are absent
/// from `semantic_versions` because a nightly date has no sound ordering
/// against a stable Rust release.
fn validate_scoped_package_msrvs(
    policy: &Policy,
    packages: &BTreeMap<PathBuf, CargoPackage>,
    workspace_package_ids: &BTreeMap<PathBuf, PackageId>,
    resolved_packages: &BTreeMap<PackageId, ResolvedPackage>,
    semantic_versions: &BTreeMap<String, RustVersion>,
    errors: &mut ErrorSink,
) {
    let mut package_msrvs = BTreeMap::new();
    let workspace_ids = workspace_package_ids.values().cloned().collect::<BTreeSet<_>>();
    let policy_ids_by_manifest = policy
        .packages()
        .iter()
        .map(|(id, package)| (package.manifest().as_path(), id.as_str()))
        .collect::<BTreeMap<_, _>>();
    for (manifest, package) in packages {
        let Some(value) = package.rust_version() else {
            // Cargo permits packages without a declared floor. Only an
            // explicit MSRV creates a comparison obligation here.
            continue;
        };
        let Some(version) = parse_exact_rust_version(value) else {
            let location = policy_ids_by_manifest.get(manifest.as_path()).map_or_else(
                || format!("workspace_packages.{}.rust-version", package.name),
                |id| format!("packages.{id}.rust-version"),
            );
            errors.push(location, format!("declared MSRV `{value}` is not an exact Rust version"));
            continue;
        };
        let Some(package_id) = workspace_package_ids.get(manifest) else {
            // Workspace classification and collection own this inconsistency.
            continue;
        };
        package_msrvs.insert(package_id.clone(), (package.name.clone(), version));
    }
    for (package_id, package) in resolved_packages {
        if workspace_ids.contains(package_id) {
            // Mutation tests intentionally edit the richer CargoPackage facts.
            // In production both records originate in the same Cargo response,
            // but keeping one authority here prevents a stale duplicate from
            // masking a workspace-manifest error.
            continue;
        }
        let Some(value) = package.rust_version.as_deref() else {
            continue;
        };
        let Some(version) = parse_exact_rust_version(value) else {
            errors.push(
                format!("resolved_packages.{package_id}.rust-version"),
                format!(
                    "dependency `{} {}` at `{}` declares MSRV `{value}`, which is not an exact Rust version",
                    package.name,
                    package.version,
                    package.manifest.display()
                ),
            );
            continue;
        };
        package_msrvs
            .insert(package_id.clone(), (format!("{}@{}", package.name, package.version), version));
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
            let Some((package, msrv)) = package_msrvs.get(&package_id) else {
                continue;
            };
            validate_toolchain_version_floor(
                format!("toolchains.{}.scopes", toolchain_id.as_str()),
                toolchain_id.as_str(),
                version,
                package,
                *msrv,
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
    };

    use super::{
        cargo_metadata_command, feature_closure, is_pinned_nightly, is_rust_target_name,
        parse_exact_rust_version, relative_path, repository_regular_file_exists,
        resolved_dependency_closure, resolved_workspace_dependencies, validate_build_rs_contract,
        validate_cargo_lockfile, validate_cargo_source_configuration,
        validate_cargo_target_classification, validate_package_source_symlink_containment,
        validate_policy_targets, validate_toolchain_version_floor,
        validate_workspace_package_classification_from_manifests, workspace_dependency_closure,
        CargoPackage, CargoTarget, CollectError, Dependency, ErrorSink, ResolvedPackage,
    };
    use crate::policy::ToolchainSource;

    fn feature_package(root_members: &[&str]) -> CargoPackage {
        CargoPackage {
            name: "example".to_owned(),
            manifest: "example/Cargo.toml".into(),
            rust_version: Some("1.56.0".to_owned()),
            metadata: serde_json::Value::Null,
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
            metadata: serde_json::Value::Null,
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
            metadata: serde_json::Value::Null,
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
            metadata: serde_json::Value::Null,
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
    fn cargo_lockfile_is_contained_and_regular_before_cargo_runs() {
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

        validate_cargo_lockfile(&repository, &cargo_directory).unwrap();

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
        let msrv = parse_exact_rust_version("1.60.0").unwrap();
        let mut errors = ErrorSink::default();

        validate_toolchain_version_floor(
            "toolchains.older",
            "older",
            parse_exact_rust_version("1.59.9").unwrap(),
            "zerocopy",
            msrv,
            &mut errors,
        );
        validate_toolchain_version_floor(
            "toolchains.equal",
            "equal",
            parse_exact_rust_version("1.60.0").unwrap(),
            "zerocopy",
            msrv,
            &mut errors,
        );
        validate_toolchain_version_floor(
            "toolchains.newer",
            "newer",
            parse_exact_rust_version("1.61.0").unwrap(),
            "zerocopy",
            msrv,
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
        assert_eq!(
            inventory.zerocopy_docs_rs_rustdoc_args(),
            [
                "--cfg",
                "doc_cfg",
                "--generate-link-to-definition",
                "--extend-css",
                "rustdoc/style.css",
            ]
        );
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
    fn build_rs_metadata_and_policy_toolchains_must_match_both_ways() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy = crate::policy::Policy::read(root.join("ci/zc.toml")).unwrap();
        let mut collected = super::CollectedRepository::collect(&root, &policy).unwrap();

        let stale_policy_id = policy
            .toolchains()
            .iter()
            .find(|(_, toolchain)| toolchain.source() == crate::policy::ToolchainSource::BuildRs)
            .map(|(id, _)| id.as_str().to_owned())
            .expect("repository policy has a build-rs compatibility toolchain");
        assert!(collected.toolchain_metadata.build_rs.remove(&stale_policy_id).is_some());
        let missing_policy_id = "unplanned-build-rs-toolchain";
        assert!(collected
            .toolchain_metadata
            .build_rs
            .insert(missing_policy_id.to_owned(), "1.70.0".to_owned())
            .is_none());

        let diagnostic = collected.validate(&policy).unwrap_err().to_string();
        assert!(
            diagnostic.contains(&format!(
                "build-rs metadata key `{missing_policy_id}` has no policy toolchain"
            )),
            "{diagnostic}"
        );
        assert!(
            diagnostic.contains(&format!(
                "toolchains.{stale_policy_id}: build-rs policy toolchain has no matching manifest metadata key"
            )),
            "{diagnostic}"
        );
    }

    #[test]
    fn docs_rs_rustdoc_args_fail_closed_on_malformed_metadata() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy = crate::policy::Policy::read(root.join("ci/zc.toml")).unwrap();
        let collected = super::CollectedRepository::collect(&root, &policy).unwrap();

        for (case, metadata) in [
            ("missing tables", serde_json::json!({})),
            (
                "scalar instead of array",
                serde_json::json!({"docs": {"rs": {"rustdoc-args": "--cfg"}}}),
            ),
            ("empty array", serde_json::json!({"docs": {"rs": {"rustdoc-args": []}}})),
            ("non-string argument", serde_json::json!({"docs": {"rs": {"rustdoc-args": [true]}}})),
            ("empty argument", serde_json::json!({"docs": {"rs": {"rustdoc-args": [""]}}})),
            (
                "control character",
                serde_json::json!({"docs": {"rs": {"rustdoc-args": ["bad\nargument"]}}}),
            ),
            (
                "argument-internal whitespace",
                serde_json::json!({"docs": {"rs": {"rustdoc-args": ["two words"]}}}),
            ),
        ] {
            let mut mutation = collected.clone();
            mutation.packages.get_mut(Path::new("zerocopy/Cargo.toml")).unwrap().metadata =
                metadata;

            let errors = mutation.validate(&policy).unwrap_err();
            assert!(
                errors.errors().iter().any(|error| {
                    error
                        .location()
                        .starts_with("zerocopy/Cargo.toml.package.metadata.docs.rs.rustdoc-args")
                }),
                "{case}: {errors}"
            );
        }
    }

    #[test]
    fn docs_rs_arguments_are_owned_only_by_the_canonical_package() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy = crate::policy::Policy::read(root.join("ci/zc.toml")).unwrap();
        let mut collected = super::CollectedRepository::collect(&root, &policy).unwrap();
        let metadata =
            collected.packages.get(Path::new("zerocopy/Cargo.toml")).unwrap().metadata.clone();
        collected.packages.get_mut(Path::new("zerocopy/Cargo.toml")).unwrap().metadata =
            serde_json::json!({});
        collected
            .packages
            .get_mut(Path::new("zerocopy/zerocopy-derive/Cargo.toml"))
            .unwrap()
            .metadata = metadata;

        let errors = collected.validate(&policy).unwrap_err();
        assert!(
            errors.errors().iter().any(|error| error.location()
                == "zerocopy/Cargo.toml.package.metadata.docs.rs.rustdoc-args"),
            "{errors}"
        );
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
