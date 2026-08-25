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

use cargo_metadata::{MetadataCommand, TargetKind};
use thiserror::Error;

use crate::{
    metadata::{ReadMetadataError, ToolchainMetadata},
    policy::{FeatureProfile, Policy, ToolchainSource},
};

const PRIMARY_PACKAGE_ID: &str = "zerocopy";

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
    features: BTreeMap<String, BTreeSet<String>>,
    dependencies: BTreeMap<String, Dependency>,
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

/// Live facts kept separate from semantic validation for mutation tests.
#[derive(Clone, Debug)]
pub struct CollectedRepository {
    repository_root: PathBuf,
    packages: BTreeMap<PathBuf, CargoPackage>,
    conventional_sources: BTreeSet<PathBuf>,
    existing_files: BTreeMap<PathBuf, bool>,
    primary_manifest_source: String,
    toolchain_metadata: ToolchainMetadata,
}

impl CollectedRepository {
    /// Collects Cargo metadata and repository file facts without interpreting
    /// policy semantics.
    ///
    /// Cargo is run with `--locked --offline --no-deps`. Inventory must never
    /// update a lockfile or turn a validation command into network access.
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
        let toolchain_metadata = ToolchainMetadata::read(&primary_manifest)?;

        let command = cargo_metadata_command(
            &primary_manifest,
            cargo_directory,
            &toolchain_metadata.pinned_stable,
        );
        let metadata = command.exec().map_err(|source| CollectError::CargoMetadata {
            manifest: primary_manifest.clone(),
            source,
        })?;

        let mut packages = BTreeMap::new();
        for package in metadata.workspace_packages() {
            let manifest = relative_path(&repository_root, package.manifest_path.as_std_path())?;
            let mut dependencies = BTreeMap::<String, Dependency>::new();
            for dependency in &package.dependencies {
                let key = dependency.rename.as_ref().unwrap_or(&dependency.name).clone();
                dependencies
                    .entry(key)
                    .and_modify(|known| known.optional |= dependency.optional)
                    .or_insert(Dependency { optional: dependency.optional });
            }

            let mut targets = BTreeSet::new();
            for target in &package.targets {
                let source = relative_path(&repository_root, target.src_path.as_std_path())?;
                let kinds = target.kind.iter().map(target_kind_name).collect();
                targets.insert(CargoTarget {
                    package: package.name.to_string(),
                    name: target.name.clone(),
                    kinds,
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
                features: package
                    .features
                    .iter()
                    .map(|(name, members)| {
                        (name.clone(), members.iter().cloned().collect::<BTreeSet<_>>())
                    })
                    .collect(),
                dependencies,
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

        validate_policy_targets(policy, &mut errors);
        let build_rs_versions = validate_build_rs_contract(
            &self.primary_manifest_source,
            &self.toolchain_metadata.build_rs,
            &mut errors,
        );
        let toolchain_versions = validate_toolchains(
            policy,
            &self.packages,
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
        })
    }

    /// Returns the canonical repository root used for collection.
    pub fn repository_root(&self) -> &Path {
        &self.repository_root
    }
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
        .no_deps()
        .other_options(vec!["--locked".to_owned(), "--offline".to_owned()]);
    command
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

            if has_only_kind(target, "lib") || has_only_kind(target, "proc-macro") {
                validate_library_target(package_directory, package, target, &location, errors);
            } else if has_only_kind(target, "test") {
                validate_integration_test_target(
                    manifest,
                    package_directory,
                    package,
                    target,
                    &location,
                    errors,
                );
            } else if has_only_kind(target, "bench") {
                validate_codegen_bench_target(
                    manifest,
                    package_directory,
                    package,
                    target,
                    &location,
                    errors,
                );
            } else if has_only_kind(target, "custom-build") {
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

    validate_scoped_package_msrvs(policy, packages, &semantic_versions, errors);
    versions
}

/// Checks each semantic compiler against the packages it actually builds.
///
/// A package can declare an MSRV independently of the primary Zerocopy crate,
/// and a toolchain need not select every package. Deriving this relation from
/// policy scopes avoids both silent guaranteed failures and stale global
/// comparisons when a future scope stops building a package. Dated nightly
/// pins are intentionally absent from `semantic_versions`: there is no sound
/// ordering between a nightly date and a stable Rust release.
fn validate_scoped_package_msrvs(
    policy: &Policy,
    packages: &BTreeMap<PathBuf, CargoPackage>,
    semantic_versions: &BTreeMap<String, RustVersion>,
    errors: &mut ErrorSink,
) {
    let mut package_msrvs = BTreeMap::new();
    for (id, package_policy) in policy.packages() {
        let Some(package) = packages.get(package_policy.manifest().as_path()) else {
            // The package-to-manifest inventory check owns this diagnostic.
            continue;
        };
        let Some(value) = package.rust_version() else {
            // Cargo permits packages without a declared floor. Only an
            // explicit MSRV creates a comparison obligation here.
            continue;
        };
        let Some(version) = parse_exact_rust_version(value) else {
            errors.push(
                format!("packages.{}.rust-version", id.as_str()),
                format!("declared MSRV `{value}` is not an exact Rust version"),
            );
            continue;
        };
        package_msrvs.insert(id.as_str().to_owned(), version);
    }

    for (toolchain_id, toolchain) in policy.toolchains() {
        let Some(version) = semantic_versions.get(toolchain_id.as_str()).copied() else {
            continue;
        };
        // A package may appear in multiple disjoint profile/target scopes on
        // the same toolchain. Compare its MSRV once, independent of how many
        // matrix cells those scopes later expand into.
        let selected_packages = toolchain
            .scopes()
            .iter()
            .flat_map(|scope| scope.packages())
            .map(|id| id.as_str())
            .collect::<BTreeSet<_>>();
        for package in selected_packages {
            let Some(msrv) = package_msrvs.get(package).copied() else {
                continue;
            };
            validate_toolchain_version_floor(
                format!("toolchains.{}.scopes", toolchain_id.as_str()),
                toolchain_id.as_str(),
                version,
                package,
                msrv,
                errors,
            );
        }
    }
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
        validate_build_rs_contract, validate_cargo_target_classification,
        validate_toolchain_version_floor, validate_workspace_package_classification_from_manifests,
        CargoPackage, CargoTarget, CollectError, Dependency, ErrorSink,
    };

    fn feature_package(root_members: &[&str]) -> CargoPackage {
        CargoPackage {
            name: "example".to_owned(),
            manifest: "example/Cargo.toml".into(),
            rust_version: Some("1.56.0".to_owned()),
            features: [(
                "stable".to_owned(),
                root_members.iter().map(|member| (*member).to_owned()).collect(),
            )]
            .into_iter()
            .collect(),
            dependencies: BTreeMap::new(),
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
        CargoTarget {
            package: package.to_owned(),
            name: name.to_owned(),
            kinds: kinds.iter().map(|kind| (*kind).to_owned()).collect(),
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
            features: BTreeMap::new(),
            dependencies: BTreeMap::new(),
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
            features: BTreeMap::new(),
            dependencies: BTreeMap::new(),
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
    fn cargo_metadata_ignores_ambient_cargo_and_toolchain_overrides() {
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
                "--no-deps",
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
            [("RUSTUP_AUTO_INSTALL", "0"), ("RUSTUP_TOOLCHAIN", "1.93.1")]
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
    fn repository_validation_uses_each_scoped_packages_declared_msrv() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let policy = crate::policy::Policy::read(root.join("ci/zc.toml")).unwrap();
        let mut collected = super::CollectedRepository::collect(&root, &policy).unwrap();

        // Zerocopy Derive currently has no independent MSRV. Model a future
        // declaration above every configured compiler. Only the non-nightly
        // toolchains whose scopes actually select this package should fail.
        collected
            .packages
            .get_mut(Path::new("zerocopy/zerocopy-derive/Cargo.toml"))
            .unwrap()
            .rust_version = Some("999.0.0".to_owned());

        let errors = collected.validate(&policy).unwrap_err();
        let diagnostic = errors.to_string();
        assert_eq!(errors.errors().len(), 2, "{diagnostic}");
        for (toolchain, version) in [("msrv", "1.56.0"), ("stable", "1.93.1")] {
            assert!(
                diagnostic.contains(&format!(
                    "toolchains.{toolchain}.scopes: toolchain `{toolchain}` Rust version `{version}` is older than package `zerocopy-derive` MSRV `999.0.0`"
                )),
                "{diagnostic}"
            );
        }
        assert!(!diagnostic.contains("toolchain `nightly`"), "{diagnostic}");
        assert!(!diagnostic.contains("toolchain `no-zerocopy"), "{diagnostic}");
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
