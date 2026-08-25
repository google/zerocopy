// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The strictly validated, repository-owned CI policy.
//!
//! This module describes ordinary, unprivileged build and test coverage. It
//! intentionally does not describe workflow permissions, secrets, runners,
//! action references, or publication. Those security-sensitive choices remain
//! in the small, hand-written GitHub Actions workflows and must be reviewed as
//! YAML. A future planner may use this policy to choose work, but it must not
//! use policy data to grant privileges.
//!
//! Cargo metadata remains authoritative for package features and Rust version
//! numbers. The policy names the stable aggregate feature and says which Cargo
//! metadata field supplies each toolchain. Repository inventory validation is
//! responsible for checking those cross-file contracts before planning work.

use std::{
    borrow::Borrow,
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt, fs, io,
    path::{Component, Path, PathBuf},
};

use serde::Deserialize;
use thiserror::Error;

/// The only policy schema understood by this version of `zc`.
pub const POLICY_SCHEMA_VERSION: u32 = 1;

/// GitHub Actions expands at most 256 jobs from one matrix.
pub const GITHUB_MAX_MATRIX_CELLS: u64 = 256;

/// A hard bound on logical work expanded before it is split into matrices.
///
/// This permits up to 256 maximum-sized shards while preventing an accidental
/// Cartesian-product explosion from consuming unbounded memory in the planner.
pub const MAX_PLAN_CELLS: u64 = GITHUB_MAX_MATRIX_CELLS * GITHUB_MAX_MATRIX_CELLS;

/// A conservative interpretation of GitHub's one-megabyte job-output limit.
///
/// GitHub estimates output size using UTF-16. Keeping the configured ceiling at
/// or below this decimal megabyte leaves the planner responsible for any
/// additional safety margin.
pub const GITHUB_MAX_JOB_OUTPUT_UTF16_BYTES: u64 = 1_000_000;

/// A validated CI policy.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Policy {
    /// The parsed schema version.
    schema_version: u32,
    /// GitHub event names grouped by the amount of work they receive.
    events: Events,
    /// Cargo feature selection behavior.
    features: Features,
    /// Cargo packages, keyed by stable policy identifier.
    packages: BTreeMap<Id, Package>,
    /// Compilation targets, keyed by target triple.
    targets: BTreeMap<Id, Target>,
    /// Named, resolved target selections.
    target_sets: BTreeMap<Id, BTreeSet<Id>>,
    /// Rust toolchains and the exact work assigned to each one.
    toolchains: BTreeMap<Id, Toolchain>,
    /// Miri borrow models, keyed by stable policy identifier.
    miri_models: BTreeMap<Id, MiriModel>,
    /// The Miri matrix policy.
    miri: Miri,
    /// The semver-check matrix policy.
    semver: Semver,
    /// Independent files which freeze behavior of the old workflow.
    baselines: Baselines,
    /// Safety limits applied before data reaches GitHub Actions.
    limits: Limits,
}

impl Policy {
    /// Reads and validates policy at `path`.
    pub fn read(path: impl AsRef<Path>) -> Result<Self, ReadPolicyError> {
        let path = path.as_ref();
        let source = fs::read_to_string(path)
            .map_err(|source| ReadPolicyError::Read { path: path.to_path_buf(), source })?;
        Self::parse(&source)
            .map_err(|source| ReadPolicyError::Policy { path: path.to_path_buf(), source })
    }

    /// Parses and validates policy source.
    pub fn parse(source: &str) -> Result<Self, PolicyError> {
        let raw: RawPolicy = toml::from_str(source).map_err(PolicyError::Toml)?;
        raw.validate().map_err(PolicyError::Invalid)
    }

    /// Returns the policy schema version.
    pub fn schema_version(&self) -> u32 {
        self.schema_version
    }

    /// Returns the event classification policy.
    pub fn events(&self) -> &Events {
        &self.events
    }

    /// Returns the feature-selection policy.
    pub fn features(&self) -> &Features {
        &self.features
    }

    /// Returns packages keyed by stable policy identifier.
    pub fn packages(&self) -> &BTreeMap<Id, Package> {
        &self.packages
    }

    /// Returns compilation targets keyed by target triple.
    pub fn targets(&self) -> &BTreeMap<Id, Target> {
        &self.targets
    }

    /// Returns resolved target sets keyed by stable policy identifier.
    pub fn target_sets(&self) -> &BTreeMap<Id, BTreeSet<Id>> {
        &self.target_sets
    }

    /// Returns toolchains keyed by stable policy identifier.
    pub fn toolchains(&self) -> &BTreeMap<Id, Toolchain> {
        &self.toolchains
    }

    /// Returns Miri models keyed by stable policy identifier.
    pub fn miri_models(&self) -> &BTreeMap<Id, MiriModel> {
        &self.miri_models
    }

    /// Returns the Miri coverage policy.
    pub fn miri(&self) -> &Miri {
        &self.miri
    }

    /// Returns the semver-check coverage policy.
    pub fn semver(&self) -> &Semver {
        &self.semver
    }

    /// Returns paths to independently captured legacy behavior.
    pub fn baselines(&self) -> &Baselines {
        &self.baselines
    }

    /// Returns planning safety limits.
    pub fn limits(&self) -> &Limits {
        &self.limits
    }
}

/// An error reading a policy file.
#[derive(Debug, Error)]
pub enum ReadPolicyError {
    /// The file could not be read.
    #[error("failed to read CI policy `{path}`: {source}")]
    Read {
        /// The path passed to [`Policy::read`].
        path: PathBuf,
        /// The underlying file-system error.
        #[source]
        source: io::Error,
    },
    /// The file did not contain a valid policy.
    #[error("failed to load CI policy `{path}`: {source}")]
    Policy {
        /// The path passed to [`Policy::read`].
        path: PathBuf,
        /// The parse or validation error.
        #[source]
        source: PolicyError,
    },
}

/// An error parsing or semantically validating policy source.
#[derive(Debug, Error)]
pub enum PolicyError {
    /// TOML syntax, types, or table keys were invalid.
    #[error("failed to parse policy TOML: {0}")]
    Toml(#[source] toml::de::Error),
    /// The TOML was well-typed but violated one or more policy invariants.
    #[error("{0}")]
    Invalid(ValidationErrors),
}

/// All semantic errors found in one validation pass.
#[derive(Debug)]
pub struct ValidationErrors(Vec<ValidationError>);

impl ValidationErrors {
    /// Returns the individual errors in deterministic reporting order.
    pub fn errors(&self) -> &[ValidationError] {
        &self.0
    }
}

impl fmt::Display for ValidationErrors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "CI policy has {} validation error(s):", self.0.len())?;
        for error in &self.0 {
            writeln!(f, "- {}: {}", error.location, error.message)?;
        }
        Ok(())
    }
}

impl Error for ValidationErrors {}

/// One actionable policy validation error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidationError {
    location: String,
    message: String,
}

impl ValidationError {
    /// The dotted field or indexed selection which caused the error.
    pub fn location(&self) -> &str {
        &self.location
    }

    /// A plain-language description of how to repair the error.
    pub fn message(&self) -> &str {
        &self.message
    }
}

/// A stable identifier used by references in the policy.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Id(String);

impl Id {
    /// Returns the identifier as policy text.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Borrow<str> for Id {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

/// A normalized path relative to the repository root.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct RepoPath(PathBuf);

impl RepoPath {
    /// Returns the path without joining it to a checkout.
    pub fn as_path(&self) -> &Path {
        &self.0
    }
}

/// Event categories understood by the planner.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Events {
    /// Events which run the latency-optimized selection.
    reduced: BTreeSet<Id>,
    /// Events which run all required work.
    full: BTreeSet<Id>,
}

impl Events {
    /// Returns events which run the latency-optimized selection.
    pub fn reduced(&self) -> &BTreeSet<Id> {
        &self.reduced
    }

    /// Returns events which run all required work.
    pub fn full(&self) -> &BTreeSet<Id> {
        &self.full
    }

    /// Classifies an exact GitHub event name.
    ///
    /// `None` is intentional: callers must reject unknown events instead of
    /// treating every non-pull-request event as full coverage.
    pub fn category(&self, event_name: &str) -> Option<EventCategory> {
        if self.reduced.iter().any(|event| event.as_str() == event_name) {
            Some(EventCategory::Reduced)
        } else if self.full.iter().any(|event| event.as_str() == event_name) {
            Some(EventCategory::Full)
        } else {
            None
        }
    }
}

/// Cargo feature behavior and its named profiles.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Features {
    /// The Cargo feature which reaches every stable feature.
    ///
    /// Inventory code derives the nightly-only complement from Cargo's feature
    /// graph. Do not add a second, hand-maintained nightly-feature list here.
    stable_feature_root: Id,
    /// Semantic feature profiles keyed by stable policy identifier.
    profiles: BTreeMap<Id, FeatureProfile>,
}

impl Features {
    /// Returns the Cargo feature which reaches every stable feature.
    pub fn stable_feature_root(&self) -> &Id {
        &self.stable_feature_root
    }

    /// Returns semantic feature profiles keyed by stable identifier.
    pub fn profiles(&self) -> &BTreeMap<Id, FeatureProfile> {
        &self.profiles
    }
}

/// One named Cargo feature selection.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FeatureProfile {
    /// Use Cargo's default feature selection.
    Default,
    /// Pass `--no-default-features` without selecting a feature.
    ///
    /// The current manifest has no `default` feature, so current policy does
    /// not need this profile. The schema supports it so inventory validation
    /// can require it if a future manifest adds a Cargo `default` feature.
    NoDefault,
    /// Select only the stable aggregate feature without default features.
    StableAggregate,
    /// Pass `--all-features`.
    All,
}

/// A Cargo package covered by the ordinary build and Miri matrices.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Package {
    /// The package manifest relative to the repository root.
    manifest: RepoPath,
    /// Feature profiles which are meaningful for this package.
    profiles: BTreeSet<Id>,
}

impl Package {
    /// Returns the package manifest relative to the repository root.
    pub fn manifest(&self) -> &RepoPath {
        &self.manifest
    }

    /// Returns feature profiles which are meaningful for this package.
    pub fn profiles(&self) -> &BTreeSet<Id> {
        &self.profiles
    }
}

/// How the executor exercises a compilation target.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TargetMode {
    /// Build and execute tests on the runner.
    Native,
    /// Compile test code and build library code without executing tests.
    Cross,
    /// Check only library code because test dependencies cannot be compiled.
    ///
    /// This name records the current thumb-specific workflow contract. If a
    /// second target needs the same treatment, changing this schema to a
    /// behavior-based name should be a deliberate, reviewed migration.
    Thumb,
}

/// One Rust compilation target.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Target {
    /// How ordinary Cargo work runs for this target.
    mode: TargetMode,
    /// Whether reduced pull-request CI includes this target.
    pr_eligible: bool,
    /// Whether the current Miri setup supports this target.
    miri_eligible: bool,
    /// Whether semver coverage must select or explicitly waive this target.
    semver_eligible: bool,
}

impl Target {
    /// Returns how ordinary Cargo work runs for this target.
    pub fn mode(&self) -> TargetMode {
        self.mode
    }

    /// Returns whether reduced pull-request CI includes this target.
    pub fn pr_eligible(&self) -> bool {
        self.pr_eligible
    }

    /// Returns whether the current Miri setup supports this target.
    pub fn miri_eligible(&self) -> bool {
        self.miri_eligible
    }

    /// Returns whether semver must select or explicitly waive this target.
    pub fn semver_eligible(&self) -> bool {
        self.semver_eligible
    }
}

/// The Cargo metadata field which supplies a toolchain's exact version.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ToolchainSource {
    /// `package.rust-version` in `zerocopy/Cargo.toml`.
    ManifestRustVersion,
    /// `package.metadata.ci.pinned-stable` in `zerocopy/Cargo.toml`.
    PinnedStable,
    /// `package.metadata.ci.pinned-nightly` in `zerocopy/Cargo.toml`.
    PinnedNightly,
    /// An entry in `package.metadata.build-rs`.
    ///
    /// For this source, the toolchain identifier is also the metadata key.
    BuildRs,
}

/// Exact package, feature-profile, and target selections.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Scope {
    /// Selected package identifiers.
    packages: BTreeSet<Id>,
    /// Selected feature-profile identifiers.
    profiles: BTreeSet<Id>,
    /// The named target set to expand.
    target_set: Id,
}

impl Scope {
    /// Returns selected package identifiers.
    pub fn packages(&self) -> &BTreeSet<Id> {
        &self.packages
    }

    /// Returns selected feature-profile identifiers.
    pub fn profiles(&self) -> &BTreeSet<Id> {
        &self.profiles
    }

    /// Returns the named target set to expand.
    pub fn target_set(&self) -> &Id {
        &self.target_set
    }
}

/// One toolchain and all ordinary build-matrix work assigned to it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Toolchain {
    /// Where repository inventory finds the exact version.
    source: ToolchainSource,
    /// Non-overlapping scopes run on this toolchain.
    scopes: Vec<Scope>,
}

impl Toolchain {
    /// Returns where repository inventory finds the exact version.
    pub fn source(&self) -> ToolchainSource {
        self.source
    }

    /// Returns non-overlapping scopes run on this toolchain.
    pub fn scopes(&self) -> &[Scope] {
        &self.scopes
    }
}

/// One Miri borrow model.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MiriModel {
    /// Additional `MIRIFLAGS` arguments for the model, in argument order.
    flags: Vec<String>,
}

impl MiriModel {
    /// Returns additional `MIRIFLAGS` arguments in argument order.
    pub fn flags(&self) -> &[String] {
        &self.flags
    }
}

/// The Miri matrix configuration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Miri {
    /// The toolchain used by Miri.
    toolchain: Id,
    /// The event category on which Miri runs.
    event_category: EventCategory,
    /// Non-overlapping package, profile, and target selections.
    scopes: Vec<Scope>,
}

impl Miri {
    /// Returns the toolchain used by Miri.
    pub fn toolchain(&self) -> &Id {
        &self.toolchain
    }

    /// Returns the event category on which Miri runs.
    pub fn event_category(&self) -> EventCategory {
        self.event_category
    }

    /// Returns non-overlapping package, profile, and target selections.
    pub fn scopes(&self) -> &[Scope] {
        &self.scopes
    }
}

/// Which event category receives a kind of work.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EventCategory {
    /// Only latency-optimized events.
    Reduced,
    /// Full-coverage events.
    Full,
}

/// Semver checking and its explicit coverage waivers.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Semver {
    /// The Cargo package to check.
    package: Id,
    /// The toolchain used by cargo-semver-checks.
    toolchain: Id,
    /// The feature profile used by cargo-semver-checks.
    profile: Id,
    /// The exact selected target set.
    target_set: Id,
    /// Targets deliberately omitted from semver checking.
    waivers: BTreeMap<Id, SemverWaiver>,
}

impl Semver {
    /// Returns the Cargo package to check.
    pub fn package(&self) -> &Id {
        &self.package
    }

    /// Returns the toolchain used by cargo-semver-checks.
    pub fn toolchain(&self) -> &Id {
        &self.toolchain
    }

    /// Returns the feature profile used by cargo-semver-checks.
    pub fn profile(&self) -> &Id {
        &self.profile
    }

    /// Returns the exact selected target set.
    pub fn target_set(&self) -> &Id {
        &self.target_set
    }

    /// Returns targets deliberately omitted from semver checking.
    pub fn waivers(&self) -> &BTreeMap<Id, SemverWaiver> {
        &self.waivers
    }
}

/// A deliberate target-specific exception to semver coverage.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemverWaiver {
    /// The tracking issue, written as `#` followed by decimal digits.
    issue: String,
    /// Why the target cannot currently be checked.
    reason: String,
}

impl SemverWaiver {
    /// Returns the tracking issue.
    pub fn issue(&self) -> &str {
        &self.issue
    }

    /// Returns why the target cannot currently be checked.
    pub fn reason(&self) -> &str {
        &self.reason
    }
}

/// Paths to independently captured legacy behavior.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Baselines {
    /// Source hashes and independently checked counts.
    manifest: RepoPath,
    /// Reduced ordinary build-matrix cells.
    build_reduced: RepoPath,
    /// Full ordinary build-matrix cells.
    build_full: RepoPath,
    /// Reduced Miri cells.
    miri_reduced: RepoPath,
    /// Full Miri cells.
    miri_full: RepoPath,
    /// Normalized commands implied by matrix cells.
    logical_obligations: RepoPath,
    /// Operations outside the two Cargo matrices.
    standalone_obligations: RepoPath,
    /// Exact argument vectors for behavior-sensitive commands.
    command_goldens: RepoPath,
}

impl Baselines {
    /// Returns the source-hash and count manifest.
    pub fn manifest(&self) -> &RepoPath {
        &self.manifest
    }

    /// Returns the reduced ordinary build-cell baseline.
    pub fn build_reduced(&self) -> &RepoPath {
        &self.build_reduced
    }

    /// Returns the full ordinary build-cell baseline.
    pub fn build_full(&self) -> &RepoPath {
        &self.build_full
    }

    /// Returns the reduced Miri-cell baseline.
    pub fn miri_reduced(&self) -> &RepoPath {
        &self.miri_reduced
    }

    /// Returns the full Miri-cell baseline.
    pub fn miri_full(&self) -> &RepoPath {
        &self.miri_full
    }

    /// Returns the normalized logical-obligation baseline.
    pub fn logical_obligations(&self) -> &RepoPath {
        &self.logical_obligations
    }

    /// Returns the standalone-obligation baseline.
    pub fn standalone_obligations(&self) -> &RepoPath {
        &self.standalone_obligations
    }

    /// Returns exact argument-vector goldens.
    pub fn command_goldens(&self) -> &RepoPath {
        &self.command_goldens
    }
}

/// Limits which keep generated Actions data within documented safe bounds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Limits {
    /// Maximum cells allowed in one generated matrix.
    max_matrix_cells: u64,
    /// Maximum logical cells expanded before matrix sharding.
    max_plan_cells: u64,
    /// Maximum UTF-16 byte estimate allowed in one job's outputs.
    max_job_output_utf16_bytes: u64,
}

impl Limits {
    /// Returns the maximum cells allowed in one generated matrix.
    pub fn max_matrix_cells(&self) -> u64 {
        self.max_matrix_cells
    }

    /// Returns the maximum logical cells expanded before matrix sharding.
    pub fn max_plan_cells(&self) -> u64 {
        self.max_plan_cells
    }

    /// Returns the maximum UTF-16 byte estimate allowed in job outputs.
    pub fn max_job_output_utf16_bytes(&self) -> u64 {
        self.max_job_output_utf16_bytes
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawPolicy {
    schema_version: u32,
    events: RawEvents,
    features: RawFeatures,
    feature_profiles: Vec<RawFeatureProfile>,
    packages: Vec<RawPackage>,
    targets: Vec<RawTarget>,
    target_sets: Vec<RawTargetSet>,
    toolchains: Vec<RawToolchain>,
    miri_models: Vec<RawMiriModel>,
    miri: RawMiri,
    semver: RawSemver,
    baselines: RawBaselines,
    limits: RawLimits,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawEvents {
    reduced: Vec<String>,
    full: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawFeatures {
    stable_feature_root: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawFeatureProfile {
    id: String,
    selection: RawFeatureSelection,
}

#[derive(Clone, Copy, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum RawFeatureSelection {
    Default,
    NoDefault,
    StableAggregate,
    All,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawPackage {
    id: String,
    manifest: String,
    profiles: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawTarget {
    id: String,
    mode: RawTargetMode,
    pr_eligible: bool,
    miri_eligible: bool,
    semver_eligible: bool,
}

#[derive(Clone, Copy, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum RawTargetMode {
    Native,
    Cross,
    Thumb,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawTargetSet {
    id: String,
    selection: RawTargetSetSelection,
    include: Vec<String>,
    exclude: Vec<String>,
}

#[derive(Clone, Copy, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum RawTargetSetSelection {
    All,
    MiriEligible,
    Explicit,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawToolchain {
    id: String,
    source: RawToolchainSource,
    scopes: Vec<RawScope>,
}

#[derive(Clone, Copy, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum RawToolchainSource {
    ManifestRustVersion,
    PinnedStable,
    PinnedNightly,
    BuildRs,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawScope {
    packages: Vec<String>,
    profiles: Vec<String>,
    target_set: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawMiriModel {
    id: String,
    flags: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawMiri {
    toolchain: String,
    event_category: RawEventCategory,
    scopes: Vec<RawScope>,
}

#[derive(Clone, Copy, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum RawEventCategory {
    Reduced,
    Full,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawSemver {
    package: String,
    toolchain: String,
    profile: String,
    target_set: String,
    waivers: Vec<RawSemverWaiver>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawSemverWaiver {
    target: String,
    issue: String,
    reason: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawBaselines {
    manifest: String,
    build_reduced: String,
    build_full: String,
    miri_reduced: String,
    miri_full: String,
    logical_obligations: String,
    standalone_obligations: String,
    command_goldens: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawLimits {
    max_matrix_cells: u64,
    max_plan_cells: u64,
    max_job_output_utf16_bytes: u64,
}

impl RawPolicy {
    fn validate(self) -> Result<Policy, ValidationErrors> {
        let mut validator = Validator::default();

        if self.schema_version != POLICY_SCHEMA_VERSION {
            validator.error(
                "schema_version",
                format!(
                    "unsupported schema version {}; this zc supports exactly {}",
                    self.schema_version, POLICY_SCHEMA_VERSION
                ),
            );
        }

        let events = Events {
            reduced: validator.id_set("events.reduced", &self.events.reduced),
            full: validator.id_set("events.full", &self.events.full),
        };
        for event in events.reduced.intersection(&events.full) {
            validator.error(
                "events",
                format!(
                    "event `{event}` appears in both reduced and full; every event must select exactly one category"
                ),
            );
        }

        let stable_feature_root =
            validator.id("features.stable_feature_root", &self.features.stable_feature_root);
        let profiles = validator.feature_profiles(self.feature_profiles);
        let packages = validator.packages(self.packages);
        let targets = validator.targets(self.targets);
        let target_sets = validator.target_sets(self.target_sets, &targets);
        let toolchains = validator.toolchains(self.toolchains);
        let miri_models = validator.miri_models(self.miri_models);
        let miri = validator.miri(self.miri);
        let semver = validator.semver(self.semver);
        let baselines = validator.baselines(self.baselines);
        let limits = Limits {
            max_matrix_cells: self.limits.max_matrix_cells,
            max_plan_cells: self.limits.max_plan_cells,
            max_job_output_utf16_bytes: self.limits.max_job_output_utf16_bytes,
        };

        validator.validate_limits(&limits);
        validator.validate_references(
            &profiles,
            &packages,
            &targets,
            &target_sets,
            &toolchains,
            &miri_models,
            &miri,
            &semver,
            &limits,
        );

        if !validator.errors.is_empty() {
            return Err(ValidationErrors(validator.errors));
        }

        Ok(Policy {
            schema_version: self.schema_version,
            events,
            features: Features {
                stable_feature_root: stable_feature_root
                    .expect("a missing feature root must produce a validation error"),
                profiles,
            },
            packages,
            targets,
            target_sets,
            toolchains,
            miri_models,
            miri,
            semver,
            baselines: baselines.expect("an invalid path must produce a validation error"),
            limits,
        })
    }
}

#[derive(Default)]
struct Validator {
    errors: Vec<ValidationError>,
}

impl Validator {
    fn error(&mut self, location: impl Into<String>, message: impl Into<String>) {
        self.errors.push(ValidationError {
            location: escape_control_characters(location.into()),
            message: escape_control_characters(message.into()),
        });
    }

    fn id(&mut self, location: &str, value: &str) -> Option<Id> {
        let valid = !value.is_empty()
            && value.bytes().enumerate().all(|(index, byte)| match byte {
                b'a'..=b'z' | b'0'..=b'9' | b'_' => true,
                b'-' | b'.' => index != 0,
                _ => false,
            })
            && !value.ends_with('-')
            && !value.ends_with('.')
            && value != "."
            && value != "..";
        if !valid {
            self.error(
                location,
                format!(
                    "`{value}` is not a stable identifier; use lowercase ASCII letters, digits, `_`, `-`, or `.`, and do not start or end with `-` or `.`"
                ),
            );
            return None;
        }
        Some(Id(value.to_owned()))
    }

    fn id_set(&mut self, location: &str, values: &[String]) -> BTreeSet<Id> {
        self.id_set_inner(location, values, false)
    }

    fn id_set_allow_empty(&mut self, location: &str, values: &[String]) -> BTreeSet<Id> {
        self.id_set_inner(location, values, true)
    }

    fn id_set_inner(
        &mut self,
        location: &str,
        values: &[String],
        allow_empty: bool,
    ) -> BTreeSet<Id> {
        if values.is_empty() && !allow_empty {
            self.error(location, "selection cannot be empty");
        }

        let mut ids = BTreeSet::new();
        for (index, value) in values.iter().enumerate() {
            if let Some(id) = self.id(&format!("{location}[{index}]"), value) {
                if !ids.insert(id.clone()) {
                    self.error(
                        format!("{location}[{index}]"),
                        format!("duplicate identifier `{id}` in the same selection"),
                    );
                }
            }
        }
        ids
    }

    fn repo_path(&mut self, location: &str, value: &str) -> Option<RepoPath> {
        let path = Path::new(value);
        let has_empty_component = value.split('/').any(str::is_empty);
        let has_dot_component = value.split('/').any(|component| matches!(component, "." | ".."));
        let has_windows_separator = value.contains('\\');
        let has_windows_prefix = value.contains(':');
        let has_control_character = value.chars().any(char::is_control);
        let has_unsafe_component =
            path.components().any(|component| !matches!(component, Component::Normal(_)));
        if value.is_empty()
            || has_empty_component
            || has_dot_component
            || has_windows_separator
            || has_windows_prefix
            || has_control_character
            || has_unsafe_component
        {
            self.error(
                location,
                format!(
                    "{value:?} is not a safe repository-relative path; use non-empty `/`-separated components without `.`, `..`, a root, or a platform prefix"
                ),
            );
            return None;
        }
        Some(RepoPath(path.to_path_buf()))
    }

    fn feature_profiles(
        &mut self,
        raw_profiles: Vec<RawFeatureProfile>,
    ) -> BTreeMap<Id, FeatureProfile> {
        if raw_profiles.is_empty() {
            self.error("feature_profiles", "category cannot be empty");
        }

        let mut profiles = BTreeMap::new();
        let mut selections = BTreeMap::new();
        for (index, raw) in raw_profiles.into_iter().enumerate() {
            let location = format!("feature_profiles[{index}]");
            let Some(id) = self.id(&format!("{location}.id"), &raw.id) else {
                continue;
            };
            let selection = match raw.selection {
                RawFeatureSelection::Default => FeatureProfile::Default,
                RawFeatureSelection::NoDefault => FeatureProfile::NoDefault,
                RawFeatureSelection::StableAggregate => FeatureProfile::StableAggregate,
                RawFeatureSelection::All => FeatureProfile::All,
            };
            if profiles.contains_key(&id) {
                self.error(format!("{location}.id"), format!("duplicate profile ID `{id}`"));
                continue;
            }
            if let Some(previous) = selections.insert(selection, id.clone()) {
                self.error(
                    format!("{location}.selection"),
                    format!(
                        "selection duplicates profile `{previous}`; equivalent profiles would silently repeat work"
                    ),
                );
            }
            profiles.insert(id, selection);
        }
        profiles
    }

    fn packages(&mut self, raw_packages: Vec<RawPackage>) -> BTreeMap<Id, Package> {
        if raw_packages.is_empty() {
            self.error("packages", "category cannot be empty");
        }

        let mut packages = BTreeMap::new();
        let mut manifests = BTreeMap::new();
        for (index, raw) in raw_packages.into_iter().enumerate() {
            let location = format!("packages[{index}]");
            let id = self.id(&format!("{location}.id"), &raw.id);
            let manifest = self.repo_path(&format!("{location}.manifest"), &raw.manifest);
            let profiles = self.id_set(&format!("{location}.profiles"), &raw.profiles);
            let (Some(id), Some(manifest)) = (id, manifest) else {
                continue;
            };
            if packages.contains_key(&id) {
                self.error(format!("{location}.id"), format!("duplicate package ID `{id}`"));
                continue;
            }
            if let Some(previous) = manifests.insert(manifest.clone(), id.clone()) {
                self.error(
                    format!("{location}.manifest"),
                    format!("manifest is already assigned to package `{previous}`"),
                );
            }
            packages.insert(id, Package { manifest, profiles });
        }
        packages
    }

    fn targets(&mut self, raw_targets: Vec<RawTarget>) -> BTreeMap<Id, Target> {
        if raw_targets.is_empty() {
            self.error("targets", "category cannot be empty");
        }

        let mut targets = BTreeMap::new();
        for (index, raw) in raw_targets.into_iter().enumerate() {
            let location = format!("targets[{index}]");
            let Some(id) = self.id(&format!("{location}.id"), &raw.id) else {
                continue;
            };
            if targets.contains_key(&id) {
                self.error(format!("{location}.id"), format!("duplicate target ID `{id}`"));
                continue;
            }
            let mode = match raw.mode {
                RawTargetMode::Native => TargetMode::Native,
                RawTargetMode::Cross => TargetMode::Cross,
                RawTargetMode::Thumb => TargetMode::Thumb,
            };
            targets.insert(
                id,
                Target {
                    mode,
                    pr_eligible: raw.pr_eligible,
                    miri_eligible: raw.miri_eligible,
                    semver_eligible: raw.semver_eligible,
                },
            );
        }

        if !targets.values().any(|target| target.pr_eligible) {
            self.error("targets", "at least one target must be eligible for pull-request CI");
        }
        if !targets.values().any(|target| target.miri_eligible) {
            self.error("targets", "at least one target must be eligible for Miri");
        }
        if !targets.values().any(|target| target.semver_eligible) {
            self.error("targets", "at least one target must be eligible for semver checking");
        }
        targets
    }

    fn target_sets(
        &mut self,
        raw_sets: Vec<RawTargetSet>,
        targets: &BTreeMap<Id, Target>,
    ) -> BTreeMap<Id, BTreeSet<Id>> {
        if raw_sets.is_empty() {
            self.error("target_sets", "category cannot be empty");
        }

        let mut sets = BTreeMap::new();
        for (index, raw) in raw_sets.into_iter().enumerate() {
            let location = format!("target_sets[{index}]");
            let id = self.id(&format!("{location}.id"), &raw.id);
            let include = self.id_set_allow_empty(&format!("{location}.include"), &raw.include);
            let exclude = self.id_set_allow_empty(&format!("{location}.exclude"), &raw.exclude);
            let mut members = match raw.selection {
                RawTargetSetSelection::All => targets.keys().cloned().collect(),
                RawTargetSetSelection::MiriEligible => targets
                    .iter()
                    .filter(|(_, target)| target.miri_eligible)
                    .map(|(id, _)| id.clone())
                    .collect(),
                RawTargetSetSelection::Explicit => BTreeSet::new(),
            };

            for target in &include {
                if !targets.contains_key(target) {
                    self.error(format!("{location}.include"), format!("unknown target `{target}`"));
                } else if !members.insert(target.clone()) {
                    self.error(
                        format!("{location}.include"),
                        format!(
                            "target `{target}` is already selected by the base expression; remove the redundant include"
                        ),
                    );
                }
            }
            for target in &exclude {
                if include.contains(target) {
                    self.error(
                        &location,
                        format!("target `{target}` cannot appear in both include and exclude"),
                    );
                    continue;
                }
                if !targets.contains_key(target) {
                    self.error(format!("{location}.exclude"), format!("unknown target `{target}`"));
                } else if !members.remove(target) {
                    self.error(
                        format!("{location}.exclude"),
                        format!(
                            "target `{target}` is not selected by the base expression; remove the ineffective exclude"
                        ),
                    );
                }
            }
            if members.is_empty() {
                self.error(&location, "target-set expression cannot select no targets");
            }
            let Some(id) = id else {
                continue;
            };
            if sets.contains_key(&id) {
                self.error(format!("{location}.id"), format!("duplicate target-set ID `{id}`"));
                continue;
            }
            sets.insert(id, members);
        }
        sets
    }

    fn scope(&mut self, location: &str, raw: RawScope) -> Option<Scope> {
        let packages = self.id_set(&format!("{location}.packages"), &raw.packages);
        let profiles = self.id_set(&format!("{location}.profiles"), &raw.profiles);
        let target_set = self.id(&format!("{location}.target_set"), &raw.target_set);
        target_set.map(|target_set| Scope { packages, profiles, target_set })
    }

    fn scopes(&mut self, location: &str, raw_scopes: Vec<RawScope>) -> Vec<Scope> {
        if raw_scopes.is_empty() {
            self.error(location, "selection cannot be empty");
        }
        raw_scopes
            .into_iter()
            .enumerate()
            .filter_map(|(index, raw)| self.scope(&format!("{location}[{index}]"), raw))
            .collect()
    }

    fn toolchains(&mut self, raw_toolchains: Vec<RawToolchain>) -> BTreeMap<Id, Toolchain> {
        if raw_toolchains.is_empty() {
            self.error("toolchains", "category cannot be empty");
        }

        let mut toolchains = BTreeMap::new();
        let mut standard_sources = BTreeMap::new();
        for (index, raw) in raw_toolchains.into_iter().enumerate() {
            let location = format!("toolchains[{index}]");
            let id = self.id(&format!("{location}.id"), &raw.id);
            let source = match raw.source {
                RawToolchainSource::ManifestRustVersion => ToolchainSource::ManifestRustVersion,
                RawToolchainSource::PinnedStable => ToolchainSource::PinnedStable,
                RawToolchainSource::PinnedNightly => ToolchainSource::PinnedNightly,
                RawToolchainSource::BuildRs => ToolchainSource::BuildRs,
            };
            let scopes = self.scopes(&format!("{location}.scopes"), raw.scopes);
            let Some(id) = id else {
                continue;
            };
            if toolchains.contains_key(&id) {
                self.error(format!("{location}.id"), format!("duplicate toolchain ID `{id}`"));
                continue;
            }
            if source != ToolchainSource::BuildRs {
                if let Some(previous) = standard_sources.insert(source, id.clone()) {
                    self.error(
                        format!("{location}.source"),
                        format!("source is already used by standard toolchain `{previous}`"),
                    );
                }
            }
            toolchains.insert(id, Toolchain { source, scopes });
        }
        toolchains
    }

    fn miri_models(&mut self, raw_models: Vec<RawMiriModel>) -> BTreeMap<Id, MiriModel> {
        if raw_models.is_empty() {
            self.error("miri_models", "category cannot be empty");
        }

        let mut models = BTreeMap::new();
        let mut flag_sets = BTreeMap::new();
        for (index, raw) in raw_models.into_iter().enumerate() {
            let location = format!("miri_models[{index}]");
            let Some(id) = self.id(&format!("{location}.id"), &raw.id) else {
                continue;
            };
            for (flag_index, flag) in raw.flags.iter().enumerate() {
                if flag.is_empty()
                    || !flag.starts_with('-')
                    || flag
                        .chars()
                        .any(|character| character.is_whitespace() || character.is_control())
                {
                    self.error(
                        format!("{location}.flags[{flag_index}]"),
                        "each Miri flag must be one non-empty argument beginning with `-` and containing no whitespace or control characters",
                    );
                }
            }
            if models.contains_key(&id) {
                self.error(format!("{location}.id"), format!("duplicate Miri-model ID `{id}`"));
                continue;
            }
            if let Some(previous) = flag_sets.insert(raw.flags.clone(), id.clone()) {
                self.error(
                    format!("{location}.flags"),
                    format!("flags duplicate Miri model `{previous}` and would repeat work"),
                );
            }
            models.insert(id, MiriModel { flags: raw.flags });
        }
        models
    }

    fn miri(&mut self, raw: RawMiri) -> Miri {
        let toolchain = self
            .id("miri.toolchain", &raw.toolchain)
            .unwrap_or_else(|| Id("invalid-miri-toolchain".to_owned()));
        let event_category = match raw.event_category {
            RawEventCategory::Reduced => EventCategory::Reduced,
            RawEventCategory::Full => EventCategory::Full,
        };
        let scopes = self.scopes("miri.scopes", raw.scopes);
        Miri { toolchain, event_category, scopes }
    }

    fn semver(&mut self, raw: RawSemver) -> Semver {
        let package = self
            .id("semver.package", &raw.package)
            .unwrap_or_else(|| Id("invalid-semver-package".to_owned()));
        let toolchain = self
            .id("semver.toolchain", &raw.toolchain)
            .unwrap_or_else(|| Id("invalid-semver-toolchain".to_owned()));
        let profile = self
            .id("semver.profile", &raw.profile)
            .unwrap_or_else(|| Id("invalid-semver-profile".to_owned()));
        let target_set = self
            .id("semver.target_set", &raw.target_set)
            .unwrap_or_else(|| Id("invalid-semver-target-set".to_owned()));
        let mut waivers = BTreeMap::new();
        for (index, raw) in raw.waivers.into_iter().enumerate() {
            let location = format!("semver.waivers[{index}]");
            let Some(target) = self.id(&format!("{location}.target"), &raw.target) else {
                continue;
            };
            if !is_issue_reference(&raw.issue) {
                self.error(
                    format!("{location}.issue"),
                    format!("`{}` is not an issue reference such as `#1565`", raw.issue),
                );
            }
            if raw.reason.trim().is_empty() {
                self.error(format!("{location}.reason"), "waiver reason cannot be empty");
            }
            if waivers.contains_key(&target) {
                self.error(
                    format!("{location}.target"),
                    format!("duplicate semver waiver for target `{target}`"),
                );
                continue;
            }
            waivers.insert(target, SemverWaiver { issue: raw.issue, reason: raw.reason });
        }
        Semver { package, toolchain, profile, target_set, waivers }
    }

    fn baselines(&mut self, raw: RawBaselines) -> Option<Baselines> {
        let manifest = self.repo_path("baselines.manifest", &raw.manifest);
        let build_reduced = self.repo_path("baselines.build_reduced", &raw.build_reduced);
        let build_full = self.repo_path("baselines.build_full", &raw.build_full);
        let miri_reduced = self.repo_path("baselines.miri_reduced", &raw.miri_reduced);
        let miri_full = self.repo_path("baselines.miri_full", &raw.miri_full);
        let logical_obligations =
            self.repo_path("baselines.logical_obligations", &raw.logical_obligations);
        let standalone_obligations =
            self.repo_path("baselines.standalone_obligations", &raw.standalone_obligations);
        let command_goldens = self.repo_path("baselines.command_goldens", &raw.command_goldens);

        let paths = [
            manifest.as_ref(),
            build_reduced.as_ref(),
            build_full.as_ref(),
            miri_reduced.as_ref(),
            miri_full.as_ref(),
            logical_obligations.as_ref(),
            standalone_obligations.as_ref(),
            command_goldens.as_ref(),
        ];
        let mut distinct = BTreeSet::new();
        for path in paths.into_iter().flatten() {
            if !distinct.insert(path.clone()) {
                self.error(
                    "baselines",
                    format!(
                        "baseline path `{}` is assigned more than once",
                        path.as_path().display()
                    ),
                );
            }
        }

        Some(Baselines {
            manifest: manifest?,
            build_reduced: build_reduced?,
            build_full: build_full?,
            miri_reduced: miri_reduced?,
            miri_full: miri_full?,
            logical_obligations: logical_obligations?,
            standalone_obligations: standalone_obligations?,
            command_goldens: command_goldens?,
        })
    }

    fn validate_limits(&mut self, limits: &Limits) {
        if !(1..=GITHUB_MAX_MATRIX_CELLS).contains(&limits.max_matrix_cells) {
            self.error(
                "limits.max_matrix_cells",
                format!("must be between 1 and GitHub's hard limit of {GITHUB_MAX_MATRIX_CELLS}"),
            );
        }
        if !(1..=MAX_PLAN_CELLS).contains(&limits.max_plan_cells) {
            self.error(
                "limits.max_plan_cells",
                format!("must be between 1 and the hard safety bound of {MAX_PLAN_CELLS}"),
            );
        }
        if !(1..=GITHUB_MAX_JOB_OUTPUT_UTF16_BYTES).contains(&limits.max_job_output_utf16_bytes) {
            self.error(
                "limits.max_job_output_utf16_bytes",
                format!(
                    "must be between 1 and the safe GitHub bound of {GITHUB_MAX_JOB_OUTPUT_UTF16_BYTES}"
                ),
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_references(
        &mut self,
        profiles: &BTreeMap<Id, FeatureProfile>,
        packages: &BTreeMap<Id, Package>,
        targets: &BTreeMap<Id, Target>,
        target_sets: &BTreeMap<Id, BTreeSet<Id>>,
        toolchains: &BTreeMap<Id, Toolchain>,
        miri_models: &BTreeMap<Id, MiriModel>,
        miri: &Miri,
        semver: &Semver,
        limits: &Limits,
    ) {
        let mut package_profiles = BTreeSet::new();
        for (package_id, package) in packages {
            for profile in &package.profiles {
                if !profiles.contains_key(profile) {
                    self.error(
                        format!("packages.{package_id}.profiles"),
                        format!("unknown feature profile `{profile}`"),
                    );
                }
                package_profiles.insert(profile.clone());
            }
        }
        for profile in profiles.keys() {
            if !package_profiles.contains(profile) {
                self.error(
                    format!("feature_profiles.{profile}"),
                    "feature profile is not valid for any package",
                );
            }
        }

        let mut targets_in_sets = BTreeSet::new();
        for (set_id, members) in target_sets {
            for target in members {
                if targets.contains_key(target) {
                    targets_in_sets.insert(target.clone());
                } else {
                    self.error(
                        format!("target_sets.{set_id}.members"),
                        format!("unknown target `{target}`"),
                    );
                }
            }
        }
        for target in targets.keys() {
            if !targets_in_sets.contains(target) {
                self.error(format!("targets.{target}"), "target is not selected by any target set");
            }
        }

        for source in [
            ToolchainSource::ManifestRustVersion,
            ToolchainSource::PinnedStable,
            ToolchainSource::PinnedNightly,
        ] {
            if !toolchains.values().any(|toolchain| toolchain.source == source) {
                self.error(
                    "toolchains",
                    format!("no standard toolchain uses source `{}`", source.description()),
                );
            }
        }

        // Count every Cartesian product before constructing its cells. For a
        // valid policy these counts are exact: later validation rejects
        // dangling references, invalid package/profile pairs, and overlapping
        // scopes. An invalid policy can only make these counts conservative,
        // which is safe because that policy will be rejected regardless.
        // Cache each target-set cardinality so that many scopes which name the
        // same set cannot turn the preflight itself into repeated expansion.
        let full_target_counts = target_sets
            .iter()
            .map(|(id, members)| (id.clone(), u64::try_from(members.len()).unwrap_or(u64::MAX)))
            .collect::<BTreeMap<_, _>>();
        let reduced_target_counts = target_sets
            .iter()
            .map(|(id, members)| {
                let count = members
                    .iter()
                    .filter(|target| {
                        targets.get(*target).is_some_and(|target| target.pr_eligible())
                    })
                    .count();
                (id.clone(), u64::try_from(count).unwrap_or(u64::MAX))
            })
            .collect::<BTreeMap<_, _>>();
        let full_build_cell_count = toolchains.values().fold(0u64, |count, toolchain| {
            count.saturating_add(Self::scope_cell_count(&toolchain.scopes, &full_target_counts))
        });
        let reduced_build_cell_count = toolchains.values().fold(0u64, |count, toolchain| {
            count.saturating_add(Self::scope_cell_count(&toolchain.scopes, &reduced_target_counts))
        });
        let miri_logical_cell_count = Self::scope_cell_count(&miri.scopes, &full_target_counts);
        let miri_matrix_cell_count = miri_logical_cell_count
            .saturating_mul(u64::try_from(miri_models.len()).unwrap_or(u64::MAX));
        // The coverage proof below compares the selected Miri cells with the
        // complete required universe. Count that universe without constructing
        // it: malformed policy may make the missing Cartesian product much
        // larger than the selected scopes which `max_plan_cells` bounds.
        let required_miri_cell_count = miri_coverage_cell_count(
            packages.values().map(|package| package.profiles.len()),
            targets.values().filter(|target| target.miri_eligible).count(),
        );
        let (reduced_miri_cell_count, full_miri_cell_count) = match miri.event_category {
            EventCategory::Reduced => (miri_matrix_cell_count, 0),
            EventCategory::Full => (0, miri_matrix_cell_count),
        };
        // Semver has its own matrix, but its target membership is the matching
        // ordinary-build slice: full events select the complete configured set,
        // while reduced events keep only targets marked `pr_eligible`. Keep
        // this preflight coordinated with `plan::enumerate_semver_candidates`.
        // Counting it here ensures a limit which can admit only the two Cargo
        // matrices fails during policy validation rather than later planning.
        let full_semver_cell_count = target_sets
            .get(&semver.target_set)
            .map_or(0, |members| u64::try_from(members.len()).unwrap_or(u64::MAX));
        let reduced_semver_cell_count = target_sets.get(&semver.target_set).map_or(0, |members| {
            u64::try_from(
                members
                    .iter()
                    .filter(|target| {
                        targets.get(*target).is_some_and(|target| target.pr_eligible())
                    })
                    .count(),
            )
            .unwrap_or(u64::MAX)
        });
        let reduced_event_cell_count = reduced_build_cell_count
            .saturating_add(reduced_miri_cell_count)
            .saturating_add(reduced_semver_cell_count);
        let full_event_cell_count = full_build_cell_count
            .saturating_add(full_miri_cell_count)
            .saturating_add(full_semver_cell_count);
        self.check_plan_size("reduced-event", reduced_event_cell_count, limits);
        self.check_plan_size("full-event", full_event_cell_count, limits);

        // `max_plan_cells` is not trusted until this validator succeeds. Cap
        // allocation at the hard limit even when the configured value is
        // invalidly large. Bound the two raw expansions independently too: an
        // invalid empty Miri-model list would otherwise multiply a large Miri
        // scope by zero and hide the allocation from the event counts.
        let materialization_limit = limits.max_plan_cells.min(MAX_PLAN_CELLS);
        if full_build_cell_count > materialization_limit
            || miri_logical_cell_count > materialization_limit
            || reduced_event_cell_count > materialization_limit
            || full_event_cell_count > materialization_limit
        {
            return;
        }

        let mut used_target_sets = BTreeSet::new();
        let mut build_cells = BTreeSet::new();
        for (toolchain_id, toolchain) in toolchains {
            for scope in &toolchain.scopes {
                used_target_sets.insert(scope.target_set.clone());
            }
            let cells = self.expand_scopes(
                &format!("toolchains.{toolchain_id}.scopes"),
                &toolchain.scopes,
                profiles,
                packages,
                targets,
                target_sets,
                false,
            );
            build_cells.extend(cells.into_iter().map(|(package, profile, target)| {
                (toolchain_id.clone(), package, profile, target)
            }));
        }

        for (package_id, package) in packages {
            for profile in &package.profiles {
                if !build_cells.iter().any(|(_, package, cell_profile, _)| {
                    package == package_id && cell_profile == profile
                }) {
                    self.error(
                        format!("packages.{package_id}.profiles"),
                        format!(
                            "profile `{profile}` is never selected by an ordinary toolchain scope"
                        ),
                    );
                }
            }
        }
        for target in targets.keys() {
            if !build_cells.iter().any(|(_, _, _, cell_target)| cell_target == target) {
                self.error(
                    format!("targets.{target}"),
                    "target is never selected by an ordinary toolchain scope",
                );
            }
        }
        if let Some(toolchain) = toolchains.get(&miri.toolchain) {
            if toolchain.source != ToolchainSource::PinnedNightly {
                self.error(
                    "miri.toolchain",
                    format!(
                        "toolchain `{}` does not use the pinned-nightly Cargo metadata source",
                        miri.toolchain
                    ),
                );
            }
        } else {
            self.error("miri.toolchain", format!("unknown toolchain `{}`", miri.toolchain));
        }
        for scope in &miri.scopes {
            used_target_sets.insert(scope.target_set.clone());
        }
        let miri_cells = self.expand_scopes(
            "miri.scopes",
            &miri.scopes,
            profiles,
            packages,
            targets,
            target_sets,
            true,
        );
        // `expand_scopes` admits only existing packages, profiles declared by
        // those packages, and existing Miri-eligible targets. Its BTreeSet also
        // makes the selected cells distinct. The selected set is therefore a
        // subset of the required Cartesian universe, so equal cardinality is
        // equivalent to complete coverage. Do not restore a traversal of the
        // missing universe here: malformed policy can make it arbitrarily
        // larger than the selected scopes and produce one allocation per cell.
        let selected_miri_cell_count = u64::try_from(miri_cells.len()).unwrap_or(u64::MAX);
        if selected_miri_cell_count != required_miri_cell_count {
            self.error(
                "miri.scopes",
                format!(
                    "Miri scopes select {selected_miri_cell_count} of {required_miri_cell_count} required Miri-eligible package/profile/target cells"
                ),
            );
        }

        used_target_sets.insert(semver.target_set.clone());
        self.validate_semver(semver, profiles, packages, targets, target_sets, toolchains);

        for target_set in target_sets.keys() {
            if !used_target_sets.contains(target_set) {
                self.error(format!("target_sets.{target_set}"), "target set is never referenced");
            }
        }
    }

    fn scope_cell_count(scopes: &[Scope], target_counts: &BTreeMap<Id, u64>) -> u64 {
        scopes.iter().fold(0, |count, scope| {
            let target_count = target_counts.get(&scope.target_set).copied().unwrap_or(0);
            count.saturating_add(cartesian_cell_count(
                scope.packages.len(),
                scope.profiles.len(),
                target_count,
            ))
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn expand_scopes(
        &mut self,
        location: &str,
        scopes: &[Scope],
        profiles: &BTreeMap<Id, FeatureProfile>,
        packages: &BTreeMap<Id, Package>,
        targets: &BTreeMap<Id, Target>,
        target_sets: &BTreeMap<Id, BTreeSet<Id>>,
        require_miri_eligible: bool,
    ) -> BTreeSet<(Id, Id, Id)> {
        let mut cells = BTreeMap::new();
        for (scope_index, scope) in scopes.iter().enumerate() {
            let scope_location = format!("{location}[{scope_index}]");
            for package in &scope.packages {
                if !packages.contains_key(package) {
                    self.error(
                        format!("{scope_location}.packages"),
                        format!("unknown package `{package}`"),
                    );
                }
            }
            for profile in &scope.profiles {
                if !profiles.contains_key(profile) {
                    self.error(
                        format!("{scope_location}.profiles"),
                        format!("unknown feature profile `{profile}`"),
                    );
                }
            }
            let Some(scope_targets) = target_sets.get(&scope.target_set) else {
                self.error(
                    format!("{scope_location}.target_set"),
                    format!("unknown target set `{}`", scope.target_set),
                );
                continue;
            };

            for package in &scope.packages {
                let Some(package_policy) = packages.get(package) else {
                    continue;
                };
                for profile in &scope.profiles {
                    if !package_policy.profiles.contains(profile) {
                        self.error(
                            format!("{scope_location}.profiles"),
                            format!("profile `{profile}` is not valid for package `{package}`"),
                        );
                        continue;
                    }
                    for target in scope_targets {
                        let Some(target_policy) = targets.get(target) else {
                            continue;
                        };
                        if require_miri_eligible && !target_policy.miri_eligible {
                            self.error(
                                format!("{scope_location}.target_set"),
                                format!("target `{target}` is not marked Miri-eligible"),
                            );
                            continue;
                        }
                        let cell = (package.clone(), profile.clone(), target.clone());
                        if let Some(previous_scope) = cells.insert(cell.clone(), scope_index) {
                            self.error(
                                &scope_location,
                                format!(
                                    "cell `{package}/{profile}/{target}` overlaps scope {previous_scope} and would run twice"
                                ),
                            );
                        }
                    }
                }
            }
        }
        cells.into_keys().collect()
    }

    fn check_plan_size(&mut self, name: &str, count: u64, limits: &Limits) {
        if count > limits.max_plan_cells {
            self.error(
                "limits.max_plan_cells",
                format!(
                    "{name} plan expands to {count} cells before sharding, above the configured limit of {}",
                    limits.max_plan_cells
                ),
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_semver(
        &mut self,
        semver: &Semver,
        profiles: &BTreeMap<Id, FeatureProfile>,
        packages: &BTreeMap<Id, Package>,
        targets: &BTreeMap<Id, Target>,
        target_sets: &BTreeMap<Id, BTreeSet<Id>>,
        toolchains: &BTreeMap<Id, Toolchain>,
    ) {
        let package = packages.get(&semver.package);
        if package.is_none() {
            self.error("semver.package", format!("unknown package `{}`", semver.package));
        }
        match profiles.get(&semver.profile) {
            None => self.error(
                "semver.profile",
                format!("unknown feature profile `{}`", semver.profile),
            ),
            Some(FeatureProfile::StableAggregate) => {}
            Some(_) => self.error(
                "semver.profile",
                format!(
                    "profile `{}` must select the stable aggregate because nightly-only API has no compatibility guarantee",
                    semver.profile
                ),
            ),
        }
        if let Some(package) = package {
            if !package.profiles.contains(&semver.profile) {
                self.error(
                    "semver.profile",
                    format!(
                        "profile `{}` is not valid for package `{}`",
                        semver.profile, semver.package
                    ),
                );
            }
        }
        let toolchain = toolchains.get(&semver.toolchain);
        match toolchain {
            None => {
                self.error("semver.toolchain", format!("unknown toolchain `{}`", semver.toolchain))
            }
            Some(toolchain) if toolchain.source != ToolchainSource::PinnedStable => self.error(
                "semver.toolchain",
                format!(
                    "toolchain `{}` does not use the pinned-stable Cargo metadata source",
                    semver.toolchain
                ),
            ),
            Some(_) => {}
        }
        let selected_targets = target_sets.get(&semver.target_set);
        if selected_targets.is_none() {
            self.error("semver.target_set", format!("unknown target set `{}`", semver.target_set));
        }

        if let (Some(toolchain), Some(selected_targets)) = (toolchain, selected_targets) {
            for target in selected_targets {
                if !toolchain_selects(
                    toolchain,
                    &semver.package,
                    &semver.profile,
                    target,
                    target_sets,
                ) {
                    self.error(
                        "semver.target_set",
                        format!(
                            "toolchain `{}` does not build `{}/{}/{target}`, so semver cannot reuse that matrix cell",
                            semver.toolchain, semver.package, semver.profile
                        ),
                    );
                }
            }
        }

        for target in semver.waivers.keys() {
            if !targets.contains_key(target) {
                self.error("semver.waivers", format!("unknown target `{target}`"));
            }
        }

        if let Some(selected_targets) = selected_targets {
            for (target_id, target) in targets {
                let selected = selected_targets.contains(target_id);
                let waived = semver.waivers.contains_key(target_id);
                if target.semver_eligible {
                    match (selected, waived) {
                        (false, false) => self.error(
                            "semver.target_set",
                            format!(
                                "semver-eligible target `{target_id}` is neither selected nor waived"
                            ),
                        ),
                        (true, true) => self.error(
                            "semver.waivers",
                            format!("target `{target_id}` is both selected and waived"),
                        ),
                        (true, false) | (false, true) => {}
                    }
                } else {
                    if selected {
                        self.error(
                            "semver.target_set",
                            format!(
                                "target `{target_id}` is selected but is not marked semver-eligible"
                            ),
                        );
                    }
                    if waived {
                        self.error(
                            "semver.waivers",
                            format!(
                                "target `{target_id}` is waived but is not marked semver-eligible"
                            ),
                        );
                    }
                }
            }
        }
    }
}

fn cartesian_cell_count(packages: usize, profiles: usize, targets: u64) -> u64 {
    u64::try_from(packages)
        .unwrap_or(u64::MAX)
        .saturating_mul(u64::try_from(profiles).unwrap_or(u64::MAX))
        .saturating_mul(targets)
}

fn miri_coverage_cell_count(
    package_profile_counts: impl IntoIterator<Item = usize>,
    miri_eligible_targets: usize,
) -> u64 {
    package_profile_counts
        .into_iter()
        .fold(0u64, |count, profiles| {
            count.saturating_add(u64::try_from(profiles).unwrap_or(u64::MAX))
        })
        .saturating_mul(u64::try_from(miri_eligible_targets).unwrap_or(u64::MAX))
}

fn escape_control_characters(value: String) -> String {
    let mut escaped = String::new();
    for character in value.chars() {
        if character.is_control() {
            escaped.extend(character.escape_default());
        } else {
            escaped.push(character);
        }
    }
    escaped
}

impl ToolchainSource {
    fn description(self) -> &'static str {
        match self {
            Self::ManifestRustVersion => "manifest-rust-version",
            Self::PinnedStable => "pinned-stable",
            Self::PinnedNightly => "pinned-nightly",
            Self::BuildRs => "build-rs",
        }
    }
}

fn toolchain_selects(
    toolchain: &Toolchain,
    package: &Id,
    profile: &Id,
    target: &Id,
    target_sets: &BTreeMap<Id, BTreeSet<Id>>,
) -> bool {
    toolchain.scopes.iter().any(|scope| {
        scope.packages.contains(package)
            && scope.profiles.contains(profile)
            && target_sets.get(&scope.target_set).is_some_and(|targets| targets.contains(target))
    })
}

fn is_issue_reference(issue: &str) -> bool {
    issue.strip_prefix('#').is_some_and(|number| {
        !number.is_empty() && number.bytes().all(|byte| byte.is_ascii_digit())
    })
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeSet, path::PathBuf};

    use super::{
        miri_coverage_cell_count, EventCategory, FeatureProfile, Policy, PolicyError,
        ReadPolicyError, TargetMode, ToolchainSource, ValidationErrors,
    };

    const REPOSITORY_POLICY: &str = include_str!("../../../ci/zc.toml");
    const BUILD_REDUCED_BASELINE: &str = include_str!("../../../ci/baselines/build-pr.tsv");
    const BUILD_FULL_BASELINE: &str = include_str!("../../../ci/baselines/build-full.tsv");
    const MIRI_REDUCED_BASELINE: &str = include_str!("../../../ci/baselines/miri-pr.tsv");
    const MIRI_FULL_BASELINE: &str = include_str!("../../../ci/baselines/miri-full.tsv");
    const UNKNOWN_KEY: &str = include_str!("../testdata/policy-unknown-key.toml");
    const INVALID_MULTIPLE: &str = include_str!("../testdata/policy-invalid-multiple.toml");
    const INVALID_MULTIPLE_DIAGNOSTICS: &str =
        include_str!("../testdata/policy-invalid-multiple.stderr");

    fn id(value: &str) -> super::Id {
        super::Id(value.to_owned())
    }

    fn mutate(source: &str, needle: &str, replacement: &str) -> String {
        assert!(source.contains(needle), "mutation needle not found: {needle}");
        source.replacen(needle, replacement, 1)
    }

    fn validation_errors(source: &str) -> ValidationErrors {
        match Policy::parse(source).unwrap_err() {
            PolicyError::Invalid(errors) => errors,
            PolicyError::Toml(error) => panic!("expected semantic errors, got TOML error: {error}"),
        }
    }

    fn invalid(source: &str) -> String {
        validation_errors(source).to_string()
    }

    fn baseline_rows(source: &str, header: &str) -> BTreeSet<String> {
        source
            .lines()
            .filter(|line| !line.is_empty() && !line.starts_with('#') && *line != header)
            .map(str::to_owned)
            .collect()
    }

    fn assert_invalid_contains(source: &str, expected: &[&str]) {
        let rendered = invalid(source);
        for expected in expected {
            assert!(
                rendered.contains(expected),
                "expected `{expected}` in validation errors:\n{rendered}"
            );
        }
    }

    #[test]
    fn repository_policy_models_the_frozen_matrix() {
        let policy = Policy::parse(REPOSITORY_POLICY).unwrap();

        assert_eq!(policy.schema_version(), 1);
        assert_eq!(policy.packages().len(), 2);
        assert_eq!(policy.targets().len(), 11);
        assert_eq!(policy.toolchains().len(), 11);
        assert_eq!(policy.miri_models().len(), 2);
        assert_eq!(policy.features().profiles().len(), 3);
        assert_eq!(
            policy.features().stable_feature_root().as_str(),
            "__internal_use_only_features_that_work_on_stable"
        );
        assert_eq!(
            policy.features().profiles().get(&id("default")),
            Some(&FeatureProfile::Default)
        );
        assert_eq!(
            policy.features().profiles().get(&id("stable")),
            Some(&FeatureProfile::StableAggregate)
        );
        assert_eq!(policy.features().profiles().get(&id("all")), Some(&FeatureProfile::All));

        let thumb = policy.targets().get(&id("thumbv6m-none-eabi")).unwrap();
        assert_eq!(thumb.mode(), TargetMode::Thumb);
        assert!(!thumb.pr_eligible());
        assert!(!thumb.miri_eligible());
        assert!(!thumb.semver_eligible());
        assert_eq!(
            policy.toolchains().get(&id("nightly")).unwrap().source(),
            ToolchainSource::PinnedNightly
        );

        let mut build_cells = BTreeSet::new();
        for (toolchain_id, toolchain) in policy.toolchains() {
            for scope in toolchain.scopes() {
                let targets = &policy.target_sets()[scope.target_set()];
                for package in scope.packages() {
                    for profile in scope.profiles() {
                        for target in targets {
                            build_cells
                                .insert(format!("{package}\t{toolchain_id}\t{profile}\t{target}"));
                        }
                    }
                }
            }
        }
        assert_eq!(build_cells.len(), 182);
        assert_eq!(
            build_cells,
            baseline_rows(BUILD_FULL_BASELINE, "crate\ttoolchain\tfeature_profile\ttarget")
        );
        let reduced_build_cells = build_cells
            .iter()
            .filter(|cell| {
                let target = cell.rsplit('\t').next().unwrap();
                policy.targets()[target].pr_eligible()
            })
            .cloned()
            .collect::<BTreeSet<_>>();
        assert_eq!(reduced_build_cells.len(), 60);
        assert_eq!(
            reduced_build_cells,
            baseline_rows(BUILD_REDUCED_BASELINE, "crate\ttoolchain\tfeature_profile\ttarget")
        );

        let mut miri_cells = BTreeSet::new();
        for scope in policy.miri().scopes() {
            let targets = &policy.target_sets()[scope.target_set()];
            for package in scope.packages() {
                for profile in scope.profiles() {
                    for target in targets {
                        for (model_id, model) in policy.miri_models() {
                            let flags = if model.flags().is_empty() {
                                "<none>".to_owned()
                            } else {
                                model.flags().join(" ")
                            };
                            miri_cells.insert(format!(
                                "{package}\t{}\t{profile}\t{target}\t{model_id}\t{flags}",
                                policy.miri().toolchain()
                            ));
                        }
                    }
                }
            }
        }
        assert_eq!(policy.miri().event_category(), EventCategory::Full);
        assert_eq!(miri_cells.len(), 64);
        assert_eq!(
            miri_cells,
            baseline_rows(
                MIRI_FULL_BASELINE,
                "crate\ttoolchain\tfeature_profile\ttarget\tmiri_model\tmiri_model_flags"
            )
        );
        assert_eq!(
            baseline_rows(
                MIRI_REDUCED_BASELINE,
                "crate\ttoolchain\tfeature_profile\ttarget\tmiri_model\tmiri_model_flags"
            ),
            BTreeSet::new()
        );

        assert_eq!(policy.target_sets()[policy.semver().target_set()].len(), 9);
        let wasm_waiver = policy.semver().waivers().get(&id("wasm32-unknown-unknown")).unwrap();
        assert_eq!(wasm_waiver.issue(), "#1565");
    }

    #[test]
    fn event_lookup_fails_closed() {
        let policy = Policy::parse(REPOSITORY_POLICY).unwrap();

        assert_eq!(policy.events().category("pull_request"), Some(EventCategory::Reduced));
        assert_eq!(policy.events().category("merge_group"), Some(EventCategory::Full));
        assert_eq!(policy.events().category("unrecognized"), None);
    }

    #[test]
    fn rejects_unknown_keys_in_every_table_shape() {
        assert!(matches!(Policy::parse(UNKNOWN_KEY), Err(PolicyError::Toml(_))));

        let mutations = [
            (
                "events",
                "reduced = [\"pull_request\"]",
                "reduced = [\"pull_request\"]\nunexpected = true",
            ),
            (
                "features",
                "stable_feature_root = \"__internal_use_only_features_that_work_on_stable\"",
                "stable_feature_root = \"__internal_use_only_features_that_work_on_stable\"\nunexpected = true",
            ),
            (
                "feature profile",
                "selection = \"default\"",
                "selection = \"default\"\nunexpected = true",
            ),
            (
                "package",
                "manifest = \"zerocopy/Cargo.toml\"",
                "manifest = \"zerocopy/Cargo.toml\"\nunexpected = true",
            ),
            (
                "target",
                "id = \"i686-unknown-linux-gnu\"\nmode = \"native\"",
                "id = \"i686-unknown-linux-gnu\"\nmode = \"native\"\nunexpected = true",
            ),
            (
                "target set",
                "id = \"all\"\nselection = \"all\"",
                "id = \"all\"\nunexpected = true\nselection = \"all\"",
            ),
            (
                "toolchain",
                "source = \"manifest-rust-version\"",
                "source = \"manifest-rust-version\"\nunexpected = true",
            ),
            (
                "toolchain scope",
                "packages = [\"zerocopy\"]\nprofiles = [\"default\"]\ntarget_set = \"all\"",
                "packages = [\"zerocopy\"]\nprofiles = [\"default\"]\ntarget_set = \"all\"\nunexpected = true",
            ),
            (
                "Miri model",
                "id = \"stacked\"\nflags = []",
                "id = \"stacked\"\nflags = []\nunexpected = true",
            ),
            (
                "Miri",
                "[miri]\ntoolchain = \"nightly\"\nevent_category = \"full\"",
                "[miri]\ntoolchain = \"nightly\"\nevent_category = \"full\"\nunexpected = true",
            ),
            (
                "Miri scope",
                "profiles = [\"default\", \"stable\", \"all\"]\ntarget_set = \"miri-supported\"",
                "profiles = [\"default\", \"stable\", \"all\"]\ntarget_set = \"miri-supported\"\nunexpected = true",
            ),
            (
                "semver",
                "profile = \"stable\"\ntarget_set = \"semver\"",
                "profile = \"stable\"\ntarget_set = \"semver\"\nunexpected = true",
            ),
            (
                "semver waiver",
                "issue = \"#1565\"\nreason =",
                "issue = \"#1565\"\nunexpected = true\nreason =",
            ),
            (
                "baselines",
                "manifest = \"ci/baselines/manifest.tsv\"",
                "manifest = \"ci/baselines/manifest.tsv\"\nunexpected = true",
            ),
            (
                "limits",
                "max_matrix_cells = 256",
                "max_matrix_cells = 256\nunexpected = true",
            ),
        ];

        for (name, needle, replacement) in mutations {
            let source = mutate(REPOSITORY_POLICY, needle, replacement);
            let error = Policy::parse(&source).unwrap_err();
            assert!(
                matches!(error, PolicyError::Toml(_)),
                "unknown key in {name} was not rejected during parsing: {error}"
            );
            assert!(error.to_string().contains("unknown field"));
        }
    }

    #[test]
    fn reports_independent_semantic_errors_in_a_stable_order() {
        assert_eq!(invalid(INVALID_MULTIPLE), INVALID_MULTIPLE_DIAGNOSTICS);
    }

    #[test]
    fn rejects_unsupported_schema_versions() {
        let source = mutate(REPOSITORY_POLICY, "schema_version = 1", "schema_version = 2");
        assert_invalid_contains(&source, &["unsupported schema version 2"]);
    }

    #[test]
    fn rejects_unstable_identifiers_and_unsafe_paths() {
        for invalid_id in ["Uppercase", "has/slash", "has space", ".leading"] {
            let source = mutate(
                REPOSITORY_POLICY,
                "reduced = [\"pull_request\"]",
                &format!("reduced = [\"{invalid_id}\"]"),
            );
            assert_invalid_contains(&source, &["is not a stable identifier"]);
        }

        let escaped = mutate(
            REPOSITORY_POLICY,
            "reduced = [\"pull_request\"]",
            "reduced = [\"pull_\\u001Brequest\"]",
        );
        assert!(!Policy::parse(&escaped).unwrap_err().to_string().contains('\u{001b}'));

        for unsafe_path in [
            "/absolute.toml",
            "../outside.toml",
            "./manifest.toml",
            "dir/./manifest.toml",
            "dir/.",
            "dir//manifest.toml",
            "dir\\manifest.toml",
            "C:/manifest.toml",
        ] {
            let source = mutate(
                REPOSITORY_POLICY,
                "manifest = \"zerocopy/Cargo.toml\"",
                &format!("manifest = '{unsafe_path}'"),
            );
            assert_invalid_contains(&source, &["is not a safe repository-relative path"]);
        }
    }

    #[test]
    fn rejects_duplicates_empty_selections_and_dangling_references() {
        let duplicate = mutate(
            REPOSITORY_POLICY,
            "id = \"stable\"\nselection = \"stable-aggregate\"",
            "id = \"default\"\nselection = \"stable-aggregate\"",
        );
        assert_invalid_contains(&duplicate, &["duplicate profile ID `default`"]);

        let empty = mutate(
            REPOSITORY_POLICY,
            "profiles = [\"default\", \"stable\", \"all\"]",
            "profiles = []",
        );
        assert_invalid_contains(&empty, &["selection cannot be empty"]);

        let dangling = mutate(
            REPOSITORY_POLICY,
            "manifest = \"zerocopy/zerocopy-derive/Cargo.toml\"\nprofiles = [\"default\"]",
            "manifest = \"zerocopy/zerocopy-derive/Cargo.toml\"\nprofiles = [\"missing\"]",
        );
        assert_invalid_contains(&dangling, &["unknown feature profile `missing`"]);
    }

    #[test]
    fn rejects_overlapping_events_and_scope_products() {
        let events = mutate(
            REPOSITORY_POLICY,
            "full = [\"merge_group\", \"push\", \"workflow_dispatch\"]",
            "full = [\"pull_request\", \"merge_group\", \"push\"]",
        );
        assert_invalid_contains(&events, &["appears in both reduced and full"]);

        let scopes = mutate(
            REPOSITORY_POLICY,
            "profiles = [\"stable\", \"all\"]\ntarget_set = \"without-thumb\"",
            "profiles = [\"default\"]\ntarget_set = \"all\"",
        );
        assert_invalid_contains(&scopes, &["overlaps scope 0 and would run twice"]);
    }

    #[test]
    fn rejects_miri_and_semver_coverage_drift() {
        let unsupported_miri_target = mutate(
            REPOSITORY_POLICY,
            "profiles = [\"default\", \"stable\", \"all\"]\ntarget_set = \"miri-supported\"",
            "profiles = [\"default\", \"stable\", \"all\"]\ntarget_set = \"semver\"",
        );
        assert_invalid_contains(
            &unsupported_miri_target,
            &["target `riscv64gc-unknown-linux-gnu` is not marked Miri-eligible"],
        );

        let missing_miri_profile = mutate(
            REPOSITORY_POLICY,
            "profiles = [\"default\", \"stable\", \"all\"]\ntarget_set = \"miri-supported\"",
            "profiles = [\"default\", \"stable\"]\ntarget_set = \"miri-supported\"",
        );
        assert_invalid_contains(
            &missing_miri_profile,
            &["Miri scopes select 24 of 32 required Miri-eligible package/profile/target cells"],
        );

        let wrong_semver_profile = mutate(
            REPOSITORY_POLICY,
            "toolchain = \"stable\"\nprofile = \"stable\"\ntarget_set = \"semver\"",
            "toolchain = \"stable\"\nprofile = \"default\"\ntarget_set = \"semver\"",
        );
        assert_invalid_contains(
            &wrong_semver_profile,
            &["must select the stable aggregate because nightly-only API has no compatibility guarantee"],
        );

        let wrong_semver_toolchain = mutate(
            REPOSITORY_POLICY,
            "toolchain = \"stable\"\nprofile = \"stable\"\ntarget_set = \"semver\"",
            "toolchain = \"nightly\"\nprofile = \"stable\"\ntarget_set = \"semver\"",
        );
        assert_invalid_contains(
            &wrong_semver_toolchain,
            &["does not use the pinned-stable Cargo metadata source"],
        );

        let selected_and_waived = mutate(
            REPOSITORY_POLICY,
            "target = \"wasm32-unknown-unknown\"\nissue = \"#1565\"",
            "target = \"x86_64-unknown-linux-gnu\"\nissue = \"#1565\"",
        );
        assert_invalid_contains(&selected_and_waived, &["is both selected and waived"]);

        let omitted = mutate(
            REPOSITORY_POLICY,
            "id = \"semver\"\nselection = \"all\"\ninclude = []\nexclude = [\"thumbv6m-none-eabi\", \"wasm32-unknown-unknown\"]",
            "id = \"semver\"\nselection = \"all\"\ninclude = []\nexclude = [\"s390x-unknown-linux-gnu\", \"thumbv6m-none-eabi\", \"wasm32-unknown-unknown\"]",
        );
        assert_invalid_contains(&omitted, &["is neither selected nor waived"]);

        let inapplicable = mutate(
            REPOSITORY_POLICY,
            "id = \"semver\"\nselection = \"all\"\ninclude = []\nexclude = [\"thumbv6m-none-eabi\", \"wasm32-unknown-unknown\"]",
            "id = \"semver\"\nselection = \"all\"\ninclude = []\nexclude = [\"wasm32-unknown-unknown\"]",
        );
        assert_invalid_contains(&inapplicable, &["is not marked semver-eligible"]);
    }

    #[test]
    fn target_set_expressions_reject_redundant_or_ineffective_changes() {
        let redundant = mutate(
            REPOSITORY_POLICY,
            "id = \"all\"\nselection = \"all\"\ninclude = []",
            "id = \"all\"\nselection = \"all\"\ninclude = [\"x86_64-unknown-linux-gnu\"]",
        );
        assert_invalid_contains(&redundant, &["remove the redundant include"]);

        let ineffective = mutate(
            REPOSITORY_POLICY,
            "id = \"aarch64\"\nselection = \"explicit\"\ninclude = [\"aarch64-unknown-linux-gnu\"]\nexclude = []",
            "id = \"aarch64\"\nselection = \"explicit\"\ninclude = [\"aarch64-unknown-linux-gnu\"]\nexclude = [\"x86_64-unknown-linux-gnu\"]",
        );
        assert_invalid_contains(&ineffective, &["remove the ineffective exclude"]);

        let overlap = mutate(
            REPOSITORY_POLICY,
            "id = \"x86-linux\"\nselection = \"explicit\"\ninclude = [\"i686-unknown-linux-gnu\", \"x86_64-unknown-linux-gnu\"]\nexclude = []",
            "id = \"x86-linux\"\nselection = \"explicit\"\ninclude = [\"i686-unknown-linux-gnu\", \"x86_64-unknown-linux-gnu\"]\nexclude = [\"i686-unknown-linux-gnu\"]",
        );
        assert_invalid_contains(&overlap, &["cannot appear in both include and exclude"]);
    }

    #[test]
    fn rejects_platform_limits_and_expansions_above_policy_limits() {
        for (needle, replacement, expected) in [
            ("max_matrix_cells = 256", "max_matrix_cells = 0", "between 1"),
            ("max_matrix_cells = 256", "max_matrix_cells = 257", "hard limit of 256"),
            ("max_plan_cells = 4096", "max_plan_cells = 0", "between 1"),
            ("max_plan_cells = 4096", "max_plan_cells = 65537", "hard safety bound of 65536"),
            (
                "max_job_output_utf16_bytes = 900000",
                "max_job_output_utf16_bytes = 1000001",
                "safe GitHub bound of 1000000",
            ),
        ] {
            let source = mutate(REPOSITORY_POLICY, needle, replacement);
            assert_invalid_contains(&source, &[expected]);
        }

        let matrix_limit =
            mutate(REPOSITORY_POLICY, "max_matrix_cells = 256", "max_matrix_cells = 181");
        assert_eq!(Policy::parse(&matrix_limit).unwrap().limits().max_matrix_cells(), 181);

        let plan_limit = mutate(REPOSITORY_POLICY, "max_plan_cells = 4096", "max_plan_cells = 254");
        assert_invalid_contains(&plan_limit, &["full-event plan expands to 255 cells"]);
    }

    #[test]
    fn cartesian_cell_counts_saturate_instead_of_wrapping() {
        assert_eq!(super::cartesian_cell_count(2, 3, 5), 30);
        assert_eq!(super::cartesian_cell_count(usize::MAX, usize::MAX, 2), u64::MAX);
        assert_eq!(miri_coverage_cell_count([3, 1], 8), 32);
        assert_eq!(miri_coverage_cell_count([usize::MAX, usize::MAX], usize::MAX), u64::MAX);
    }

    #[test]
    fn miri_coverage_audit_summarizes_an_unselected_cartesian_product() {
        let extra_packages = (0..29)
            .map(|index| {
                format!(
                    "[[packages]]\nid = \"extra-{index:02}\"\nmanifest = \"extra/{index:02}/Cargo.toml\"\nprofiles = [\"default\"]\n\n"
                )
            })
            .collect::<String>();
        let source =
            mutate(REPOSITORY_POLICY, "[[targets]]", &format!("{extra_packages}[[targets]]"));
        let source = mutate(&source, "max_plan_cells = 4096", "max_plan_cells = 256");
        let errors = validation_errors(&source);

        assert!(
            errors.errors().iter().all(|error| error.location() != "limits.max_plan_cells"),
            "selected plans should remain within the configured limit: {errors}"
        );
        let miri_errors = errors
            .errors()
            .iter()
            .filter(|error| error.location() == "miri.scopes")
            .collect::<Vec<_>>();
        assert_eq!(miri_errors.len(), 1, "unexpected Miri diagnostics: {errors}");
        assert_eq!(
            miri_errors[0].message(),
            "Miri scopes select 32 of 264 required Miri-eligible package/profile/target cells"
        );
    }

    #[test]
    fn rejects_control_characters_in_miri_flags() {
        for flag in [r"-Zfoo\u0000bar", r"-Zfoo\u001Bbar"] {
            let source = mutate(
                REPOSITORY_POLICY,
                r#"flags = ["-Zmiri-tree-borrows"]"#,
                &format!(r#"flags = ["{flag}"]"#),
            );
            assert_invalid_contains(
                &source,
                &["each Miri flag must be one non-empty argument beginning with `-`"],
            );
        }
    }

    #[test]
    fn behavior_significant_lists_are_required() {
        let flags = mutate(REPOSITORY_POLICY, "flags = []\n", "");
        let flags_error = Policy::parse(&flags).unwrap_err();
        assert!(matches!(flags_error, PolicyError::Toml(_)));
        assert!(flags_error.to_string().contains("missing field `flags`"));

        for (needle, replacement) in [
            ("id = \"all\"\nselection = \"all\"\ninclude = []", "id = \"all\"\ninclude = []"),
            (
                "id = \"all\"\nselection = \"all\"\ninclude = []",
                "id = \"all\"\nselection = \"all\"",
            ),
            (
                "id = \"all\"\nselection = \"all\"\ninclude = []\nexclude = []",
                "id = \"all\"\nselection = \"all\"\ninclude = []",
            ),
        ] {
            let target_set = mutate(REPOSITORY_POLICY, needle, replacement);
            let error = Policy::parse(&target_set).unwrap_err();
            assert!(matches!(error, PolicyError::Toml(_)));
            assert!(error.to_string().contains("missing field"));
        }

        let waiver_block = r##"
[[semver.waivers]]
target = "wasm32-unknown-unknown"
issue = "#1565"
reason = "cargo-semver-checks does not yet support this target"
"##;
        let waivers = mutate(REPOSITORY_POLICY, waiver_block, "\n");
        let waivers_error = Policy::parse(&waivers).unwrap_err();
        assert!(matches!(waivers_error, PolicyError::Toml(_)));
        assert!(waivers_error.to_string().contains("missing field `waivers`"));
    }

    #[test]
    fn read_errors_retain_the_requested_path() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("testdata/policy-intentionally-does-not-exist.toml");
        let error = Policy::read(&path).unwrap_err();

        match &error {
            ReadPolicyError::Read { path: error_path, .. } => assert_eq!(error_path, &path),
            ReadPolicyError::Policy { .. } => panic!("expected a read error"),
        }
        assert!(error.to_string().contains(&path.display().to_string()));
    }
}
