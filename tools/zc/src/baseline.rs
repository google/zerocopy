// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Strict, data-only access to the frozen legacy CI baseline.
//!
//! The files in `ci/baselines` are independent review evidence. They were
//! derived from the old workflow at a pinned commit; this module deliberately
//! does not parse that workflow or regenerate its truth. A future planner can
//! instead construct the same public row types and compare exact sets. This is
//! stronger than comparing counts: one omitted obligation and one unrelated
//! addition cannot cancel each other out.
//!
//! This reader is intentionally stricter than a general TSV reader. The
//! baseline is repository-owned canonical data, so accepting alternate headers,
//! row orders, numeric spellings, JSON spellings, paths, or identifiers would
//! create needless ways for two reviews to describe the same fact. Strictness
//! also makes accidental hand edits fail near their source.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt,
    fs::{self, File},
    io::{self, Read},
    path::{Component, Path, PathBuf},
    str::FromStr,
};

const MANIFEST_HEADER: &str = "key\tvalue";
const BUILD_HEADER: &str = "crate\ttoolchain\tfeature_profile\ttarget";
const MIRI_HEADER: &str = "crate\ttoolchain\tfeature_profile\ttarget\tmiri_model\tmiri_model_flags";
const LOGICAL_HEADER: &str = "kind\tcrate\ttoolchain\tfeature_profile\ttarget\tmiri_model\tpr_occurrences\tfull_occurrences\tcondition\tsources";
const STANDALONE_HEADER: &str = "obligation\tevents\tjob\tstep\tworking_directory\tform\tpayload";
const COMMAND_GOLDEN_HEADER: &str =
    "golden\tjob\tstep\tworking_directory\tenvironment_json\tform\tpayload\tdynamic_value\tnote";

/// Paths to all files which together form one legacy baseline.
///
/// Callers should obtain these paths from the validated CI policy and join
/// them to a pinned repository root. The reader takes explicit paths rather
/// than assuming filenames so that the policy remains the authority for where
/// reviewed evidence lives.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LegacyBaselinePaths {
    pub manifest: PathBuf,
    pub build_reduced: PathBuf,
    pub build_full: PathBuf,
    pub miri_reduced: PathBuf,
    pub miri_full: PathBuf,
    pub logical_obligations: PathBuf,
    pub standalone_obligations: PathBuf,
    pub command_goldens: PathBuf,
}

/// Already-open files corresponding exactly to [`LegacyBaselinePaths`].
///
/// The checked CI boundary retains these handles while it compares file
/// identities and parses bytes. Keep the fields coordinated with
/// [`LegacyBaselinePaths`], [`LegacyBaselines::read_open`], and the bundle
/// construction in `ci.rs`; adding a baseline role requires updating all four.
pub(crate) struct LegacyBaselineFiles<'a> {
    pub manifest: &'a File,
    pub build_reduced: &'a File,
    pub build_full: &'a File,
    pub miri_reduced: &'a File,
    pub miri_full: &'a File,
    pub logical_obligations: &'a File,
    pub standalone_obligations: &'a File,
    pub command_goldens: &'a File,
}

/// One lowercase, stable identifier used by the old workflow matrices.
///
/// This deliberately matches the identifier grammar used by the typed policy.
/// Keeping path separators, whitespace, shell punctuation, and control bytes
/// out of identifiers makes them safe to carry through JSON and GitHub matrix
/// fields without adding a second interpretation layer.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct BaselineId(String);

impl BaselineId {
    /// Returns the identifier exactly as recorded in the baseline.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    fn parse(value: &str) -> Result<Self, String> {
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
        if valid {
            Ok(Self(value.to_owned()))
        } else {
            Err("must be a lowercase stable identifier using only ASCII letters, digits, `_`, `-`, or `.`".into())
        }
    }
}

impl fmt::Display for BaselineId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

impl FromStr for BaselineId {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        Self::parse(value)
    }
}

/// A canonical working directory relative to the repository root.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum WorkingDirectory {
    /// The repository root, spelled exactly `.` in the legacy files.
    RepositoryRoot,
    /// A nonempty, normalized repository-relative path.
    Relative(String),
}

impl WorkingDirectory {
    /// Parses the baseline spelling of a working directory.
    pub fn parse(value: &str) -> Result<Self, String> {
        if value == "." {
            return Ok(Self::RepositoryRoot);
        }
        validate_repo_relative_path(value)?;
        Ok(Self::Relative(value.to_owned()))
    }

    /// Returns the canonical baseline spelling.
    pub fn as_str(&self) -> &str {
        match self {
            Self::RepositoryRoot => ".",
            Self::Relative(path) => path,
        }
    }

    /// Rechecks both the spelling and its canonical enum representation.
    ///
    /// The variants are public because planned records expose this type, so a
    /// caller can construct `Relative(".")` without going through `parse`.
    /// Comparing the reparsed value, rather than merely accepting its string,
    /// prevents that alternate representation from entering a typed baseline.
    fn validate(&self) -> Result<(), String> {
        let canonical = Self::parse(self.as_str())?;
        if canonical == *self {
            Ok(())
        } else {
            Err(format!(
                "working directory `{}` must use its canonical enum representation",
                self.as_str()
            ))
        }
    }
}

/// One ordinary build matrix cell.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct BuildCell {
    package: BaselineId,
    toolchain: BaselineId,
    feature_profile: BaselineId,
    target: BaselineId,
}

impl BuildCell {
    /// Constructs a cell from already validated identifiers.
    pub fn new(
        package: BaselineId,
        toolchain: BaselineId,
        feature_profile: BaselineId,
        target: BaselineId,
    ) -> Self {
        Self { package, toolchain, feature_profile, target }
    }

    pub fn package(&self) -> &BaselineId {
        &self.package
    }

    pub fn toolchain(&self) -> &BaselineId {
        &self.toolchain
    }

    pub fn feature_profile(&self) -> &BaselineId {
        &self.feature_profile
    }

    pub fn target(&self) -> &BaselineId {
        &self.target
    }
}

/// One Miri matrix cell.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MiriCell {
    package: BaselineId,
    toolchain: BaselineId,
    feature_profile: BaselineId,
    target: BaselineId,
    model: BaselineId,
    /// Exact model-specific flags. `<none>` in the TSV becomes an empty vector.
    model_flags: Vec<String>,
}

impl MiriCell {
    /// Constructs a Miri cell, rejecting flags which cannot have canonical TSV
    /// or command-line representations.
    pub fn new(
        package: BaselineId,
        toolchain: BaselineId,
        feature_profile: BaselineId,
        target: BaselineId,
        model: BaselineId,
        model_flags: Vec<String>,
    ) -> Result<Self, String> {
        validate_model_flags(&model_flags)?;
        Ok(Self { package, toolchain, feature_profile, target, model, model_flags })
    }

    pub fn package(&self) -> &BaselineId {
        &self.package
    }

    pub fn toolchain(&self) -> &BaselineId {
        &self.toolchain
    }

    pub fn feature_profile(&self) -> &BaselineId {
        &self.feature_profile
    }

    pub fn target(&self) -> &BaselineId {
        &self.target
    }

    pub fn model(&self) -> &BaselineId {
        &self.model
    }

    pub fn model_flags(&self) -> &[String] {
        &self.model_flags
    }
}

/// A condition attached to one normalized logical obligation.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ObligationCondition {
    /// The operation runs without an additional workflow condition.
    Always,
    /// The operation runs only after all required dependencies succeed.
    Success,
    /// The operation runs when GitHub reports workflow cancellation.
    Cancelled,
    /// The operation is omitted only by the documented local escape hatch.
    UnlessSkipCargoSemverChecks,
}

/// One physical workflow location which performs a logical obligation.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ObligationSource {
    job: BaselineId,
    step: String,
}

impl ObligationSource {
    pub fn new(job: BaselineId, step: impl Into<String>) -> Result<Self, String> {
        let step = step.into();
        validate_text(&step)?;
        Ok(Self { job, step })
    }

    pub fn job(&self) -> &BaselineId {
        &self.job
    }

    pub fn step(&self) -> &str {
        &self.step
    }
}

/// One normalized unit of legacy CI work.
///
/// Optional matrix dimensions are empty in the TSV and become `None`. This
/// avoids giving the empty string a second meaning in future plan comparison.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LogicalObligation {
    kind: BaselineId,
    package: Option<BaselineId>,
    toolchain: Option<BaselineId>,
    feature_profile: Option<BaselineId>,
    target: Option<BaselineId>,
    miri_model: Option<BaselineId>,
    reduced_occurrences: u32,
    full_occurrences: u32,
    condition: ObligationCondition,
    sources: Vec<ObligationSource>,
}

impl LogicalObligation {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        kind: BaselineId,
        package: Option<BaselineId>,
        toolchain: Option<BaselineId>,
        feature_profile: Option<BaselineId>,
        target: Option<BaselineId>,
        miri_model: Option<BaselineId>,
        reduced_occurrences: u32,
        full_occurrences: u32,
        condition: ObligationCondition,
        sources: Vec<ObligationSource>,
    ) -> Result<Self, String> {
        if reduced_occurrences == 0 && full_occurrences == 0 {
            return Err("must occur in at least one event category".into());
        }
        if sources.is_empty() {
            return Err("must have at least one physical source".into());
        }
        if sources.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err("sources must be unique and strictly sorted".into());
        }
        Ok(Self {
            kind,
            package,
            toolchain,
            feature_profile,
            target,
            miri_model,
            reduced_occurrences,
            full_occurrences,
            condition,
            sources,
        })
    }

    pub fn kind(&self) -> &BaselineId {
        &self.kind
    }

    pub fn package(&self) -> Option<&BaselineId> {
        self.package.as_ref()
    }

    pub fn toolchain(&self) -> Option<&BaselineId> {
        self.toolchain.as_ref()
    }

    pub fn feature_profile(&self) -> Option<&BaselineId> {
        self.feature_profile.as_ref()
    }

    pub fn target(&self) -> Option<&BaselineId> {
        self.target.as_ref()
    }

    pub fn miri_model(&self) -> Option<&BaselineId> {
        self.miri_model.as_ref()
    }

    pub fn reduced_occurrences(&self) -> u32 {
        self.reduced_occurrences
    }

    pub fn full_occurrences(&self) -> u32 {
        self.full_occurrences
    }

    pub fn condition(&self) -> &ObligationCondition {
        &self.condition
    }

    pub fn sources(&self) -> &[ObligationSource] {
        &self.sources
    }

    /// Returns the fields which identify this logical unit of work.
    pub fn key(&self) -> LogicalObligationKey {
        LogicalObligationKey {
            kind: self.kind.clone(),
            package: self.package.clone(),
            toolchain: self.toolchain.clone(),
            feature_profile: self.feature_profile.clone(),
            target: self.target.clone(),
            miri_model: self.miri_model.clone(),
        }
    }
}

/// The fields which uniquely identify one logical CI obligation.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LogicalObligationKey {
    kind: BaselineId,
    package: Option<BaselineId>,
    toolchain: Option<BaselineId>,
    feature_profile: Option<BaselineId>,
    target: Option<BaselineId>,
    miri_model: Option<BaselineId>,
}

/// Logical obligations which are known to have unique semantic keys.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LogicalObligations(BTreeMap<LogicalObligationKey, LogicalObligation>);

impl LogicalObligations {
    /// Creates an empty validated collection.
    pub fn new() -> Self {
        Self(BTreeMap::new())
    }

    /// Inserts an obligation unless its semantic key is already present.
    pub fn insert(
        &mut self,
        obligation: LogicalObligation,
    ) -> Result<(), DuplicateLogicalObligation> {
        let key = obligation.key();
        if self.0.contains_key(&key) {
            return Err(DuplicateLogicalObligation { key: Box::new(key) });
        }
        self.0.insert(key, obligation);
        Ok(())
    }

    /// Validates and collects logical obligations without overwriting a key.
    pub fn try_from_iter(
        obligations: impl IntoIterator<Item = LogicalObligation>,
    ) -> Result<Self, DuplicateLogicalObligation> {
        let mut collected = Self::new();
        for obligation in obligations {
            collected.insert(obligation)?;
        }
        Ok(collected)
    }

    /// Returns the number of unique obligations.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns whether no obligations are present.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Iterates over obligations in semantic-key order.
    pub fn values(&self) -> impl Iterator<Item = &LogicalObligation> {
        self.0.values()
    }

    fn value_set(&self) -> BTreeSet<LogicalObligation> {
        self.0.values().cloned().collect()
    }
}

/// Two planned logical obligations used the same semantic key.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DuplicateLogicalObligation {
    key: Box<LogicalObligationKey>,
}

impl DuplicateLogicalObligation {
    /// Returns the duplicated key.
    pub fn key(&self) -> &LogicalObligationKey {
        &self.key
    }
}

impl fmt::Display for DuplicateLogicalObligation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "duplicate logical-obligation key: {:?}", self.key)
    }
}

impl Error for DuplicateLogicalObligation {}

impl Default for LogicalObligations {
    fn default() -> Self {
        Self::new()
    }
}

/// Event coverage recorded for a standalone obligation.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum StandaloneEvents {
    PullRequestAndFull,
}

/// How a standalone legacy obligation is invoked.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum StandaloneInvocation {
    Direct(Vec<String>),
    Action(String),
    PrePushChild(Vec<String>),
    PrePushInternal(String),
    ShellContract(String),
}

/// One physical operation outside the ordinary build and Miri matrices.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct StandaloneObligation {
    obligation: BaselineId,
    events: StandaloneEvents,
    job: BaselineId,
    step: String,
    working_directory: WorkingDirectory,
    invocation: StandaloneInvocation,
}

impl StandaloneObligation {
    pub fn new(
        obligation: BaselineId,
        events: StandaloneEvents,
        job: BaselineId,
        step: impl Into<String>,
        working_directory: WorkingDirectory,
        invocation: StandaloneInvocation,
    ) -> Result<Self, String> {
        let step = step.into();
        validate_text(&step)?;
        // Reparse the public enum's string-bearing variants so constructing a
        // planned row cannot bypass the same invariants as reading a fixture.
        working_directory.validate()?;
        validate_standalone_invocation(&invocation)?;
        Ok(Self { obligation, events, job, step, working_directory, invocation })
    }

    pub fn obligation(&self) -> &BaselineId {
        &self.obligation
    }

    pub fn events(&self) -> &StandaloneEvents {
        &self.events
    }

    pub fn job(&self) -> &BaselineId {
        &self.job
    }

    pub fn step(&self) -> &str {
        &self.step
    }

    pub fn working_directory(&self) -> &WorkingDirectory {
        &self.working_directory
    }

    pub fn invocation(&self) -> &StandaloneInvocation {
        &self.invocation
    }
}

/// A small, canonical JSON value used by action-input command goldens.
///
/// The legacy payloads need only strings, arrays, and objects. Rejecting JSON
/// numbers, booleans, and null keeps this representation precise and prevents
/// a future file edit from gaining an unreviewed interpretation.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum JsonValue {
    String(String),
    Array(Vec<JsonValue>),
    Object(BTreeMap<String, JsonValue>),
}

/// The typed payload recorded by one representative command golden.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum CommandPayload {
    Argv { argv: Vec<String>, dynamic_value: Option<String> },
    ArgvTemplate { argv: Vec<String>, dynamic_value: String },
    ActionInputs { inputs: BTreeMap<String, JsonValue>, dynamic_value: String },
}

/// The behavior-bearing part of one representative command or action.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CommandBehavior {
    name: BaselineId,
    job: BaselineId,
    step: String,
    working_directory: WorkingDirectory,
    environment: BTreeMap<String, String>,
    payload: CommandPayload,
}

impl CommandBehavior {
    pub fn new(
        name: BaselineId,
        job: BaselineId,
        step: impl Into<String>,
        working_directory: WorkingDirectory,
        environment: BTreeMap<String, String>,
        payload: CommandPayload,
    ) -> Result<Self, String> {
        let step = step.into();
        validate_text(&step)?;
        working_directory.validate()?;
        validate_environment(&environment)?;
        validate_command_payload(&payload)?;
        Ok(Self { name, job, step, working_directory, environment, payload })
    }

    pub fn name(&self) -> &BaselineId {
        &self.name
    }

    pub fn job(&self) -> &BaselineId {
        &self.job
    }

    pub fn step(&self) -> &str {
        &self.step
    }

    pub fn working_directory(&self) -> &WorkingDirectory {
        &self.working_directory
    }

    pub fn environment(&self) -> &BTreeMap<String, String> {
        &self.environment
    }

    pub fn payload(&self) -> &CommandPayload {
        &self.payload
    }
}

/// Planned command behaviors with one behavior per golden name.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandBehaviors(BTreeMap<BaselineId, CommandBehavior>);

impl CommandBehaviors {
    /// Creates an empty validated collection.
    pub fn new() -> Self {
        Self(BTreeMap::new())
    }

    /// Inserts a behavior unless its golden name is already present.
    pub fn insert(&mut self, behavior: CommandBehavior) -> Result<(), DuplicateCommandBehavior> {
        let name = behavior.name.clone();
        if self.0.contains_key(&name) {
            return Err(DuplicateCommandBehavior { name });
        }
        self.0.insert(name, behavior);
        Ok(())
    }

    /// Validates and collects behaviors without overwriting a golden name.
    pub fn try_from_iter(
        behaviors: impl IntoIterator<Item = CommandBehavior>,
    ) -> Result<Self, DuplicateCommandBehavior> {
        let mut collected = Self::new();
        for behavior in behaviors {
            collected.insert(behavior)?;
        }
        Ok(collected)
    }

    /// Returns the number of named behaviors.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns whether no behaviors are present.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Iterates over behavior in golden-name order.
    pub fn values(&self) -> impl Iterator<Item = &CommandBehavior> {
        self.0.values()
    }

    fn value_set(&self) -> BTreeSet<CommandBehavior> {
        self.0.values().cloned().collect()
    }
}

impl Default for CommandBehaviors {
    fn default() -> Self {
        Self::new()
    }
}

/// Two planned command behaviors used the same golden name.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DuplicateCommandBehavior {
    name: BaselineId,
}

impl DuplicateCommandBehavior {
    /// Returns the duplicated name.
    pub fn name(&self) -> &BaselineId {
        &self.name
    }
}

impl fmt::Display for DuplicateCommandBehavior {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "duplicate command-golden name `{}`", self.name)
    }
}

impl Error for DuplicateCommandBehavior {}

/// One reviewed command behavior and the prose which explains its purpose.
///
/// The note is intentionally not part of [`CommandBehavior`]. Editing review
/// prose must not look like an executable plan change, and a planner must not
/// reproduce prose merely to compare command behavior.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandGolden {
    behavior: CommandBehavior,
    note: String,
}

impl CommandGolden {
    /// Returns the behavior compared with a future plan.
    pub fn behavior(&self) -> &CommandBehavior {
        &self.behavior
    }

    /// Returns the reviewer-facing explanation recorded with the behavior.
    pub fn note(&self) -> &str {
        &self.note
    }
}

/// Source identity and independently checked row counts for a legacy baseline.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LegacyManifest {
    source_commit: String,
    workflow_sha256: String,
    pre_push_sha256: String,
    cargo_toml_sha256: String,
    build_reduced_cells: u64,
    build_full_cells: u64,
    miri_reduced_cells: u64,
    miri_full_cells: u64,
    standalone_occurrences: u64,
    normalized_logical_obligations: u64,
}

impl LegacyManifest {
    pub fn source_commit(&self) -> &str {
        &self.source_commit
    }

    pub fn workflow_sha256(&self) -> &str {
        &self.workflow_sha256
    }

    pub fn pre_push_sha256(&self) -> &str {
        &self.pre_push_sha256
    }

    pub fn cargo_toml_sha256(&self) -> &str {
        &self.cargo_toml_sha256
    }

    pub fn build_reduced_cells(&self) -> u64 {
        self.build_reduced_cells
    }

    pub fn build_full_cells(&self) -> u64 {
        self.build_full_cells
    }

    pub fn miri_reduced_cells(&self) -> u64 {
        self.miri_reduced_cells
    }

    pub fn miri_full_cells(&self) -> u64 {
        self.miri_full_cells
    }

    pub fn standalone_occurrences(&self) -> u64 {
        self.standalone_occurrences
    }

    pub fn normalized_logical_obligations(&self) -> u64 {
        self.normalized_logical_obligations
    }
}

/// All independently frozen legacy CI evidence, parsed into deterministic sets.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LegacyBaselines {
    manifest: LegacyManifest,
    build_reduced: BTreeSet<BuildCell>,
    build_full: BTreeSet<BuildCell>,
    miri_reduced: BTreeSet<MiriCell>,
    miri_full: BTreeSet<MiriCell>,
    logical_obligations: LogicalObligations,
    standalone_obligations: BTreeSet<StandaloneObligation>,
    command_goldens: BTreeMap<BaselineId, CommandGolden>,
}

impl LegacyBaselines {
    pub fn manifest(&self) -> &LegacyManifest {
        &self.manifest
    }

    pub fn build_reduced(&self) -> &BTreeSet<BuildCell> {
        &self.build_reduced
    }

    pub fn build_full(&self) -> &BTreeSet<BuildCell> {
        &self.build_full
    }

    pub fn miri_reduced(&self) -> &BTreeSet<MiriCell> {
        &self.miri_reduced
    }

    pub fn miri_full(&self) -> &BTreeSet<MiriCell> {
        &self.miri_full
    }

    pub fn logical_obligations(&self) -> &LogicalObligations {
        &self.logical_obligations
    }

    pub fn standalone_obligations(&self) -> &BTreeSet<StandaloneObligation> {
        &self.standalone_obligations
    }

    pub fn command_goldens(&self) -> &BTreeMap<BaselineId, CommandGolden> {
        &self.command_goldens
    }

    /// Reads, strictly parses, and cross-checks all files in one baseline.
    pub fn read(paths: &LegacyBaselinePaths) -> Result<Self, BaselineError> {
        let manifest = read_source(&paths.manifest)?;
        let build_reduced = read_source(&paths.build_reduced)?;
        let build_full = read_source(&paths.build_full)?;
        let miri_reduced = read_source(&paths.miri_reduced)?;
        let miri_full = read_source(&paths.miri_full)?;
        let logical_obligations = read_source(&paths.logical_obligations)?;
        let standalone_obligations = read_source(&paths.standalone_obligations)?;
        let command_goldens = read_source(&paths.command_goldens)?;
        Self::parse_sources(
            paths,
            BaselineSources {
                manifest: &manifest,
                build_reduced: &build_reduced,
                build_full: &build_full,
                miri_reduced: &miri_reduced,
                miri_full: &miri_full,
                logical_obligations: &logical_obligations,
                standalone_obligations: &standalone_obligations,
                command_goldens: &command_goldens,
            },
        )
    }

    /// Reads and parses baseline bytes through already-validated handles.
    pub(crate) fn read_open(
        paths: &LegacyBaselinePaths,
        files: LegacyBaselineFiles<'_>,
    ) -> Result<Self, BaselineError> {
        let manifest = read_open_source(&paths.manifest, files.manifest)?;
        let build_reduced = read_open_source(&paths.build_reduced, files.build_reduced)?;
        let build_full = read_open_source(&paths.build_full, files.build_full)?;
        let miri_reduced = read_open_source(&paths.miri_reduced, files.miri_reduced)?;
        let miri_full = read_open_source(&paths.miri_full, files.miri_full)?;
        let logical_obligations =
            read_open_source(&paths.logical_obligations, files.logical_obligations)?;
        let standalone_obligations =
            read_open_source(&paths.standalone_obligations, files.standalone_obligations)?;
        let command_goldens = read_open_source(&paths.command_goldens, files.command_goldens)?;
        Self::parse_sources(
            paths,
            BaselineSources {
                manifest: &manifest,
                build_reduced: &build_reduced,
                build_full: &build_full,
                miri_reduced: &miri_reduced,
                miri_full: &miri_full,
                logical_obligations: &logical_obligations,
                standalone_obligations: &standalone_obligations,
                command_goldens: &command_goldens,
            },
        )
    }

    fn parse_sources(
        paths: &LegacyBaselinePaths,
        sources: BaselineSources<'_>,
    ) -> Result<Self, BaselineError> {
        let manifest = parse_manifest(&paths.manifest, sources.manifest)?;
        let build_reduced = parse_build_cells(&paths.build_reduced, sources.build_reduced)?;
        let build_full = parse_build_cells(&paths.build_full, sources.build_full)?;
        let miri_reduced = parse_miri_cells(&paths.miri_reduced, sources.miri_reduced)?;
        let miri_full = parse_miri_cells(&paths.miri_full, sources.miri_full)?;
        let logical_obligations =
            parse_logical_obligations(&paths.logical_obligations, sources.logical_obligations)?;
        let standalone_obligations = parse_standalone_obligations(
            &paths.standalone_obligations,
            sources.standalone_obligations,
        )?;
        let command_goldens =
            parse_command_goldens(&paths.command_goldens, sources.command_goldens)?;

        check_manifest_count(
            &paths.manifest,
            "build_pr_cells",
            manifest.build_reduced_cells,
            build_reduced.len(),
        )?;
        check_manifest_count(
            &paths.manifest,
            "build_full_cells",
            manifest.build_full_cells,
            build_full.len(),
        )?;
        check_manifest_count(
            &paths.manifest,
            "miri_pr_cells",
            manifest.miri_reduced_cells,
            miri_reduced.len(),
        )?;
        check_manifest_count(
            &paths.manifest,
            "miri_full_cells",
            manifest.miri_full_cells,
            miri_full.len(),
        )?;
        check_manifest_count(
            &paths.manifest,
            "standalone_occurrences",
            manifest.standalone_occurrences,
            standalone_obligations.len(),
        )?;
        check_manifest_count(
            &paths.manifest,
            "normalized_logical_obligations",
            manifest.normalized_logical_obligations,
            logical_obligations.len(),
        )?;

        Ok(Self {
            manifest,
            build_reduced,
            build_full,
            miri_reduced,
            miri_full,
            logical_obligations,
            standalone_obligations,
            command_goldens,
        })
    }

    /// Compares the reduced build plan with the exact frozen set.
    pub fn compare_build_reduced(
        &self,
        planned: &BTreeSet<BuildCell>,
    ) -> Result<(), SetDifference<BuildCell>> {
        compare_exact(&self.build_reduced, planned)
    }

    /// Compares the full build plan with the exact frozen set.
    pub fn compare_build_full(
        &self,
        planned: &BTreeSet<BuildCell>,
    ) -> Result<(), SetDifference<BuildCell>> {
        compare_exact(&self.build_full, planned)
    }

    /// Compares the reduced Miri plan with the exact frozen set.
    pub fn compare_miri_reduced(
        &self,
        planned: &BTreeSet<MiriCell>,
    ) -> Result<(), SetDifference<MiriCell>> {
        compare_exact(&self.miri_reduced, planned)
    }

    /// Compares the full Miri plan with the exact frozen set.
    pub fn compare_miri_full(
        &self,
        planned: &BTreeSet<MiriCell>,
    ) -> Result<(), SetDifference<MiriCell>> {
        compare_exact(&self.miri_full, planned)
    }

    /// Compares normalized logical work with the exact frozen set.
    pub fn compare_logical_obligations(
        &self,
        planned: &LogicalObligations,
    ) -> Result<(), SetDifference<LogicalObligation>> {
        compare_exact(&self.logical_obligations.value_set(), &planned.value_set())
    }

    /// Compares standalone work with the exact frozen set.
    pub fn compare_standalone_obligations(
        &self,
        planned: &BTreeSet<StandaloneObligation>,
    ) -> Result<(), SetDifference<StandaloneObligation>> {
        compare_exact(&self.standalone_obligations, planned)
    }

    /// Compares representative expanded commands with the exact frozen set.
    pub fn compare_command_goldens(
        &self,
        planned: &CommandBehaviors,
    ) -> Result<(), SetDifference<CommandBehavior>> {
        let baseline =
            self.command_goldens.values().map(|golden| golden.behavior.clone()).collect();
        compare_exact(&baseline, &planned.value_set())
    }
}

/// Exact missing and extra values found while comparing a plan to a baseline.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SetDifference<T: Ord> {
    /// Baseline values which the proposed plan does not contain.
    missing_from_plan: BTreeSet<T>,
    /// Proposed values which are absent from the reviewed baseline.
    extra_in_plan: BTreeSet<T>,
}

impl<T: Ord> SetDifference<T> {
    pub fn missing_from_plan(&self) -> &BTreeSet<T> {
        &self.missing_from_plan
    }

    pub fn extra_in_plan(&self) -> &BTreeSet<T> {
        &self.extra_in_plan
    }
}

impl<T: fmt::Debug + Ord> fmt::Display for SetDifference<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            formatter,
            "plan differs from the legacy baseline: {} missing, {} extra",
            self.missing_from_plan.len(),
            self.extra_in_plan.len()
        )?;
        for value in &self.missing_from_plan {
            writeln!(formatter, "- missing: {value:?}")?;
        }
        for value in &self.extra_in_plan {
            writeln!(formatter, "- extra: {value:?}")?;
        }
        Ok(())
    }
}

impl<T: fmt::Debug + Ord> Error for SetDifference<T> {}

/// Compares complete sets without allowing missing and extra rows to cancel.
pub fn compare_exact<T: Clone + Ord>(
    baseline: &BTreeSet<T>,
    planned: &BTreeSet<T>,
) -> Result<(), SetDifference<T>> {
    let difference = SetDifference {
        missing_from_plan: baseline.difference(planned).cloned().collect(),
        extra_in_plan: planned.difference(baseline).cloned().collect(),
    };
    if difference.missing_from_plan.is_empty() && difference.extra_in_plan.is_empty() {
        Ok(())
    } else {
        Err(difference)
    }
}

/// A read or strict-format error in one baseline file.
#[derive(Debug)]
pub struct BaselineError {
    path: PathBuf,
    line: Option<usize>,
    message: String,
    source: Option<io::Error>,
}

impl BaselineError {
    fn format(path: &Path, line: Option<usize>, message: impl Into<String>) -> Self {
        let mut escaped = String::new();
        for character in message.into().chars() {
            if character.is_control() {
                escaped.extend(character.escape_default());
            } else {
                escaped.push(character);
            }
        }
        Self { path: path.to_path_buf(), line, message: escaped, source: None }
    }

    /// Returns the file whose evidence could not be read or validated.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Returns the one-based line number, when the error belongs to one line.
    pub fn line(&self) -> Option<usize> {
        self.line
    }
}

impl fmt::Display for BaselineError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "legacy baseline `{}`", self.path.display())?;
        if let Some(line) = self.line {
            write!(formatter, " line {line}")?;
        }
        write!(formatter, ": {}", self.message)
    }
}

impl Error for BaselineError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.source.as_ref().map(|source| source as &(dyn Error + 'static))
    }
}

fn read_source(path: &Path) -> Result<String, BaselineError> {
    fs::read_to_string(path).map_err(|source| BaselineError {
        path: path.to_path_buf(),
        line: None,
        message: format!("failed to read file: {source}"),
        source: Some(source),
    })
}

fn read_open_source(path: &Path, file: &File) -> Result<String, BaselineError> {
    let mut source = String::new();
    let mut reader = file;
    reader.read_to_string(&mut source).map_err(|source| BaselineError {
        path: path.to_path_buf(),
        line: None,
        message: format!("failed to read file: {source}"),
        source: Some(source),
    })?;
    Ok(source)
}

struct BaselineSources<'a> {
    manifest: &'a str,
    build_reduced: &'a str,
    build_full: &'a str,
    miri_reduced: &'a str,
    miri_full: &'a str,
    logical_obligations: &'a str,
    standalone_obligations: &'a str,
    command_goldens: &'a str,
}

struct DataRow<'a> {
    line: usize,
    fields: Vec<&'a str>,
}

/// Parses the common canonical TSV envelope before schema-specific fields.
///
/// Comments may document provenance before the header. Once data begins, every
/// physical line is significant: blank lines and comments are rejected rather
/// than silently disappearing from a reviewed fixture.
fn data_rows<'a>(
    path: &Path,
    source: &'a str,
    header: &str,
    field_count: usize,
) -> Result<Vec<DataRow<'a>>, BaselineError> {
    if source.contains('\r') {
        return Err(BaselineError::format(path, None, "carriage returns are not permitted"));
    }
    if !source.ends_with('\n') {
        return Err(BaselineError::format(path, None, "file must end with one newline"));
    }

    let mut saw_header = false;
    let mut previous_row: Option<&str> = None;
    let mut rows = Vec::new();
    for (line_index, line) in source.split_terminator('\n').enumerate() {
        let line_number = line_index + 1;
        if !saw_header {
            if line.starts_with('#') {
                if line.chars().any(char::is_control) {
                    return Err(BaselineError::format(
                        path,
                        Some(line_number),
                        "comments must not contain control characters",
                    ));
                }
                continue;
            }
            if line.is_empty() {
                return Err(BaselineError::format(
                    path,
                    Some(line_number),
                    "blank lines are not canonical",
                ));
            }
            if line != header {
                return Err(BaselineError::format(
                    path,
                    Some(line_number),
                    format!("expected exact header `{header}`, found `{line}`"),
                ));
            }
            saw_header = true;
            continue;
        }

        if line.is_empty() {
            return Err(BaselineError::format(
                path,
                Some(line_number),
                "blank lines are not canonical",
            ));
        }
        if line.starts_with('#') {
            return Err(BaselineError::format(
                path,
                Some(line_number),
                "comments are permitted only before the header",
            ));
        }
        if let Some(previous) = previous_row {
            if line == previous {
                return Err(BaselineError::format(
                    path,
                    Some(line_number),
                    "duplicate row; data rows must be unique",
                ));
            }
            if line < previous {
                return Err(BaselineError::format(
                    path,
                    Some(line_number),
                    "row is out of order; data rows must be strictly bytewise sorted",
                ));
            }
        }
        previous_row = Some(line);

        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != field_count {
            return Err(BaselineError::format(
                path,
                Some(line_number),
                format!("expected {field_count} tab-separated fields, found {}", fields.len()),
            ));
        }
        rows.push(DataRow { line: line_number, fields });
    }
    if !saw_header {
        return Err(BaselineError::format(path, None, format!("missing exact header `{header}`")));
    }
    Ok(rows)
}

fn parse_manifest(path: &Path, source: &str) -> Result<LegacyManifest, BaselineError> {
    let rows = data_rows(path, source, MANIFEST_HEADER, 2)?;
    let mut values = BTreeMap::new();
    for row in rows {
        let key = row.fields[0];
        validate_manifest_key(key)
            .map_err(|reason| field_error(path, row.line, "key", key, reason))?;
        if values.insert(key, (row.line, row.fields[1])).is_some() {
            // Raw duplicate rows were already rejected. Reaching this branch
            // means one key has two conflicting values, which is equally
            // ambiguous and must not be treated as last-one-wins data.
            return Err(field_error(path, row.line, "key", key, "manifest keys must be unique"));
        }
    }

    const KEYS: &[&str] = &[
        "build_full_cells",
        "build_pr_cells",
        "cargo_toml_sha256",
        "generic_manual_build_sets_equal",
        "generic_manual_miri_sets_equal",
        "miri_full_cells",
        "miri_pr_cells",
        "normalized_logical_obligations",
        "pre_push_sha256",
        "source_commit",
        "standalone_occurrences",
        "workflow_sha256",
    ];
    for key in values.keys() {
        if !KEYS.contains(key) {
            return Err(BaselineError::format(
                path,
                Some(values[key].0),
                format!("unknown manifest key `{key}`"),
            ));
        }
    }
    for key in KEYS {
        if !values.contains_key(key) {
            return Err(BaselineError::format(path, None, format!("missing manifest key `{key}`")));
        }
    }

    let value = |key: &str| values[key].1;
    for key in ["generic_manual_build_sets_equal", "generic_manual_miri_sets_equal"] {
        if value(key) != "true" {
            return Err(BaselineError::format(
                path,
                Some(values[key].0),
                format!(
                    "`{key}` must be `true`; unequal independent derivations are not valid evidence"
                ),
            ));
        }
    }

    Ok(LegacyManifest {
        source_commit: parse_lower_hex(value("source_commit"), 40).map_err(|reason| {
            field_error(path, values["source_commit"].0, "value", value("source_commit"), reason)
        })?,
        workflow_sha256: parse_lower_hex(value("workflow_sha256"), 64).map_err(|reason| {
            field_error(
                path,
                values["workflow_sha256"].0,
                "value",
                value("workflow_sha256"),
                reason,
            )
        })?,
        pre_push_sha256: parse_lower_hex(value("pre_push_sha256"), 64).map_err(|reason| {
            field_error(
                path,
                values["pre_push_sha256"].0,
                "value",
                value("pre_push_sha256"),
                reason,
            )
        })?,
        cargo_toml_sha256: parse_lower_hex(value("cargo_toml_sha256"), 64).map_err(|reason| {
            field_error(
                path,
                values["cargo_toml_sha256"].0,
                "value",
                value("cargo_toml_sha256"),
                reason,
            )
        })?,
        build_reduced_cells: manifest_count(path, &values, "build_pr_cells")?,
        build_full_cells: manifest_count(path, &values, "build_full_cells")?,
        miri_reduced_cells: manifest_count(path, &values, "miri_pr_cells")?,
        miri_full_cells: manifest_count(path, &values, "miri_full_cells")?,
        standalone_occurrences: manifest_count(path, &values, "standalone_occurrences")?,
        normalized_logical_obligations: manifest_count(
            path,
            &values,
            "normalized_logical_obligations",
        )?,
    })
}

fn validate_manifest_key(value: &str) -> Result<(), String> {
    if !value.is_empty()
        && value
            .bytes()
            .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'_')
    {
        Ok(())
    } else {
        Err("must use lowercase ASCII letters, digits, or `_`".into())
    }
}

fn manifest_count(
    path: &Path,
    values: &BTreeMap<&str, (usize, &str)>,
    key: &str,
) -> Result<u64, BaselineError> {
    parse_u64(values[key].1)
        .map_err(|reason| field_error(path, values[key].0, "value", values[key].1, reason))
}

fn parse_build_cells(path: &Path, source: &str) -> Result<BTreeSet<BuildCell>, BaselineError> {
    let rows = data_rows(path, source, BUILD_HEADER, 4)?;
    let mut cells = BTreeSet::new();
    for row in rows {
        let cell = BuildCell {
            package: parse_id_field(path, &row, 0, "crate")?,
            toolchain: parse_id_field(path, &row, 1, "toolchain")?,
            feature_profile: parse_id_field(path, &row, 2, "feature_profile")?,
            target: parse_id_field(path, &row, 3, "target")?,
        };
        insert_unique(path, row.line, &mut cells, cell)?;
    }
    Ok(cells)
}

fn parse_miri_cells(path: &Path, source: &str) -> Result<BTreeSet<MiriCell>, BaselineError> {
    let rows = data_rows(path, source, MIRI_HEADER, 6)?;
    let mut cells = BTreeSet::new();
    for row in rows {
        let cell = MiriCell {
            package: parse_id_field(path, &row, 0, "crate")?,
            toolchain: parse_id_field(path, &row, 1, "toolchain")?,
            feature_profile: parse_id_field(path, &row, 2, "feature_profile")?,
            target: parse_id_field(path, &row, 3, "target")?,
            model: parse_id_field(path, &row, 4, "miri_model")?,
            model_flags: parse_flag_list(row.fields[5]).map_err(|reason| {
                field_error(path, row.line, "miri_model_flags", row.fields[5], reason)
            })?,
        };
        insert_unique(path, row.line, &mut cells, cell)?;
    }
    Ok(cells)
}

fn parse_logical_obligations(
    path: &Path,
    source: &str,
) -> Result<LogicalObligations, BaselineError> {
    let rows = data_rows(path, source, LOGICAL_HEADER, 10)?;
    let mut obligations = LogicalObligations::new();
    for row in rows {
        let condition = match row.fields[8] {
            "always" => ObligationCondition::Always,
            "success()" => ObligationCondition::Success,
            "cancelled()" => ObligationCondition::Cancelled,
            "unless SKIP_CARGO_SEMVER_CHECKS=1" => ObligationCondition::UnlessSkipCargoSemverChecks,
            value => {
                return Err(field_error(
                    path,
                    row.line,
                    "condition",
                    value,
                    "is not a supported legacy condition",
                ));
            }
        };
        let obligation = LogicalObligation {
            kind: parse_id_field(path, &row, 0, "kind")?,
            package: parse_optional_id_field(path, &row, 1, "crate")?,
            toolchain: parse_optional_id_field(path, &row, 2, "toolchain")?,
            feature_profile: parse_optional_id_field(path, &row, 3, "feature_profile")?,
            target: parse_optional_id_field(path, &row, 4, "target")?,
            miri_model: parse_optional_id_field(path, &row, 5, "miri_model")?,
            reduced_occurrences: parse_u32(row.fields[6]).map_err(|reason| {
                field_error(path, row.line, "pr_occurrences", row.fields[6], reason)
            })?,
            full_occurrences: parse_u32(row.fields[7]).map_err(|reason| {
                field_error(path, row.line, "full_occurrences", row.fields[7], reason)
            })?,
            condition,
            sources: parse_obligation_sources(row.fields[9])
                .map_err(|reason| field_error(path, row.line, "sources", row.fields[9], reason))?,
        };
        if obligation.reduced_occurrences == 0 && obligation.full_occurrences == 0 {
            return Err(BaselineError::format(
                path,
                Some(row.line),
                "logical obligation has zero occurrences in every event category",
            ));
        }
        obligations
            .insert(obligation)
            .map_err(|error| BaselineError::format(path, Some(row.line), error.to_string()))?;
    }
    Ok(obligations)
}

fn parse_standalone_obligations(
    path: &Path,
    source: &str,
) -> Result<BTreeSet<StandaloneObligation>, BaselineError> {
    let rows = data_rows(path, source, STANDALONE_HEADER, 7)?;
    let mut obligations = BTreeSet::new();
    for row in rows {
        let events = match row.fields[1] {
            "pull_request,full" => StandaloneEvents::PullRequestAndFull,
            value => {
                return Err(field_error(
                    path,
                    row.line,
                    "events",
                    value,
                    "must use the canonical `pull_request,full` event set",
                ));
            }
        };
        let invocation = match row.fields[5] {
            "direct" => {
                StandaloneInvocation::Direct(parse_argv(row.fields[6]).map_err(|reason| {
                    field_error(path, row.line, "payload", row.fields[6], reason)
                })?)
            }
            "action" => {
                validate_action_reference(row.fields[6]).map_err(|reason| {
                    field_error(path, row.line, "payload", row.fields[6], reason)
                })?;
                StandaloneInvocation::Action(row.fields[6].to_owned())
            }
            "pre-push-child" => {
                StandaloneInvocation::PrePushChild(parse_argv(row.fields[6]).map_err(|reason| {
                    field_error(path, row.line, "payload", row.fields[6], reason)
                })?)
            }
            "pre-push-internal" => {
                validate_text(row.fields[6]).map_err(|reason| {
                    field_error(path, row.line, "payload", row.fields[6], reason)
                })?;
                StandaloneInvocation::PrePushInternal(row.fields[6].to_owned())
            }
            "shell-contract" => {
                validate_text(row.fields[6]).map_err(|reason| {
                    field_error(path, row.line, "payload", row.fields[6], reason)
                })?;
                StandaloneInvocation::ShellContract(row.fields[6].to_owned())
            }
            value => {
                return Err(field_error(
                    path,
                    row.line,
                    "form",
                    value,
                    "is not one of `direct`, `action`, `pre-push-child`, `pre-push-internal`, or `shell-contract`",
                ));
            }
        };
        validate_text(row.fields[3])
            .map_err(|reason| field_error(path, row.line, "step", row.fields[3], reason))?;
        let obligation = StandaloneObligation {
            obligation: parse_id_field(path, &row, 0, "obligation")?,
            events,
            job: parse_id_field(path, &row, 2, "job")?,
            step: row.fields[3].to_owned(),
            working_directory: WorkingDirectory::parse(row.fields[4]).map_err(|reason| {
                field_error(path, row.line, "working_directory", row.fields[4], reason)
            })?,
            invocation,
        };
        insert_unique(path, row.line, &mut obligations, obligation)?;
    }
    Ok(obligations)
}

fn parse_command_goldens(
    path: &Path,
    source: &str,
) -> Result<BTreeMap<BaselineId, CommandGolden>, BaselineError> {
    let rows = data_rows(path, source, COMMAND_GOLDEN_HEADER, 9)?;
    let mut goldens = BTreeMap::new();
    for row in rows {
        let environment = parse_environment(row.fields[4]).map_err(|reason| {
            field_error(path, row.line, "environment_json", row.fields[4], reason)
        })?;
        let payload = match row.fields[5] {
            "argv" => {
                let dynamic_value = if row.fields[7].is_empty() {
                    None
                } else {
                    validate_text(row.fields[7]).map_err(|reason| {
                        field_error(path, row.line, "dynamic_value", row.fields[7], reason)
                    })?;
                    Some(row.fields[7].to_owned())
                };
                CommandPayload::Argv {
                    argv: parse_argv(row.fields[6]).map_err(|reason| {
                        field_error(path, row.line, "payload", row.fields[6], reason)
                    })?,
                    dynamic_value,
                }
            }
            "argv-template" => {
                validate_text(row.fields[7]).map_err(|reason| {
                    field_error(path, row.line, "dynamic_value", row.fields[7], reason)
                })?;
                let argv = parse_argv(row.fields[6]).map_err(|reason| {
                    field_error(path, row.line, "payload", row.fields[6], reason)
                })?;
                let occurrences = argv.iter().filter(|argument| *argument == row.fields[7]).count();
                if occurrences != 1 {
                    return Err(BaselineError::format(
                        path,
                        Some(row.line),
                        format!(
                            "argv template must contain dynamic value `{}` exactly once, found {occurrences}",
                            row.fields[7]
                        ),
                    ));
                }
                CommandPayload::ArgvTemplate { argv, dynamic_value: row.fields[7].to_owned() }
            }
            "action-inputs" => {
                validate_text(row.fields[7]).map_err(|reason| {
                    field_error(path, row.line, "dynamic_value", row.fields[7], reason)
                })?;
                let value = parse_canonical_json(row.fields[6]).map_err(|reason| {
                    field_error(path, row.line, "payload", row.fields[6], reason)
                })?;
                let JsonValue::Object(inputs) = value else {
                    return Err(field_error(
                        path,
                        row.line,
                        "payload",
                        row.fields[6],
                        "action inputs must be a JSON object",
                    ));
                };
                validate_json_text(&JsonValue::Object(inputs.clone())).map_err(|reason| {
                    field_error(path, row.line, "payload", row.fields[6], reason)
                })?;
                validate_action_inputs(&inputs).map_err(|reason| {
                    field_error(path, row.line, "payload", row.fields[6], reason)
                })?;
                CommandPayload::ActionInputs { inputs, dynamic_value: row.fields[7].to_owned() }
            }
            value => {
                return Err(field_error(
                    path,
                    row.line,
                    "form",
                    value,
                    "is not one of `argv`, `argv-template`, or `action-inputs`",
                ));
            }
        };
        validate_text(row.fields[2])
            .map_err(|reason| field_error(path, row.line, "step", row.fields[2], reason))?;
        validate_text(row.fields[8])
            .map_err(|reason| field_error(path, row.line, "note", row.fields[8], reason))?;
        let name = parse_id_field(path, &row, 0, "golden")?;
        let behavior = CommandBehavior {
            name: name.clone(),
            job: parse_id_field(path, &row, 1, "job")?,
            step: row.fields[2].to_owned(),
            working_directory: WorkingDirectory::parse(row.fields[3]).map_err(|reason| {
                field_error(path, row.line, "working_directory", row.fields[3], reason)
            })?,
            environment,
            payload,
        };
        let golden = CommandGolden { behavior, note: row.fields[8].to_owned() };
        if goldens.insert(name.clone(), golden).is_some() {
            return Err(BaselineError::format(
                path,
                Some(row.line),
                format!("command-golden name `{name}` duplicates an earlier row"),
            ));
        }
    }
    Ok(goldens)
}

fn parse_id_field(
    path: &Path,
    row: &DataRow<'_>,
    index: usize,
    field: &str,
) -> Result<BaselineId, BaselineError> {
    BaselineId::parse(row.fields[index])
        .map_err(|reason| field_error(path, row.line, field, row.fields[index], reason))
}

fn parse_optional_id_field(
    path: &Path,
    row: &DataRow<'_>,
    index: usize,
    field: &str,
) -> Result<Option<BaselineId>, BaselineError> {
    if row.fields[index].is_empty() {
        Ok(None)
    } else {
        parse_id_field(path, row, index, field).map(Some)
    }
}

fn field_error(
    path: &Path,
    line: usize,
    field: &str,
    value: &str,
    reason: impl Into<String>,
) -> BaselineError {
    BaselineError::format(
        path,
        Some(line),
        format!("invalid `{field}` value {value:?}: {}", reason.into()),
    )
}

fn insert_unique<T: Ord>(
    path: &Path,
    line: usize,
    values: &mut BTreeSet<T>,
    value: T,
) -> Result<(), BaselineError> {
    if values.insert(value) {
        Ok(())
    } else {
        Err(BaselineError::format(path, Some(line), "row duplicates an earlier typed value"))
    }
}

fn parse_u64(value: &str) -> Result<u64, String> {
    if value.is_empty() || (value.len() > 1 && value.starts_with('0')) {
        return Err("must be a canonical unsigned decimal integer".into());
    }
    if !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err("must be a canonical unsigned decimal integer".into());
    }
    value.parse().map_err(|_| "is too large for an unsigned 64-bit integer".into())
}

fn parse_u32(value: &str) -> Result<u32, String> {
    let value = parse_u64(value)?;
    u32::try_from(value).map_err(|_| "is too large for an unsigned 32-bit integer".into())
}

fn parse_lower_hex(value: &str, length: usize) -> Result<String, String> {
    if value.len() == length
        && value.bytes().all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
    {
        Ok(value.to_owned())
    } else {
        Err(format!("must contain exactly {length} lowercase hexadecimal digits"))
    }
}

fn validate_repo_relative_path(value: &str) -> Result<(), String> {
    let path = Path::new(value);
    let unsafe_component =
        path.components().any(|component| !matches!(component, Component::Normal(_)));
    let dot_component = value.split('/').any(|component| matches!(component, "." | ".."));
    if value.is_empty()
        || value.split('/').any(str::is_empty)
        || dot_component
        || value.contains('\\')
        || value.contains(':')
        || value.chars().any(char::is_control)
        || unsafe_component
    {
        Err("must be a safe, normalized repository-relative path".into())
    } else {
        Ok(())
    }
}

fn validate_text(value: &str) -> Result<(), String> {
    if value.is_empty() {
        return Err("must not be empty".into());
    }
    if value.trim() != value {
        return Err("must not have leading or trailing whitespace".into());
    }
    if value.chars().any(char::is_control) {
        return Err("must not contain control characters".into());
    }
    Ok(())
}

fn parse_flag_list(value: &str) -> Result<Vec<String>, String> {
    if value == "<none>" {
        return Ok(Vec::new());
    }
    validate_text(value)?;
    let flags = value.split(' ').map(str::to_owned).collect::<Vec<_>>();
    validate_model_flags(&flags)?;
    Ok(flags)
}

fn validate_model_flags(flags: &[String]) -> Result<(), String> {
    for flag in flags {
        if flag.is_empty()
            || !flag.starts_with('-')
            || flag.chars().any(char::is_control)
            || flag.chars().any(char::is_whitespace)
        {
            return Err(
                "must be `<none>` or a single-space-separated list of nonempty option flags".into(),
            );
        }
    }
    Ok(())
}

fn validate_standalone_invocation(invocation: &StandaloneInvocation) -> Result<(), String> {
    match invocation {
        StandaloneInvocation::Direct(argv) | StandaloneInvocation::PrePushChild(argv) => {
            validate_argv(argv)
        }
        StandaloneInvocation::Action(reference) => validate_action_reference(reference),
        StandaloneInvocation::PrePushInternal(payload)
        | StandaloneInvocation::ShellContract(payload) => validate_text(payload),
    }
}

fn parse_obligation_sources(value: &str) -> Result<Vec<ObligationSource>, String> {
    validate_text(value)?;
    let mut sources = Vec::new();
    for source in value.split(" | ") {
        let Some((job, step)) = source.split_once('/') else {
            return Err("each source must have canonical `job/step` form".into());
        };
        let job =
            BaselineId::parse(job).map_err(|reason| format!("source job `{job}` {reason}"))?;
        validate_text(step).map_err(|reason| format!("source step `{step}` {reason}"))?;
        sources.push(ObligationSource { job, step: step.to_owned() });
    }
    if sources.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err("sources must be unique and strictly sorted".into());
    }
    Ok(sources)
}

fn validate_action_reference(value: &str) -> Result<(), String> {
    if let Some(path) = value.strip_prefix("./") {
        validate_repo_relative_path(path)?;
        return Ok(());
    }
    let Some((repository, revision)) = value.split_once('@') else {
        return Err(
            "must be a local `./path` or an external `owner/repository@40-hex-revision`".into()
        );
    };
    if repository.matches('/').count() != 1
        || repository.split('/').any(|component| {
            component.is_empty()
                || matches!(component, "." | "..")
                || component.bytes().any(|byte| {
                    !(byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-' | b'.'))
                })
        })
    {
        return Err("external action repository must have canonical `owner/repository` form".into());
    }
    parse_lower_hex(revision, 40).map(|_| ())
}

fn check_manifest_count(
    path: &Path,
    key: &str,
    expected: u64,
    actual: usize,
) -> Result<(), BaselineError> {
    let actual = actual as u64;
    if expected == actual {
        Ok(())
    } else {
        Err(BaselineError::format(
            path,
            None,
            format!(
                "manifest `{key}` records {expected}, but the parsed fixture contains {actual}"
            ),
        ))
    }
}

fn parse_environment(value: &str) -> Result<BTreeMap<String, String>, String> {
    let parsed = parse_canonical_json(value)?;
    let JsonValue::Object(values) = parsed else {
        return Err("must be a JSON object".into());
    };
    let mut environment = BTreeMap::new();
    for (name, value) in values {
        let JsonValue::String(value) = value else {
            return Err(format!("environment variable `{name}` must have a string value"));
        };
        environment.insert(name, value);
    }
    validate_environment(&environment)?;
    Ok(environment)
}

fn validate_environment(environment: &BTreeMap<String, String>) -> Result<(), String> {
    for (name, value) in environment {
        validate_environment_name(name)?;
        if value.chars().any(char::is_control) {
            return Err(format!("environment variable `{name}` contains a control character"));
        }
    }
    Ok(())
}

fn validate_environment_name(value: &str) -> Result<(), String> {
    let mut bytes = value.bytes();
    let Some(first) = bytes.next() else {
        return Err("environment variable name must not be empty".into());
    };
    if !(first.is_ascii_uppercase() || first == b'_')
        || !bytes.all(|byte| byte.is_ascii_uppercase() || byte.is_ascii_digit() || byte == b'_')
    {
        return Err(format!("environment variable name `{value}` is not canonical ASCII"));
    }
    Ok(())
}

fn parse_argv(value: &str) -> Result<Vec<String>, String> {
    let parsed = parse_canonical_json(value)?;
    let JsonValue::Array(values) = parsed else {
        return Err("must be a JSON array".into());
    };
    let mut argv = Vec::new();
    for value in values {
        let JsonValue::String(value) = value else {
            return Err("argv elements must all be JSON strings".into());
        };
        if value.chars().any(char::is_control) {
            return Err("argv strings must not contain control characters".into());
        }
        argv.push(value);
    }
    validate_argv(&argv)?;
    Ok(argv)
}

fn validate_argv(argv: &[String]) -> Result<(), String> {
    if argv.is_empty() {
        return Err("argv must contain at least one argument".into());
    }
    if argv.iter().any(|value| value.chars().any(char::is_control)) {
        return Err("argv strings must not contain control characters".into());
    }
    Ok(())
}

fn validate_command_payload(payload: &CommandPayload) -> Result<(), String> {
    match payload {
        CommandPayload::Argv { argv, dynamic_value } => {
            validate_argv(argv)?;
            if let Some(value) = dynamic_value {
                validate_text(value)?;
            }
        }
        CommandPayload::ArgvTemplate { argv, dynamic_value } => {
            validate_argv(argv)?;
            validate_text(dynamic_value)?;
            let occurrences = argv.iter().filter(|argument| *argument == dynamic_value).count();
            if occurrences != 1 {
                return Err(format!(
                    "argv template must contain dynamic value `{dynamic_value}` exactly once, found {occurrences}"
                ));
            }
        }
        CommandPayload::ActionInputs { inputs, dynamic_value } => {
            validate_text(dynamic_value)?;
            validate_action_inputs(inputs)?;
        }
    }
    Ok(())
}

fn validate_action_inputs(inputs: &BTreeMap<String, JsonValue>) -> Result<(), String> {
    if inputs.keys().map(String::as_str).collect::<Vec<_>>() != ["uses", "with"] {
        return Err("action-input payload must have exactly sorted `uses` and `with` keys".into());
    }
    let Some(JsonValue::String(uses)) = inputs.get("uses") else {
        return Err("action-input `uses` must be a string".into());
    };
    validate_action_reference(uses)?;
    let Some(JsonValue::Object(with)) = inputs.get("with") else {
        return Err("action-input `with` must be an object".into());
    };
    if with.is_empty() {
        return Err("action-input `with` must not be empty".into());
    }
    for (name, value) in with {
        BaselineId::parse(name).map_err(|reason| format!("action input name `{name}` {reason}"))?;
        let JsonValue::String(value) = value else {
            return Err(format!("action input `{name}` must have a string value"));
        };
        if value.chars().any(char::is_control) {
            return Err(format!("action input `{name}` contains a control character"));
        }
    }
    Ok(())
}

fn validate_json_text(value: &JsonValue) -> Result<(), String> {
    match value {
        JsonValue::String(value) => {
            if value.chars().any(char::is_control) {
                Err("JSON strings must not contain control characters".into())
            } else {
                Ok(())
            }
        }
        JsonValue::Array(values) => {
            for value in values {
                validate_json_text(value)?;
            }
            Ok(())
        }
        JsonValue::Object(values) => {
            for (key, value) in values {
                if key.is_empty() || key.chars().any(char::is_control) {
                    return Err(
                        "JSON object keys must be nonempty and contain no control characters"
                            .into(),
                    );
                }
                validate_json_text(value)?;
            }
            Ok(())
        }
    }
}

/// Parses the deliberately small JSON subset used by the baseline and then
/// requires byte-for-byte canonical serialization. This rejects insignificant
/// whitespace, alternate escapes, and unsorted object keys rather than allowing
/// multiple reviewed spellings for one command.
fn parse_canonical_json(source: &str) -> Result<JsonValue, String> {
    let mut parser = JsonParser { source, offset: 0 };
    let value = parser.parse_value()?;
    if parser.offset != source.len() {
        return Err(format!("unexpected JSON input at byte {}", parser.offset));
    }
    let mut canonical = String::new();
    write_json(&value, &mut canonical);
    if canonical != source {
        return Err("JSON must use compact canonical spelling and sorted object keys".into());
    }
    Ok(value)
}

struct JsonParser<'a> {
    source: &'a str,
    offset: usize,
}

impl JsonParser<'_> {
    fn parse_value(&mut self) -> Result<JsonValue, String> {
        match self.peek_byte() {
            Some(b'"') => self.parse_string().map(JsonValue::String),
            Some(b'[') => self.parse_array(),
            Some(b'{') => self.parse_object(),
            Some(byte) => Err(format!(
                "unsupported or malformed JSON value beginning with byte `{byte}` at byte {}",
                self.offset
            )),
            None => Err("JSON value must not be empty".into()),
        }
    }

    fn parse_array(&mut self) -> Result<JsonValue, String> {
        self.expect_byte(b'[')?;
        let mut values = Vec::new();
        if self.consume_byte(b']') {
            return Ok(JsonValue::Array(values));
        }
        loop {
            values.push(self.parse_value()?);
            if self.consume_byte(b']') {
                break;
            }
            self.expect_byte(b',')?;
        }
        Ok(JsonValue::Array(values))
    }

    fn parse_object(&mut self) -> Result<JsonValue, String> {
        self.expect_byte(b'{')?;
        let mut values = BTreeMap::new();
        if self.consume_byte(b'}') {
            return Ok(JsonValue::Object(values));
        }
        loop {
            let key = self.parse_string()?;
            self.expect_byte(b':')?;
            let value = self.parse_value()?;
            if values.insert(key.clone(), value).is_some() {
                return Err(format!("duplicate JSON object key `{key}`"));
            }
            if self.consume_byte(b'}') {
                break;
            }
            self.expect_byte(b',')?;
        }
        Ok(JsonValue::Object(values))
    }

    fn parse_string(&mut self) -> Result<String, String> {
        self.expect_byte(b'"')?;
        let mut value = String::new();
        loop {
            let Some(byte) = self.peek_byte() else {
                return Err("unterminated JSON string".into());
            };
            match byte {
                b'"' => {
                    self.offset += 1;
                    return Ok(value);
                }
                b'\\' => {
                    self.offset += 1;
                    let Some(escape) = self.peek_byte() else {
                        return Err("unterminated JSON escape".into());
                    };
                    self.offset += 1;
                    match escape {
                        b'"' => value.push('"'),
                        b'\\' => value.push('\\'),
                        b'/' => value.push('/'),
                        b'b' => value.push('\u{0008}'),
                        b'f' => value.push('\u{000c}'),
                        b'n' => value.push('\n'),
                        b'r' => value.push('\r'),
                        b't' => value.push('\t'),
                        b'u' => value.push(self.parse_unicode_escape()?),
                        _ => {
                            return Err(format!("invalid JSON escape at byte {}", self.offset - 1));
                        }
                    }
                }
                0x00..=0x1f => {
                    return Err(format!(
                        "unescaped control byte in JSON string at byte {}",
                        self.offset
                    ));
                }
                _ => {
                    let character = self.source[self.offset..]
                        .chars()
                        .next()
                        .expect("a nonempty UTF-8 suffix has one character");
                    value.push(character);
                    self.offset += character.len_utf8();
                }
            }
        }
    }

    fn parse_unicode_escape(&mut self) -> Result<char, String> {
        let first = self.parse_hex_quad()?;
        let scalar = if (0xd800..=0xdbff).contains(&first) {
            self.expect_byte(b'\\')?;
            self.expect_byte(b'u')?;
            let second = self.parse_hex_quad()?;
            if !(0xdc00..=0xdfff).contains(&second) {
                return Err("high UTF-16 surrogate is not followed by a low surrogate".into());
            }
            0x10000 + (((first - 0xd800) as u32) << 10) + (second - 0xdc00) as u32
        } else if (0xdc00..=0xdfff).contains(&first) {
            return Err("unpaired low UTF-16 surrogate".into());
        } else {
            first as u32
        };
        char::from_u32(scalar).ok_or_else(|| "JSON escape is not a Unicode scalar value".into())
    }

    fn parse_hex_quad(&mut self) -> Result<u16, String> {
        let mut value = 0_u16;
        for _ in 0..4 {
            let Some(byte) = self.peek_byte() else {
                return Err("incomplete JSON Unicode escape".into());
            };
            let Some(digit) = (byte as char).to_digit(16) else {
                return Err(format!("non-hexadecimal JSON Unicode escape byte at {}", self.offset));
            };
            self.offset += 1;
            value = (value << 4) | digit as u16;
        }
        Ok(value)
    }

    fn peek_byte(&self) -> Option<u8> {
        self.source.as_bytes().get(self.offset).copied()
    }

    fn consume_byte(&mut self, expected: u8) -> bool {
        if self.peek_byte() == Some(expected) {
            self.offset += 1;
            true
        } else {
            false
        }
    }

    fn expect_byte(&mut self, expected: u8) -> Result<(), String> {
        if self.consume_byte(expected) {
            Ok(())
        } else {
            Err(format!("expected JSON byte `{}` at byte {}", expected as char, self.offset))
        }
    }
}

fn write_json(value: &JsonValue, output: &mut String) {
    match value {
        JsonValue::String(value) => write_json_string(value, output),
        JsonValue::Array(values) => {
            output.push('[');
            for (index, value) in values.iter().enumerate() {
                if index != 0 {
                    output.push(',');
                }
                write_json(value, output);
            }
            output.push(']');
        }
        JsonValue::Object(values) => {
            output.push('{');
            for (index, (key, value)) in values.iter().enumerate() {
                if index != 0 {
                    output.push(',');
                }
                write_json_string(key, output);
                output.push(':');
                write_json(value, output);
            }
            output.push('}');
        }
    }
}

fn write_json_string(value: &str, output: &mut String) {
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\u{0008}' => output.push_str("\\b"),
            '\u{000c}' => output.push_str("\\f"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character.is_control() => {
                use fmt::Write as _;
                write!(output, "\\u{:04x}", character as u32)
                    .expect("writing to a String cannot fail");
            }
            character => output.push(character),
        }
    }
    output.push('"');
}

#[cfg(test)]
mod tests {
    use super::*;

    const MANIFEST: &str = include_str!("../../../ci/baselines/manifest.tsv");
    const BUILD_REDUCED: &str = include_str!("../../../ci/baselines/build-pr.tsv");
    const BUILD_FULL: &str = include_str!("../../../ci/baselines/build-full.tsv");
    const MIRI_REDUCED: &str = include_str!("../../../ci/baselines/miri-pr.tsv");
    const MIRI_FULL: &str = include_str!("../../../ci/baselines/miri-full.tsv");
    const LOGICAL: &str = include_str!("../../../ci/baselines/logical-obligations.tsv");
    const STANDALONE: &str = include_str!("../../../ci/baselines/standalone-obligations.tsv");
    const COMMAND_GOLDENS: &str = include_str!("../../../ci/baselines/command-goldens.tsv");

    fn fixture_paths() -> LegacyBaselinePaths {
        LegacyBaselinePaths {
            manifest: "manifest.tsv".into(),
            build_reduced: "build-pr.tsv".into(),
            build_full: "build-full.tsv".into(),
            miri_reduced: "miri-pr.tsv".into(),
            miri_full: "miri-full.tsv".into(),
            logical_obligations: "logical-obligations.tsv".into(),
            standalone_obligations: "standalone-obligations.tsv".into(),
            command_goldens: "command-goldens.tsv".into(),
        }
    }

    fn parse_sources_with<'a>(
        paths: &LegacyBaselinePaths,
        build_reduced: &'a str,
        manifest: &'a str,
    ) -> Result<LegacyBaselines, BaselineError> {
        LegacyBaselines::parse_sources(
            paths,
            BaselineSources {
                manifest,
                build_reduced,
                build_full: BUILD_FULL,
                miri_reduced: MIRI_REDUCED,
                miri_full: MIRI_FULL,
                logical_obligations: LOGICAL,
                standalone_obligations: STANDALONE,
                command_goldens: COMMAND_GOLDENS,
            },
        )
    }

    fn current_baseline() -> LegacyBaselines {
        parse_sources_with(&fixture_paths(), BUILD_REDUCED, MANIFEST).unwrap()
    }

    fn replace_once(source: &str, old: &str, new: &str) -> String {
        assert!(source.contains(old), "mutation anchor must occur: {old:?}");
        source.replacen(old, new, 1)
    }

    fn swap_first_two_data_rows(source: &str, header: &str) -> String {
        let mut lines = source.lines().collect::<Vec<_>>();
        let header = lines.iter().position(|line| *line == header).unwrap();
        lines.swap(header + 1, header + 2);
        lines.join("\n") + "\n"
    }

    #[test]
    fn parses_every_current_fixture_exactly() {
        let baseline = current_baseline();

        assert_eq!(baseline.manifest.source_commit, "286dd29655e7ae2f5603a8af89c270cc3bd52f2e");
        assert_eq!(baseline.build_reduced.len(), 60);
        assert_eq!(baseline.build_full.len(), 182);
        assert!(baseline.miri_reduced.is_empty());
        assert_eq!(baseline.miri_full.len(), 64);
        assert_eq!(baseline.logical_obligations.len(), 475);
        assert_eq!(baseline.standalone_obligations.len(), 31);
        assert_eq!(baseline.command_goldens.len(), 13);

        let stacked =
            baseline.miri_full.iter().find(|cell| cell.model.as_str() == "stacked").unwrap();
        assert!(stacked.model_flags.is_empty());
        let tree = baseline.miri_full.iter().find(|cell| cell.model.as_str() == "tree").unwrap();
        assert_eq!(tree.model_flags, ["-Zmiri-tree-borrows"]);

        // Re-comparing the parsed sets also exercises the no-difference path
        // through every public comparator.
        baseline.compare_build_reduced(&baseline.build_reduced).unwrap();
        baseline.compare_build_full(&baseline.build_full).unwrap();
        baseline.compare_miri_reduced(&baseline.miri_reduced).unwrap();
        baseline.compare_miri_full(&baseline.miri_full).unwrap();
        baseline.compare_logical_obligations(&baseline.logical_obligations).unwrap();
        baseline.compare_standalone_obligations(&baseline.standalone_obligations).unwrap();
        let behaviors = CommandBehaviors::try_from_iter(
            baseline.command_goldens.values().map(|golden| golden.behavior.clone()),
        )
        .unwrap();
        baseline.compare_command_goldens(&behaviors).unwrap();
    }

    #[test]
    fn exact_comparison_reports_missing_and_extra_rows_separately() {
        let baseline = current_baseline();
        let mut planned = baseline.build_reduced.clone();
        let missing = planned.iter().next().unwrap().clone();
        assert!(planned.remove(&missing));
        let extra = BuildCell {
            package: "future-package".parse().unwrap(),
            toolchain: "stable".parse().unwrap(),
            feature_profile: "default".parse().unwrap(),
            target: "x86_64-unknown-linux-gnu".parse().unwrap(),
        };
        assert!(planned.insert(extra.clone()));

        let difference = baseline.compare_build_reduced(&planned).unwrap_err();
        assert_eq!(difference.missing_from_plan(), &BTreeSet::from([missing]));
        assert_eq!(difference.extra_in_plan(), &BTreeSet::from([extra]));
        let diagnostic = difference.to_string();
        assert!(diagnostic.contains("1 missing, 1 extra"));
        assert!(diagnostic.contains("- missing: BuildCell"));
        assert!(diagnostic.contains("- extra: BuildCell"));
    }

    #[test]
    fn missing_and_extra_fixture_rows_fail_manifest_cross_checks() {
        let paths = fixture_paths();
        let first = "zerocopy\tmsrv\tdefault\ti686-unknown-linux-gnu\n";
        let missing = replace_once(BUILD_REDUCED, first, "");
        let error = parse_sources_with(&paths, &missing, MANIFEST).unwrap_err();
        assert!(error.to_string().contains("records 60"));
        assert!(error.to_string().contains("contains 59"));

        // `qemu` sorts between the existing `i686` and `x86_64` target rows,
        // so this mutation reaches the count cross-check rather than failing
        // earlier for an unrelated ordering problem.
        let extra_row = concat!(
            "zerocopy\tmsrv\tdefault\ti686-unknown-linux-gnu\n",
            "zerocopy\tmsrv\tdefault\tqemu-unknown-linux-gnu\n"
        );
        let extra = replace_once(BUILD_REDUCED, first, extra_row);
        let error = parse_sources_with(&paths, &extra, MANIFEST).unwrap_err();
        assert!(error.to_string().contains("records 60"));
        assert!(error.to_string().contains("contains 61"));
    }

    #[test]
    fn rejects_reordered_and_duplicate_rows() {
        let path = Path::new("build-pr.tsv");
        let reordered = swap_first_two_data_rows(BUILD_REDUCED, BUILD_HEADER);
        let error = parse_build_cells(path, &reordered).unwrap_err();
        assert!(error.to_string().contains("strictly bytewise sorted"));

        let first = "zerocopy\tmsrv\tdefault\ti686-unknown-linux-gnu\n";
        let duplicate = replace_once(BUILD_REDUCED, first, &format!("{first}{first}"));
        let error = parse_build_cells(path, &duplicate).unwrap_err();
        assert!(error.to_string().contains("duplicate row"));
    }

    #[test]
    fn rejects_wrong_headers_field_counts_and_carriage_returns() {
        let path = Path::new("build-pr.tsv");
        let wrong_header = replace_once(BUILD_REDUCED, BUILD_HEADER, "crate\ttoolchain\ttarget");
        assert!(parse_build_cells(path, &wrong_header)
            .unwrap_err()
            .to_string()
            .contains("expected exact header"));

        let row = "zerocopy\tmsrv\tdefault\ti686-unknown-linux-gnu";
        let too_many = replace_once(BUILD_REDUCED, row, &format!("{row}\textra"));
        assert!(parse_build_cells(path, &too_many)
            .unwrap_err()
            .to_string()
            .contains("expected 4 tab-separated fields"));

        let carriage_return = BUILD_REDUCED.replacen('\n', "\r\n", 1);
        assert!(parse_build_cells(path, &carriage_return)
            .unwrap_err()
            .to_string()
            .contains("carriage returns"));

        let comment_control =
            replace_once(BUILD_REDUCED, "# Copyright 2026", "# Copyright\u{0001} 2026");
        assert!(parse_build_cells(path, &comment_control)
            .unwrap_err()
            .to_string()
            .contains("comments must not contain control characters"));
    }

    #[test]
    fn rejects_unsafe_identifiers_paths_and_action_references() {
        let build = replace_once(
            BUILD_REDUCED,
            "zerocopy\tmsrv\tdefault\ti686-unknown-linux-gnu",
            "../zerocopy\tmsrv\tdefault\ti686-unknown-linux-gnu",
        );
        assert!(parse_build_cells(Path::new("build-pr.tsv"), &build)
            .unwrap_err()
            .to_string()
            .contains("stable identifier"));

        let escaped = replace_once(
            BUILD_REDUCED,
            "zerocopy\tmsrv\tdefault\ti686-unknown-linux-gnu",
            "zero\u{001b}copy\tmsrv\tdefault\ti686-unknown-linux-gnu",
        );
        let diagnostic =
            parse_build_cells(Path::new("build-pr.tsv"), &escaped).unwrap_err().to_string();
        assert!(!diagnostic.contains('\u{001b}'));

        let standalone =
            replace_once(STANDALONE, "\tzerocopy\tdirect\t", "\t../zerocopy\tdirect\t");
        assert!(parse_standalone_obligations(Path::new("standalone.tsv"), &standalone)
            .unwrap_err()
            .to_string()
            .contains("safe, normalized repository-relative path"));

        for path in ["dir/./file", "dir/."] {
            assert!(WorkingDirectory::parse(path).is_err());
        }
        assert!(WorkingDirectory::parse(".github/actions/check").is_ok());

        let action = replace_once(
            STANDALONE,
            "docker/build-push-action@53b7df96c91f9c12dcc8a07bcb9ccacbed38856a",
            "docker/build-push-action@floating-tag",
        );
        assert!(parse_standalone_obligations(Path::new("standalone.tsv"), &action)
            .unwrap_err()
            .to_string()
            .contains("lowercase hexadecimal"));

        let revision = "0123456789abcdef0123456789abcdef01234567";
        for repository in ["../repo", "owner/.."] {
            assert!(validate_action_reference(&format!("{repository}@{revision}")).is_err());
        }
    }

    #[test]
    fn rejects_missing_extra_false_and_noncanonical_manifest_values() {
        let path = Path::new("manifest.tsv");
        let missing = replace_once(MANIFEST, "build_pr_cells\t60\n", "");
        assert!(parse_manifest(path, &missing)
            .unwrap_err()
            .to_string()
            .contains("missing manifest key `build_pr_cells`"));

        let extra = replace_once(
            MANIFEST,
            "generic_manual_miri_sets_equal\ttrue\n",
            "generic_manual_miri_sets_equal\ttrue\nlegacy_extra\t1\n",
        );
        assert!(parse_manifest(path, &extra)
            .unwrap_err()
            .to_string()
            .contains("unknown manifest key `legacy_extra`"));

        let unequal = replace_once(
            MANIFEST,
            "generic_manual_build_sets_equal\ttrue",
            "generic_manual_build_sets_equal\tfalse",
        );
        assert!(parse_manifest(path, &unequal)
            .unwrap_err()
            .to_string()
            .contains("not valid evidence"));

        let leading_zero = replace_once(MANIFEST, "build_pr_cells\t60", "build_pr_cells\t060");
        assert!(parse_manifest(path, &leading_zero)
            .unwrap_err()
            .to_string()
            .contains("canonical unsigned decimal"));
    }

    #[test]
    fn rejects_malformed_and_noncanonical_json_fields() {
        let path = Path::new("command-goldens.tsv");
        let environment = replace_once(
            COMMAND_GOLDENS,
            r#"{"RUSTFLAGS":"-C target-cpu=atmega328p"}"#,
            r#"{"RUSTFLAGS":}"#,
        );
        assert!(parse_command_goldens(path, &environment)
            .unwrap_err()
            .to_string()
            .contains("environment_json"));

        let argv = replace_once(
            COMMAND_GOLDENS,
            r#"["./cargo.sh","+nightly","check","--target=avr-none","-Zbuild-std=core","--features","simd,simd-nightly,float-nightly,derive"]"#,
            r#"["./cargo.sh",]"#,
        );
        assert!(parse_command_goldens(path, &argv).unwrap_err().to_string().contains("payload"));

        let noncanonical = replace_once(
            COMMAND_GOLDENS,
            r#"{"MIRIFLAGS":" -Zmiri-strict-provenance -Zmiri-backtrace=full","RUSTDOCFLAGS":"-Dwarnings --cfg=zerocopy_unstable_ptr","RUSTFLAGS":"-Dwarnings -Zrandomize-layout"}"#,
            r#"{"RUSTFLAGS":"-Dwarnings -Zrandomize-layout","MIRIFLAGS":" -Zmiri-strict-provenance -Zmiri-backtrace=full","RUSTDOCFLAGS":"-Dwarnings --cfg=zerocopy_unstable_ptr"}"#,
        );
        assert!(parse_command_goldens(path, &noncanonical)
            .unwrap_err()
            .to_string()
            .contains("compact canonical spelling"));

        let decoded_control = replace_once(
            COMMAND_GOLDENS,
            r#"{"RUSTFLAGS":"-C target-cpu=atmega328p"}"#,
            r#"{"RUSTFLAGS":"\n"}"#,
        );
        assert!(parse_command_goldens(path, &decoded_control)
            .unwrap_err()
            .to_string()
            .contains("control character"));

        let decoded_escape = replace_once(
            COMMAND_GOLDENS,
            r#"{"RUSTFLAGS":"-C target-cpu=atmega328p"}"#,
            r#"{"\u001b":"-C target-cpu=atmega328p"}"#,
        );
        let diagnostic = parse_command_goldens(path, &decoded_escape).unwrap_err().to_string();
        assert!(!diagnostic.contains('\u{001b}'));
    }

    #[test]
    fn rejects_inconsistent_command_forms() {
        let path = Path::new("command-goldens.tsv");
        let template_without_dynamic_value = replace_once(
            COMMAND_GOLDENS,
            "\targv\t[\"./cargo.sh\",\"+nightly\",\"check\",\"--target=avr-none\",\"-Zbuild-std=core\",\"--features\",\"simd,simd-nightly,float-nightly,derive\"]\t\t",
            "\targv-template\t[\"./cargo.sh\",\"+nightly\",\"check\",\"--target=avr-none\",\"-Zbuild-std=core\",\"--features\",\"simd,simd-nightly,float-nightly,derive\"]\t\t",
        );
        assert!(parse_command_goldens(path, &template_without_dynamic_value)
            .unwrap_err()
            .to_string()
            .contains("dynamic_value"));

        let missing_template_placeholder = replace_once(COMMAND_GOLDENS, "\"<2*nproc>\"", "\"2\"");
        assert!(parse_command_goldens(path, &missing_template_placeholder)
            .unwrap_err()
            .to_string()
            .contains("exactly once"));
    }

    #[test]
    fn command_comparison_ignores_notes_but_not_behavior() {
        let baseline = current_baseline();
        let changed_note = replace_once(
            COMMAND_GOLDENS,
            "The step-level RUSTFLAGS replaces the workflow value.",
            "Equivalent command with clearer reviewer prose.",
        );
        let changed_note = parse_command_goldens(Path::new("commands.tsv"), &changed_note).unwrap();
        let planned = CommandBehaviors::try_from_iter(
            changed_note.values().map(|golden| golden.behavior.clone()),
        )
        .unwrap();
        baseline.compare_command_goldens(&planned).unwrap();

        let changed_environment = replace_once(
            COMMAND_GOLDENS,
            r#"{"RUSTFLAGS":"-C target-cpu=atmega328p"}"#,
            r#"{"RUSTFLAGS":"-C target-cpu=atmega328"}"#,
        );
        let changed_environment =
            parse_command_goldens(Path::new("commands.tsv"), &changed_environment).unwrap();
        let planned = CommandBehaviors::try_from_iter(
            changed_environment.values().map(|golden| golden.behavior.clone()),
        )
        .unwrap();
        assert!(baseline.compare_command_goldens(&planned).is_err());
    }

    #[test]
    fn rejects_noncanonical_logical_counts_and_sources() {
        let path = Path::new("logical.tsv");
        let count = replace_once(
            LOGICAL,
            "avr-check\t\t\t\t\t\t1\t1\talways",
            "avr-check\t\t\t\t\t\t01\t1\talways",
        );
        assert!(parse_logical_obligations(path, &count)
            .unwrap_err()
            .to_string()
            .contains("canonical unsigned decimal"));

        let sources = replace_once(
            LOGICAL,
            "check-all-toolchains-tested/Run check | run-git-hooks/Run dependency check",
            "run-git-hooks/Run dependency check | check-all-toolchains-tested/Run check",
        );
        assert!(parse_logical_obligations(path, &sources)
            .unwrap_err()
            .to_string()
            .contains("sources must be unique and strictly sorted"));
    }

    #[test]
    fn rejects_conflicting_duplicate_semantic_keys() {
        let logical_row =
            "avr-check\t\t\t\t\t\t1\t1\talways\tcheck_avr_atmega/Check avr-none target\n";
        let conflicting_logical = format!(
            "{logical_row}avr-check\t\t\t\t\t\t2\t1\talways\tcheck_avr_atmega/Check avr-none target\n"
        );
        let logical = replace_once(LOGICAL, logical_row, &conflicting_logical);
        assert!(parse_logical_obligations(Path::new("logical.tsv"), &logical)
            .unwrap_err()
            .to_string()
            .contains("duplicate logical-obligation key"));

        let command_row =
            COMMAND_GOLDENS.lines().find(|line| line.starts_with("avr-check\t")).unwrap();
        let conflicting_command =
            command_row.replacen("\tcheck_avr_atmega\t", "\tdifferent_job\t", 1);
        let commands = replace_once(
            COMMAND_GOLDENS,
            &format!("{command_row}\n"),
            &format!("{command_row}\n{conflicting_command}\n"),
        );
        assert!(parse_command_goldens(Path::new("commands.tsv"), &commands)
            .unwrap_err()
            .to_string()
            .contains("command-golden name `avr-check` duplicates"));

        let id = |value: &str| value.parse::<BaselineId>().unwrap();
        let source = ObligationSource::new(id("job"), "Step").unwrap();
        let obligation = |full_occurrences| {
            LogicalObligation::new(
                id("cargo-test"),
                Some(id("zerocopy")),
                Some(id("stable")),
                Some(id("default")),
                Some(id("x86_64-unknown-linux-gnu")),
                None,
                1,
                full_occurrences,
                ObligationCondition::Always,
                vec![source.clone()],
            )
            .unwrap()
        };
        assert!(LogicalObligations::try_from_iter([obligation(1), obligation(2)]).is_err());

        let behavior = |argument: &str| {
            CommandBehavior::new(
                id("golden"),
                id("job"),
                "Step",
                WorkingDirectory::RepositoryRoot,
                BTreeMap::new(),
                CommandPayload::Argv { argv: vec![argument.to_owned()], dynamic_value: None },
            )
            .unwrap()
        };
        assert!(CommandBehaviors::try_from_iter([behavior("one"), behavior("two")]).is_err());
    }

    #[test]
    fn small_json_parser_rejects_ambiguous_or_unsupported_forms() {
        assert_eq!(
            parse_canonical_json(r#"{"a":["b"],"c":{"d":"e"}}"#).unwrap(),
            JsonValue::Object(BTreeMap::from([
                ("a".into(), JsonValue::Array(vec![JsonValue::String("b".into())])),
                (
                    "c".into(),
                    JsonValue::Object(BTreeMap::from([(
                        "d".into(),
                        JsonValue::String("e".into())
                    )]))
                ),
            ]))
        );

        for invalid in [
            r#"{"b":"1","a":"2"}"#,
            r#"{"a":"1","a":"2"}"#,
            r#"{ "a":"1"}"#,
            r#"["value",]"#,
            r#""\u0061""#,
            "true",
            "1",
            "null",
        ] {
            assert!(
                parse_canonical_json(invalid).is_err(),
                "unexpectedly accepted noncanonical JSON: {invalid}"
            );
        }
    }

    #[test]
    fn public_constructors_recheck_string_bearing_values() {
        let id = |value: &str| value.parse::<BaselineId>().unwrap();
        assert!(MiriCell::new(
            id("zerocopy"),
            id("nightly"),
            id("default"),
            id("x86_64-unknown-linux-gnu"),
            id("tree"),
            vec!["-Zvalid".into(), "two words".into()],
        )
        .is_err());

        assert!(StandaloneObligation::new(
            id("operation"),
            StandaloneEvents::PullRequestAndFull,
            id("job"),
            "Step",
            WorkingDirectory::Relative("../outside".into()),
            StandaloneInvocation::Direct(vec!["command".into()]),
        )
        .is_err());

        let noncanonical_root = WorkingDirectory::Relative(".".into());
        let error = StandaloneObligation::new(
            id("operation"),
            StandaloneEvents::PullRequestAndFull,
            id("job"),
            "Step",
            noncanonical_root.clone(),
            StandaloneInvocation::Direct(vec!["command".into()]),
        )
        .unwrap_err();
        assert!(error.contains("canonical enum representation"));

        let error = CommandBehavior::new(
            id("golden"),
            id("job"),
            "Step",
            noncanonical_root,
            BTreeMap::new(),
            CommandPayload::Argv { argv: vec!["command".into()], dynamic_value: None },
        )
        .unwrap_err();
        assert!(error.contains("canonical enum representation"));

        assert!(LogicalObligation::new(
            id("cargo-test"),
            Some(id("zerocopy")),
            Some(id("stable")),
            Some(id("default")),
            Some(id("x86_64-unknown-linux-gnu")),
            None,
            0,
            0,
            ObligationCondition::Always,
            vec![ObligationSource::new(id("job"), "Step").unwrap()],
        )
        .is_err());

        let malformed_inputs =
            BTreeMap::from([("uses".into(), JsonValue::String("owner/repo@floating".into()))]);
        assert!(CommandBehavior::new(
            id("golden"),
            id("job"),
            "Step",
            WorkingDirectory::RepositoryRoot,
            BTreeMap::new(),
            CommandPayload::ActionInputs {
                inputs: malformed_inputs,
                dynamic_value: "third-party implementation".into(),
            },
        )
        .is_err());
    }
}
