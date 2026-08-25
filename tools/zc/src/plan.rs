// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure, deterministic selection of CI matrix membership.
//!
//! [`CiInputs`] is the only public input boundary. By the time data reaches
//! this module, `ci/zc.toml`, live Cargo metadata, repository structure, and
//! the frozen legacy files have each passed their owning validator. Planning
//! therefore performs no file-system access and has no ambient inputs.
//!
//! This module selects ordinary build, Miri, and semver matrix members; it does
//! not prove how GitHub executes them. In particular, a plan never contains
//! permissions, secrets, runner labels, action references, publication
//! choices, or shell commands. Keep those security-sensitive concerns in the
//! small hand-written workflows.
//!
//! The types below record the intended semantics preserved by the review
//! artifact and typed executor. The workflow consumes only complete selectors;
//! the executor resolves their command behavior again from this checked plan.
//! Matrix membership equality alone cannot prove, for example, that native
//! tests are executed, cross-target tests are only compiled, or Miri tests are
//! interpreted.
//!
//! The selectors below coordinate three independently reviewed sources:
//! policy supplies stable IDs and scopes, inventory supplies exact compiler
//! versions and Cargo package paths, and `ci/baselines/*.tsv` freezes the old
//! build and Miri sets. Every call compares all four reduced/full membership
//! sets before returning a plan, so a policy edit cannot silently redefine the
//! selected legacy matrix.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    path::{Path, PathBuf},
    str::FromStr,
};

use thiserror::Error;

use crate::{
    baseline::{BaselineId, BuildCell, LegacyBaselines, MiriCell, SetDifference},
    ci::CiInputs,
    inventory::RepositoryInventory,
    policy::{EventCategory, FeatureProfile, Id, Policy, Scope, Semver, TargetMode},
};

/// Whether the event receives reduced or full policy coverage.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum EventClass {
    /// Latency-optimized coverage, currently used by pull requests.
    Reduced,
    /// Full coverage, used by merge queue, manual, and push events.
    Full,
}

impl From<EventCategory> for EventClass {
    fn from(category: EventCategory) -> Self {
        match category {
            EventCategory::Reduced => Self::Reduced,
            EventCategory::Full => Self::Full,
        }
    }
}

impl fmt::Display for EventClass {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Reduced => formatter.write_str("reduced"),
            Self::Full => formatter.write_str("full"),
        }
    }
}

// The row-oriented TSV baselines freeze reduced and full matrix membership,
// but they cannot say which GitHub event selects each set. Keep this small,
// independent event-class baseline until that relationship has its own
// versioned input. The invariant below makes a policy-only event change fail
// instead of silently changing which event receives which legacy matrix.
const LEGACY_EVENT_CLASSES: [(&str, EventClass); 4] = [
    ("merge_group", EventClass::Full),
    ("pull_request", EventClass::Reduced),
    ("push", EventClass::Full),
    ("workflow_dispatch", EventClass::Full),
];

/// How the typed executor must handle an ordinary compilation target.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ExecutionMode {
    /// Build and execute tests on the runner.
    Native,
    /// Compile test code and build library code without executing tests.
    Cross,
    /// Check only library code because test dependencies cannot be compiled.
    Thumb,
}

impl From<TargetMode> for ExecutionMode {
    fn from(mode: TargetMode) -> Self {
        match mode {
            TargetMode::Native => Self::Native,
            TargetMode::Cross => Self::Cross,
            TargetMode::Thumb => Self::Thumb,
        }
    }
}

/// A semantic Cargo feature selection.
///
/// The variants record meaning, and [`Self::cargo_args`] is the one checked
/// translation of that meaning to exact Cargo argument boundaries. Keeping the
/// translation here makes adding a variant a compiler-enforced update instead
/// of requiring unrelated projection and execution code to agree on strings.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FeatureSelection {
    /// Use Cargo's default feature selection.
    Default,
    /// Disable Cargo defaults without selecting another feature.
    NoDefault,
    /// Disable defaults and select the repository's stable aggregate feature.
    StableAggregate {
        /// The Cargo feature name obtained from validated policy.
        feature: String,
    },
    /// Select every Cargo feature.
    All,
}

impl FeatureSelection {
    /// Returns the exact ordered Cargo arguments for this selection.
    ///
    /// The vector preserves argument boundaries; the executor passes its
    /// entries directly to a process rather than joining them into shell text.
    pub fn cargo_args(&self) -> Vec<String> {
        match self {
            Self::Default => Vec::new(),
            Self::NoDefault => vec!["--no-default-features".to_owned()],
            Self::StableAggregate { feature } => {
                vec!["--no-default-features".to_owned(), "--features".to_owned(), feature.clone()]
            }
            Self::All => vec!["--all-features".to_owned()],
        }
    }
}

/// A package selected for work.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PackageSelector {
    id: String,
    manifest: PathBuf,
}

impl PackageSelector {
    /// Returns the stable policy and Cargo package ID.
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Returns the package manifest relative to the repository root.
    pub fn manifest(&self) -> &Path {
        &self.manifest
    }
}

/// An exact Rust toolchain selected for work.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ToolchainSelector {
    id: String,
    version: String,
}

impl ToolchainSelector {
    /// Returns the stable policy toolchain ID.
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Returns the exact compiler descriptor resolved by repository inventory.
    pub fn version(&self) -> &str {
        &self.version
    }
}

/// A named semantic feature profile selected for work.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FeatureSelector {
    profile: String,
    selection: FeatureSelection,
}

impl FeatureSelector {
    /// Returns the stable policy profile ID.
    pub fn profile(&self) -> &str {
        &self.profile
    }

    /// Returns the profile's Cargo semantics.
    pub fn selection(&self) -> &FeatureSelection {
        &self.selection
    }
}

/// An ordinary Rust compilation target selected for matrix membership.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TargetSelector {
    triple: String,
    mode: ExecutionMode,
}

impl TargetSelector {
    /// Returns the exact Rust target triple.
    pub fn triple(&self) -> &str {
        &self.triple
    }

    /// Returns the intended execution behavior for this ordinary target.
    pub fn mode(&self) -> ExecutionMode {
        self.mode
    }
}

/// A target whose tests Miri interprets.
///
/// This deliberately does not expose [`ExecutionMode`]. A target's ordinary
/// build mode describes what a native or cross-compilation job can execute;
/// it does not apply to Miri. Every selected Miri target runs tests inside the
/// Miri interpreter, including targets whose ordinary build mode is `Cross`.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MiriTargetSelector {
    triple: String,
}

impl MiriTargetSelector {
    /// Returns the target triple whose tests Miri must interpret.
    pub fn triple(&self) -> &str {
        &self.triple
    }
}

/// A target whose public API is checked for semver compatibility.
///
/// This deliberately does not expose [`ExecutionMode`]. The semver action
/// examines target-specific public API; it does not execute the ordinary
/// build behavior associated with the same target.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SemverTargetSelector {
    triple: String,
}

impl SemverTargetSelector {
    /// Returns the Rust target triple whose public API must be checked.
    pub fn triple(&self) -> &str {
        &self.triple
    }
}

/// A Miri borrow model selected for work.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MiriModelSelector {
    id: String,
    flags: Vec<String>,
}

impl MiriModelSelector {
    /// Returns the stable policy model ID.
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Returns exact model-specific flags in argument order.
    pub fn flags(&self) -> &[String] {
        &self.flags
    }
}

/// One selected ordinary build matrix member with typed semantic intent.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct BuildPlanCell {
    package: PackageSelector,
    toolchain: ToolchainSelector,
    features: FeatureSelector,
    target: TargetSelector,
}

impl BuildPlanCell {
    /// Returns the package selector.
    pub fn package(&self) -> &PackageSelector {
        &self.package
    }

    /// Returns the exact toolchain selector.
    pub fn toolchain(&self) -> &ToolchainSelector {
        &self.toolchain
    }

    /// Returns the semantic feature selector.
    pub fn features(&self) -> &FeatureSelector {
        &self.features
    }

    /// Returns the compilation-target selector.
    pub fn target(&self) -> &TargetSelector {
        &self.target
    }
}

/// One selected Miri matrix member with typed semantic intent.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MiriPlanCell {
    package: PackageSelector,
    toolchain: ToolchainSelector,
    features: FeatureSelector,
    target: MiriTargetSelector,
    model: MiriModelSelector,
}

impl MiriPlanCell {
    /// Returns the package selector.
    pub fn package(&self) -> &PackageSelector {
        &self.package
    }

    /// Returns the exact toolchain selector.
    pub fn toolchain(&self) -> &ToolchainSelector {
        &self.toolchain
    }

    /// Returns the semantic feature selector.
    pub fn features(&self) -> &FeatureSelector {
        &self.features
    }

    /// Returns the target whose tests Miri must interpret.
    pub fn target(&self) -> &MiriTargetSelector {
        &self.target
    }

    /// Returns the Miri model selector.
    pub fn model(&self) -> &MiriModelSelector {
        &self.model
    }
}

/// One selected semver matrix member with typed semantic intent.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SemverPlanCell {
    package: PackageSelector,
    toolchain: ToolchainSelector,
    features: FeatureSelector,
    target: SemverTargetSelector,
}

impl SemverPlanCell {
    /// Returns the package selector.
    pub fn package(&self) -> &PackageSelector {
        &self.package
    }

    /// Returns the exact toolchain selector.
    pub fn toolchain(&self) -> &ToolchainSelector {
        &self.toolchain
    }

    /// Returns the semantic feature selector.
    pub fn features(&self) -> &FeatureSelector {
        &self.features
    }

    /// Returns the target whose public API must be checked.
    pub fn target(&self) -> &SemverTargetSelector {
        &self.target
    }
}

/// Why the shared evaluator included or excluded one cell.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DecisionReason {
    /// Full events include every ordinary build candidate.
    FullEventIncludesBuild,
    /// A reduced event includes this target because policy marks it eligible.
    ReducedEventIncludesEligibleTarget,
    /// A reduced event excludes this target because it is not eligible.
    ReducedEventExcludesIneligibleTarget,
    /// This event category matches the category configured for Miri.
    MiriEventCategoryMatches,
    /// This event category does not match the category configured for Miri.
    MiriEventCategoryDoesNotMatch,
    /// Full events include every configured semver target.
    FullEventIncludesSemver,
    /// A reduced event includes this semver target because ordinary policy
    /// marks the corresponding target eligible for reduced events.
    ReducedEventIncludesEligibleSemverTarget,
    /// A reduced event excludes this semver target because ordinary policy
    /// does not mark the corresponding target eligible for reduced events.
    ReducedEventExcludesIneligibleSemverTarget,
}

impl fmt::Display for DecisionReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FullEventIncludesBuild => {
                formatter.write_str("included because full events run every build cell")
            }
            Self::ReducedEventIncludesEligibleTarget => formatter
                .write_str("included because policy marks the target eligible for reduced events"),
            Self::ReducedEventExcludesIneligibleTarget => formatter.write_str(
                "excluded because policy does not mark the target eligible for reduced events",
            ),
            Self::MiriEventCategoryMatches => {
                formatter.write_str("included because this event category runs Miri")
            }
            Self::MiriEventCategoryDoesNotMatch => {
                formatter.write_str("excluded because Miri runs in the other event category")
            }
            Self::FullEventIncludesSemver => {
                formatter.write_str("included because full events run every semver cell")
            }
            Self::ReducedEventIncludesEligibleSemverTarget => formatter.write_str(
                "included because policy marks the semver target eligible for reduced events",
            ),
            Self::ReducedEventExcludesIneligibleSemverTarget => formatter.write_str(
                "excluded because policy does not mark the semver target eligible for reduced events",
            ),
        }
    }
}

/// The inclusion decision produced by the shared evaluator.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CellDecision {
    /// The cell appears in the selected matrix membership.
    Included(DecisionReason),
    /// The candidate remains visible only in explanations.
    Excluded(DecisionReason),
}

impl CellDecision {
    /// Returns whether this candidate appears in the selected matrix.
    pub fn is_included(&self) -> bool {
        matches!(self, Self::Included(_))
    }

    /// Returns the typed reason for this decision.
    pub fn reason(&self) -> DecisionReason {
        match *self {
            Self::Included(reason) | Self::Excluded(reason) => reason,
        }
    }
}

impl fmt::Display for CellDecision {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.reason().fmt(formatter)
    }
}

/// One explained ordinary build candidate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExplainedBuildCell {
    cell: BuildPlanCell,
    decision: CellDecision,
}

impl ExplainedBuildCell {
    /// Returns the fully resolved candidate.
    pub fn cell(&self) -> &BuildPlanCell {
        &self.cell
    }

    /// Returns whether and why the candidate is selected.
    pub fn decision(&self) -> CellDecision {
        self.decision
    }
}

impl fmt::Display for ExplainedBuildCell {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "build {}/{}/{}/{}: {}",
            self.cell.package.id,
            self.cell.toolchain.id,
            self.cell.features.profile,
            self.cell.target.triple,
            self.decision
        )
    }
}

/// One explained Miri candidate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExplainedMiriCell {
    cell: MiriPlanCell,
    decision: CellDecision,
}

impl ExplainedMiriCell {
    /// Returns the fully resolved candidate.
    pub fn cell(&self) -> &MiriPlanCell {
        &self.cell
    }

    /// Returns whether and why the candidate is selected.
    pub fn decision(&self) -> CellDecision {
        self.decision
    }
}

/// One explained semver candidate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExplainedSemverCell {
    cell: SemverPlanCell,
    decision: CellDecision,
}

impl ExplainedSemverCell {
    /// Returns the fully resolved candidate.
    pub fn cell(&self) -> &SemverPlanCell {
        &self.cell
    }

    /// Returns whether and why the candidate is selected.
    pub fn decision(&self) -> CellDecision {
        self.decision
    }
}

impl fmt::Display for ExplainedSemverCell {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "semver {}/{}/{}/{}: {}",
            self.cell.package.id,
            self.cell.toolchain.id,
            self.cell.features.profile,
            self.cell.target.triple,
            self.decision
        )
    }
}

impl fmt::Display for ExplainedMiriCell {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "miri {}/{}/{}/{}/{}: {}",
            self.cell.package.id,
            self.cell.toolchain.id,
            self.cell.features.profile,
            self.cell.target.triple,
            self.cell.model.id,
            self.decision
        )
    }
}

/// Membership decisions for every policy-generated candidate for one event.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlanExplanation {
    event: String,
    class: EventClass,
    builds: Vec<ExplainedBuildCell>,
    miri: Vec<ExplainedMiriCell>,
    semver: Vec<ExplainedSemverCell>,
}

impl PlanExplanation {
    /// Applies the same membership selection path used by [`Plan::create`].
    pub fn create(inputs: &CiInputs, event: &str) -> Result<Self, PlanError> {
        EvaluatedPlan::evaluate(inputs, event).map(EvaluatedPlan::into_explanation)
    }

    /// Returns the exact GitHub event name.
    pub fn event(&self) -> &str {
        &self.event
    }

    /// Returns the event's policy category.
    pub fn class(&self) -> EventClass {
        self.class
    }

    /// Returns all ordinary candidates in deterministic order.
    pub fn builds(&self) -> &[ExplainedBuildCell] {
        &self.builds
    }

    /// Returns all Miri candidates in deterministic order.
    pub fn miri(&self) -> &[ExplainedMiriCell] {
        &self.miri
    }

    /// Returns all semver candidates in deterministic order.
    pub fn semver(&self) -> &[ExplainedSemverCell] {
        &self.semver
    }
}

impl fmt::Display for PlanExplanation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(formatter, "event `{}` has {} coverage:", self.event, self.class)?;
        for cell in &self.builds {
            writeln!(formatter, "- {cell}")?;
        }
        for cell in &self.miri {
            writeln!(formatter, "- {cell}")?;
        }
        for cell in &self.semver {
            writeln!(formatter, "- {cell}")?;
        }
        Ok(())
    }
}

/// The selected, data-only matrix membership for one exact event.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Plan {
    event: String,
    class: EventClass,
    builds: Vec<BuildPlanCell>,
    miri: Vec<MiriPlanCell>,
    semver: Vec<SemverPlanCell>,
}

impl Plan {
    /// Expands one exact event from fully validated inputs.
    pub fn create(inputs: &CiInputs, event: &str) -> Result<Self, PlanError> {
        EvaluatedPlan::evaluate(inputs, event).map(EvaluatedPlan::into_plan)
    }

    /// Returns the exact GitHub event name.
    pub fn event(&self) -> &str {
        &self.event
    }

    /// Returns the event's policy category.
    pub fn class(&self) -> EventClass {
        self.class
    }

    /// Returns ordinary build cells in deterministic order.
    pub fn builds(&self) -> &[BuildPlanCell] {
        &self.builds
    }

    /// Returns Miri cells in deterministic order.
    pub fn miri(&self) -> &[MiriPlanCell] {
        &self.miri
    }

    /// Returns semver cells in deterministic order.
    pub fn semver(&self) -> &[SemverPlanCell] {
        &self.semver
    }
}

#[derive(Clone, Debug)]
struct BuildCandidate {
    cell: BuildPlanCell,
    reduced_eligible: bool,
}

#[derive(Clone, Debug)]
struct SemverCandidate {
    cell: SemverPlanCell,
    reduced_eligible: bool,
}

#[derive(Clone, Debug)]
struct EvaluatedPlan {
    event: String,
    class: EventClass,
    builds: Vec<ExplainedBuildCell>,
    miri: Vec<ExplainedMiriCell>,
    semver: Vec<ExplainedSemverCell>,
}

impl EvaluatedPlan {
    fn evaluate(inputs: &CiInputs, event: &str) -> Result<Self, PlanError> {
        let policy = inputs.policy();
        validate_legacy_event_classes(policy)?;
        let class = classify_event(policy, event)?;
        let build_candidates = enumerate_build_candidates(policy, inputs.repository())?;
        let miri_candidates = enumerate_miri_candidates(policy, inputs.repository())?;
        let semver_candidates = enumerate_semver_candidates(policy, &build_candidates)?;

        validate_legacy_membership(policy, inputs.legacy(), &build_candidates, &miri_candidates)?;

        let builds = build_candidates
            .values()
            .map(|candidate| ExplainedBuildCell {
                cell: candidate.cell.clone(),
                decision: evaluate_build(class, candidate.reduced_eligible),
            })
            .collect::<Vec<_>>();
        let miri_class = EventClass::from(policy.miri().event_category());
        let miri = miri_candidates
            .iter()
            .cloned()
            .map(|cell| ExplainedMiriCell { cell, decision: evaluate_miri(class, miri_class) })
            .collect::<Vec<_>>();
        let semver = semver_candidates
            .values()
            .map(|candidate| ExplainedSemverCell {
                cell: candidate.cell.clone(),
                decision: evaluate_semver(class, candidate.reduced_eligible),
            })
            .collect::<Vec<_>>();

        let selected = builds.iter().filter(|cell| cell.decision.is_included()).count()
            + miri.iter().filter(|cell| cell.decision.is_included()).count()
            + semver.iter().filter(|cell| cell.decision.is_included()).count();
        enforce_plan_limit(selected, policy.limits().max_plan_cells())?;

        Ok(Self { event: event.to_owned(), class, builds, miri, semver })
    }

    fn into_plan(self) -> Plan {
        let builds = self
            .builds
            .into_iter()
            .filter_map(|candidate| candidate.decision.is_included().then_some(candidate.cell))
            .collect();
        let miri = self
            .miri
            .into_iter()
            .filter_map(|candidate| candidate.decision.is_included().then_some(candidate.cell))
            .collect();
        let semver = self
            .semver
            .into_iter()
            .filter_map(|candidate| candidate.decision.is_included().then_some(candidate.cell))
            .collect();
        Plan { event: self.event, class: self.class, builds, miri, semver }
    }

    fn into_explanation(self) -> PlanExplanation {
        PlanExplanation {
            event: self.event,
            class: self.class,
            builds: self.builds,
            miri: self.miri,
            semver: self.semver,
        }
    }
}

fn classify_event(policy: &Policy, event: &str) -> Result<EventClass, PlanError> {
    policy.events().category(event).map(EventClass::from).ok_or_else(|| {
        let known = policy
            .events()
            .reduced()
            .iter()
            .chain(policy.events().full())
            .map(Id::as_str)
            .collect::<Vec<_>>()
            .join(", ");
        PlanError::UnknownEvent {
            event: event.to_owned(),
            display_event: escape_control_characters(event),
            known,
        }
    })
}

fn validate_legacy_event_classes(policy: &Policy) -> Result<(), PlanError> {
    let actual = policy
        .events()
        .reduced()
        .iter()
        .map(|event| (event.as_str(), EventClass::Reduced))
        .chain(policy.events().full().iter().map(|event| (event.as_str(), EventClass::Full)))
        .collect::<BTreeMap<_, _>>();
    let expected = LEGACY_EVENT_CLASSES.into_iter().collect::<BTreeMap<_, _>>();
    if actual == expected {
        return Ok(());
    }

    let format_classes = |classes: &BTreeMap<&str, EventClass>| {
        classes
            .iter()
            .map(|(event, class)| format!("{event}={class}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    Err(PlanError::LegacyEventClassMismatch {
        expected: format_classes(&expected),
        actual: format_classes(&actual),
    })
}

fn enumerate_build_candidates(
    policy: &Policy,
    repository: &RepositoryInventory,
) -> Result<BTreeMap<BuildPlanCell, BuildCandidate>, PlanError> {
    let mut cells = BTreeMap::new();
    for (toolchain_id, toolchain_policy) in policy.toolchains() {
        let toolchain = toolchain_selector(repository, toolchain_id)?;
        for scope in toolchain_policy.scopes() {
            for package_id in scope.packages() {
                let package = package_selector(repository, package_id)?;
                for profile_id in scope.profiles() {
                    let features = feature_selector(policy, profile_id)?;
                    for target_id in target_set(policy, scope)? {
                        let target_policy =
                            policy.targets().get(target_id.as_str()).ok_or_else(|| {
                                PlanError::MissingValidatedInput {
                                    location: format!("targets.{}", target_id.as_str()),
                                }
                            })?;
                        let cell = BuildPlanCell {
                            package: package.clone(),
                            toolchain: toolchain.clone(),
                            features: features.clone(),
                            target: target_selector(target_id, target_policy.mode()),
                        };
                        let candidate = BuildCandidate {
                            cell: cell.clone(),
                            reduced_eligible: target_policy.pr_eligible(),
                        };
                        if cells.insert(cell.clone(), candidate).is_some() {
                            return Err(PlanError::DuplicateCell {
                                kind: "ordinary build",
                                selector: format_build_selector(&cell),
                            });
                        }
                    }
                }
            }
        }
    }
    Ok(cells)
}

fn enumerate_miri_candidates(
    policy: &Policy,
    repository: &RepositoryInventory,
) -> Result<BTreeSet<MiriPlanCell>, PlanError> {
    let mut cells = BTreeSet::new();
    let miri = policy.miri();
    let toolchain = toolchain_selector(repository, miri.toolchain())?;
    for scope in miri.scopes() {
        for package_id in scope.packages() {
            let package = package_selector(repository, package_id)?;
            for profile_id in scope.profiles() {
                let features = feature_selector(policy, profile_id)?;
                for target_id in target_set(policy, scope)? {
                    if !policy.targets().contains_key(target_id.as_str()) {
                        return Err(PlanError::MissingValidatedInput {
                            location: format!("targets.{}", target_id.as_str()),
                        });
                    }
                    let target = miri_target_selector(target_id);
                    for (model_id, model) in policy.miri_models() {
                        let cell = MiriPlanCell {
                            package: package.clone(),
                            toolchain: toolchain.clone(),
                            features: features.clone(),
                            target: target.clone(),
                            model: MiriModelSelector {
                                id: model_id.as_str().to_owned(),
                                flags: model.flags().to_vec(),
                            },
                        };
                        if !cells.insert(cell.clone()) {
                            return Err(PlanError::DuplicateCell {
                                kind: "Miri",
                                selector: format_miri_selector(&cell),
                            });
                        }
                    }
                }
            }
        }
    }
    Ok(cells)
}

/// Derives semver work from the corresponding ordinary-build candidates.
///
/// Semver has its own matrix and runner, but its event-specific membership is
/// deliberately the same as the package/toolchain/profile slice which used to
/// host it. A full event selects every configured semver target; a reduced
/// event inherits the target's ordinary reduced-event eligibility. Looking up
/// every configured target in `builds` also makes the policy invariant that
/// semver coverage is backed by ordinary build coverage fail closed here.
fn enumerate_semver_candidates(
    policy: &Policy,
    builds: &BTreeMap<BuildPlanCell, BuildCandidate>,
) -> Result<BTreeMap<SemverPlanCell, SemverCandidate>, PlanError> {
    let semver = policy.semver();
    let targets = policy.target_sets().get(semver.target_set().as_str()).ok_or_else(|| {
        PlanError::MissingValidatedInput {
            location: format!("target_sets.{}", semver.target_set().as_str()),
        }
    })?;
    let matching_builds = index_semver_build_coverage(semver, builds);
    let mut cells = BTreeMap::new();
    for target in targets {
        let matches = matching_builds.get(target.as_str()).map(Vec::as_slice).unwrap_or_default();
        let candidate = match matches {
            [candidate] => *candidate,
            [] => {
                return Err(PlanError::MissingValidatedInput {
                    location: format!(
                        "semver build coverage for {}/{}/{}/{}",
                        semver.package(),
                        semver.toolchain(),
                        semver.profile(),
                        target,
                    ),
                });
            }
            candidates => {
                return Err(PlanError::DuplicateCell {
                    kind: "semver build coverage",
                    selector: format!(
                        "{}/{}/{}/{} ({})",
                        semver.package(),
                        semver.toolchain(),
                        semver.profile(),
                        target,
                        candidates.len(),
                    ),
                });
            }
        };
        let cell = SemverPlanCell {
            package: candidate.cell.package.clone(),
            toolchain: candidate.cell.toolchain.clone(),
            features: candidate.cell.features.clone(),
            target: SemverTargetSelector { triple: target.as_str().to_owned() },
        };
        let semver_candidate =
            SemverCandidate { cell: cell.clone(), reduced_eligible: candidate.reduced_eligible };
        if cells.insert(cell.clone(), semver_candidate).is_some() {
            return Err(PlanError::DuplicateCell {
                kind: "semver",
                selector: format_semver_selector(&cell),
            });
        }
    }
    Ok(cells)
}

/// Indexes the ordinary-build slice which can provide semver coverage.
///
/// Keep this scan outside the configured-target loop above. The number of
/// ordinary scopes and the number of semver targets have independent bounds;
/// rescanning every expanded build for every target would make otherwise valid
/// high-cardinality policy take quadratic time. Retaining every match rather
/// than overwriting one preserves the duplicate diagnostic at the checked
/// planning boundary.
fn index_semver_build_coverage<'a>(
    semver: &Semver,
    builds: &'a BTreeMap<BuildPlanCell, BuildCandidate>,
) -> BTreeMap<&'a str, Vec<&'a BuildCandidate>> {
    let mut by_target: BTreeMap<&str, Vec<&BuildCandidate>> = BTreeMap::new();
    for candidate in builds.values() {
        let cell = &candidate.cell;
        if cell.package.id() == semver.package().as_str()
            && cell.toolchain.id() == semver.toolchain().as_str()
            && cell.features.profile() == semver.profile().as_str()
        {
            by_target.entry(cell.target.triple()).or_default().push(candidate);
        }
    }
    by_target
}

fn target_set<'a>(policy: &'a Policy, scope: &Scope) -> Result<&'a BTreeSet<Id>, PlanError> {
    policy.target_sets().get(scope.target_set().as_str()).ok_or_else(|| {
        PlanError::MissingValidatedInput {
            location: format!("target_sets.{}", scope.target_set().as_str()),
        }
    })
}

fn package_selector(
    repository: &RepositoryInventory,
    id: &Id,
) -> Result<PackageSelector, PlanError> {
    let package = repository.policy_packages().get(id.as_str()).ok_or_else(|| {
        PlanError::MissingValidatedInput { location: format!("inventory.packages.{}", id.as_str()) }
    })?;
    Ok(PackageSelector {
        id: id.as_str().to_owned(),
        manifest: package.cargo().manifest().to_path_buf(),
    })
}

fn toolchain_selector(
    repository: &RepositoryInventory,
    id: &Id,
) -> Result<ToolchainSelector, PlanError> {
    let version = repository.toolchain_versions().get(id.as_str()).ok_or_else(|| {
        PlanError::MissingValidatedInput {
            location: format!("inventory.toolchains.{}", id.as_str()),
        }
    })?;
    Ok(ToolchainSelector { id: id.as_str().to_owned(), version: version.clone() })
}

fn feature_selector(policy: &Policy, id: &Id) -> Result<FeatureSelector, PlanError> {
    let profile = policy.features().profiles().get(id.as_str()).ok_or_else(|| {
        PlanError::MissingValidatedInput { location: format!("feature_profiles.{}", id.as_str()) }
    })?;
    let selection = match profile {
        FeatureProfile::Default => FeatureSelection::Default,
        FeatureProfile::NoDefault => FeatureSelection::NoDefault,
        FeatureProfile::StableAggregate => FeatureSelection::StableAggregate {
            feature: policy.features().stable_feature_root().as_str().to_owned(),
        },
        FeatureProfile::All => FeatureSelection::All,
    };
    Ok(FeatureSelector { profile: id.as_str().to_owned(), selection })
}

fn target_selector(id: &Id, mode: TargetMode) -> TargetSelector {
    TargetSelector { triple: id.as_str().to_owned(), mode: ExecutionMode::from(mode) }
}

fn miri_target_selector(id: &Id) -> MiriTargetSelector {
    MiriTargetSelector { triple: id.as_str().to_owned() }
}

fn evaluate_build(class: EventClass, reduced_eligible: bool) -> CellDecision {
    match (class, reduced_eligible) {
        (EventClass::Full, _) => CellDecision::Included(DecisionReason::FullEventIncludesBuild),
        (EventClass::Reduced, true) => {
            CellDecision::Included(DecisionReason::ReducedEventIncludesEligibleTarget)
        }
        (EventClass::Reduced, false) => {
            CellDecision::Excluded(DecisionReason::ReducedEventExcludesIneligibleTarget)
        }
    }
}

fn evaluate_miri(actual: EventClass, configured: EventClass) -> CellDecision {
    if actual == configured {
        CellDecision::Included(DecisionReason::MiriEventCategoryMatches)
    } else {
        CellDecision::Excluded(DecisionReason::MiriEventCategoryDoesNotMatch)
    }
}

fn evaluate_semver(class: EventClass, reduced_eligible: bool) -> CellDecision {
    match (class, reduced_eligible) {
        (EventClass::Full, _) => CellDecision::Included(DecisionReason::FullEventIncludesSemver),
        (EventClass::Reduced, true) => {
            CellDecision::Included(DecisionReason::ReducedEventIncludesEligibleSemverTarget)
        }
        (EventClass::Reduced, false) => {
            CellDecision::Excluded(DecisionReason::ReducedEventExcludesIneligibleSemverTarget)
        }
    }
}

fn validate_legacy_membership(
    policy: &Policy,
    legacy: &LegacyBaselines,
    builds: &BTreeMap<BuildPlanCell, BuildCandidate>,
    miri: &BTreeSet<MiriPlanCell>,
) -> Result<(), PlanError> {
    let build_full = builds.keys().map(build_baseline_cell).collect::<Result<BTreeSet<_>, _>>()?;
    let build_reduced = builds
        .values()
        .filter(|candidate| candidate.reduced_eligible)
        .map(|candidate| build_baseline_cell(&candidate.cell))
        .collect::<Result<BTreeSet<_>, _>>()?;
    compare_build("reduced", legacy.compare_build_reduced(&build_reduced))?;
    compare_build("full", legacy.compare_build_full(&build_full))?;

    let miri_all = miri.iter().map(miri_baseline_cell).collect::<Result<BTreeSet<_>, _>>()?;
    let configured = EventClass::from(policy.miri().event_category());
    let empty = BTreeSet::new();
    let (miri_reduced, miri_full) = match configured {
        EventClass::Reduced => (&miri_all, &empty),
        EventClass::Full => (&empty, &miri_all),
    };
    compare_miri("reduced", legacy.compare_miri_reduced(miri_reduced))?;
    compare_miri("full", legacy.compare_miri_full(miri_full))?;
    Ok(())
}

fn build_baseline_cell(cell: &BuildPlanCell) -> Result<BuildCell, PlanError> {
    Ok(BuildCell::new(
        baseline_id("package", cell.package.id())?,
        baseline_id("toolchain", cell.toolchain.id())?,
        baseline_id("feature profile", cell.features.profile())?,
        baseline_id("target", cell.target.triple())?,
    ))
}

fn miri_baseline_cell(cell: &MiriPlanCell) -> Result<MiriCell, PlanError> {
    MiriCell::new(
        baseline_id("package", cell.package.id())?,
        baseline_id("toolchain", cell.toolchain.id())?,
        baseline_id("feature profile", cell.features.profile())?,
        baseline_id("target", cell.target.triple())?,
        baseline_id("Miri model", cell.model.id())?,
        cell.model.flags().to_vec(),
    )
    .map_err(|message| PlanError::InvalidLegacyProjection {
        selector: format_miri_selector(cell),
        message,
    })
}

fn baseline_id(kind: &'static str, value: &str) -> Result<BaselineId, PlanError> {
    BaselineId::from_str(value).map_err(|message| PlanError::InvalidLegacyProjection {
        selector: format!("{kind} `{value}`"),
        message,
    })
}

fn compare_build(
    category: &'static str,
    result: Result<(), SetDifference<BuildCell>>,
) -> Result<(), PlanError> {
    result.map_err(|difference| legacy_mismatch("ordinary build", category, &difference))
}

fn compare_miri(
    category: &'static str,
    result: Result<(), SetDifference<MiriCell>>,
) -> Result<(), PlanError> {
    result.map_err(|difference| legacy_mismatch("Miri", category, &difference))
}

fn legacy_mismatch<T: fmt::Debug + Ord>(
    kind: &'static str,
    category: &'static str,
    difference: &SetDifference<T>,
) -> PlanError {
    PlanError::LegacyMismatch {
        kind,
        category,
        missing: difference.missing_from_plan().len(),
        extra: difference.extra_in_plan().len(),
        details: difference.to_string(),
    }
}

fn enforce_plan_limit(planned: usize, maximum: u64) -> Result<(), PlanError> {
    let planned = u64::try_from(planned).unwrap_or(u64::MAX);
    if planned <= maximum {
        Ok(())
    } else {
        Err(PlanError::PlanLimitExceeded { planned, maximum })
    }
}

fn format_build_selector(cell: &BuildPlanCell) -> String {
    format!(
        "{}/{}/{}/{}",
        cell.package.id, cell.toolchain.id, cell.features.profile, cell.target.triple
    )
}

fn format_miri_selector(cell: &MiriPlanCell) -> String {
    format!(
        "{}/{}/{}/{}/{}",
        cell.package.id,
        cell.toolchain.id,
        cell.features.profile,
        cell.target.triple,
        cell.model.id
    )
}

fn format_semver_selector(cell: &SemverPlanCell) -> String {
    format!(
        "{}/{}/{}/{}",
        cell.package.id, cell.toolchain.id, cell.features.profile, cell.target.triple
    )
}

fn escape_control_characters(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    for character in value.chars() {
        if character.is_control() {
            escaped.extend(character.escape_default());
        } else {
            escaped.push(character);
        }
    }
    escaped
}

/// A deterministic planning or legacy-membership failure.
#[derive(Debug, Error, Eq, PartialEq)]
pub enum PlanError {
    /// The event is absent from both policy categories.
    #[error("unknown GitHub event `{display_event}`; configured events are: {known}")]
    UnknownEvent {
        /// The rejected event name, retained exactly for programmatic use.
        event: String,
        /// The rejected name with control characters escaped for diagnostics.
        display_event: String,
        /// Deterministically ordered configured names.
        known: String,
    },
    /// Event names or classes differed from their independent legacy baseline.
    #[error(
        "event classes differ from the legacy baseline: expected [{expected}]; found [{actual}]"
    )]
    LegacyEventClassMismatch {
        /// Deterministically ordered baseline event assignments.
        expected: String,
        /// Deterministically ordered policy event assignments.
        actual: String,
    },
    /// Data disappeared after the checked input boundary.
    #[error("validated CI input `{location}` is missing")]
    MissingValidatedInput {
        /// The missing policy or inventory location.
        location: String,
    },
    /// Policy scopes expanded the same logical cell twice.
    #[error("{kind} selector `{selector}` was generated more than once")]
    DuplicateCell {
        /// The kind of planned work.
        kind: &'static str,
        /// The stable human-readable selector.
        selector: String,
    },
    /// A validated selector could not be represented by the legacy row type.
    #[error("cannot compare {selector} with the legacy baseline: {message}")]
    InvalidLegacyProjection {
        /// The selector being converted.
        selector: String,
        /// The baseline type's strict parse diagnostic.
        message: String,
    },
    /// Selected matrix membership differed from frozen legacy evidence.
    #[error(
        "{category} {kind} matrix membership differs from the legacy baseline: {missing} missing, {extra} extra\n{details}"
    )]
    LegacyMismatch {
        /// The kind of planned work.
        kind: &'static str,
        /// The reduced or full category.
        category: &'static str,
        /// Baseline cells missing from the plan.
        missing: usize,
        /// Planned cells absent from the baseline.
        extra: usize,
        /// Exact missing and extra rows.
        details: String,
    },
    /// Expanded work exceeded the policy's pre-sharding safety bound.
    #[error("plan expands to {planned} cells, above limits.max_plan_cells ({maximum})")]
    PlanLimitExceeded {
        /// Included logical cells.
        planned: u64,
        /// The configured maximum.
        maximum: u64,
    },
}

impl PlanError {
    /// Returns the rejected event name for an unknown-event error.
    pub fn unknown_event(&self) -> Option<&str> {
        match self {
            Self::UnknownEvent { event, .. } => Some(event),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, path::Path, sync::OnceLock};

    use super::{
        enforce_plan_limit, enumerate_semver_candidates, index_semver_build_coverage,
        BuildCandidate, BuildPlanCell, CellDecision, DecisionReason, EventClass, ExecutionMode,
        FeatureSelection, FeatureSelector, PackageSelector, Plan, PlanError, PlanExplanation,
        TargetSelector, ToolchainSelector,
    };
    use crate::{ci::CiInputs, policy::Policy};

    const REPOSITORY_POLICY: &str = include_str!("../../../ci/zc.toml");

    fn inputs() -> &'static CiInputs {
        static INPUTS: OnceLock<CiInputs> = OnceLock::new();
        INPUTS.get_or_init(|| {
            let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
            CiInputs::load(root).unwrap()
        })
    }

    fn build_candidate(
        package: &str,
        toolchain: &str,
        profile: &str,
        target: String,
        reduced_eligible: bool,
    ) -> BuildCandidate {
        let selection = if profile == "stable" {
            FeatureSelection::StableAggregate {
                feature: "__internal_use_only_features_that_work_on_stable".to_owned(),
            }
        } else {
            FeatureSelection::Default
        };
        BuildCandidate {
            cell: BuildPlanCell {
                package: PackageSelector {
                    id: package.to_owned(),
                    manifest: format!("{package}/Cargo.toml").into(),
                },
                toolchain: ToolchainSelector {
                    id: toolchain.to_owned(),
                    version: "synthetic-version".to_owned(),
                },
                features: FeatureSelector { profile: profile.to_owned(), selection },
                target: TargetSelector { triple: target, mode: ExecutionMode::Native },
            },
            reduced_eligible,
        }
    }

    fn insert_build_candidate(
        builds: &mut BTreeMap<BuildPlanCell, BuildCandidate>,
        candidate: BuildCandidate,
    ) {
        assert!(builds.insert(candidate.cell.clone(), candidate).is_none());
    }

    #[test]
    fn plans_each_exact_legacy_event_class() {
        for event in ["pull_request", "merge_group", "push", "workflow_dispatch"] {
            let plan = Plan::create(inputs(), event).unwrap();
            if event == "pull_request" {
                assert_eq!(plan.class(), EventClass::Reduced);
                assert_eq!(plan.builds().len(), 60);
                assert!(plan.miri().is_empty());
                assert_eq!(plan.semver().len(), 3);
            } else {
                assert_eq!(plan.class(), EventClass::Full);
                assert_eq!(plan.builds().len(), 182);
                assert_eq!(plan.miri().len(), 64);
                assert_eq!(plan.semver().len(), 9);
            }
        }
    }

    #[test]
    fn rejects_unknown_events_without_a_fallback() {
        let error = Plan::create(inputs(), "pull_request_target").unwrap_err();

        assert_eq!(error.unknown_event(), Some("pull_request_target"));
        let diagnostic = error.to_string();
        assert!(diagnostic.contains("pull_request"));
        assert!(diagnostic.contains("merge_group"));
    }

    #[test]
    fn escapes_unknown_event_diagnostics_but_preserves_the_raw_name() {
        let raw = "pull\nrequest\u{7}";
        let error = Plan::create(inputs(), raw).unwrap_err();

        assert_eq!(error.unknown_event(), Some(raw));
        let diagnostic = error.to_string();
        assert!(diagnostic.contains(r"pull\nrequest\u{7}"));
        assert!(!diagnostic.contains('\n'));
        assert!(!diagnostic.contains('\u{7}'));
    }

    #[test]
    fn current_plans_have_exact_legacy_membership() {
        let reduced = Plan::create(inputs(), "pull_request").unwrap();
        let full = Plan::create(inputs(), "merge_group").unwrap();

        assert_eq!(reduced.builds().len(), inputs().legacy().build_reduced().len());
        assert_eq!(reduced.miri().len(), inputs().legacy().miri_reduced().len());
        assert_eq!(full.builds().len(), inputs().legacy().build_full().len());
        assert_eq!(full.miri().len(), inputs().legacy().miri_full().len());
        assert_eq!(reduced.semver().len(), 3);
        assert_eq!(full.semver().len(), 9);
        assert_eq!(full, Plan::create(inputs(), "merge_group").unwrap());
    }

    #[test]
    fn selectors_expose_data_without_commands_or_workflow_authority() {
        let plan = Plan::create(inputs(), "merge_group").unwrap();
        let cell = plan
            .builds()
            .iter()
            .find(|cell| {
                cell.package().id() == "zerocopy"
                    && cell.toolchain().id() == "nightly"
                    && cell.features().profile() == "stable"
                    && cell.target().triple() == "x86_64-unknown-linux-gnu"
            })
            .unwrap();

        assert_eq!(cell.package().manifest(), Path::new("zerocopy/Cargo.toml"));
        assert_eq!(cell.toolchain().version(), "nightly-2026-01-25");
        assert_eq!(cell.target().mode(), ExecutionMode::Native);
        assert!(matches!(
            cell.features().selection(),
            FeatureSelection::StableAggregate { feature }
                if feature == "__internal_use_only_features_that_work_on_stable"
        ));
    }

    #[test]
    fn every_feature_selection_has_exact_cargo_argument_boundaries() {
        assert_eq!(FeatureSelection::Default.cargo_args(), Vec::<String>::new());
        assert_eq!(
            FeatureSelection::NoDefault.cargo_args(),
            ["--no-default-features"].map(str::to_owned)
        );
        assert_eq!(
            FeatureSelection::StableAggregate { feature: "stable-root".to_owned() }.cargo_args(),
            ["--no-default-features", "--features", "stable-root"].map(str::to_owned)
        );
        assert_eq!(FeatureSelection::All.cargo_args(), ["--all-features"].map(str::to_owned));
    }

    #[test]
    fn miri_is_full_only() {
        let reduced = PlanExplanation::create(inputs(), "pull_request").unwrap();
        let full = PlanExplanation::create(inputs(), "push").unwrap();

        assert!(reduced.miri().iter().all(|cell| !cell.decision().is_included()));
        assert!(full.miri().iter().all(|cell| cell.decision().is_included()));
        assert_eq!(full.miri().len(), 64);
    }

    #[test]
    fn semver_preserves_the_build_slices_event_membership() {
        let reduced = PlanExplanation::create(inputs(), "pull_request").unwrap();
        let full = PlanExplanation::create(inputs(), "push").unwrap();

        let reduced_selected = reduced
            .semver()
            .iter()
            .filter(|cell| cell.decision().is_included())
            .map(|cell| cell.cell().target().triple())
            .collect::<Vec<_>>();
        assert_eq!(
            reduced_selected,
            ["i686-unknown-linux-gnu", "x86_64-pc-windows-msvc", "x86_64-unknown-linux-gnu",]
        );
        assert_eq!(full.semver().len(), 9);
        assert!(full.semver().iter().all(|cell| cell.decision().is_included()));

        let reduced_arm = reduced
            .semver()
            .iter()
            .find(|cell| cell.cell().target().triple() == "arm-unknown-linux-gnueabi")
            .unwrap();
        assert_eq!(
            reduced_arm.decision(),
            CellDecision::Excluded(DecisionReason::ReducedEventExcludesIneligibleSemverTarget)
        );
    }

    #[test]
    fn semver_build_coverage_indexes_high_cardinality_input_once() {
        const MATCHING_CANDIDATES: usize = 20_000;

        let policy = Policy::parse(REPOSITORY_POLICY).unwrap();
        let semver = policy.semver();
        let mut builds = BTreeMap::new();
        for index in 0..MATCHING_CANDIDATES {
            let target = format!("synthetic-target-{index:05}");
            insert_build_candidate(
                &mut builds,
                build_candidate(
                    semver.package().as_str(),
                    semver.toolchain().as_str(),
                    semver.profile().as_str(),
                    target.clone(),
                    index % 2 == 0,
                ),
            );
            // A large unrelated slice proves that indexing filters while it
            // makes its one pass rather than materializing all ordinary work.
            insert_build_candidate(
                &mut builds,
                build_candidate(
                    "unrelated-package",
                    semver.toolchain().as_str(),
                    semver.profile().as_str(),
                    target,
                    false,
                ),
            );
        }

        let by_target = index_semver_build_coverage(semver, &builds);
        assert_eq!(by_target.len(), MATCHING_CANDIDATES);
        assert!(by_target.values().all(|candidates| candidates.len() == 1));
        assert!(by_target["synthetic-target-00000"][0].reduced_eligible);
        assert!(!by_target["synthetic-target-19999"][0].reduced_eligible);
    }

    #[test]
    fn semver_index_uses_distinct_policy_toolchain_and_profile_ids() {
        const TOOLCHAIN_DECLARATION: &str = "id = \"stable\"\nsource = \"pinned-stable\"";
        const RENAMED_TOOLCHAIN_DECLARATION: &str =
            "id = \"semver-stable\"\nsource = \"pinned-stable\"";
        const SEMVER_SELECTION: &str = concat!(
            "toolchain = \"stable\"\n",
            "profile = \"stable\"\n",
            "target_set = \"semver\"",
        );
        const RENAMED_SEMVER_SELECTION: &str = concat!(
            "toolchain = \"semver-stable\"\n",
            "profile = \"stable\"\n",
            "target_set = \"semver\"",
        );

        assert_eq!(REPOSITORY_POLICY.matches(TOOLCHAIN_DECLARATION).count(), 1);
        let source =
            REPOSITORY_POLICY.replacen(TOOLCHAIN_DECLARATION, RENAMED_TOOLCHAIN_DECLARATION, 1);
        assert_eq!(source.matches(SEMVER_SELECTION).count(), 1);
        let source = source.replacen(SEMVER_SELECTION, RENAMED_SEMVER_SELECTION, 1);
        let policy = Policy::parse(&source).unwrap();
        let semver = policy.semver();
        assert_ne!(semver.toolchain().as_str(), semver.profile().as_str());

        let targets = policy.target_sets().get(semver.target_set().as_str()).unwrap();
        let mut builds = BTreeMap::new();
        for target in targets {
            let reduced_eligible = policy.targets()[target.as_str()].pr_eligible();
            insert_build_candidate(
                &mut builds,
                build_candidate(
                    semver.package().as_str(),
                    semver.toolchain().as_str(),
                    semver.profile().as_str(),
                    target.as_str().to_owned(),
                    reduced_eligible,
                ),
            );
        }

        let candidates = enumerate_semver_candidates(&policy, &builds).unwrap();
        assert_eq!(candidates.len(), targets.len());
        assert!(candidates.values().all(|candidate| {
            candidate.cell.toolchain.id() == "semver-stable"
                && candidate.cell.features.profile() == "stable"
        }));
    }

    #[test]
    fn miri_interprets_tests_for_an_ordinary_cross_target() {
        let plan = Plan::create(inputs(), "merge_group").unwrap();
        let cross_target = "arm-unknown-linux-gnueabi";
        let ordinary =
            plan.builds().iter().find(|cell| cell.target().triple() == cross_target).unwrap();
        assert_eq!(ordinary.target().mode(), ExecutionMode::Cross);

        // A Miri target deliberately has no ordinary `ExecutionMode`: being a
        // `MiriTargetSelector` means that Miri interprets this cell's tests.
        let interpreted = plan.miri().iter().find(|cell| cell.target().triple() == cross_target);
        assert!(interpreted.is_some());
    }

    #[test]
    fn explanations_cover_included_and_excluded_candidates() {
        let explanation = PlanExplanation::create(inputs(), "pull_request").unwrap();
        let included = explanation
            .builds()
            .iter()
            .find(|cell| {
                cell.cell().target().triple() == "i686-unknown-linux-gnu"
                    && cell.decision().is_included()
            })
            .unwrap();
        let excluded = explanation
            .builds()
            .iter()
            .find(|cell| {
                cell.cell().target().triple() == "arm-unknown-linux-gnueabi"
                    && !cell.decision().is_included()
            })
            .unwrap();

        assert_eq!(
            included.decision(),
            CellDecision::Included(DecisionReason::ReducedEventIncludesEligibleTarget)
        );
        assert_eq!(
            excluded.decision(),
            CellDecision::Excluded(DecisionReason::ReducedEventExcludesIneligibleTarget)
        );
        assert!(included.to_string().contains("included because"));
        assert!(excluded.to_string().contains("excluded because"));
        let semver = explanation
            .semver()
            .iter()
            .find(|cell| cell.cell().target().triple() == "arm-unknown-linux-gnueabi")
            .unwrap();
        assert!(semver.to_string().starts_with("semver "));
        assert!(semver.to_string().contains("excluded because"));
        let rendered = explanation.to_string();
        assert!(rendered.contains("event `pull_request` has reduced coverage"));
        assert!(rendered.contains("included because"));
        assert!(rendered.contains("excluded because"));
    }

    #[test]
    fn reports_plan_limit_with_both_values() {
        assert!(enforce_plan_limit(100, 100).is_ok());
        let error = enforce_plan_limit(101, 100).unwrap_err();

        assert_eq!(error, PlanError::PlanLimitExceeded { planned: 101, maximum: 100 });
        assert!(error.to_string().contains("101"));
        assert!(error.to_string().contains("100"));
    }
}
