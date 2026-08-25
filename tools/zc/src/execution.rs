// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure modeling and legacy-parity validation of unprivileged CI behavior.
//!
//! [`Plan`](crate::plan::Plan) decides matrix membership. This module takes the
//! next deliberately separate step: it expands each selected cell into the
//! ordinary Cargo or Miri operations which that cell means. It does not execute
//! a process, inspect workflow YAML, or make any decision about runners,
//! permissions, secrets, actions, environments, or publication. Those remain
//! visible workflow authority in `.github/workflows/ci.yml`.
//!
//! The operation builders below are intended to become the single semantic
//! source for a later executor. Until then, every place where their command
//! spelling remains duplicated in `ci.yml` is called out explicitly. The
//! independent files under `ci/baselines/` are comparison evidence only: this
//! module never reads a baseline row to construct proposed behavior. In
//! particular, the legacy comparison covers the repository state named by the
//! baseline manifest. It is not an inventory of control-plane validation jobs
//! added after that frozen source commit. Live workflow jobs and pre-push
//! checks remain protected by their separate, present-day audits and tests.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt,
    path::Path,
    str::FromStr,
};

use crate::{
    baseline::{
        BaselineId, CommandBehavior, CommandBehaviors, CommandPayload, JsonValue, LegacyBaselines,
        LogicalObligation, LogicalObligations, ObligationCondition, ObligationSource,
        SetDifference, StandaloneEvents, StandaloneInvocation, StandaloneObligation,
        WorkingDirectory,
    },
    ci::CiInputs,
    plan::{BuildPlanCell, EventClass, ExecutionMode, FeatureSelection, MiriPlanCell, Plan},
    policy::{Policy, ToolchainSource},
    semver_adapter::{SemverAdapterSpec, SEMVER_FEATURE_GROUP},
};

const BUILD_JOB: &str = "build_test";
const MIRI_JOB: &str = "miri";
const MATRIX_WORKING_DIRECTORY: &str = "zerocopy";

// These environment values are workflow command behavior, not policy. Keep
// them coordinated with the top-level `env` block and the "Configure
// environment variables" step in `.github/workflows/ci.yml`. A future
// executor should consume these constants directly, at which point YAML no
// longer needs to reproduce them.
const BASE_RUSTFLAGS: &str = "-Dwarnings";
const BASE_RUSTDOCFLAGS: &str = "-Dwarnings --cfg=zerocopy_unstable_ptr";
const NIGHTLY_RUSTFLAGS: &str = "-Zrandomize-layout";
const NIGHTLY_MIRIFLAGS: &str = "-Zmiri-strict-provenance -Zmiri-backtrace=full";

/// A deterministic failure proving that proposed execution behavior differs
/// from independently captured legacy evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionAuditError {
    violations: Vec<String>,
}

impl ExecutionAuditError {
    /// Returns all violations in stable category order.
    pub fn violations(&self) -> &[String] {
        &self.violations
    }

    fn one(violation: impl Into<String>) -> Self {
        Self { violations: vec![violation.into()] }
    }

    fn from_set(violations: BTreeSet<String>) -> Self {
        Self { violations: violations.into_iter().collect() }
    }
}

impl fmt::Display for ExecutionAuditError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(formatter, "CI execution behavior has {} violation(s):", self.violations.len())?;
        for violation in &self.violations {
            for (index, line) in violation.lines().enumerate() {
                if index == 0 {
                    writeln!(formatter, "- {line}")?;
                } else {
                    writeln!(formatter, "  {line}")?;
                }
            }
        }
        Ok(())
    }
}

impl Error for ExecutionAuditError {}

/// Expands all selected cells and compares command behavior, logical work,
/// and standalone work with the exact frozen legacy sets.
///
/// This function is pure after [`CiInputs`] has loaded: it performs no file or
/// process I/O. Callers should make it part of the checked input boundary
/// before allowing a projection to reach a workflow.
pub fn audit_execution(inputs: &CiInputs) -> Result<(), ExecutionAuditError> {
    let mut mutation = NoMutation;
    let proposed = derive_execution(inputs, &mut mutation)
        .map_err(|message| ExecutionAuditError::one(format!("model construction: {message}")))?;
    compare_execution(inputs.legacy(), &proposed)
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum MatrixOperationKind {
    CargoTest,
    CargoCheckTests,
    CargoBuild,
    CargoCheckLibrary,
    CargoClippyTests,
    CargoClippyLibrary,
    CargoDoc,
    CargoSemverCheck,
    MiriTest,
}

impl MatrixOperationKind {
    fn id(self) -> &'static str {
        match self {
            Self::CargoTest => "cargo-test",
            Self::CargoCheckTests => "cargo-check-tests",
            Self::CargoBuild => "cargo-build",
            Self::CargoCheckLibrary => "cargo-check-library",
            Self::CargoClippyTests => "cargo-clippy-tests",
            Self::CargoClippyLibrary => "cargo-clippy-library",
            Self::CargoDoc => "cargo-doc",
            Self::CargoSemverCheck => "cargo-semver-check",
            Self::MiriTest => "miri-test",
        }
    }

    fn step(self) -> &'static str {
        match self {
            Self::CargoTest => "Test native target",
            Self::CargoCheckTests | Self::CargoBuild => "Check cross target",
            Self::CargoCheckLibrary => "Check thumb library",
            Self::CargoClippyTests => "Clippy tests",
            Self::CargoClippyLibrary => "Clippy",
            Self::CargoDoc => "Cargo doc",
            Self::CargoSemverCheck => "Check semver compatibility",
            Self::MiriTest => "Run tests under Miri",
        }
    }

    fn job(self) -> &'static str {
        match self {
            Self::MiriTest => MIRI_JOB,
            _ => BUILD_JOB,
        }
    }

    fn condition(self) -> ObligationCondition {
        match self {
            Self::CargoSemverCheck => ObligationCondition::UnlessSkipCargoSemverChecks,
            _ => ObligationCondition::Always,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct LogicalKey {
    kind: String,
    package: Option<String>,
    toolchain: Option<String>,
    feature_profile: Option<String>,
    target: Option<String>,
    miri_model: Option<String>,
}

#[derive(Clone, Debug)]
struct LogicalSpec {
    key: LogicalKey,
    condition: ObligationCondition,
    job: String,
    step: String,
}

#[derive(Clone, Debug)]
struct CommandSpec {
    job: String,
    step: String,
    working_directory: WorkingDirectory,
    environment: BTreeMap<String, String>,
    payload: CommandPayload,
}

impl CommandSpec {
    /// Checks every command-bearing field even when this command is not one of
    /// the representative command goldens.
    ///
    /// `CommandBehavior` is also the strict parser boundary for the frozen
    /// command evidence. Constructing and discarding one here deliberately
    /// gives every proposed command the same identifier, text, working
    /// directory, environment, and payload checks without deriving any value
    /// from that evidence.
    fn validate(&self, operation: MatrixOperationKind) -> Result<(), String> {
        self.clone().into_behavior(operation.id()).map(drop).map_err(|reason| {
            format!("typed operation {operation:?} carries an invalid command: {reason}")
        })
    }

    fn into_behavior(self, name: &str) -> Result<CommandBehavior, String> {
        CommandBehavior::new(
            baseline_id(name)?,
            baseline_id(&self.job)?,
            self.step,
            self.working_directory,
            self.environment,
            self.payload,
        )
    }
}

#[derive(Clone, Debug)]
struct MatrixOperation {
    kind: MatrixOperationKind,
    logical: LogicalSpec,
    command: CommandSpec,
    golden: Option<&'static str>,
    applicable: bool,
}

#[derive(Clone, Debug)]
struct BuildCellSemantics {
    package: String,
    manifest: String,
    toolchain: String,
    toolchain_version: String,
    pinned_nightly: bool,
    feature_profile: String,
    features: FeatureSelection,
    target: String,
    mode: ExecutionMode,
}

impl BuildCellSemantics {
    fn from_plan(cell: &BuildPlanCell, policy: &Policy) -> Result<Self, String> {
        Ok(Self {
            package: cell.package().id().to_owned(),
            manifest: path_text(cell.package().manifest())?,
            toolchain: cell.toolchain().id().to_owned(),
            toolchain_version: cell.toolchain().version().to_owned(),
            pinned_nightly: is_pinned_nightly(policy, cell.toolchain().id())?,
            feature_profile: cell.features().profile().to_owned(),
            features: cell.features().selection().clone(),
            target: cell.target().triple().to_owned(),
            mode: cell.target().mode(),
        })
    }
}

#[derive(Clone, Debug)]
struct MiriCellSemantics {
    package: String,
    toolchain: String,
    pinned_nightly: bool,
    feature_profile: String,
    features: FeatureSelection,
    target: String,
    model: String,
    model_flags: Vec<String>,
}

impl MiriCellSemantics {
    fn from_plan(cell: &MiriPlanCell, policy: &Policy) -> Result<Self, String> {
        Ok(Self {
            package: cell.package().id().to_owned(),
            toolchain: cell.toolchain().id().to_owned(),
            pinned_nightly: is_pinned_nightly(policy, cell.toolchain().id())?,
            feature_profile: cell.features().profile().to_owned(),
            features: cell.features().selection().clone(),
            target: cell.target().triple().to_owned(),
            model: cell.model().id().to_owned(),
            model_flags: cell.model().flags().to_vec(),
        })
    }
}

fn is_pinned_nightly(policy: &Policy, toolchain: &str) -> Result<bool, String> {
    let configured = policy
        .toolchains()
        .get(toolchain)
        .ok_or_else(|| format!("plan references unknown toolchain `{toolchain}`"))?;
    Ok(configured.source() == ToolchainSource::PinnedNightly)
}

#[derive(Clone, Debug)]
struct LogicalAccumulator {
    condition: ObligationCondition,
    sources: BTreeSet<(String, String)>,
    reduced_occurrences: u32,
    full_occurrences: u32,
}

impl LogicalAccumulator {
    fn new(condition: ObligationCondition) -> Self {
        Self { condition, sources: BTreeSet::new(), reduced_occurrences: 0, full_occurrences: 0 }
    }

    fn record(&mut self, class: EventClass, spec: &LogicalSpec) -> Result<(), String> {
        if self.condition != spec.condition {
            return Err(format!(
                "logical obligation `{}` has inconsistent conditions",
                spec.key.kind
            ));
        }
        self.sources.insert((spec.job.clone(), spec.step.clone()));
        let count = match class {
            EventClass::Reduced => &mut self.reduced_occurrences,
            EventClass::Full => &mut self.full_occurrences,
        };
        *count = count.checked_add(1).ok_or_else(|| {
            format!("logical obligation `{}` occurrence count overflowed", spec.key.kind)
        })?;
        Ok(())
    }
}

#[derive(Debug)]
struct DerivedExecution {
    logical: LogicalObligations,
    standalone: BTreeSet<StandaloneObligation>,
    commands: CommandBehaviors,
}

trait ModelMutation {
    fn mutate_docs_rs_rustdoc_args(&mut self, _arguments: &mut Vec<String>) {}
    fn mutate_build_cell(&mut self, _class: EventClass, _cell: &mut BuildCellSemantics) {}
    fn mutate_miri_cell(&mut self, _class: EventClass, _cell: &mut MiriCellSemantics) {}
    fn mutate_operation(&mut self, _class: EventClass, _operation: &mut MatrixOperation) {}
}

struct NoMutation;

impl ModelMutation for NoMutation {}

fn derive_execution(
    inputs: &CiInputs,
    mutation: &mut impl ModelMutation,
) -> Result<DerivedExecution, String> {
    // GitHub requires the semver action invocation to remain literal workflow
    // YAML. Build its typed specification once here as well as auditing that
    // YAML at the `CiInputs` boundary. Matrix command modeling and the live
    // adapter therefore cannot acquire independent action identities, input
    // sets, or explicit environment values.
    let semver_adapter =
        SemverAdapterSpec::from_checked_inputs(inputs.policy(), inputs.repository())
            .map_err(|error| format!("semver adapter: {error}"))?;
    let mut docs_rs_rustdoc_args = inputs.repository().zerocopy_docs_rs_rustdoc_args().to_vec();
    mutation.mutate_docs_rs_rustdoc_args(&mut docs_rs_rustdoc_args);
    let reduced = plan_for_class(inputs, EventClass::Reduced)?;
    let full = plan_for_class(inputs, EventClass::Full)?;
    let mut logical = BTreeMap::<LogicalKey, LogicalAccumulator>::new();
    let mut commands = CommandBehaviors::new();

    for (class, plan) in [(EventClass::Reduced, &reduced), (EventClass::Full, &full)] {
        for cell in plan.builds() {
            let mut cell = BuildCellSemantics::from_plan(cell, inputs.policy())?;
            mutation.mutate_build_cell(class, &mut cell);
            for mut operation in
                build_operations(inputs.policy(), &semver_adapter, &docs_rs_rustdoc_args, &cell)?
            {
                mutation.mutate_operation(class, &mut operation);
                validate_operation(&operation)?;
                if !operation.applicable {
                    continue;
                }
                record_logical(&mut logical, class, &operation.logical)?;
                if class == EventClass::Full {
                    collect_golden(&mut commands, operation)?;
                }
            }
        }
        for cell in plan.miri() {
            let mut cell = MiriCellSemantics::from_plan(cell, inputs.policy())?;
            mutation.mutate_miri_cell(class, &mut cell);
            let mut operation = miri_operation(&cell)?;
            mutation.mutate_operation(class, &mut operation);
            validate_operation(&operation)?;
            if !operation.applicable {
                continue;
            }
            record_logical(&mut logical, class, &operation.logical)?;
            if class == EventClass::Full {
                collect_golden(&mut commands, operation)?;
            }
        }
    }

    let mut standalone = BTreeSet::new();
    for spec in LEGACY_STANDALONE_SPECS {
        let obligation = standalone_obligation(spec)?;
        if !standalone.insert(obligation) {
            return Err(format!("standalone operation `{}/{}` is duplicated", spec.job, spec.step));
        }
        let logical_spec = standalone_logical_spec(spec);
        record_logical(&mut logical, EventClass::Reduced, &logical_spec)?;
        record_logical(&mut logical, EventClass::Full, &logical_spec)?;
        if let Some(golden) = spec.golden {
            let command = standalone_command(spec, golden)?.into_behavior(golden.name)?;
            commands.insert(command).map_err(|error| error.to_string())?;
        }
    }

    let obligations = logical
        .into_iter()
        .map(|(key, value)| logical_obligation(key, value))
        .collect::<Result<Vec<_>, _>>()?;
    let logical =
        LogicalObligations::try_from_iter(obligations).map_err(|error| error.to_string())?;
    Ok(DerivedExecution { logical, standalone, commands })
}

fn plan_for_class(inputs: &CiInputs, class: EventClass) -> Result<Plan, String> {
    let events = match class {
        EventClass::Reduced => inputs.policy().events().reduced(),
        EventClass::Full => inputs.policy().events().full(),
    };
    let event = events.iter().next().ok_or_else(|| format!("policy has no {class} event"))?;
    Plan::create(inputs, event.as_str()).map_err(|error| error.to_string())
}

fn record_logical(
    logical: &mut BTreeMap<LogicalKey, LogicalAccumulator>,
    class: EventClass,
    spec: &LogicalSpec,
) -> Result<(), String> {
    logical
        .entry(spec.key.clone())
        .or_insert_with(|| LogicalAccumulator::new(spec.condition.clone()))
        .record(class, spec)
}

fn collect_golden(
    commands: &mut CommandBehaviors,
    operation: MatrixOperation,
) -> Result<(), String> {
    let Some(name) = operation.golden else {
        return Ok(());
    };
    commands.insert(operation.command.into_behavior(name)?).map_err(|error| error.to_string())
}

fn validate_operation(operation: &MatrixOperation) -> Result<(), String> {
    if operation.logical.key.kind != operation.kind.id() {
        return Err(format!(
            "typed operation {:?} carries logical kind `{}`",
            operation.kind, operation.logical.key.kind
        ));
    }
    if operation.logical.step != operation.kind.step() {
        return Err(format!(
            "typed operation {:?} carries step `{}`",
            operation.kind, operation.logical.step
        ));
    }
    if operation.logical.job != operation.kind.job() {
        return Err(format!(
            "typed operation {:?} carries logical job {:?}",
            operation.kind, operation.logical.job
        ));
    }
    if operation.logical.condition != operation.kind.condition() {
        return Err(format!(
            "typed operation {:?} carries logical condition {:?}",
            operation.kind, operation.logical.condition
        ));
    }
    if !operation.applicable {
        return Ok(());
    }
    if operation.command.job != operation.logical.job {
        return Err(format!(
            "typed operation {:?} carries command job {:?}, but its logical job is {:?}",
            operation.kind, operation.command.job, operation.logical.job
        ));
    }
    if operation.command.step != operation.logical.step {
        return Err(format!(
            "typed operation {:?} carries command step {:?}, but its logical step is {:?}",
            operation.kind, operation.command.step, operation.logical.step
        ));
    }
    operation.command.validate(operation.kind)?;
    Ok(())
}

fn matrix_logical_spec(
    kind: MatrixOperationKind,
    package: &str,
    toolchain: &str,
    profile: &str,
    target: Option<&str>,
    miri_model: Option<&str>,
) -> LogicalSpec {
    LogicalSpec {
        key: LogicalKey {
            kind: kind.id().to_owned(),
            package: Some(package.to_owned()),
            toolchain: Some(toolchain.to_owned()),
            feature_profile: Some(profile.to_owned()),
            target: target.map(str::to_owned),
            miri_model: miri_model.map(str::to_owned),
        },
        condition: kind.condition(),
        job: kind.job().to_owned(),
        step: kind.step().to_owned(),
    }
}

fn matrix_command(
    kind: MatrixOperationKind,
    environment: BTreeMap<String, String>,
    payload: CommandPayload,
) -> CommandSpec {
    CommandSpec {
        job: kind.job().to_owned(),
        step: kind.step().to_owned(),
        working_directory: WorkingDirectory::Relative(MATRIX_WORKING_DIRECTORY.to_owned()),
        environment,
        payload,
    }
}

fn build_operations(
    policy: &Policy,
    semver_adapter: &SemverAdapterSpec,
    docs_rs_rustdoc_args: &[String],
    cell: &BuildCellSemantics,
) -> Result<Vec<MatrixOperation>, String> {
    let mut operations = Vec::new();
    match cell.mode {
        ExecutionMode::Native => operations.push(cargo_operation(
            MatrixOperationKind::CargoTest,
            cell,
            "test",
            &[],
            &[],
            Some(cell.target.as_str()),
            native_default_golden(cell),
        )),
        ExecutionMode::Cross => {
            operations.push(cargo_operation(
                MatrixOperationKind::CargoCheckTests,
                cell,
                "check",
                &["--tests"],
                &[],
                Some(cell.target.as_str()),
                cross_golden(cell, "cross-check-tests"),
            ));
            operations.push(cargo_operation(
                MatrixOperationKind::CargoBuild,
                cell,
                "build",
                &[],
                &[],
                Some(cell.target.as_str()),
                cross_golden(cell, "cross-build"),
            ));
        }
        ExecutionMode::Thumb => operations.push(cargo_operation(
            MatrixOperationKind::CargoCheckLibrary,
            cell,
            "check",
            &[],
            &[],
            Some(cell.target.as_str()),
            thumb_golden(cell, "thumb-check"),
        )),
    }

    if cell.pinned_nightly {
        let (kind, trailing, golden) = match cell.mode {
            ExecutionMode::Thumb => (
                MatrixOperationKind::CargoClippyLibrary,
                &[][..],
                thumb_golden(cell, "thumb-clippy"),
            ),
            ExecutionMode::Native | ExecutionMode::Cross => (
                MatrixOperationKind::CargoClippyTests,
                &["--tests"][..],
                nightly_clippy_golden(cell),
            ),
        };
        operations.push(cargo_operation(
            kind,
            cell,
            "clippy",
            &[],
            trailing,
            Some(cell.target.as_str()),
            golden,
        ));
    }

    operations.push(docs_operation(docs_rs_rustdoc_args, cell));
    if semver_applies(policy, cell)? {
        operations.push(semver_operation(semver_adapter, cell)?);
    }
    Ok(operations)
}

fn cargo_operation(
    kind: MatrixOperationKind,
    cell: &BuildCellSemantics,
    cargo_subcommand: &str,
    leading_arguments: &[&str],
    trailing_arguments: &[&str],
    logical_target: Option<&str>,
    golden: Option<&'static str>,
) -> MatrixOperation {
    let mut argv =
        vec!["./cargo.sh".to_owned(), format!("+{}", cell.toolchain), cargo_subcommand.to_owned()];
    argv.extend(leading_arguments.iter().map(|argument| (*argument).to_owned()));
    argv.extend([
        "--package".to_owned(),
        cell.package.clone(),
        "--target".to_owned(),
        cell.target.clone(),
    ]);
    argv.extend(cell.features.cargo_args());
    argv.extend(trailing_arguments.iter().map(|argument| (*argument).to_owned()));
    argv.push("--verbose".to_owned());

    MatrixOperation {
        kind,
        logical: matrix_logical_spec(
            kind,
            &cell.package,
            &cell.toolchain,
            &cell.feature_profile,
            logical_target,
            None,
        ),
        command: matrix_command(
            kind,
            ordinary_environment(cell.pinned_nightly),
            CommandPayload::Argv { argv, dynamic_value: None },
        ),
        golden,
        applicable: true,
    }
}

fn docs_operation(docs_rs_rustdoc_args: &[String], cell: &BuildCellSemantics) -> MatrixOperation {
    let kind = MatrixOperationKind::CargoDoc;
    let mut argv = vec![
        "./cargo.sh".to_owned(),
        format!("+{}", cell.toolchain),
        "doc".to_owned(),
        "--no-deps".to_owned(),
        "--document-private-items".to_owned(),
        "--package".to_owned(),
        cell.package.clone(),
    ];
    argv.extend(cell.features.cargo_args());

    // Repository inventory obtains this ordered sequence from the canonical
    // Zerocopy package's `package.metadata.docs.rs.rustdoc-args`. `ci.yml`
    // independently performs the same Cargo metadata lookup before invoking
    // Cargo doc; keep that workflow adapter coordinated until a typed executor
    // owns the invocation itself. Inventory rejects whitespace inside an
    // element, so joining with one space preserves every argument boundary
    // understood by RUSTDOCFLAGS.
    let docs_rs_rustdoc_args = docs_rs_rustdoc_args.join(" ");

    // The current command-golden format records only the environment variables
    // whose special value belongs to this command. `ci.yml` still inherits
    // ordinary matrix variables as well. Retaining this narrow representation
    // is an awkward legacy exception; broadening it requires an intentional
    // command-baseline migration rather than copying baseline data here.
    let environment = if cell.pinned_nightly {
        BTreeMap::from([(
            "RUSTDOCFLAGS".to_owned(),
            format!(
                "-Z unstable-options --document-hidden-items {docs_rs_rustdoc_args} {BASE_RUSTDOCFLAGS}"
            ),
        )])
    } else {
        BTreeMap::from([("RUSTDOCFLAGS".to_owned(), BASE_RUSTDOCFLAGS.to_owned())])
    };
    MatrixOperation {
        kind,
        // `cargo doc` intentionally has no `--target`; all target cells for
        // the same package/toolchain/profile normalize to one obligation with
        // an occurrence count. Keep this coupled to the Cargo doc step in
        // `ci.yml` and the comment in logical-obligations.tsv.
        logical: matrix_logical_spec(
            kind,
            &cell.package,
            &cell.toolchain,
            &cell.feature_profile,
            None,
            None,
        ),
        command: matrix_command(
            kind,
            environment,
            CommandPayload::Argv {
                argv,
                dynamic_value: cell
                    .pinned_nightly
                    .then(|| "metadata docs.rs rustdoc-args".to_owned()),
            },
        ),
        golden: nightly_docs_golden(cell),
        applicable: true,
    }
}

fn semver_applies(policy: &Policy, cell: &BuildCellSemantics) -> Result<bool, String> {
    let semver = policy.semver();
    let targets = policy
        .target_sets()
        .get(semver.target_set().as_str())
        .ok_or_else(|| format!("semver target set `{}` is absent", semver.target_set()))?;
    Ok(cell.package == semver.package().as_str()
        && cell.toolchain == semver.toolchain().as_str()
        && cell.feature_profile == semver.profile().as_str()
        && targets.iter().any(|target| target.as_str() == cell.target))
}

fn semver_operation(
    adapter: &SemverAdapterSpec,
    cell: &BuildCellSemantics,
) -> Result<MatrixOperation, String> {
    let kind = MatrixOperationKind::CargoSemverCheck;
    let stable_feature = match &cell.features {
        FeatureSelection::StableAggregate { feature } => feature.clone(),
        selection => {
            return Err(format!(
                "semver cell `{}/{}/{}/{}` requires stable-aggregate features, found {selection:?}",
                cell.package, cell.toolchain, cell.feature_profile, cell.target
            ));
        }
    };
    let mut resolved_inputs = adapter.inputs().clone();
    let expected_static_inputs = [
        ("feature-group", SEMVER_FEATURE_GROUP),
        ("features", stable_feature.as_str()),
        ("manifest-path", cell.manifest.as_str()),
        ("package", cell.package.as_str()),
    ];
    for (name, actual) in expected_static_inputs {
        let expected = resolved_inputs
            .get(name)
            .ok_or_else(|| format!("typed semver adapter has no `{name}` input"))?;
        if expected != actual {
            return Err(format!(
                "semver cell `{}/{}/{}/{}` resolves `{name}` to `{actual}`, but the typed adapter requires `{expected}`",
                cell.package, cell.toolchain, cell.feature_profile, cell.target
            ));
        }
    }
    resolved_inputs.insert("rust-target".to_owned(), cell.target.clone());
    resolved_inputs.insert("rust-toolchain".to_owned(), cell.toolchain_version.clone());
    let with =
        resolved_inputs.into_iter().map(|(name, value)| (name, JsonValue::String(value))).collect();
    let inputs = BTreeMap::from([
        ("uses".to_owned(), JsonValue::String(adapter.action().to_owned())),
        ("with".to_owned(), JsonValue::Object(with)),
    ]);
    Ok(MatrixOperation {
        kind,
        logical: matrix_logical_spec(
            kind,
            &cell.package,
            &cell.toolchain,
            &cell.feature_profile,
            Some(&cell.target),
            None,
        ),
        command: CommandSpec {
            job: BUILD_JOB.to_owned(),
            step: kind.step().to_owned(),
            working_directory: WorkingDirectory::RepositoryRoot,
            environment: adapter.environment().clone(),
            payload: CommandPayload::ActionInputs {
                inputs,
                dynamic_value: "third-party action implementation".to_owned(),
            },
        },
        golden: semver_golden(cell),
        applicable: true,
    })
}

fn miri_operation(cell: &MiriCellSemantics) -> Result<MatrixOperation, String> {
    if !cell.pinned_nightly {
        return Err(format!("Miri cell uses non-nightly toolchain `{}`", cell.toolchain));
    }
    let kind = MatrixOperationKind::MiriTest;
    let dynamic = "<2*nproc>".to_owned();
    let mut argv = vec![
        "./cargo.sh".to_owned(),
        format!("+{}", cell.toolchain),
        "miri".to_owned(),
        "nextest".to_owned(),
        "run".to_owned(),
        "--locked".to_owned(),
        "--ignore-default-filter".to_owned(),
        "--test-threads".to_owned(),
        dynamic.clone(),
        "--package".to_owned(),
        cell.package.clone(),
        "--target".to_owned(),
        cell.target.clone(),
    ];
    argv.extend(cell.features.cargo_args());
    let model_flags = cell.model_flags.join(" ");
    let mut environment = ordinary_environment(true);
    environment.insert("MIRIFLAGS".to_owned(), format!(" {NIGHTLY_MIRIFLAGS} {model_flags}"));
    Ok(MatrixOperation {
        kind,
        logical: matrix_logical_spec(
            kind,
            &cell.package,
            &cell.toolchain,
            &cell.feature_profile,
            Some(&cell.target),
            Some(&cell.model),
        ),
        command: matrix_command(
            kind,
            environment,
            CommandPayload::ArgvTemplate { argv, dynamic_value: dynamic },
        ),
        golden: miri_golden(cell),
        applicable: true,
    })
}

fn ordinary_environment(pinned_nightly: bool) -> BTreeMap<String, String> {
    let mut environment = BTreeMap::from([
        ("RUSTDOCFLAGS".to_owned(), BASE_RUSTDOCFLAGS.to_owned()),
        ("RUSTFLAGS".to_owned(), BASE_RUSTFLAGS.to_owned()),
    ]);
    if pinned_nightly {
        environment.insert("RUSTFLAGS".to_owned(), format!("{BASE_RUSTFLAGS} {NIGHTLY_RUSTFLAGS}"));
        // The leading space is the exact result of appending the nightly
        // value to an initially empty MIRIFLAGS in `ci.yml`.
        environment.insert("MIRIFLAGS".to_owned(), format!(" {NIGHTLY_MIRIFLAGS}"));
    }
    environment
}

// The selectors in these helpers name the representative rows reviewed in
// command-goldens.tsv. They do not control operation applicability. Exact
// package/toolchain/target names are appropriate here because changing a
// representative is itself a baseline migration; behavior decisions above use
// typed execution mode, feature selection, toolchain source, and semver policy.
fn native_default_golden(cell: &BuildCellSemantics) -> Option<&'static str> {
    (cell.package == "zerocopy"
        && cell.toolchain == "stable"
        && cell.feature_profile == "default"
        && cell.target == "x86_64-unknown-linux-gnu")
        .then_some("native-default")
}

fn cross_golden(cell: &BuildCellSemantics, name: &'static str) -> Option<&'static str> {
    (cell.package == "zerocopy"
        && cell.pinned_nightly
        && cell.feature_profile == "all"
        && cell.target == "powerpc-unknown-linux-gnu")
        .then_some(name)
}

fn thumb_golden(cell: &BuildCellSemantics, name: &'static str) -> Option<&'static str> {
    (cell.package == "zerocopy"
        && cell.pinned_nightly
        && cell.feature_profile == "default"
        && cell.target == "thumbv6m-none-eabi")
        .then_some(name)
}

fn nightly_clippy_golden(cell: &BuildCellSemantics) -> Option<&'static str> {
    (cell.package == "zerocopy"
        && cell.pinned_nightly
        && cell.feature_profile == "all"
        && cell.target == "x86_64-unknown-linux-gnu")
        .then_some("nightly-clippy-tests")
}

fn nightly_docs_golden(cell: &BuildCellSemantics) -> Option<&'static str> {
    (cell.package == "zerocopy"
        && cell.pinned_nightly
        && cell.feature_profile == "all"
        && cell.target == "x86_64-unknown-linux-gnu")
        .then_some("nightly-docs")
}

fn semver_golden(cell: &BuildCellSemantics) -> Option<&'static str> {
    (cell.target == "x86_64-unknown-linux-gnu").then_some("semver")
}

fn miri_golden(cell: &MiriCellSemantics) -> Option<&'static str> {
    if cell.package != "zerocopy"
        || cell.feature_profile != "default"
        || cell.target != "x86_64-unknown-linux-gnu"
    {
        return None;
    }
    match cell.model.as_str() {
        "stacked" => Some("miri-stacked"),
        "tree" => Some("miri-tree"),
        _ => None,
    }
}

fn logical_obligation(
    key: LogicalKey,
    value: LogicalAccumulator,
) -> Result<LogicalObligation, String> {
    let sources = value
        .sources
        .into_iter()
        .map(|(job, step)| ObligationSource::new(baseline_id(&job)?, step))
        .collect::<Result<Vec<_>, String>>()?;
    LogicalObligation::new(
        baseline_id(&key.kind)?,
        optional_baseline_id(key.package)?,
        optional_baseline_id(key.toolchain)?,
        optional_baseline_id(key.feature_profile)?,
        optional_baseline_id(key.target)?,
        optional_baseline_id(key.miri_model)?,
        value.reduced_occurrences,
        value.full_occurrences,
        value.condition,
        sources,
    )
}

fn baseline_id(value: &str) -> Result<BaselineId, String> {
    BaselineId::from_str(value)
}

fn optional_baseline_id(value: Option<String>) -> Result<Option<BaselineId>, String> {
    value.map(|value| baseline_id(&value)).transpose()
}

fn path_text(path: &Path) -> Result<String, String> {
    path.to_str()
        .map(|path| path.replace('\\', "/"))
        .ok_or_else(|| format!("repository path `{path:?}` is not UTF-8"))
}

#[derive(Clone, Copy)]
enum StandaloneFormSpec {
    Direct(&'static [&'static str]),
    Action(&'static str),
    PrePushChild(&'static [&'static str]),
    PrePushInternal(&'static str),
    ShellContract(&'static str),
}

#[derive(Clone, Copy)]
enum StandaloneGoldenEnvironment {
    Avr,
    NightlyRustOnly,
}

#[derive(Clone, Copy)]
struct StandaloneGoldenSpec {
    name: &'static str,
    environment: StandaloneGoldenEnvironment,
}

#[derive(Clone, Copy)]
struct StandaloneSpec {
    obligation: &'static str,
    job: &'static str,
    step: &'static str,
    working_directory: &'static str,
    form: StandaloneFormSpec,
    condition: ObligationConditionSpec,
    golden: Option<StandaloneGoldenSpec>,
}

#[derive(Clone, Copy)]
enum ObligationConditionSpec {
    Always,
    Success,
    Cancelled,
}

impl ObligationConditionSpec {
    fn typed(self) -> ObligationCondition {
        match self {
            Self::Always => ObligationCondition::Always,
            Self::Success => ObligationCondition::Success,
            Self::Cancelled => ObligationCondition::Cancelled,
        }
    }
}

const ALWAYS: ObligationConditionSpec = ObligationConditionSpec::Always;

// This explicit list reconstructs the non-matrix command contract at the
// source commit named by `ci/baselines/manifest.tsv`. Keep it coordinated with
// the independently frozen standalone-obligation, logical-obligation, and
// command-golden evidence, not blindly with the live workflow or pre-push
// hook. In particular, a control-plane validation job introduced later in this
// stack does not belong here merely because it is present in the current
// workflow or hook. Present-day job membership and hook behavior are checked
// at separate boundaries. An intentional refresh of this list must also
// refresh the baseline source identity and its independently collected
// evidence, or introduce a separate present-day behavior audit.
//
// Unlike the baseline, this list is proposed typed behavior. It is used to
// construct normalized logical obligations and the three standalone command
// goldens without copying values from the evidence being checked.
const LEGACY_STANDALONE_SPECS: &[StandaloneSpec] = &[
    StandaloneSpec {
        obligation: "avr-check",
        job: "check_avr_atmega",
        step: "Check avr-none target",
        working_directory: "zerocopy",
        form: StandaloneFormSpec::Direct(&[
            "./cargo.sh",
            "+nightly",
            "check",
            "--target=avr-none",
            "-Zbuild-std=core",
            "--features",
            "simd,simd-nightly,float-nightly,derive",
        ]),
        condition: ALWAYS,
        golden: Some(StandaloneGoldenSpec {
            name: "avr-check",
            environment: StandaloneGoldenEnvironment::Avr,
        }),
    },
    StandaloneSpec {
        obligation: "avr-clippy",
        job: "check_avr_atmega",
        step: "Clippy check avr-none target",
        working_directory: "zerocopy",
        form: StandaloneFormSpec::Direct(&[
            "./cargo.sh",
            "+nightly",
            "clippy",
            "--target=avr-none",
            "-Zbuild-std=core",
            "--features",
            "simd,simd-nightly,float-nightly,derive",
        ]),
        condition: ALWAYS,
        golden: Some(StandaloneGoldenSpec {
            name: "avr-clippy",
            environment: StandaloneGoldenEnvironment::Avr,
        }),
    },
    StandaloneSpec {
        obligation: "big-endian-aarch64-build",
        job: "check_be_aarch64",
        step: "Check big endian for aarch64_be-unknown-linux-gnu target",
        working_directory: "zerocopy",
        form: StandaloneFormSpec::Direct(&[
            "./cargo.sh",
            "+nightly",
            "build",
            "--target=aarch64_be-unknown-linux-gnu",
            "-Zbuild-std",
            "--features",
            "simd",
        ]),
        condition: ALWAYS,
        golden: Some(StandaloneGoldenSpec {
            name: "big-endian-aarch64",
            environment: StandaloneGoldenEnvironment::NightlyRustOnly,
        }),
    },
    StandaloneSpec {
        obligation: "check-actions",
        job: "check_actions",
        step: "Check Actions",
        working_directory: ".",
        form: StandaloneFormSpec::Direct(&["./ci/check_actions.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-actions",
        job: "run-git-hooks",
        step: "Run dependency check",
        working_directory: ".",
        form: StandaloneFormSpec::PrePushChild(&["./ci/check_actions.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-format",
        job: "check_fmt",
        step: "Check Rust formatting",
        working_directory: ".",
        form: StandaloneFormSpec::Direct(&["./ci/check_fmt.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-format",
        job: "run-git-hooks",
        step: "Run dependency check",
        working_directory: ".",
        form: StandaloneFormSpec::PrePushChild(&["./ci/check_fmt.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-hook-inventory",
        job: "run-git-hooks",
        step: "Run dependency check",
        working_directory: ".",
        form: StandaloneFormSpec::PrePushInternal("githooks/pre-push inventory loops"),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-job-dependencies",
        job: "check-job-dependencies",
        step: "Run dependency check",
        working_directory: ".",
        form: StandaloneFormSpec::Direct(&["./ci/check_job_dependencies.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-job-dependencies",
        job: "run-git-hooks",
        step: "Run dependency check",
        working_directory: ".",
        form: StandaloneFormSpec::PrePushChild(&["./ci/check_job_dependencies.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-msrv-minimal",
        job: "check_msrv_is_minimal",
        step: "Check MSRV is minimal",
        working_directory: "zerocopy",
        form: StandaloneFormSpec::Direct(&["./ci/check_msrv_is_minimal.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-msrv-minimal",
        job: "run-git-hooks",
        step: "Run dependency check",
        working_directory: ".",
        form: StandaloneFormSpec::PrePushChild(&["./zerocopy/ci/check_msrv_is_minimal.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-readme",
        job: "check_readme",
        step: "Check README.md",
        working_directory: "zerocopy",
        form: StandaloneFormSpec::Direct(&["./ci/check_readme.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-readme",
        job: "run-git-hooks",
        step: "Run dependency check",
        working_directory: ".",
        form: StandaloneFormSpec::PrePushChild(&["./zerocopy/ci/check_readme.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-stale-stderr",
        job: "check_stale_stderr",
        step: "Check stale stderr",
        working_directory: "zerocopy",
        form: StandaloneFormSpec::Direct(&["./ci/check_stale_stderr.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-stale-stderr",
        job: "run-git-hooks",
        step: "Run dependency check",
        working_directory: ".",
        form: StandaloneFormSpec::PrePushChild(&["./zerocopy/ci/check_stale_stderr.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-todo-comments",
        job: "check-todo",
        step: "Run todo check",
        working_directory: ".",
        form: StandaloneFormSpec::Direct(&["./ci/check_todo.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-toolchains",
        job: "check-all-toolchains-tested",
        step: "Run check",
        working_directory: "zerocopy",
        form: StandaloneFormSpec::Direct(&["./ci/check_all_toolchains_tested.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-toolchains",
        job: "run-git-hooks",
        step: "Run dependency check",
        working_directory: ".",
        form: StandaloneFormSpec::PrePushChild(&["./zerocopy/ci/check_all_toolchains_tested.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-versions",
        job: "check_versions",
        step: "Check crate versions match",
        working_directory: "zerocopy",
        form: StandaloneFormSpec::Direct(&["./ci/check_versions.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "check-versions",
        job: "run-git-hooks",
        step: "Run dependency check",
        working_directory: ".",
        form: StandaloneFormSpec::PrePushChild(&["./zerocopy/ci/check_versions.sh"]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "ci-image-build-export",
        job: "build_docker_env",
        step: "Build, cache, and export image",
        working_directory: ".",
        form: StandaloneFormSpec::Action(
            "docker/build-push-action@53b7df96c91f9c12dcc8a07bcb9ccacbed38856a",
        ),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "ci-image-upload",
        job: "build_docker_env",
        step: "Upload image for matrix jobs",
        working_directory: ".",
        form: StandaloneFormSpec::Action("./.github/actions/upload-file-artifact"),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "codegen-clippy",
        job: "codegen",
        step: "Clippy",
        working_directory: "zerocopy",
        form: StandaloneFormSpec::Direct(&[
            "./cargo.sh",
            "+nightly",
            "clippy",
            "--locked",
            "--package",
            "zerocopy",
            "--target",
            "x86_64-unknown-linux-gnu",
            "--all-features",
            "--test",
            "codegen",
            "--verbose",
            "--",
            "-Dwarnings",
        ]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "codegen-test",
        job: "codegen",
        step: "Run tests",
        working_directory: "zerocopy",
        form: StandaloneFormSpec::Direct(&[
            "./cargo.sh",
            "+nightly",
            "test",
            "--locked",
            "--package",
            "zerocopy",
            "--target",
            "x86_64-unknown-linux-gnu",
            "--all-features",
            "--verbose",
            "--test",
            "codegen",
        ]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "coverage-generate",
        job: "coverage",
        step: "Generate code coverage",
        working_directory: "zerocopy",
        form: StandaloneFormSpec::Direct(&[
            "./cargo.sh",
            "+nightly",
            "llvm-cov",
            "--package",
            "zerocopy",
            "--target",
            "x86_64-unknown-linux-gnu",
            "--all-features",
            "--doctests",
            "--lcov",
            "--output-path",
            "lcov.info",
            "--verbose",
        ]),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "coverage-upload",
        job: "coverage",
        step: "Upload coverage to Codecov",
        working_directory: ".",
        form: StandaloneFormSpec::Action(
            "codecov/codecov-action@fb8b3582c8e4def4969c97caa2f19720cb33a72f",
        ),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "kani",
        job: "kani",
        step: "Run tests under Kani",
        working_directory: ".",
        form: StandaloneFormSpec::Action(
            "model-checking/kani-github-action@f838096619a707b0f6b2118cf435eaccfa33e51f",
        ),
        condition: ALWAYS,
        golden: None,
    },
    StandaloneSpec {
        obligation: "required-check-aggregate",
        job: "all-jobs-succeed",
        step: "Require every dependency to succeed",
        working_directory: ".",
        form: StandaloneFormSpec::ShellContract(
            "jq validates needs; miri must be skipped only on pull_request",
        ),
        condition: ObligationConditionSpec::Success,
        golden: None,
    },
    StandaloneSpec {
        obligation: "required-check-cancellation",
        job: "all-jobs-succeed",
        step: "Reject workflow cancellation",
        working_directory: ".",
        form: StandaloneFormSpec::ShellContract("exit 1 when cancelled() is true"),
        condition: ObligationConditionSpec::Cancelled,
        golden: None,
    },
    StandaloneSpec {
        obligation: "zizmor",
        job: "zizmor",
        step: "zizmor",
        working_directory: ".",
        form: StandaloneFormSpec::Action(
            "zizmorcore/zizmor-action@3dc1ecc9bcb9e94e9b2c709687979e1298497054",
        ),
        condition: ALWAYS,
        golden: None,
    },
];

fn standalone_obligation(spec: &StandaloneSpec) -> Result<StandaloneObligation, String> {
    let invocation = match spec.form {
        StandaloneFormSpec::Direct(argv) => StandaloneInvocation::Direct(strings(argv)),
        StandaloneFormSpec::Action(action) => StandaloneInvocation::Action(action.to_owned()),
        StandaloneFormSpec::PrePushChild(argv) => StandaloneInvocation::PrePushChild(strings(argv)),
        StandaloneFormSpec::PrePushInternal(description) => {
            StandaloneInvocation::PrePushInternal(description.to_owned())
        }
        StandaloneFormSpec::ShellContract(description) => {
            StandaloneInvocation::ShellContract(description.to_owned())
        }
    };
    StandaloneObligation::new(
        baseline_id(spec.obligation)?,
        StandaloneEvents::PullRequestAndFull,
        baseline_id(spec.job)?,
        spec.step,
        WorkingDirectory::parse(spec.working_directory)?,
        invocation,
    )
}

fn standalone_logical_spec(spec: &StandaloneSpec) -> LogicalSpec {
    LogicalSpec {
        key: LogicalKey {
            kind: spec.obligation.to_owned(),
            package: None,
            toolchain: None,
            feature_profile: None,
            target: None,
            miri_model: None,
        },
        condition: spec.condition.typed(),
        job: spec.job.to_owned(),
        step: spec.step.to_owned(),
    }
}

fn standalone_command(
    spec: &StandaloneSpec,
    golden: StandaloneGoldenSpec,
) -> Result<CommandSpec, String> {
    let StandaloneFormSpec::Direct(argv) = spec.form else {
        return Err(format!("standalone golden `{}` is not a direct command", golden.name));
    };
    let environment = match golden.environment {
        StandaloneGoldenEnvironment::Avr => {
            BTreeMap::from([("RUSTFLAGS".to_owned(), "-C target-cpu=atmega328p".to_owned())])
        }
        StandaloneGoldenEnvironment::NightlyRustOnly => BTreeMap::from([(
            "RUSTFLAGS".to_owned(),
            format!("{BASE_RUSTFLAGS} {NIGHTLY_RUSTFLAGS}"),
        )]),
    };
    Ok(CommandSpec {
        job: spec.job.to_owned(),
        step: spec.step.to_owned(),
        working_directory: WorkingDirectory::parse(spec.working_directory)?,
        environment,
        payload: CommandPayload::Argv { argv: strings(argv), dynamic_value: None },
    })
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| (*value).to_owned()).collect()
}

fn compare_execution(
    legacy: &LegacyBaselines,
    proposed: &DerivedExecution,
) -> Result<(), ExecutionAuditError> {
    let mut violations = BTreeSet::new();
    collect_difference(
        &mut violations,
        "command behaviors",
        legacy.compare_command_goldens(&proposed.commands),
    );
    collect_difference(
        &mut violations,
        "logical obligations",
        legacy.compare_logical_obligations(&proposed.logical),
    );
    collect_difference(
        &mut violations,
        "standalone obligations",
        legacy.compare_standalone_obligations(&proposed.standalone),
    );
    if violations.is_empty() {
        Ok(())
    } else {
        Err(ExecutionAuditError::from_set(violations))
    }
}

fn collect_difference<T: fmt::Debug + Ord>(
    violations: &mut BTreeSet<String>,
    category: &str,
    difference: Result<(), SetDifference<T>>,
) {
    if let Err(difference) = difference {
        violations.insert(format!("{category}: {difference}"));
    }
}

#[cfg(test)]
mod tests {
    use std::{path::Path, sync::OnceLock};

    use super::{
        audit_execution, compare_execution, derive_execution, BuildCellSemantics, EventClass,
        ExecutionMode, FeatureSelection, MatrixOperation, MatrixOperationKind, ModelMutation,
        MIRI_JOB,
    };
    use crate::{baseline::CommandPayload, ci::CiInputs};

    fn inputs() -> &'static CiInputs {
        static INPUTS: OnceLock<CiInputs> = OnceLock::new();
        INPUTS.get_or_init(|| {
            let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
            CiInputs::load(root).unwrap()
        })
    }

    fn audit_with(mutation: &mut impl ModelMutation) -> String {
        let proposed = derive_execution(inputs(), mutation).unwrap();
        compare_execution(inputs().legacy(), &proposed).unwrap_err().to_string()
    }

    fn model_error_with(mutation: &mut impl ModelMutation) -> String {
        derive_execution(inputs(), mutation).unwrap_err()
    }

    fn is_non_golden_native_test(class: EventClass, operation: &MatrixOperation) -> bool {
        class == EventClass::Full
            && operation.kind == MatrixOperationKind::CargoTest
            && operation.golden.is_none()
            && operation.logical.key.package.as_deref() == Some("zerocopy")
            && operation.logical.key.toolchain.as_deref() == Some("stable")
            && operation.logical.key.feature_profile.as_deref() == Some("default")
            && operation.logical.key.target.as_deref() == Some("i686-unknown-linux-gnu")
    }

    #[test]
    fn typed_behavior_matches_all_frozen_legacy_evidence_exactly() {
        audit_execution(inputs()).unwrap();
    }

    struct NonGoldenArgvMutation(bool);

    impl ModelMutation for NonGoldenArgvMutation {
        fn mutate_operation(&mut self, class: EventClass, operation: &mut MatrixOperation) {
            if self.0 || !is_non_golden_native_test(class, operation) {
                return;
            }
            let CommandPayload::Argv { argv, .. } = &mut operation.command.payload else {
                panic!("selected native Cargo test must use an argv payload");
            };
            argv.clear();
            self.0 = true;
        }
    }

    #[test]
    fn invalid_argv_on_a_non_golden_cell_fails_model_construction() {
        let mut mutation = NonGoldenArgvMutation(false);
        let diagnostic = model_error_with(&mut mutation);
        assert!(mutation.0, "the test must mutate its intended non-golden cell");
        assert!(diagnostic.contains("argv must contain at least one argument"));
    }

    struct NonGoldenEnvironmentMutation(bool);

    impl ModelMutation for NonGoldenEnvironmentMutation {
        fn mutate_operation(&mut self, class: EventClass, operation: &mut MatrixOperation) {
            if self.0 || !is_non_golden_native_test(class, operation) {
                return;
            }
            operation
                .command
                .environment
                .insert("RUSTFLAGS".to_owned(), "-Dwarnings\n-Aunused".to_owned());
            self.0 = true;
        }
    }

    #[test]
    fn invalid_environment_on_a_non_golden_cell_fails_model_construction() {
        let mut mutation = NonGoldenEnvironmentMutation(false);
        let diagnostic = model_error_with(&mut mutation);
        assert!(mutation.0, "the test must mutate its intended non-golden cell");
        assert!(diagnostic.contains("environment variable `RUSTFLAGS` contains a control"));
        assert!(!diagnostic.contains('\n'));
    }

    struct NonGoldenCommandJobMutation(bool);

    impl ModelMutation for NonGoldenCommandJobMutation {
        fn mutate_operation(&mut self, class: EventClass, operation: &mut MatrixOperation) {
            if self.0 || !is_non_golden_native_test(class, operation) {
                return;
            }
            operation.command.job = MIRI_JOB.to_owned();
            self.0 = true;
        }
    }

    #[test]
    fn incoherent_command_job_on_a_non_golden_cell_fails_model_construction() {
        let mut mutation = NonGoldenCommandJobMutation(false);
        let diagnostic = model_error_with(&mut mutation);
        assert!(mutation.0, "the test must mutate its intended non-golden cell");
        assert!(diagnostic.contains("command job \"miri\""));
        assert!(diagnostic.contains("logical job is \"build_test\""));
    }

    struct NonGoldenCommandStepMutation(bool);

    impl ModelMutation for NonGoldenCommandStepMutation {
        fn mutate_operation(&mut self, class: EventClass, operation: &mut MatrixOperation) {
            if self.0 || !is_non_golden_native_test(class, operation) {
                return;
            }
            operation.command.step = "Wrong step".to_owned();
            self.0 = true;
        }
    }

    #[test]
    fn incoherent_command_step_on_a_non_golden_cell_fails_model_construction() {
        let mut mutation = NonGoldenCommandStepMutation(false);
        let diagnostic = model_error_with(&mut mutation);
        assert!(mutation.0, "the test must mutate its intended non-golden cell");
        assert!(diagnostic.contains("command step \"Wrong step\""));
        assert!(diagnostic.contains("logical step is \"Test native target\""));
    }

    struct ExecutionModeMutation(bool);

    impl ModelMutation for ExecutionModeMutation {
        fn mutate_build_cell(&mut self, class: EventClass, cell: &mut BuildCellSemantics) {
            if !self.0
                && class == EventClass::Full
                && cell.toolchain == "stable"
                && cell.features == FeatureSelection::Default
                && cell.target == "x86_64-unknown-linux-gnu"
            {
                self.0 = true;
                cell.mode = ExecutionMode::Cross;
            }
        }
    }

    #[test]
    fn changed_execution_mode_fails_logical_and_command_parity() {
        let diagnostic = audit_with(&mut ExecutionModeMutation(false));
        assert!(diagnostic.contains("logical obligations"));
        assert!(diagnostic.contains("command behaviors"));
    }

    struct FeatureSelectionMutation(bool);

    impl ModelMutation for FeatureSelectionMutation {
        fn mutate_build_cell(&mut self, class: EventClass, cell: &mut BuildCellSemantics) {
            if !self.0
                && class == EventClass::Full
                && cell.toolchain == "stable"
                && cell.features == FeatureSelection::Default
                && cell.target == "x86_64-unknown-linux-gnu"
            {
                self.0 = true;
                cell.features = FeatureSelection::All;
            }
        }
    }

    #[test]
    fn changed_feature_semantics_fails_exact_command_parity() {
        let diagnostic = audit_with(&mut FeatureSelectionMutation(false));
        assert!(diagnostic.contains("command behaviors"));
        assert!(diagnostic.contains("--all-features"));
    }

    struct DocsMetadataMutation;

    impl ModelMutation for DocsMetadataMutation {
        fn mutate_docs_rs_rustdoc_args(&mut self, arguments: &mut Vec<String>) {
            let argument = arguments.iter_mut().find(|argument| *argument == "doc_cfg").unwrap();
            *argument = "changed_doc_cfg".to_owned();
        }
    }

    #[test]
    fn changed_docs_rs_metadata_fails_exact_command_parity() {
        let diagnostic = audit_with(&mut DocsMetadataMutation);
        assert!(diagnostic.contains("command behaviors"));
        assert!(diagnostic.contains("changed_doc_cfg"));
    }

    struct DocsMetadataOrderMutation;

    impl ModelMutation for DocsMetadataOrderMutation {
        fn mutate_docs_rs_rustdoc_args(&mut self, arguments: &mut Vec<String>) {
            arguments.swap(0, 1);
        }
    }

    #[test]
    fn reordered_docs_rs_metadata_fails_exact_command_parity() {
        let diagnostic = audit_with(&mut DocsMetadataOrderMutation);
        assert!(diagnostic.contains("command behaviors"));
        assert!(diagnostic.contains("doc_cfg --cfg"));
    }

    struct ArgvMutation(bool);

    impl ModelMutation for ArgvMutation {
        fn mutate_operation(&mut self, class: EventClass, operation: &mut MatrixOperation) {
            if self.0 || class != EventClass::Full || operation.golden != Some("native-default") {
                return;
            }
            if let CommandPayload::Argv { argv, .. } = &mut operation.command.payload {
                argv.push("--mutated".to_owned());
                self.0 = true;
            }
        }
    }

    #[test]
    fn changed_argv_fails_exact_command_parity() {
        let diagnostic = audit_with(&mut ArgvMutation(false));
        assert!(diagnostic.contains("command behaviors"));
        assert!(diagnostic.contains("--mutated"));
    }

    struct EnvironmentMutation(bool);

    impl ModelMutation for EnvironmentMutation {
        fn mutate_operation(&mut self, class: EventClass, operation: &mut MatrixOperation) {
            if !self.0 && class == EventClass::Full && operation.golden == Some("native-default") {
                operation.command.environment.insert("RUSTFLAGS".to_owned(), "-Aall".to_owned());
                self.0 = true;
            }
        }
    }

    #[test]
    fn changed_environment_fails_exact_command_parity() {
        let diagnostic = audit_with(&mut EnvironmentMutation(false));
        assert!(diagnostic.contains("command behaviors"));
        assert!(diagnostic.contains("-Aall"));
    }

    struct WorkingDirectoryMutation(bool);

    impl ModelMutation for WorkingDirectoryMutation {
        fn mutate_operation(&mut self, class: EventClass, operation: &mut MatrixOperation) {
            if !self.0 && class == EventClass::Full && operation.golden == Some("native-default") {
                operation.command.working_directory =
                    crate::baseline::WorkingDirectory::RepositoryRoot;
                self.0 = true;
            }
        }
    }

    #[test]
    fn changed_working_directory_fails_exact_command_parity() {
        let diagnostic = audit_with(&mut WorkingDirectoryMutation(false));
        assert!(diagnostic.contains("command behaviors"));
        assert!(diagnostic.contains("RepositoryRoot"));
    }

    struct ApplicabilityMutation(bool);

    impl ModelMutation for ApplicabilityMutation {
        fn mutate_operation(&mut self, class: EventClass, operation: &mut MatrixOperation) {
            if !self.0
                && class == EventClass::Full
                && operation.kind == MatrixOperationKind::CargoDoc
            {
                operation.applicable = false;
                self.0 = true;
            }
        }
    }

    #[test]
    fn changed_applicability_fails_logical_parity() {
        let diagnostic = audit_with(&mut ApplicabilityMutation(false));
        assert!(diagnostic.contains("logical obligations"));
    }
}
