// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Modeling, parity validation, and local execution of unprivileged CI work.
//!
//! [`Plan`](crate::plan::Plan) decides matrix membership. This module takes the
//! next deliberately separate step: it expands each selected cell into the
//! ordinary Cargo or Miri operations which that cell means. The local executor
//! can run one explicitly selected cell, but it does not inspect workflow YAML
//! or make any decision about runners, permissions, secrets, actions, or
//! publication. Those remain visible workflow authority in
//! `.github/workflows/ci.yml`.
//!
//! The operation builders below are the single semantic source for both parity
//! checking and local execution. `ci.yml` passes complete cell selectors back
//! to this module instead of reproducing Cargo or Miri commands. The semver
//! action remains an explicit workflow-owned exception because GitHub requires
//! a literal `uses` value. The independent files under `ci/baselines/` are
//! comparison evidence only: this module never reads a baseline row to
//! construct proposed behavior. In
//! particular, the legacy comparison covers the repository state named by the
//! baseline manifest. It is not an inventory of control-plane validation jobs
//! added after that frozen source commit. Live workflow jobs and pre-push
//! checks remain protected by their separate, present-day audits and tests.

use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    error::Error,
    fmt,
    fs::OpenOptions,
    io::{self, Write},
    num::{NonZeroUsize, ParseIntError},
    path::{Path, PathBuf},
    process,
    str::FromStr,
    thread,
};

use thiserror::Error as ThisError;

use crate::{
    baseline::{
        BaselineId, CommandBehavior, CommandBehaviors, CommandPayload, JsonValue, LegacyBaselines,
        LogicalObligation, LogicalObligations, ObligationCondition, ObligationSource,
        SetDifference, StandaloneEvents, StandaloneInvocation, StandaloneObligation,
        WorkingDirectory,
    },
    ci::CiInputs,
    plan::{
        BuildPlanCell, EventClass, ExecutionMode, FeatureSelection, MiriPlanCell, Plan, PlanError,
    },
    policy::{Policy, ToolchainSource},
};

const BUILD_JOB: &str = "build_test";
const MIRI_JOB: &str = "miri";
const MATRIX_WORKING_DIRECTORY: &str = "zerocopy";
// Keep the platform-neutral command model and its frozen evidence in terms of
// the public Unix wrapper. Only the host boundary below translates that exact
// program to the equivalent Windows entry point. This avoids making every
// planner, selector, baseline, and fake-host test platform-dependent.
const CARGO_WRAPPER: &str = "./cargo.sh";
const WINDOWS_CARGO_WRAPPER: &str = "./win-cargo.bat";
const AARCH64_TARGET: &str = "aarch64-unknown-linux-gnu";
const MIRI_THREAD_PLACEHOLDER: &str = "<2*nproc>";
const NPROC_STEP: &str = "Determine Miri thread count";
// This is the private half of the protocol implemented by cargo-zerocopy.
// Keep these literals synchronized: the executor sets them and the wrapper
// validates them before changing only Cargo subprocess cwd/discovery.
#[doc(hidden)]
pub const EXECUTION_CONTEXT_ENV: &str = "ZEROCOPY_INTERNAL_EXECUTION_CONTEXT";
#[doc(hidden)]
pub const MIRI_REPOSITORY_ROOT_CONTEXT: &str = "miri-repository-root";

// These environment values are executor-owned behavior for planned matrix
// cells, not policy. The workflow has similar top-level values for handwritten
// static jobs, but planned cells set this complete map directly and do not
// inherit changes to those jobs. The frozen command goldens prove that this
// model matches independently captured main.
const BASE_RUSTFLAGS: &str = "-Dwarnings";
const BASE_RUSTDOCFLAGS: &str = "-Dwarnings --cfg=zerocopy_unstable_ptr";
const NIGHTLY_RUSTFLAGS: &str = "-Zrandomize-layout";
const NIGHTLY_MIRIFLAGS: &str = "-Zmiri-strict-provenance -Zmiri-backtrace=full";

// GitHub requires `uses` to remain visible in workflow YAML. This typed value
// freezes the action identity used by the command model, while the workflow
// audit and ordinary code review continue to own the actual action authority.
// Keep it coordinated with the "Check semver compatibility" step in `ci.yml`.
const SEMVER_ACTION: &str =
    "obi1kenobi/cargo-semver-checks-action@6b69fcf40e9b5fb17adeb57e4b6ecd020649a239";

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

/// The complete identity of one selected ordinary build-plan cell.
///
/// Every field is required deliberately. A caller cannot accidentally run a
/// different profile or target merely because policy adds another cell later.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BuildCellSelector {
    event: String,
    package: String,
    toolchain: String,
    feature_profile: String,
    target: String,
}

impl BuildCellSelector {
    /// Constructs an exact ordinary-cell selector.
    pub fn new(
        event: impl Into<String>,
        package: impl Into<String>,
        toolchain: impl Into<String>,
        feature_profile: impl Into<String>,
        target: impl Into<String>,
    ) -> Self {
        Self {
            event: event.into(),
            package: package.into(),
            toolchain: toolchain.into(),
            feature_profile: feature_profile.into(),
            target: target.into(),
        }
    }

    fn description(&self) -> String {
        format!(
            "event={:?}, package={:?}, toolchain={:?}, feature_profile={:?}, target={:?}",
            self.event, self.package, self.toolchain, self.feature_profile, self.target,
        )
    }
}

/// The complete identity of one selected Miri-plan cell.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MiriCellSelector {
    event: String,
    package: String,
    toolchain: String,
    feature_profile: String,
    target: String,
    model: String,
}

impl MiriCellSelector {
    /// Constructs an exact Miri-cell selector.
    pub fn new(
        event: impl Into<String>,
        package: impl Into<String>,
        toolchain: impl Into<String>,
        feature_profile: impl Into<String>,
        target: impl Into<String>,
        model: impl Into<String>,
    ) -> Self {
        Self {
            event: event.into(),
            package: package.into(),
            toolchain: toolchain.into(),
            feature_profile: feature_profile.into(),
            target: target.into(),
            model: model.into(),
        }
    }

    fn description(&self) -> String {
        format!(
            "event={:?}, package={:?}, toolchain={:?}, feature_profile={:?}, target={:?}, miri_model={:?}",
            self.event, self.package, self.toolchain, self.feature_profile, self.target, self.model,
        )
    }
}

/// What one selected-cell invocation actually did locally.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CellExecutionReport {
    executed_steps: Vec<String>,
    workflow_owned_steps: Vec<String>,
}

impl CellExecutionReport {
    fn new() -> Self {
        Self { executed_steps: Vec::new(), workflow_owned_steps: Vec::new() }
    }

    /// Returns modeled process steps which completed successfully, in order.
    pub fn executed_steps(&self) -> &[String] {
        &self.executed_steps
    }

    /// Returns selected steps which remain owned by GitHub Actions.
    pub fn workflow_owned_steps(&self) -> &[String] {
        &self.workflow_owned_steps
    }
}

/// A deterministic selection, model, process, or Miri-setup failure.
#[derive(Debug, ThisError)]
pub enum CellExecutionError {
    /// The requested event could not be planned.
    #[error(transparent)]
    Plan(#[from] PlanError),
    /// No selected cell has the complete requested identity.
    #[error(
        "no selected {kind} cell matches {selector}; the selector is unknown or excluded for this event"
    )]
    CellNotSelected {
        /// The matrix kind being selected.
        kind: &'static str,
        /// The escaped, complete selector.
        selector: String,
    },
    /// More than one selected cell has an identity which should be unique.
    #[error("{matches} selected {kind} cells match {selector}; refusing an ambiguous execution")]
    AmbiguousCell {
        /// The matrix kind being selected.
        kind: &'static str,
        /// The escaped, complete selector.
        selector: String,
        /// Number of matching cells observed.
        matches: usize,
    },
    /// Checked inputs could not be expanded into executable behavior.
    #[error("cannot construct selected-cell execution: {message}")]
    Model {
        /// The model validation diagnostic.
        message: String,
    },
    /// A selected operation is represented by a payload this executor cannot run.
    #[error("step {step:?} has unsupported modeled payload {payload}")]
    UnsupportedPayload {
        /// Human-readable modeled step name.
        step: String,
        /// Stable payload description.
        payload: &'static str,
    },
    /// A process could not be started.
    #[error("failed to start step {step:?} with program {program:?}: {source}")]
    StartProcess {
        /// Human-readable modeled step name.
        step: String,
        /// Exact argv element used as the program.
        program: String,
        /// Operating-system process error.
        #[source]
        source: io::Error,
    },
    /// A process completed unsuccessfully.
    #[error("step {step:?} failed ({status})")]
    ProcessFailed {
        /// Human-readable modeled step name.
        step: String,
        /// Exit-code or signal description.
        status: String,
    },
    /// GNU `nproc` could not be started.
    #[error("failed to start GNU nproc while determining the Miri thread count: {source}")]
    StartNproc {
        /// Operating-system process error.
        #[source]
        source: io::Error,
    },
    /// GNU `nproc` completed unsuccessfully.
    #[error("GNU nproc failed while determining the Miri thread count ({status})")]
    NprocFailed {
        /// Exit-code or signal description.
        status: String,
    },
    /// GNU `nproc` wrote stdout which was not UTF-8.
    #[error("GNU nproc output is not UTF-8: {source}")]
    NprocOutputNotUtf8 {
        /// UTF-8 decoding error.
        #[source]
        source: std::str::Utf8Error,
    },
    /// GNU `nproc` did not write exactly one newline-terminated value.
    #[error("GNU nproc output must be exactly one nonempty line terminated by LF; got {output:?}")]
    NprocOutputShape {
        /// Decoded output, rendered escaped by the diagnostic.
        output: String,
    },
    /// GNU `nproc` did not write an unsigned decimal which fits `usize`.
    #[error("GNU nproc output {value:?} is not a base-10 usize: {source}")]
    NprocOutputParse {
        /// Single output line, without its terminating newline.
        value: String,
        /// Integer parsing error.
        #[source]
        source: ParseIntError,
    },
    /// The host unexpectedly reported no available processors.
    #[error("available processor count was zero; the Miri thread count must be nonzero")]
    ProcessorCountZero,
    /// Doubling the host's processor count overflowed the integer type.
    #[error("cannot double available processor count {available}: usize overflow")]
    ThreadCountOverflow {
        /// Processor count reported by the host query.
        available: usize,
    },
    /// The operating system could not report its available parallelism.
    #[error("failed to query available processors: {source}")]
    AvailableParallelism {
        /// Operating-system query error.
        #[source]
        source: io::Error,
    },
    /// A modeled argv template did not have exactly one dynamic element.
    #[error(
        "step {step:?} must contain dynamic argv element {placeholder:?} exactly once; found {occurrences}"
    )]
    DynamicPlaceholder {
        /// Human-readable modeled step name.
        step: String,
        /// Exact placeholder being replaced.
        placeholder: String,
        /// Number of exact argv elements found.
        occurrences: usize,
    },
    /// A GitHub step summary could not be appended.
    #[error("failed to append Miri thread count to {path:?}: {source}")]
    AppendStepSummary {
        /// `GITHUB_STEP_SUMMARY` destination.
        path: PathBuf,
        /// Underlying filesystem error.
        #[source]
        source: io::Error,
    },
}

/// Executes the modeled commands for one exact selected ordinary build cell.
///
/// The semver action is intentionally not executed: GitHub requires its
/// literal `uses` identity and security-relevant condition to remain in the
/// workflow. If the selected cell includes that action, the returned report
/// names it as workflow-owned instead of silently treating it as completed.
pub fn execute_build_cell(
    inputs: &CiInputs,
    selector: &BuildCellSelector,
) -> Result<CellExecutionReport, CellExecutionError> {
    execute_build_cell_with(inputs, selector, &mut SystemExecutionHost)
}

/// Executes the modeled command for one exact selected Miri cell.
pub fn execute_miri_cell(
    inputs: &CiInputs,
    selector: &MiriCellSelector,
) -> Result<CellExecutionReport, CellExecutionError> {
    execute_miri_cell_with(inputs, selector, &mut SystemExecutionHost)
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProcessInvocation {
    step: String,
    argv: Vec<String>,
    working_directory: PathBuf,
    environment: BTreeMap<String, String>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ProcessOutcome {
    success: bool,
    code: Option<i32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CapturedProcessOutcome {
    success: bool,
    code: Option<i32>,
    stdout: Vec<u8>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum HostPlatform {
    Linux,
    Windows,
    Other,
}

impl HostPlatform {
    const fn current() -> Self {
        if cfg!(target_os = "linux") {
            Self::Linux
        } else if cfg!(windows) {
            Self::Windows
        } else {
            Self::Other
        }
    }
}

/// The narrow host boundary keeps selection and execution tests incapable of
/// invoking Cargo or mutating the checkout. It also keeps argv as a vector all
/// the way to `std::process::Command`; no command joins checked values into
/// shell text. On Windows, the operating system necessarily dispatches the
/// reviewed batch wrapper, but each modeled argument still crosses the process
/// boundary separately.
trait ExecutionHost {
    fn platform(&self) -> HostPlatform;
    fn available_parallelism(&self) -> io::Result<NonZeroUsize>;
    fn run(&mut self, invocation: &ProcessInvocation) -> io::Result<ProcessOutcome>;
    fn run_capture(&mut self, invocation: &ProcessInvocation)
        -> io::Result<CapturedProcessOutcome>;
    fn github_step_summary(&mut self) -> Option<PathBuf>;
    fn append(&mut self, path: &Path, bytes: &[u8]) -> io::Result<()>;
}

struct SystemExecutionHost;

fn system_command(invocation: &ProcessInvocation) -> io::Result<process::Command> {
    system_command_for_platform(invocation, HostPlatform::current())
}

fn system_command_for_platform(
    invocation: &ProcessInvocation,
    platform: HostPlatform,
) -> io::Result<process::Command> {
    let (program, arguments) =
        invocation.argv.split_first().expect("validated modeled commands always have a program");
    // `cargo.sh` and `win-cargo.bat` implement the same reviewed repository
    // interface. Keep the model canonical and translate only that exact
    // executable here; unrelated programs such as `cargo` and `nproc` retain
    // their ordinary host lookup semantics.
    let program = match (platform, program.as_str()) {
        (HostPlatform::Windows, CARGO_WRAPPER) => WINDOWS_CARGO_WRAPPER,
        _ => program,
    };
    let working_directory = if invocation.working_directory.is_absolute() {
        invocation.working_directory.clone()
    } else {
        env::current_dir()?.join(&invocation.working_directory)
    };
    let program_path = Path::new(program);
    let executable = if program_path.is_absolute() || program_path.components().count() > 1 {
        working_directory.join(program_path)
    } else {
        program_path.to_path_buf()
    };
    let mut command = process::Command::new(executable);
    command
        .args(arguments)
        .current_dir(working_directory)
        // This private protocol is owned by the final Miri wrapper boundary.
        // Never pass an ambient value to setup commands such as `cargo clean`
        // or `nproc`; the final invocation adds its exact value explicitly.
        .env_remove(EXECUTION_CONTEXT_ENV)
        // Inherit unrelated runner state, but set every modeled variable
        // directly. Shell assignment and word splitting are not part of the
        // operation model.
        .envs(&invocation.environment);
    Ok(command)
}

impl ExecutionHost for SystemExecutionHost {
    fn platform(&self) -> HostPlatform {
        HostPlatform::current()
    }
    fn available_parallelism(&self) -> io::Result<NonZeroUsize> {
        thread::available_parallelism()
    }
    fn run(&mut self, invocation: &ProcessInvocation) -> io::Result<ProcessOutcome> {
        let status = system_command(invocation)?.status()?;
        Ok(ProcessOutcome { success: status.success(), code: status.code() })
    }

    fn run_capture(
        &mut self,
        invocation: &ProcessInvocation,
    ) -> io::Result<CapturedProcessOutcome> {
        // Only stdout is machine-readable. Preserve the program's stderr on
        // the runner so a start or status failure retains its native context.
        let output = system_command(invocation)?.stderr(process::Stdio::inherit()).output()?;
        Ok(CapturedProcessOutcome {
            success: output.status.success(),
            code: output.status.code(),
            stdout: output.stdout,
        })
    }

    fn github_step_summary(&mut self) -> Option<PathBuf> {
        env::var_os("GITHUB_STEP_SUMMARY").map(PathBuf::from)
    }

    fn append(&mut self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        OpenOptions::new().create(true).append(true).open(path)?.write_all(bytes)
    }
}

fn execute_build_cell_with(
    inputs: &CiInputs,
    selector: &BuildCellSelector,
    host: &mut impl ExecutionHost,
) -> Result<CellExecutionReport, CellExecutionError> {
    let repository_root = inputs.repository_root();
    let plan = Plan::create(inputs, &selector.event)?;
    let description = selector.description();
    let cell = unique_match(
        "ordinary build",
        &description,
        plan.builds().iter().filter(|cell| build_cell_matches(cell, selector)),
    )?;
    let semantics = BuildCellSemantics::from_plan(cell, inputs.policy())
        .map_err(|message| CellExecutionError::Model { message })?;
    let operations = build_operations(
        inputs.policy(),
        inputs.repository().zerocopy_docs_rs_rustdoc_args(),
        &semantics,
    )
    .map_err(|message| CellExecutionError::Model { message })?;
    let mut report = CellExecutionReport::new();

    for operation in operations {
        validate_operation(&operation).map_err(|message| CellExecutionError::Model { message })?;
        if !operation.applicable {
            return Err(CellExecutionError::Model {
                message: format!(
                    "selected operation {:?} is unexpectedly inapplicable",
                    operation.kind
                ),
            });
        }
        match &operation.command.payload {
            CommandPayload::Argv { argv, .. } => {
                run_process(host, repository_root, &operation.command, argv)?;
                report.executed_steps.push(operation.command.step.clone());
            }
            CommandPayload::ActionInputs { .. }
                if operation.kind == MatrixOperationKind::CargoSemverCheck =>
            {
                // The action identity, condition, and permission boundary must
                // stay literal in ci.yml. This explicit report is coupled to
                // that audited adapter until GitHub supports dynamic `uses`.
                report.workflow_owned_steps.push(operation.command.step.clone());
            }
            CommandPayload::ActionInputs { .. } => {
                return Err(CellExecutionError::UnsupportedPayload {
                    step: operation.command.step.clone(),
                    payload: "action inputs",
                });
            }
            CommandPayload::ArgvTemplate { .. } => {
                return Err(CellExecutionError::UnsupportedPayload {
                    step: operation.command.step.clone(),
                    payload: "argv template in an ordinary build cell",
                });
            }
        }
    }
    Ok(report)
}

fn execute_miri_cell_with(
    inputs: &CiInputs,
    selector: &MiriCellSelector,
    host: &mut impl ExecutionHost,
) -> Result<CellExecutionReport, CellExecutionError> {
    let repository_root = inputs.repository_root();
    let plan = Plan::create(inputs, &selector.event)?;
    let description = selector.description();
    let cell = unique_match(
        "Miri",
        &description,
        plan.miri().iter().filter(|cell| miri_cell_matches(cell, selector)),
    )?;
    let semantics = MiriCellSemantics::from_plan(cell, inputs.policy())
        .map_err(|message| CellExecutionError::Model { message })?;
    let operation =
        miri_operation(&semantics).map_err(|message| CellExecutionError::Model { message })?;
    validate_operation(&operation).map_err(|message| CellExecutionError::Model { message })?;
    if !operation.applicable {
        return Err(CellExecutionError::Model {
            message: "selected Miri operation is unexpectedly inapplicable".to_owned(),
        });
    }
    let CommandPayload::ArgvTemplate { argv, dynamic_value } = &operation.command.payload else {
        return Err(CellExecutionError::UnsupportedPayload {
            step: operation.command.step.clone(),
            payload: "non-template Miri command",
        });
    };
    validate_dynamic_placeholder(&operation.command.step, argv, dynamic_value)?;
    let (final_command, final_argv_template) = miri_wrapper_invocation(&operation.command, argv)?;

    execute_miri_direct(
        host,
        repository_root,
        &semantics,
        &operation.command,
        &final_command,
        &final_argv_template,
        dynamic_value,
    )
}

fn execute_miri_direct(
    host: &mut impl ExecutionHost,
    repository_root: &Path,
    semantics: &MiriCellSemantics,
    setup_command: &CommandSpec,
    final_command: &CommandSpec,
    argv_template: &[String],
    dynamic_value: &str,
) -> Result<CellExecutionReport, CellExecutionError> {
    let mut report = CellExecutionReport::new();
    if semantics.target == AARCH64_TARGET {
        // Keep this command coordinated with the workaround for rust-lang/miri
        // #3125 in ci.yml. It is setup for the modeled Miri invocation, not an
        // additional coverage decision.
        let clean = CommandSpec {
            job: MIRI_JOB.to_owned(),
            step: "Clean aarch64 Miri target".to_owned(),
            working_directory: WorkingDirectory::Relative(MATRIX_WORKING_DIRECTORY.to_owned()),
            environment: setup_command.environment.clone(),
            payload: CommandPayload::Argv {
                argv: vec!["cargo".to_owned(), "clean".to_owned()],
                dynamic_value: None,
            },
        };
        let CommandPayload::Argv { argv, .. } = &clean.payload else {
            unreachable!("the local aarch64 cleanup is a fixed argv command");
        };
        run_process(host, repository_root, &clean, argv)?;
        report.executed_steps.push(clean.step);
    }

    let threads = miri_thread_count(host, repository_root, &setup_command.environment)?;
    report.executed_steps.push(NPROC_STEP.to_owned());
    let argv = substitute_dynamic(
        &final_command.step,
        argv_template,
        dynamic_value,
        &threads.to_string(),
    )?;

    if let Some(path) = host.github_step_summary() {
        let summary = format!("Running Miri tests with {threads} threads\n");
        host.append(&path, summary.as_bytes())
            .map_err(|source| CellExecutionError::AppendStepSummary { path, source })?;
    }
    run_process(host, repository_root, final_command, &argv)?;
    report.executed_steps.push(final_command.step.clone());
    Ok(report)
}

fn miri_wrapper_invocation(
    command: &CommandSpec,
    argv: &[String],
) -> Result<(CommandSpec, Vec<String>), CellExecutionError> {
    let prefix = [CARGO_WRAPPER, "+nightly", "miri", "nextest", "run"];
    if argv.get(..prefix.len()).map(|values| values.iter().map(String::as_str).collect::<Vec<_>>())
        != Some(prefix.to_vec())
    {
        return Err(CellExecutionError::Model {
            message: format!(
                "Miri command does not begin with the frozen wrapper prefix {prefix:?}"
            ),
        });
    }
    if command.environment.contains_key(EXECUTION_CONTEXT_ENV) {
        return Err(CellExecutionError::Model {
            message: format!("Miri command must not preconfigure {EXECUTION_CONTEXT_ENV}"),
        });
    }
    let mut adapted = argv.to_vec();
    adapted.splice(5..5, ["--manifest-path".to_owned(), "zerocopy/Cargo.toml".to_owned()]);
    let mut environment = command.environment.clone();
    environment.insert(EXECUTION_CONTEXT_ENV.to_owned(), MIRI_REPOSITORY_ROOT_CONTEXT.to_owned());
    // Keep the wrapper's argv and cwd unchanged. The wrapper consumes the
    // private context and applies it only to its rustup/Cargo children, so all
    // toolchain installation, cfgs, UI variables, target directory handling,
    // and fully-qualified package resolution remain in one implementation.
    let invocation = CommandSpec { environment, ..command.clone() };
    Ok((invocation, adapted))
}

fn miri_thread_count(
    host: &mut impl ExecutionHost,
    repository_root: &Path,
    environment: &BTreeMap<String, String>,
) -> Result<usize, CellExecutionError> {
    if host.platform() != HostPlatform::Linux {
        return host
            .available_parallelism()
            .map_err(|source| CellExecutionError::AvailableParallelism { source })
            .and_then(|available| checked_miri_thread_count(available.get()));
    }
    // Keep this direct GNU `nproc` invocation coordinated with the Miri step
    // in ci.yml. The frozen workflow computes `2 * nproc`; invoking the same
    // program without a shell preserves nproc's handling of OMP overrides,
    // while Rust performs the checked multiplication instead of `bc`.
    let invocation = ProcessInvocation {
        step: NPROC_STEP.to_owned(),
        argv: vec!["nproc".to_owned()],
        working_directory: repository_root.join(MATRIX_WORKING_DIRECTORY),
        environment: environment.clone(),
    };
    let outcome = host
        .run_capture(&invocation)
        .map_err(|source| CellExecutionError::StartNproc { source })?;
    if !outcome.success {
        return Err(CellExecutionError::NprocFailed { status: process_status(outcome.code) });
    }
    parse_nproc_thread_count(&outcome.stdout)
}

fn parse_nproc_thread_count(stdout: &[u8]) -> Result<usize, CellExecutionError> {
    let output = std::str::from_utf8(stdout)
        .map_err(|source| CellExecutionError::NprocOutputNotUtf8 { source })?;
    let Some(value) = output.strip_suffix('\n') else {
        return Err(CellExecutionError::NprocOutputShape { output: output.to_owned() });
    };
    if value.is_empty() || value.contains(['\r', '\n']) {
        return Err(CellExecutionError::NprocOutputShape { output: output.to_owned() });
    }
    let available = value.parse::<usize>().map_err(|source| {
        CellExecutionError::NprocOutputParse { value: value.to_owned(), source }
    })?;
    // GNU nproc emits canonical unsigned decimal. Reject spellings which
    // Rust's integer parser might accept but the modeled program never emits.
    if !value.bytes().all(|byte| byte.is_ascii_digit()) || available.to_string() != value {
        return Err(CellExecutionError::NprocOutputShape { output: output.to_owned() });
    }
    if available == 0 {
        return Err(CellExecutionError::ProcessorCountZero);
    }
    checked_miri_thread_count(available)
}

fn checked_miri_thread_count(available: usize) -> Result<usize, CellExecutionError> {
    if available == 0 {
        return Err(CellExecutionError::ProcessorCountZero);
    }
    available.checked_mul(2).ok_or(CellExecutionError::ThreadCountOverflow { available })
}

fn run_process(
    host: &mut impl ExecutionHost,
    repository_root: &Path,
    command: &CommandSpec,
    argv: &[String],
) -> Result<(), CellExecutionError> {
    let working_directory = match &command.working_directory {
        WorkingDirectory::RepositoryRoot => repository_root.to_path_buf(),
        WorkingDirectory::Relative(path) => repository_root.join(path),
    };
    let invocation = ProcessInvocation {
        step: command.step.clone(),
        argv: argv.to_vec(),
        working_directory,
        environment: command.environment.clone(),
    };
    let program = invocation.argv.first().cloned().ok_or_else(|| CellExecutionError::Model {
        message: format!("step {:?} has an empty argv", command.step),
    })?;
    let outcome = host.run(&invocation).map_err(|source| CellExecutionError::StartProcess {
        step: command.step.clone(),
        program,
        source,
    })?;
    if !outcome.success {
        return Err(CellExecutionError::ProcessFailed {
            step: command.step.clone(),
            status: process_status(outcome.code),
        });
    }
    Ok(())
}

fn process_status(code: Option<i32>) -> String {
    code.map_or_else(|| "terminated by a signal".to_owned(), |code| format!("exit code {code}"))
}

fn validate_dynamic_placeholder(
    step: &str,
    argv: &[String],
    placeholder: &str,
) -> Result<(), CellExecutionError> {
    let occurrences = argv.iter().filter(|argument| argument.as_str() == placeholder).count();
    if occurrences != 1 {
        return Err(CellExecutionError::DynamicPlaceholder {
            step: step.to_owned(),
            placeholder: placeholder.to_owned(),
            occurrences,
        });
    }
    Ok(())
}

fn substitute_dynamic(
    step: &str,
    argv: &[String],
    placeholder: &str,
    value: &str,
) -> Result<Vec<String>, CellExecutionError> {
    validate_dynamic_placeholder(step, argv, placeholder)?;
    Ok(argv
        .iter()
        .map(|argument| if argument == placeholder { value.to_owned() } else { argument.clone() })
        .collect())
}

fn build_cell_matches(cell: &BuildPlanCell, selector: &BuildCellSelector) -> bool {
    cell.package().id() == selector.package
        && cell.toolchain().id() == selector.toolchain
        && cell.features().profile() == selector.feature_profile
        && cell.target().triple() == selector.target
}

fn miri_cell_matches(cell: &MiriPlanCell, selector: &MiriCellSelector) -> bool {
    cell.package().id() == selector.package
        && cell.toolchain().id() == selector.toolchain
        && cell.features().profile() == selector.feature_profile
        && cell.target().triple() == selector.target
        && cell.model().id() == selector.model
}

fn unique_match<'a, T>(
    kind: &'static str,
    selector: &str,
    matches: impl Iterator<Item = &'a T>,
) -> Result<&'a T, CellExecutionError> {
    let matches = matches.collect::<Vec<_>>();
    match matches.as_slice() {
        [] => Err(CellExecutionError::CellNotSelected { kind, selector: selector.to_owned() }),
        [cell] => Ok(*cell),
        cells => Err(CellExecutionError::AmbiguousCell {
            kind,
            selector: selector.to_owned(),
            matches: cells.len(),
        }),
    }
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
            for mut operation in build_operations(inputs.policy(), &docs_rs_rustdoc_args, &cell)? {
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
        operations.push(semver_operation(cell)?);
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
        vec![CARGO_WRAPPER.to_owned(), format!("+{}", cell.toolchain), cargo_subcommand.to_owned()];
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
        CARGO_WRAPPER.to_owned(),
        format!("+{}", cell.toolchain),
        "doc".to_owned(),
        "--no-deps".to_owned(),
        "--document-private-items".to_owned(),
        "--package".to_owned(),
        cell.package.clone(),
    ];
    argv.extend(cell.features.cargo_args());

    // Repository inventory obtains this ordered sequence from the canonical
    // Zerocopy package's `package.metadata.docs.rs.rustdoc-args`. Inventory
    // rejects whitespace inside an element, so joining with one space
    // preserves every argument boundary understood by RUSTDOCFLAGS.
    let docs_rs_rustdoc_args = docs_rs_rustdoc_args.join(" ");

    // Cargo doc inherits the same ordinary matrix environment as every other
    // command, then replaces RUSTDOCFLAGS. Keep this complete map coordinated
    // with the representative nightly-docs command golden. The golden used to
    // omit inherited RUSTFLAGS and MIRIFLAGS; retaining that omission in
    // executable behavior would silently differ from the captured workflow.
    let mut environment = ordinary_environment(cell.pinned_nightly);
    let rustdocflags = if cell.pinned_nightly {
        format!(
            "-Z unstable-options --document-hidden-items {docs_rs_rustdoc_args} {BASE_RUSTDOCFLAGS}"
        )
    } else {
        BASE_RUSTDOCFLAGS.to_owned()
    };
    environment.insert("RUSTDOCFLAGS".to_owned(), rustdocflags);
    MatrixOperation {
        kind,
        // `cargo doc` intentionally has no `--target`; all target cells for
        // the same package/toolchain/profile normalize to one obligation with
        // an occurrence count. Keep this coupled to the comment in
        // logical-obligations.tsv.
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

fn semver_operation(cell: &BuildCellSemantics) -> Result<MatrixOperation, String> {
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
    let with = BTreeMap::from([
        ("feature-group".to_owned(), JsonValue::String("only-explicit-features".to_owned())),
        ("features".to_owned(), JsonValue::String(stable_feature)),
        ("manifest-path".to_owned(), JsonValue::String(cell.manifest.clone())),
        ("package".to_owned(), JsonValue::String(cell.package.clone())),
        ("rust-target".to_owned(), JsonValue::String(cell.target.clone())),
        ("rust-toolchain".to_owned(), JsonValue::String(cell.toolchain_version.clone())),
    ]);
    let inputs = BTreeMap::from([
        ("uses".to_owned(), JsonValue::String(SEMVER_ACTION.to_owned())),
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
            environment: BTreeMap::from([
                ("RUSTDOCFLAGS".to_owned(), BASE_RUSTFLAGS.to_owned()),
                ("RUSTFLAGS".to_owned(), BASE_RUSTFLAGS.to_owned()),
            ]),
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
    // Keep this placeholder coordinated with the frozen command golden and
    // the direct GNU `nproc` invocation in `miri_thread_count`. The typed
    // executor removes shell parsing and `bc`, but deliberately preserves
    // nproc's processor-count semantics, including its OMP overrides.
    let dynamic = MIRI_THREAD_PLACEHOLDER.to_owned();
    let mut argv = vec![
        CARGO_WRAPPER.to_owned(),
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
    // These two operations belong to the immutable source commit named by the
    // baseline manifest. The live shell check was retired after typed
    // inventory and policy validation took ownership of this invariant; keep
    // the historical operations here so parity still proves what it replaced.
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
    use std::{
        collections::{BTreeMap, VecDeque},
        ffi::OsStr,
        io,
        num::NonZeroUsize,
        path::{Path, PathBuf},
        sync::OnceLock,
    };

    use super::{
        audit_execution, checked_miri_thread_count, compare_execution, derive_execution,
        execute_build_cell_with, execute_miri_cell_with, miri_thread_count,
        miri_wrapper_invocation, parse_nproc_thread_count, substitute_dynamic,
        system_command_for_platform, unique_match, BuildCellSelector, BuildCellSemantics,
        CapturedProcessOutcome, CellExecutionError, CommandSpec, EventClass, ExecutionHost,
        ExecutionMode, FeatureSelection, HostPlatform, MatrixOperation, MatrixOperationKind,
        MiriCellSelector, ModelMutation, ProcessInvocation, ProcessOutcome, WorkingDirectory,
        AARCH64_TARGET, CARGO_WRAPPER, EXECUTION_CONTEXT_ENV, MIRI_JOB,
        MIRI_REPOSITORY_ROOT_CONTEXT, MIRI_THREAD_PLACEHOLDER, NPROC_STEP, WINDOWS_CARGO_WRAPPER,
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

    #[derive(Debug, Default)]
    struct FakeExecutionHost {
        platform: Option<HostPlatform>,
        parallelism: Option<Result<NonZeroUsize, io::ErrorKind>>,
        invocations: Vec<ProcessInvocation>,
        outcomes: VecDeque<ProcessOutcome>,
        start_error: Option<io::ErrorKind>,
        captured_invocations: Vec<ProcessInvocation>,
        captured_outcomes: VecDeque<CapturedProcessOutcome>,
        capture_start_error: Option<io::ErrorKind>,
        step_summary: Option<PathBuf>,
        appended: BTreeMap<PathBuf, Vec<u8>>,
        append_error: Option<io::ErrorKind>,
    }

    impl ExecutionHost for FakeExecutionHost {
        fn platform(&self) -> HostPlatform {
            self.platform.unwrap_or(HostPlatform::Linux)
        }
        fn available_parallelism(&self) -> io::Result<NonZeroUsize> {
            self.parallelism
                .unwrap_or_else(|| NonZeroUsize::new(4).ok_or(io::ErrorKind::Other))
                .map_err(io::Error::from)
        }
        fn run(&mut self, invocation: &ProcessInvocation) -> io::Result<ProcessOutcome> {
            self.invocations.push(invocation.clone());
            if let Some(kind) = self.start_error.take() {
                return Err(io::Error::from(kind));
            }
            Ok(self.outcomes.pop_front().unwrap_or(ProcessOutcome { success: true, code: Some(0) }))
        }

        fn run_capture(
            &mut self,
            invocation: &ProcessInvocation,
        ) -> io::Result<CapturedProcessOutcome> {
            self.captured_invocations.push(invocation.clone());
            if let Some(kind) = self.capture_start_error.take() {
                return Err(io::Error::from(kind));
            }
            Ok(self.captured_outcomes.pop_front().unwrap_or(CapturedProcessOutcome {
                success: true,
                code: Some(0),
                stdout: b"4\n".to_vec(),
            }))
        }

        fn github_step_summary(&mut self) -> Option<PathBuf> {
            self.step_summary.clone()
        }

        fn append(&mut self, path: &Path, bytes: &[u8]) -> io::Result<()> {
            if let Some(kind) = self.append_error.take() {
                return Err(io::Error::from(kind));
            }
            self.appended.entry(path.to_path_buf()).or_default().extend_from_slice(bytes);
            Ok(())
        }
    }

    fn test_root() -> PathBuf {
        inputs().repository_root().to_path_buf()
    }

    fn build_selector(event: &str, profile: &str, target: &str) -> BuildCellSelector {
        BuildCellSelector::new(event, "zerocopy", "stable", profile, target)
    }

    fn miri_selector(event: &str, target: &str, model: &str) -> MiriCellSelector {
        MiriCellSelector::new(event, "zerocopy", "nightly", "default", target, model)
    }

    #[test]
    fn miri_keeps_wrapper_argv_and_cwd_while_setting_private_context() {
        let command = CommandSpec {
            job: MIRI_JOB.to_owned(),
            step: "Miri".to_owned(),
            working_directory: WorkingDirectory::Relative("zerocopy".to_owned()),
            environment: BTreeMap::new(),
            payload: CommandPayload::ArgvTemplate {
                argv: vec![
                    CARGO_WRAPPER.to_owned(),
                    "+nightly".to_owned(),
                    "miri".to_owned(),
                    "nextest".to_owned(),
                    "run".to_owned(),
                ],
                dynamic_value: MIRI_THREAD_PLACEHOLDER.to_owned(),
            },
        };
        let argv = vec![
            CARGO_WRAPPER.to_owned(),
            "+nightly".to_owned(),
            "miri".to_owned(),
            "nextest".to_owned(),
            "run".to_owned(),
        ];
        let (invocation, adapted) = miri_wrapper_invocation(&command, &argv).unwrap();
        assert_eq!(invocation.working_directory, WorkingDirectory::Relative("zerocopy".to_owned()));
        assert_eq!(invocation.environment[EXECUTION_CONTEXT_ENV], MIRI_REPOSITORY_ROOT_CONTEXT);
        let CommandPayload::ArgvTemplate { argv: actual, dynamic_value } = invocation.payload
        else {
            panic!("Miri must retain its template payload");
        };
        assert_eq!(actual, argv);
        assert_eq!(dynamic_value, MIRI_THREAD_PLACEHOLDER);
        assert_eq!(adapted[5..7], ["--manifest-path", "zerocopy/Cargo.toml"]);
    }

    #[test]
    fn miri_rejects_private_context_in_model_environment() {
        let command = CommandSpec {
            job: MIRI_JOB.to_owned(),
            step: "Miri".to_owned(),
            working_directory: WorkingDirectory::Relative("zerocopy".to_owned()),
            environment: BTreeMap::from([(EXECUTION_CONTEXT_ENV.to_owned(), "wrong".to_owned())]),
            payload: CommandPayload::ArgvTemplate {
                argv: vec![
                    CARGO_WRAPPER.to_owned(),
                    "+nightly".to_owned(),
                    "miri".to_owned(),
                    "nextest".to_owned(),
                    "run".to_owned(),
                ],
                dynamic_value: MIRI_THREAD_PLACEHOLDER.to_owned(),
            },
        };
        let error = miri_wrapper_invocation(
            &command,
            &[
                CARGO_WRAPPER.to_owned(),
                "+nightly".to_owned(),
                "miri".to_owned(),
                "nextest".to_owned(),
                "run".to_owned(),
            ],
        )
        .unwrap_err();
        assert!(
            matches!(error, CellExecutionError::Model { message } if message.contains(EXECUTION_CONTEXT_ENV))
        );
    }

    #[test]
    fn invalid_miri_prefix_is_rejected_during_side_effect_free_preparation() {
        let command = CommandSpec {
            job: MIRI_JOB.to_owned(),
            step: "Miri".to_owned(),
            working_directory: WorkingDirectory::Relative("zerocopy".to_owned()),
            environment: BTreeMap::new(),
            payload: CommandPayload::ArgvTemplate {
                argv: vec!["cargo".to_owned(), "miri".to_owned()],
                dynamic_value: MIRI_THREAD_PLACEHOLDER.to_owned(),
            },
        };
        let error = miri_wrapper_invocation(&command, &["cargo".to_owned(), "miri".to_owned()])
            .unwrap_err();
        assert!(matches!(error, CellExecutionError::Model { .. }));
    }

    #[test]
    fn execution_uses_checked_root_and_preserves_argv_and_environment_boundaries() {
        let root = test_root();
        assert!(root.is_absolute(), "CiInputs must retain its canonical root");
        let mut host = FakeExecutionHost::default();
        let selector = build_selector("pull_request", "stable", "x86_64-unknown-linux-gnu");
        let report = execute_build_cell_with(inputs(), &selector, &mut host).unwrap();

        assert_eq!(report.executed_steps, ["Test native target", "Cargo doc"]);
        assert_eq!(report.workflow_owned_steps, ["Check semver compatibility"]);
        assert_eq!(host.invocations.len(), 2);
        assert_eq!(
            host.invocations[0].argv,
            [
                "./cargo.sh",
                "+stable",
                "test",
                "--package",
                "zerocopy",
                "--target",
                "x86_64-unknown-linux-gnu",
                "--no-default-features",
                "--features",
                "__internal_use_only_features_that_work_on_stable",
                "--verbose",
            ]
        );
        assert_eq!(host.invocations[0].working_directory, root.join("zerocopy"));
        assert_eq!(
            host.invocations[0].environment,
            BTreeMap::from([
                ("RUSTDOCFLAGS".to_owned(), "-Dwarnings --cfg=zerocopy_unstable_ptr".to_owned(),),
                ("RUSTFLAGS".to_owned(), "-Dwarnings".to_owned()),
            ])
        );
        assert_eq!(
            host.invocations[1].environment,
            BTreeMap::from([
                ("RUSTDOCFLAGS".to_owned(), "-Dwarnings --cfg=zerocopy_unstable_ptr".to_owned()),
                ("RUSTFLAGS".to_owned(), "-Dwarnings".to_owned()),
            ])
        );
    }

    #[test]
    fn windows_translates_only_the_repository_cargo_wrapper() {
        let working_directory = test_root().join("zerocopy");
        let environment = BTreeMap::from([
            ("RUSTFLAGS".to_owned(), "-Dwarnings".to_owned()),
            ("ZC_TEST_VALUE".to_owned(), "two words".to_owned()),
        ]);
        let invocation = ProcessInvocation {
            step: "Test native target".to_owned(),
            argv: vec![
                CARGO_WRAPPER.to_owned(),
                "+stable".to_owned(),
                "test".to_owned(),
                "--features".to_owned(),
                "feature-a,feature-b".to_owned(),
            ],
            working_directory: working_directory.clone(),
            environment: environment.clone(),
        };

        let command = system_command_for_platform(&invocation, HostPlatform::Windows).unwrap();

        assert_eq!(command.get_program(), working_directory.join(WINDOWS_CARGO_WRAPPER));
        assert_eq!(
            command.get_args().collect::<Vec<_>>(),
            invocation.argv[1..].iter().map(AsRef::as_ref).collect::<Vec<&str>>()
        );
        assert_eq!(command.get_current_dir(), Some(working_directory.as_path()));
        assert_eq!(
            command
                .get_envs()
                .filter_map(|(name, value)| {
                    value.map(|value| {
                        (name.to_str().unwrap().to_owned(), value.to_str().unwrap().to_owned())
                    })
                })
                .collect::<BTreeMap<_, _>>(),
            environment
        );
        assert!(command
            .get_envs()
            .any(|(name, value)| name == OsStr::new(EXECUTION_CONTEXT_ENV) && value.is_none()));

        let mut final_invocation = invocation.clone();
        final_invocation
            .environment
            .insert(EXECUTION_CONTEXT_ENV.to_owned(), MIRI_REPOSITORY_ROOT_CONTEXT.to_owned());
        let final_command =
            system_command_for_platform(&final_invocation, HostPlatform::Windows).unwrap();
        assert!(final_command.get_envs().any(|(name, value)| {
            name == OsStr::new(EXECUTION_CONTEXT_ENV)
                && value == Some(OsStr::new(MIRI_REPOSITORY_ROOT_CONTEXT))
        }));

        let mut unrelated = invocation;
        unrelated.argv = vec!["cargo".to_owned(), "clean".to_owned()];
        let command = system_command_for_platform(&unrelated, HostPlatform::Windows).unwrap();
        assert_eq!(command.get_program(), "cargo");
        assert_eq!(command.get_args().collect::<Vec<_>>(), ["clean"]);
    }

    #[test]
    fn nightly_docs_execute_with_the_complete_effective_environment() {
        let mut host = FakeExecutionHost::default();
        let selector = BuildCellSelector::new(
            "push",
            "zerocopy",
            "nightly",
            "all",
            "x86_64-unknown-linux-gnu",
        );

        let report = execute_build_cell_with(inputs(), &selector, &mut host).unwrap();

        assert_eq!(report.executed_steps, ["Test native target", "Clippy tests", "Cargo doc"]);
        let docs =
            host.invocations.iter().find(|invocation| invocation.step == "Cargo doc").unwrap();
        assert_eq!(
            docs.environment,
            BTreeMap::from([
                (
                    "MIRIFLAGS".to_owned(),
                    " -Zmiri-strict-provenance -Zmiri-backtrace=full".to_owned(),
                ),
                (
                    "RUSTDOCFLAGS".to_owned(),
                    "-Z unstable-options --document-hidden-items --cfg doc_cfg --generate-link-to-definition --extend-css rustdoc/style.css -Dwarnings --cfg=zerocopy_unstable_ptr"
                        .to_owned(),
                ),
                ("RUSTFLAGS".to_owned(), "-Dwarnings -Zrandomize-layout".to_owned()),
            ])
        );
    }

    #[test]
    fn unknown_and_event_excluded_cells_fail_without_processes() {
        let mut host = FakeExecutionHost::default();
        let unknown = BuildCellSelector::new(
            "pull_request",
            "unknown-package",
            "stable",
            "default",
            "x86_64-unknown-linux-gnu",
        );
        assert!(matches!(
            execute_build_cell_with(inputs(), &unknown, &mut host),
            Err(CellExecutionError::CellNotSelected { .. })
        ));
        let excluded = build_selector("pull_request", "default", "aarch64-unknown-linux-gnu");
        assert!(matches!(
            execute_build_cell_with(inputs(), &excluded, &mut host),
            Err(CellExecutionError::CellNotSelected { .. })
        ));
        let excluded_miri = miri_selector("pull_request", "x86_64-unknown-linux-gnu", "stacked");
        assert!(matches!(
            execute_miri_cell_with(inputs(), &excluded_miri, &mut host),
            Err(CellExecutionError::CellNotSelected { .. })
        ));
        let unknown_event = build_selector("unknown-event", "default", "x86_64-unknown-linux-gnu");
        assert!(matches!(
            execute_build_cell_with(inputs(), &unknown_event, &mut host),
            Err(CellExecutionError::Plan(_))
        ));
        assert!(host.invocations.is_empty());
    }

    #[test]
    fn duplicate_matches_fail_closed() {
        let values = [1, 2];
        assert!(matches!(
            unique_match("test", "selector", values.iter()),
            Err(CellExecutionError::AmbiguousCell { matches: 2, .. })
        ));
    }

    #[test]
    fn x86_miri_runs_nproc_then_wrapper_with_root_context_only_at_boundary() {
        let root = test_root();
        let mut host = FakeExecutionHost::default();
        let selector = miri_selector("push", "x86_64-unknown-linux-gnu", "stacked");

        let report = execute_miri_cell_with(inputs(), &selector, &mut host).unwrap();

        assert_eq!(report.executed_steps, [NPROC_STEP, "Run tests under Miri"]);
        assert_eq!(host.captured_invocations.len(), 1);
        assert_eq!(host.captured_invocations[0].argv, ["nproc"]);
        assert_eq!(host.captured_invocations[0].working_directory, root.join("zerocopy"));
        assert_eq!(host.invocations.len(), 1);
        let invocation = &host.invocations[0];
        assert_eq!(invocation.working_directory, root.join("zerocopy"));
        assert_eq!(
            invocation.argv,
            [
                "./cargo.sh",
                "+nightly",
                "miri",
                "nextest",
                "run",
                "--manifest-path",
                "zerocopy/Cargo.toml",
                "--locked",
                "--ignore-default-filter",
                "--test-threads",
                "8",
                "--package",
                "zerocopy",
                "--target",
                "x86_64-unknown-linux-gnu",
            ]
        );
        assert!(!host.captured_invocations[0].environment.contains_key(EXECUTION_CONTEXT_ENV));
        assert!(!invocation.environment.is_empty());
        assert_eq!(invocation.environment[EXECUTION_CONTEXT_ENV], MIRI_REPOSITORY_ROOT_CONTEXT);
        assert_eq!(invocation.environment["RUSTFLAGS"], "-Dwarnings -Zrandomize-layout");
        assert_eq!(
            invocation.environment["RUSTDOCFLAGS"],
            "-Dwarnings --cfg=zerocopy_unstable_ptr"
        );
        assert_eq!(
            invocation.environment["MIRIFLAGS"],
            " -Zmiri-strict-provenance -Zmiri-backtrace=full "
        );
    }

    #[test]
    fn aarch64_miri_cleans_from_zerocopy_before_running_wrapper() {
        let root = test_root();
        let mut host = FakeExecutionHost::default();
        let selector = miri_selector("push", AARCH64_TARGET, "tree");

        let report = execute_miri_cell_with(inputs(), &selector, &mut host).unwrap();

        assert_eq!(
            report.executed_steps,
            ["Clean aarch64 Miri target", NPROC_STEP, "Run tests under Miri"]
        );
        assert_eq!(host.invocations.len(), 2);
        assert_eq!(host.invocations[0].argv, ["cargo", "clean"]);
        assert_eq!(host.invocations[0].working_directory, root.join("zerocopy"));
        assert!(!host.invocations[0].environment.contains_key(EXECUTION_CONTEXT_ENV));
        assert_eq!(host.captured_invocations[0].argv, ["nproc"]);
        assert!(!host.captured_invocations[0].environment.contains_key(EXECUTION_CONTEXT_ENV));
        assert_eq!(&host.invocations[1].argv[5..7], ["--manifest-path", "zerocopy/Cargo.toml"]);
        assert_eq!(host.invocations[1].working_directory, root.join("zerocopy"));
        assert_eq!(
            host.invocations[1].environment[EXECUTION_CONTEXT_ENV],
            MIRI_REPOSITORY_ROOT_CONTEXT
        );
    }

    #[test]
    fn parses_exact_gnu_nproc_output_and_checked_doubles_it() {
        assert_eq!(parse_nproc_thread_count(b"1\n").unwrap(), 2);
        assert_eq!(parse_nproc_thread_count(b"17\n").unwrap(), 34);
    }

    #[test]
    fn nproc_output_shape_parse_zero_and_overflow_failures_are_typed() {
        assert!(matches!(
            parse_nproc_thread_count(&[0xff, b'\n']),
            Err(CellExecutionError::NprocOutputNotUtf8 { .. })
        ));
        for output in [
            b"".as_slice(),
            b"\n".as_slice(),
            b"1".as_slice(),
            b"1\r\n".as_slice(),
            b"1\n2\n".as_slice(),
            b"+1\n".as_slice(),
            b"01\n".as_slice(),
        ] {
            assert!(
                matches!(
                    parse_nproc_thread_count(output),
                    Err(CellExecutionError::NprocOutputShape { .. })
                ),
                "unexpected result for {output:?}"
            );
        }
        assert!(matches!(
            parse_nproc_thread_count(b"not-a-number\n"),
            Err(CellExecutionError::NprocOutputParse { .. })
        ));
        let too_large = format!("{}0\n", usize::MAX);
        assert!(matches!(
            parse_nproc_thread_count(too_large.as_bytes()),
            Err(CellExecutionError::NprocOutputParse { .. })
        ));
        assert!(matches!(
            parse_nproc_thread_count(b"0\n"),
            Err(CellExecutionError::ProcessorCountZero)
        ));
        let overflow = format!("{}\n", usize::MAX);
        assert!(matches!(
            parse_nproc_thread_count(overflow.as_bytes()),
            Err(CellExecutionError::ThreadCountOverflow { available })
                if available == usize::MAX
        ));
    }

    #[test]
    fn linux_thread_count_uses_exact_nproc_invocation() {
        let root = test_root();
        let mut host = FakeExecutionHost::default();
        host.captured_outcomes.push_back(CapturedProcessOutcome {
            success: true,
            code: Some(0),
            stdout: b"17\n".to_vec(),
        });

        assert_eq!(miri_thread_count(&mut host, &root, &BTreeMap::new()).unwrap(), 34);
        assert_eq!(host.captured_invocations.len(), 1);
        assert_eq!(host.captured_invocations[0].argv, ["nproc"]);
        assert_eq!(host.captured_invocations[0].working_directory, root.join("zerocopy"));
    }

    #[test]
    fn non_linux_thread_count_uses_host_available_parallelism() {
        for platform in [HostPlatform::Windows, HostPlatform::Other] {
            let root = test_root();
            let mut host = FakeExecutionHost {
                platform: Some(platform),
                parallelism: Some(Ok(NonZeroUsize::new(3).unwrap())),
                ..FakeExecutionHost::default()
            };

            assert_eq!(miri_thread_count(&mut host, &root, &BTreeMap::new()).unwrap(), 6);
            assert!(host.captured_invocations.is_empty());
        }
    }

    #[test]
    fn non_linux_thread_count_reports_parallelism_query_failure() {
        let root = test_root();
        let mut host = FakeExecutionHost {
            platform: Some(HostPlatform::Other),
            parallelism: Some(Err(io::ErrorKind::PermissionDenied)),
            ..FakeExecutionHost::default()
        };

        assert!(matches!(
            miri_thread_count(&mut host, &root, &BTreeMap::new()),
            Err(CellExecutionError::AvailableParallelism { source })
                if source.kind() == io::ErrorKind::PermissionDenied
        ));
    }

    #[test]
    fn linux_nproc_start_failure_is_typed() {
        let root = test_root();
        let mut host = FakeExecutionHost {
            capture_start_error: Some(io::ErrorKind::NotFound),
            ..FakeExecutionHost::default()
        };

        assert!(matches!(
            miri_thread_count(&mut host, &root, &BTreeMap::new()),
            Err(CellExecutionError::StartNproc { source })
                if source.kind() == io::ErrorKind::NotFound
        ));
        assert_eq!(host.captured_invocations.len(), 1);
        assert!(host.invocations.is_empty());
    }

    #[test]
    fn linux_nproc_status_failure_is_typed() {
        let root = test_root();
        let mut host = FakeExecutionHost::default();
        host.captured_outcomes.push_back(CapturedProcessOutcome {
            success: false,
            code: Some(23),
            stdout: Vec::new(),
        });

        assert!(matches!(
            miri_thread_count(&mut host, &root, &BTreeMap::new()),
            Err(CellExecutionError::NprocFailed { status }) if status == "exit code 23"
        ));
        assert_eq!(host.captured_invocations.len(), 1);
        assert!(host.invocations.is_empty());
    }

    #[test]
    fn checked_thread_count_rejects_zero_and_overflow() {
        assert!(matches!(
            checked_miri_thread_count(0),
            Err(CellExecutionError::ProcessorCountZero)
        ));
        assert!(matches!(
            checked_miri_thread_count(usize::MAX),
            Err(CellExecutionError::ThreadCountOverflow { available })
                if available == usize::MAX
        ));
    }

    #[test]
    fn dynamic_substitution_requires_one_exact_argv_element() {
        let missing = ["prefix<threads>suffix".to_owned()];
        assert!(matches!(
            substitute_dynamic("Miri", &missing, "<threads>", "4"),
            Err(CellExecutionError::DynamicPlaceholder { occurrences: 0, .. })
        ));
        let duplicate = ["<threads>".to_owned(), "<threads>".to_owned()];
        assert!(matches!(
            substitute_dynamic("Miri", &duplicate, "<threads>", "4"),
            Err(CellExecutionError::DynamicPlaceholder { occurrences: 2, .. })
        ));
        assert_eq!(
            substitute_dynamic(
                "Miri",
                &["--test-threads".to_owned(), "<threads>".to_owned()],
                "<threads>",
                "4",
            )
            .unwrap(),
            ["--test-threads", "4"]
        );
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
