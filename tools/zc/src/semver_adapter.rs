// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! A deliberately narrow audit of the semver GitHub Actions adapter.
//!
//! GitHub requires an action reference to remain literal workflow YAML. The
//! typed planner therefore cannot execute `cargo-semver-checks` itself or emit
//! the `uses` field dynamically. That narrow handwritten boundary is
//! load-bearing: changing its preparation, action revision, explicit
//! environment, inputs, or condition can silently make the typed semver policy
//! mean something else.
//!
//! This module does not pretend to parse arbitrary GitHub Actions YAML. The
//! general workflow inventory in [`crate::workflow`] proves filenames and job
//! IDs, while the planner projects exact event-specific semver targets. Here we
//! recognize the complete canonical semver job and its preparation/action pair,
//! construct the static action specification from checked policy and repository
//! inventory, and reject unfamiliar or additional syntax. A broader workflow
//! shape must receive a deliberately reviewed parser change.
//!
//! Keep the following files coordinated:
//!
//! * `ci/zc.toml` owns the semver package, toolchain, profile, target set, and
//!   waivers.
//! * `zerocopy/Cargo.toml` owns the stable aggregate feature and package path
//!   discovered through Cargo metadata.
//! * `.github/workflows/ci.yml` contains the literal action adapter audited
//!   here.
//! * `plan.rs` derives semver work from the same checked coverage cells as the
//!   ordinary build plan. `github.rs` projects only each selected target, and
//!   this module requires the standalone job to consume that exact matrix.
//! * The planner part of that audit checks the complete workflow-level
//!   environment. This module rejects a job-level environment and requires the
//!   semver pair immediately after pinned checkout on a fresh runner, isolated
//!   from repository-owned setup and the ordinary build. Keep the audit order
//!   in `CiInputs::load` intact when changing that division of responsibility.
//! * `workflow_protocol.rs` owns the workflow path, job and output names shared
//!   with the producer. Keep this module's deliberately narrow job-range
//!   grammar coordinated with `planned_adapter/source.rs`.
//! * The workflow's `Prepare cargo-semver-checks` step implements the reviewed
//!   commit-message escape hatch and vendored-source workaround. Its exact
//!   shell, selector, and step-scoped output are audited here alongside the
//!   action which consumes that output. Do not replace the output with an
//!   ambient environment variable: another step or scope could then suppress
//!   semver checks.
//! * `execution.rs` models the same action as legacy command behavior. It must
//!   consume the constants and typed values exported here rather than growing
//!   an independent copy.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt,
    ops::Range,
    path::Path,
};

use thiserror::Error;

use crate::{
    inventory::RepositoryInventory,
    policy::{FeatureProfile, Policy},
    workflow_protocol::{
        PLAN_JOB, REPOSITORY_WORKING_DIRECTORY, SEMVER_ENABLED_OUTPUT, SEMVER_JOB,
        SEMVER_MATRIX_OUTPUT, SEMVER_STEP_NAME, TRUSTED_SHELL, WORKFLOW_PATH,
    },
};

/// The pinned action identity shared with the typed execution model.
pub(crate) const SEMVER_ACTION: &str =
    "obi1kenobi/cargo-semver-checks-action@6b69fcf40e9b5fb17adeb57e4b6ecd020649a239";

/// The action's explicit feature-selection mode.
pub(crate) const SEMVER_FEATURE_GROUP: &str = "only-explicit-features";

/// Action input which separates target-specific baseline-rustdoc caches.
pub(crate) const SEMVER_CACHE_PREFIX_INPUT: &str = "prefix-key";

/// Action input which selects the target whose public API is checked.
pub(crate) const SEMVER_TARGET_INPUT: &str = "rust-target";

/// The one dynamic value accepted by both target-specific action inputs.
pub(crate) const SEMVER_MATRIX_TARGET_EXPRESSION: &str = "${{ matrix.target }}";

/// Warnings remain errors, while unstable public API stays hidden from semver.
pub(crate) const SEMVER_WARNING_FLAGS: &str = "-Dwarnings";

const PREPARE_STEP_NAME: &str = "Prepare cargo-semver-checks";
const PREPARE_STEP_MARKER: &str = "    - name: Prepare cargo-semver-checks";
const PREPARE_STEP_ID: &str = "prepare_semver";
const PREPARE_OUTPUT_CONDITION: &str = "steps.prepare_semver.outputs.run == 'true'";
const LEGACY_SKIP_ENVIRONMENT: &str = "ZC_SKIP_CARGO_SEMVER_CHECKS";
const SEMVER_ACTION_MARKER: &str = "cargo-semver-checks-action@";
const PREPARE_ROOT_FIELD_ORDER: [&str; 5] = ["id", "shell", "working-directory", "env", "run"];
const ROOT_FIELD_ORDER: [&str; 4] = ["uses", "env", "with", "if"];

// The preparation reads the pull request head commit, so checkout identity and
// history depth are part of the adapter's behavior. Nothing except this pinned
// external action may run first on the fresh semver runner.
const CHECKOUT_STEP: &[&str] = &[
    "    - uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1",
    "      with:",
    "        fetch-depth: 2",
    "        persist-credentials: false",
];

const PREPARE_RUN: &[&str] = &[
    "set -euo pipefail",
    "# Pull request jobs check the head commit rather than GitHub's synthetic",
    "# merge commit. `PR_HEAD_SHA`, the depth-2 checkout above, and this",
    "# lookup are one contract: if checkout stops fetching that object,",
    "# `git log` fails instead of silently inspecting another message.",
    "if [[ \"$GITHUB_EVENT_NAME\" == 'pull_request' ]]; then",
    "  MESSAGE=\"$(/usr/bin/git log -1 --pretty=%B \"$PR_HEAD_SHA\")\"",
    "  MESSAGE_SOURCE='pull request head commit message'",
    "else",
    "  MESSAGE=\"$(/usr/bin/git log -1 --pretty=%B HEAD)\"",
    "  MESSAGE_SOURCE='commit message'",
    "fi",
    "if /usr/bin/grep -Eq \\",
    "  '^[[:space:]]*SKIP_CARGO_SEMVER_CHECKS=1[[:space:]]*$' \\",
    "  <<< \"$MESSAGE\"; then",
    "  printf \"Found 'SKIP_CARGO_SEMVER_CHECKS=1' in the %s; \" \\",
    "    \"$MESSAGE_SOURCE\" | /usr/bin/tee -a \"$GITHUB_STEP_SUMMARY\"",
    "  printf 'skipping cargo-semver-checks.\\n' | \\",
    "    /usr/bin/tee -a \"$GITHUB_STEP_SUMMARY\"",
    "  printf 'run=false\\n' >> \"$GITHUB_OUTPUT\"",
    "else",
    "  # FIXME(#2906): cargo-semver-checks fetches the latest Zerocopy from",
    "  # crates.io, but the vendored-source configuration cannot resolve",
    "  # that package. This exact file removal affects only this isolated",
    "  # checkout. Switch to --baseline-rev before removing the workaround.",
    "  /usr/bin/rm .cargo/config.toml",
    "  printf 'run=true\\n' >> \"$GITHUB_OUTPUT\"",
    "fi",
];

/// All semantic values expected in the handwritten adapter.
///
/// This type is crate-visible so the typed executor can share this model. Its
/// fields remain private to prevent another module from constructing an
/// unchecked, nearly-identical adapter.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SemverAdapterSpec {
    preparation_environment: BTreeMap<String, String>,
    preparation_run: Vec<String>,
    action: &'static str,
    environment: BTreeMap<String, String>,
    inputs: BTreeMap<String, String>,
    condition: Vec<String>,
}

impl SemverAdapterSpec {
    /// Derives the adapter from inputs which have already passed their owning
    /// validators.
    pub(crate) fn from_checked_inputs(
        policy: &Policy,
        repository: &RepositoryInventory,
    ) -> Result<Self, SemverAdapterViolations> {
        let mut errors = ViolationSink::default();
        let semver = policy.semver();

        let profile = policy.features().profiles().get(semver.profile().as_str());
        if profile != Some(&FeatureProfile::StableAggregate) {
            errors.push(
                "semver.profile",
                format!(
                    "profile `{}` must select the stable aggregate feature for the GitHub adapter",
                    semver.profile()
                ),
            );
        }

        let manifest = match repository.policy_packages().get(semver.package().as_str()) {
            Some(package) => match slash_path(package.cargo().manifest()) {
                Ok(path) => Some(path),
                Err(message) => {
                    errors.push("semver.package", message);
                    None
                }
            },
            None => {
                errors.push(
                    "semver.package",
                    format!(
                        "checked inventory has no package `{}` for the semver adapter",
                        semver.package()
                    ),
                );
                None
            }
        };

        let toolchain_version =
            match repository.toolchain_versions().get(semver.toolchain().as_str()) {
                Some(version) => Some(version.clone()),
                None => {
                    errors.push(
                        "semver.toolchain",
                        format!(
                            "checked inventory has no version for semver toolchain `{}`",
                            semver.toolchain()
                        ),
                    );
                    None
                }
            };

        // These values are written as unquoted YAML scalars by the deliberately
        // narrow source adapter below. Refuse repository or policy values for
        // which textual equality would not imply YAML scalar equality.
        validate_plain_string_scalar("semver.package", semver.package().as_str(), &mut errors);
        validate_plain_string_scalar("semver.profile", semver.profile().as_str(), &mut errors);
        validate_plain_string_scalar("semver.toolchain", semver.toolchain().as_str(), &mut errors);
        validate_plain_string_scalar(
            "features.stable_feature_root",
            policy.features().stable_feature_root().as_str(),
            &mut errors,
        );
        if let Some(manifest) = manifest.as_deref() {
            validate_plain_string_scalar("semver.package.manifest", manifest, &mut errors);
        }
        if let Some(toolchain_version) = toolchain_version.as_deref() {
            validate_exact_rust_version_scalar(
                "semver.toolchain.version",
                toolchain_version,
                &mut errors,
            );
        }
        if !errors.is_empty() {
            return Err(errors.finish());
        }
        let manifest = manifest.expect("a valid checked package must have a UTF-8 manifest path");
        let toolchain_version =
            toolchain_version.expect("a valid checked semver toolchain must have a version");
        let environment = BTreeMap::from([
            ("RUSTDOCFLAGS".to_owned(), SEMVER_WARNING_FLAGS.to_owned()),
            ("RUSTFLAGS".to_owned(), SEMVER_WARNING_FLAGS.to_owned()),
        ]);
        let inputs = BTreeMap::from([
            ("feature-group".to_owned(), SEMVER_FEATURE_GROUP.to_owned()),
            ("features".to_owned(), policy.features().stable_feature_root().as_str().to_owned()),
            ("manifest-path".to_owned(), manifest),
            ("package".to_owned(), semver.package().as_str().to_owned()),
            (SEMVER_CACHE_PREFIX_INPUT.to_owned(), SEMVER_MATRIX_TARGET_EXPRESSION.to_owned()),
            (SEMVER_TARGET_INPUT.to_owned(), SEMVER_MATRIX_TARGET_EXPRESSION.to_owned()),
            ("rust-toolchain".to_owned(), toolchain_version),
        ]);

        let preparation_environment = BTreeMap::from([(
            "PR_HEAD_SHA".to_owned(),
            "${{ github.event.pull_request.head.sha }}".to_owned(),
        )]);
        let preparation_run = PREPARE_RUN.iter().map(|line| (*line).to_owned()).collect();
        let condition = vec![PREPARE_OUTPUT_CONDITION.to_owned()];

        Ok(Self {
            preparation_environment,
            preparation_run,
            action: SEMVER_ACTION,
            environment,
            inputs,
            condition,
        })
    }

    /// Returns the preparation step's complete explicit environment.
    fn preparation_environment(&self) -> &BTreeMap<String, String> {
        &self.preparation_environment
    }

    /// Returns every behavior-bearing shell line in the preparation step.
    fn preparation_run(&self) -> &[String] {
        &self.preparation_run
    }

    /// Returns the exact pinned `uses` identity.
    pub(crate) fn action(&self) -> &str {
        self.action
    }

    /// Returns the action step's complete explicit environment.
    pub(crate) fn environment(&self) -> &BTreeMap<String, String> {
        &self.environment
    }

    /// Returns the complete `with` mapping, including GitHub expressions.
    pub(crate) fn inputs(&self) -> &BTreeMap<String, String> {
        &self.inputs
    }

    /// Returns the exact lines in the multiline GitHub condition.
    pub(crate) fn condition(&self) -> &[String] {
        &self.condition
    }
}

/// Checks the literal workflow adapter against its typed specification.
///
/// `source` must be the exact text retained by the workflow inventory. Taking
/// source rather than a path makes the job inventory and this behavioral audit
/// inseparable even if an editor replaces the workflow pathname during load.
pub(crate) fn audit_semver_adapter(
    source: &str,
    policy: &Policy,
    repository: &RepositoryInventory,
) -> Result<(), SemverAdapterAuditError> {
    let expected = SemverAdapterSpec::from_checked_inputs(policy, repository)?;
    audit_source(&expected, source)?;
    Ok(())
}

fn audit_source(expected: &SemverAdapterSpec, source: &str) -> Result<(), SemverAdapterViolations> {
    let mut errors = ViolationSink::default();
    if source.contains(LEGACY_SKIP_ENVIRONMENT) {
        errors.push(
            adapter_location("preparation"),
            format!(
                "legacy ambient skip channel `{LEGACY_SKIP_ENVIRONMENT}` must not appear; use the audited `{PREPARE_STEP_ID}` step output"
            ),
        );
    }

    let preparation = ParsedPreparation::parse(source)?;
    let actual = ParsedAdapter::parse(source)?;
    audit_semver_job_contract(source, preparation.marker, actual.marker, &mut errors);
    if preparation.marker >= actual.marker {
        errors.push(
            adapter_location("order"),
            format!("`{PREPARE_STEP_NAME}` must precede `{SEMVER_STEP_NAME}`"),
        );
    }
    compare_map(
        "preparation.env",
        expected.preparation_environment(),
        &preparation.environment,
        &mut errors,
    );
    if expected.preparation_run() != preparation.run {
        errors.push(
            adapter_location("preparation.run"),
            format!(
                "run block must contain the exact reviewed shell lines {:?}, found {:?}",
                expected.preparation_run(),
                preparation.run
            ),
        );
    }
    if !preparation.condition.is_empty() {
        errors.push(
            adapter_location("preparation.if"),
            format!(
                "preparation must run for every selected semver cell, found condition {:?}",
                preparation.condition,
            ),
        );
    }
    compare_value("uses", expected.action(), &actual.action, &mut errors);
    compare_map("env", expected.environment(), &actual.environment, &mut errors);
    compare_map("with", expected.inputs(), &actual.inputs, &mut errors);
    if expected.condition() != actual.condition {
        errors.push(
            adapter_location("if"),
            format!(
                "condition must be the exact typed expression {:?}, found {:?}",
                expected.condition(),
                actual.condition
            ),
        );
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors.finish())
    }
}

/// Audits the complete handwritten host and matrix boundary for semver.
///
/// The planner audit owns the complete workflow-level environment. This exact
/// job header rejects a job environment, runner or permission drift, and any
/// matrix source other than the typed semver projection. The three-step
/// sequence ensures that only pinned checkout runs before the exact preparation
/// and action on this fresh runner.
fn audit_semver_job_contract(
    source: &str,
    preparation_marker: usize,
    adapter_marker: usize,
    errors: &mut ViolationSink,
) {
    let lines = source.lines().collect::<Vec<_>>();
    let Some(job) = canonical_job_range(&lines, SEMVER_JOB, errors) else {
        return;
    };
    let steps = canonical_step_blocks(&lines, job.clone());
    let header_end = steps.first().map_or(job.end, |step| step.start);
    let actual_header = significant_lines(&lines[job.start..header_end])
        .into_iter()
        .map(str::to_owned)
        .collect::<Vec<_>>();
    let expected_header = semver_job_header();
    if actual_header != expected_header {
        errors.push(
            adapter_location("job"),
            format!(
                "`{SEMVER_JOB}` header must be exactly {expected_header:?}, found {actual_header:?}"
            ),
        );
    }

    // YAML mapping order is not semantic. A job-level field written after the
    // final step still applies to the complete job, even though the focused
    // step parsers stop when indentation returns to the job level. Require all
    // such fields to precede the first sequence item, where the exact header
    // comparison above sees them. In particular, this prevents a trailing
    // `continue-on-error` or `env` field from weakening the voting job while
    // remaining outside the audited header.
    if let Some(first_step) = steps.first() {
        for (index, line) in
            lines.iter().enumerate().take(job.end).skip(first_step.start).filter(|(_, line)| {
                !line.trim().is_empty()
                    && !line.trim_start().starts_with('#')
                    && indentation(line) == 4
                    && !line[4..].starts_with("- ")
            })
        {
            errors.push(
                adapter_location("job"),
                format!(
                    "job-level declaration after `steps` at line {} is outside the canonical header: `{}`",
                    index + 1,
                    escape_control_characters(&line[4..]),
                ),
            );
        }
    }

    let actual_markers =
        steps.iter().map(|step| lines[step.start][4..].to_owned()).collect::<Vec<_>>();
    let expected_markers = [
        "- uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1".to_owned(),
        format!("- name: {PREPARE_STEP_NAME}"),
        format!("- name: {SEMVER_STEP_NAME}"),
    ];
    if actual_markers != expected_markers {
        errors.push(
            adapter_location("steps"),
            format!(
                "`{SEMVER_JOB}` steps must be exactly {expected_markers:?} in order, found {actual_markers:?}"
            ),
        );
    }

    let checkout_markers =
        steps.iter().filter(|step| lines[step.start] == CHECKOUT_STEP[0]).collect::<Vec<_>>();
    match checkout_markers.as_slice() {
        [step] => {
            let actual = significant_lines(&lines[step.start..step.end]);
            if actual != CHECKOUT_STEP {
                errors.push(
                    adapter_location("checkout"),
                    "checkout step must match the exact canonical contract",
                );
            }
        }
        _ => errors.push(
            adapter_location("checkout"),
            format!(
                "expected exactly one canonical checkout step, found {}",
                checkout_markers.len()
            ),
        ),
    }

    if steps.len() == 3
        && !(steps[0].start < preparation_marker
            && preparation_marker < adapter_marker
            && adapter_marker == steps[2].start)
    {
        errors.push(
            adapter_location("order"),
            "checkout, preparation, and action must be the job's exact step order",
        );
    }

    // GITHUB_ENV and GITHUB_PATH are write-only file-command channels whose
    // effects GitHub injects into later steps. The exact, two-step prefix above
    // prevents new producers before semver, and this independent token check
    // makes the intended absence explicit. GITHUB_OUTPUT remains the reviewed
    // preparation's step-local skip channel; GITHUB_STEP_SUMMARY does not
    // mutate a later process environment and remains available for diagnostics.
    for (index, line) in lines
        .iter()
        .enumerate()
        .take(adapter_marker)
        .skip(job.start)
        .filter(|(_, line)| !line.trim_start().starts_with('#'))
    {
        for channel in ["GITHUB_ENV", "GITHUB_PATH"] {
            if token_mentions(line, channel) != 0 {
                errors.push(
                    adapter_line_location(index + 1),
                    format!(
                        "`{channel}` must not be referenced before the semver action; cross-step environment producers are outside the audited adapter"
                    ),
                );
            }
        }
    }
}

fn semver_job_header() -> Vec<String> {
    vec![
        format!("  {SEMVER_JOB}:"),
        format!("    if: needs.{PLAN_JOB}.outputs.{SEMVER_ENABLED_OUTPUT} == 'true'"),
        "    runs-on: ubuntu-latest".to_owned(),
        format!("    needs: [{PLAN_JOB}]"),
        "    permissions:".to_owned(),
        "      contents: read".to_owned(),
        "    strategy:".to_owned(),
        "      fail-fast: false".to_owned(),
        format!(
            "      matrix: ${{{{ fromJSON(needs.{PLAN_JOB}.outputs.{SEMVER_MATRIX_OUTPUT}) }}}}"
        ),
        "    name: Semver (${{ matrix.target }})".to_owned(),
        "    steps:".to_owned(),
    ]
}

fn slash_path(path: &Path) -> Result<String, String> {
    let Some(path) = path.to_str() else {
        return Err(format!("manifest path `{path:?}` is not UTF-8"));
    };
    Ok(path.replace('\\', "/"))
}

fn validate_plain_string_scalar(location: &str, value: &str, errors: &mut ViolationSink) {
    let mut characters = value.chars();
    let safe_start = characters
        .next()
        .is_some_and(|character| character.is_ascii_alphabetic() || character == '_');
    let safe_tail = characters.all(|character| {
        character.is_ascii_alphanumeric() || matches!(character, '_' | '-' | '.' | '/' | '+')
    });
    let reserved = matches!(
        value.to_ascii_lowercase().as_str(),
        "null" | "true" | "false" | "y" | "n" | "yes" | "no" | "on" | "off"
    );
    if !safe_start || !safe_tail || reserved {
        errors.push(
            location,
            format!(
                "value `{}` is not safe as a canonical unquoted YAML scalar",
                escape_control_characters(value)
            ),
        );
    }
}

fn validate_exact_rust_version_scalar(location: &str, value: &str, errors: &mut ViolationSink) {
    // Repository inventory has already required an exact Rust version. Repeat
    // the narrow lexical property needed at this adapter boundary: three
    // nonempty decimal components cannot be a YAML integer, float, boolean,
    // null, or date. Anything broader must first gain canonical YAML quoting.
    let components = value.split('.').collect::<Vec<_>>();
    if components.len() != 3
        || components.iter().any(|component| {
            component.is_empty() || !component.bytes().all(|byte| byte.is_ascii_digit())
        })
    {
        errors.push(
            location,
            format!(
                "value `{}` is not safe as an unquoted exact Rust version",
                escape_control_characters(value)
            ),
        );
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedPreparation {
    marker: usize,
    environment: BTreeMap<String, String>,
    run: Vec<String>,
    condition: Vec<String>,
}

impl ParsedPreparation {
    fn parse(source: &str) -> Result<Self, SemverAdapterViolations> {
        let mut errors = ViolationSink::default();
        if source.contains('\r') {
            errors.push(adapter_location("source"), "workflow must use canonical LF line endings");
        }

        let lines = source.lines().collect::<Vec<_>>();
        let semver_job = canonical_job_range(&lines, SEMVER_JOB, &mut errors);
        let markers = lines
            .iter()
            .enumerate()
            .filter_map(|(index, line)| (*line == PREPARE_STEP_MARKER).then_some(index))
            .collect::<Vec<_>>();
        if markers.len() != 1 {
            errors.push(
                preparation_location("name"),
                format!(
                    "expected exactly one canonical `{PREPARE_STEP_MARKER}` declaration, found {}",
                    markers.len()
                ),
            );
            return Err(errors.finish());
        }

        let marker = markers[0];
        let Some(semver_job) = semver_job else {
            return Err(errors.finish());
        };
        if !semver_job.contains(&marker) {
            errors.push(
                preparation_location("name"),
                format!("canonical preparation step must be inside the `{SEMVER_JOB}` job"),
            );
            return Err(errors.finish());
        }

        let start = marker + 1;
        let end = canonical_step_end(&lines, start, semver_job.end);
        let mut section = PreparationSection::Root;
        let mut root_fields = Vec::new();
        let mut id = None;
        let mut shell = None;
        let mut working_directory = None;
        let mut environment = BTreeMap::new();
        let mut run = Vec::new();
        let mut condition = Vec::new();

        for (index, line) in lines.iter().enumerate().take(end).skip(start) {
            let line_number = index + 1;
            if section == PreparationSection::Condition {
                if indentation(line) != 8 || line.trim().is_empty() {
                    errors.push(
                        adapter_line_location(line_number),
                        "condition content must be one nonempty line at exactly eight spaces",
                    );
                } else {
                    // An indented `#` is scalar content under `if: |`, not a
                    // YAML comment. Preserve it so it cannot disappear from
                    // the expression compared below.
                    condition.push(line[8..].to_owned());
                }
                continue;
            }
            if line.trim().is_empty() {
                if section == PreparationSection::Run
                    && run.last().is_some_and(|line: &String| line.ends_with('\\'))
                {
                    errors.push(
                        adapter_line_location(line_number),
                        "blank line must not interrupt a continued shell command",
                    );
                }
                continue;
            }
            // Outside a block scalar this is a YAML comment. Beneath `run: |`
            // it is shell-script content, and Actions expands `${{ ... }}`
            // before invoking Bash. Preserve the latter in the exact run
            // comparison so an apparently commented expression cannot inject
            // commands. A scalar comment after `\` is likewise compared and
            // rejected rather than being silently discarded.
            if line.trim_start().starts_with('#') && section != PreparationSection::Run {
                continue;
            }
            if line.trim_start().starts_with('#')
                && run.last().is_some_and(|line: &String| line.ends_with('\\'))
            {
                errors.push(
                    adapter_line_location(line_number),
                    "comment line must not interrupt a continued shell command",
                );
            }
            if line.trim_end() != *line {
                errors.push(
                    adapter_line_location(line_number),
                    "semantic preparation lines must not have trailing whitespace",
                );
                continue;
            }

            let indent = indentation(line);
            if indent == 6 {
                let declaration = &line[6..];
                match declaration {
                    "env:" => {
                        root_fields.push("env");
                        section = PreparationSection::Environment;
                    }
                    "run: |" => {
                        root_fields.push("run");
                        section = PreparationSection::Run;
                    }
                    "if: |" => {
                        root_fields.push("if");
                        section = PreparationSection::Condition;
                    }
                    _ if declaration.starts_with("id: ") => {
                        root_fields.push("id");
                        section = PreparationSection::Root;
                        if id.replace(declaration["id: ".len()..].to_owned()).is_some() {
                            errors.push(
                                adapter_line_location(line_number),
                                "preparation repeats its `id` field",
                            );
                        }
                    }
                    _ if declaration.starts_with("shell: ") => {
                        root_fields.push("shell");
                        section = PreparationSection::Root;
                        if shell.replace(declaration["shell: ".len()..].to_owned()).is_some() {
                            errors.push(
                                adapter_line_location(line_number),
                                "preparation repeats its `shell` field",
                            );
                        }
                    }
                    _ if declaration.starts_with("working-directory: ") => {
                        root_fields.push("working-directory");
                        section = PreparationSection::Root;
                        if working_directory
                            .replace(declaration["working-directory: ".len()..].to_owned())
                            .is_some()
                        {
                            errors.push(
                                adapter_line_location(line_number),
                                "preparation repeats its `working-directory` field",
                            );
                        }
                    }
                    _ => errors.push(
                        adapter_line_location(line_number),
                        format!(
                            "unsupported preparation root field `{}`; expected only id, shell, working-directory, env, run, and if",
                            escape_control_characters(declaration)
                        ),
                    ),
                }
                continue;
            }

            match section {
                PreparationSection::Environment if indent == 8 => insert_mapping(
                    "preparation.env",
                    &line[8..],
                    line_number,
                    &mut environment,
                    &mut errors,
                ),
                PreparationSection::Run if indent >= 8 => run.push(line[8..].to_owned()),
                PreparationSection::Root
                | PreparationSection::Environment
                | PreparationSection::Run
                | PreparationSection::Condition => errors.push(
                    adapter_line_location(line_number),
                    format!(
                        "unsupported preparation indentation in `{}`",
                        escape_control_characters(line)
                    ),
                ),
            }
        }

        if root_fields != PREPARE_ROOT_FIELD_ORDER {
            errors.push(
                preparation_location("shape"),
                format!(
                    "root fields must appear exactly as {PREPARE_ROOT_FIELD_ORDER:?}, found {root_fields:?}"
                ),
            );
        }
        match id {
            Some(actual) => compare_value("preparation.id", PREPARE_STEP_ID, &actual, &mut errors),
            None => errors.push(preparation_location("id"), "preparation has no `id` value"),
        }
        match shell {
            Some(actual) => {
                compare_value("preparation.shell", TRUSTED_SHELL, &actual, &mut errors);
            }
            None => errors.push(preparation_location("shell"), "preparation has no `shell` value"),
        }
        match working_directory {
            Some(actual) => compare_value(
                "preparation.working-directory",
                REPOSITORY_WORKING_DIRECTORY,
                &actual,
                &mut errors,
            ),
            None => errors.push(
                preparation_location("working-directory"),
                "preparation has no `working-directory` value",
            ),
        }

        let id_mentions = source.matches(&format!("id: {PREPARE_STEP_ID}")).count();
        if id_mentions != 1 {
            errors.push(
                preparation_location("id"),
                format!(
                    "expected exactly one `id: {PREPARE_STEP_ID}` occurrence in the workflow, found {id_mentions}"
                ),
            );
        }
        let output_mentions = source.matches(PREPARE_OUTPUT_CONDITION).count();
        if output_mentions != 1 {
            errors.push(
                adapter_location("if"),
                format!(
                    "expected exactly one `{PREPARE_OUTPUT_CONDITION}` occurrence in the workflow, found {output_mentions}"
                ),
            );
        }
        let id_token_mentions = lines
            .iter()
            .filter(|line| !line.trim_start().starts_with('#'))
            .map(|line| line.matches(PREPARE_STEP_ID).count())
            .sum::<usize>();
        if id_token_mentions != 2 {
            errors.push(
                preparation_location("id"),
                format!(
                    "expected `{PREPARE_STEP_ID}` only in its ID and audited consumer, found {id_token_mentions} occurrences"
                ),
            );
        }

        if errors.is_empty() {
            Ok(Self { marker, environment, run, condition })
        } else {
            Err(errors.finish())
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PreparationSection {
    Root,
    Environment,
    Run,
    Condition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedAdapter {
    marker: usize,
    action: String,
    environment: BTreeMap<String, String>,
    inputs: BTreeMap<String, String>,
    condition: Vec<String>,
}

impl ParsedAdapter {
    fn parse(source: &str) -> Result<Self, SemverAdapterViolations> {
        let mut errors = ViolationSink::default();
        if source.contains('\r') {
            errors.push(adapter_location("source"), "workflow must use canonical LF line endings");
        }

        let lines = source.lines().collect::<Vec<_>>();
        let semver_job = canonical_job_range(&lines, SEMVER_JOB, &mut errors);
        let action_mentions = source.match_indices(SEMVER_ACTION_MARKER).count();
        if action_mentions != 1 {
            errors.push(
                adapter_location("uses"),
                format!(
                    "expected exactly one `{SEMVER_ACTION_MARKER}` occurrence in the workflow, found {action_mentions}"
                ),
            );
        }
        let semver_step_marker = format!("    - name: {SEMVER_STEP_NAME}");
        let markers = lines
            .iter()
            .enumerate()
            .filter_map(|(index, line)| (*line == semver_step_marker).then_some(index))
            .collect::<Vec<_>>();
        if markers.len() != 1 {
            errors.push(
                adapter_location("name"),
                format!(
                    "expected exactly one canonical `{semver_step_marker}` declaration, found {}",
                    markers.len()
                ),
            );
            return Err(errors.finish());
        }

        let marker = markers[0];
        let Some(semver_job) = semver_job else {
            return Err(errors.finish());
        };
        if !semver_job.contains(&marker) {
            errors.push(
                adapter_location("name"),
                format!("canonical semver step must be inside the `{SEMVER_JOB}` job"),
            );
            return Err(errors.finish());
        }

        let start = marker + 1;
        let end = canonical_step_end(&lines, start, semver_job.end);

        let mut section = Section::Root;
        let mut root_fields = Vec::new();
        let mut action = None;
        let mut environment = BTreeMap::new();
        let mut inputs = BTreeMap::new();
        let mut condition = Vec::new();

        for (index, line) in lines.iter().enumerate().take(end).skip(start) {
            let line_number = index + 1;
            if section == Section::Condition {
                if indentation(line) != 8 || line.trim().is_empty() {
                    errors.push(
                        adapter_line_location(line_number),
                        "condition content must be one nonempty line at exactly eight spaces",
                    );
                } else {
                    condition.push(line[8..].to_owned());
                }
                continue;
            }
            if line.trim().is_empty() || line.trim_start().starts_with('#') {
                continue;
            }
            if line.trim_end() != *line {
                errors.push(
                    adapter_line_location(line_number),
                    "semantic adapter lines must not have trailing whitespace",
                );
                continue;
            }

            match indentation(line) {
                6 => {
                    let declaration = &line[6..];
                    match declaration {
                        "env:" => {
                            root_fields.push("env");
                            section = Section::Environment;
                        }
                        "with:" => {
                            root_fields.push("with");
                            section = Section::Inputs;
                        }
                        "if: |" => {
                            root_fields.push("if");
                            section = Section::Condition;
                        }
                        _ if declaration.starts_with("uses: ") => {
                            root_fields.push("uses");
                            section = Section::Root;
                            let value = &declaration["uses: ".len()..];
                            let value = match value.split_once(" # ") {
                                Some((value, comment)) if !comment.is_empty() => value,
                                Some((_value, _comment)) => {
                                    errors.push(
                                        adapter_line_location(line_number),
                                        "inline action comment must not be empty",
                                    );
                                    continue;
                                }
                                None => value,
                            };
                            if action.replace(value.to_owned()).is_some() {
                                errors.push(
                                    adapter_line_location(line_number),
                                    "adapter repeats its `uses` field",
                                );
                            }
                        }
                        _ => errors.push(
                            adapter_line_location(line_number),
                            format!(
                                "unsupported root field `{}`; expected only uses, env, with, and if",
                                escape_control_characters(declaration)
                            ),
                        ),
                    }
                }
                8 => match section {
                    Section::Environment => insert_mapping(
                        "env",
                        &line[8..],
                        line_number,
                        &mut environment,
                        &mut errors,
                    ),
                    Section::Inputs => {
                        insert_mapping("with", &line[8..], line_number, &mut inputs, &mut errors)
                    }
                    Section::Root | Section::Condition => errors.push(
                        adapter_line_location(line_number),
                        "mapping entry appears outside `env` or `with`",
                    ),
                },
                _ => errors.push(
                    adapter_line_location(line_number),
                    format!("unsupported indentation in `{}`", escape_control_characters(line)),
                ),
            }
        }

        if root_fields != ROOT_FIELD_ORDER {
            errors.push(
                adapter_location("shape"),
                format!(
                    "root fields must appear exactly as {ROOT_FIELD_ORDER:?}, found {root_fields:?}"
                ),
            );
        }
        let Some(action) = action else {
            errors.push(adapter_location("uses"), "adapter has no `uses` value");
            return Err(errors.finish());
        };
        if errors.is_empty() {
            Ok(Self { marker, action, environment, inputs, condition })
        } else {
            Err(errors.finish())
        }
    }
}

/// Finds one canonical top-level job without accepting general YAML syntax.
///
/// This deliberately duplicates the small job-range grammar in
/// `planned_adapter/source.rs`: an exact two-space job declaration ends at the
/// next semantic two-space declaration. Keep the two implementations
/// coordinated. Sharing the planned adapter's private error-sink-aware helper
/// would couple otherwise independent focused audits more tightly than this
/// grammar warrants.
fn canonical_job_range(
    lines: &[&str],
    job: &str,
    errors: &mut ViolationSink,
) -> Option<Range<usize>> {
    let marker = format!("  {job}:");
    let starts = lines
        .iter()
        .enumerate()
        .filter_map(|(index, line)| (*line == marker).then_some(index))
        .collect::<Vec<_>>();
    if starts.len() != 1 {
        errors.push(
            format!("{WORKFLOW_PATH}:{job}"),
            format!("expected exactly one canonical job declaration, found {}", starts.len()),
        );
        return None;
    }
    let start = starts[0];
    let end = lines
        .iter()
        .enumerate()
        .skip(start + 1)
        .find_map(|(index, line)| {
            (!line.trim().is_empty()
                && !line.trim_start().starts_with('#')
                && indentation(line) == 2)
                .then_some(index)
        })
        .unwrap_or(lines.len());
    Some(start..end)
}

fn canonical_step_end(lines: &[&str], start: usize, job_end: usize) -> usize {
    let mut end = job_end;
    for (index, line) in lines.iter().enumerate().take(job_end).skip(start) {
        if !line.trim().is_empty() && !line.trim_start().starts_with('#') && indentation(line) <= 4
        {
            end = index;
            break;
        }
    }
    // Blank lines and sibling-level comments between this step and the next
    // sequence item are not part of the adapter. Strip only a trailing run: a
    // blank or comment followed by another semantic field remains inside the
    // block and is rejected, so whitespace cannot hide an unsupported field.
    while end > start {
        let line = lines[end - 1];
        if line.trim().is_empty() || (line.trim_start().starts_with('#') && indentation(line) <= 6)
        {
            end -= 1;
        } else {
            break;
        }
    }
    end
}

/// Returns the canonical top-level sequence items in one job's `steps` block.
///
/// The focused parsers require four-space sequence markers. Treating every
/// such marker as a step makes an unfamiliar anchor, alias, or named step
/// visible to the exact sequence comparison instead of silently skipping it.
fn canonical_step_blocks(lines: &[&str], job: Range<usize>) -> Vec<Range<usize>> {
    let starts = lines
        .iter()
        .enumerate()
        .take(job.end)
        .skip(job.start + 1)
        .filter_map(|(index, line)| {
            (!line.trim().is_empty()
                && !line.trim_start().starts_with('#')
                && indentation(line) == 4
                && line[4..].starts_with("- "))
            .then_some(index)
        })
        .collect::<Vec<_>>();
    starts
        .iter()
        .enumerate()
        .map(|(position, start)| {
            let end = starts.get(position + 1).copied().unwrap_or(job.end);
            *start..end
        })
        .collect()
}

fn significant_lines<'a>(lines: &'a [&'a str]) -> Vec<&'a str> {
    lines
        .iter()
        .filter(|line| !line.trim().is_empty() && !line.trim_start().starts_with('#'))
        .copied()
        .collect()
}

fn token_mentions(text: &str, token: &str) -> usize {
    text.match_indices(token)
        .filter(|(start, _)| {
            let end = start + token.len();
            let before = text[..*start].bytes().next_back();
            let after = text[end..].bytes().next();
            !before.is_some_and(is_identifier_byte) && !after.is_some_and(is_identifier_byte)
        })
        .count()
}

fn is_identifier_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Section {
    Root,
    Environment,
    Inputs,
    Condition,
}

fn insert_mapping(
    section: &str,
    declaration: &str,
    line: usize,
    values: &mut BTreeMap<String, String>,
    errors: &mut ViolationSink,
) {
    let Some((key, value)) = declaration.split_once(": ") else {
        errors.push(
            adapter_line_location(line),
            format!("`{section}` entries must have canonical `key: value` form"),
        );
        return;
    };
    if key.is_empty()
        || value.is_empty()
        || key.chars().any(char::is_control)
        || value.chars().any(char::is_control)
    {
        errors.push(
            adapter_line_location(line),
            format!("`{section}` entry contains an empty value or control character"),
        );
        return;
    }
    if values.insert(key.to_owned(), value.to_owned()).is_some() {
        errors.push(
            adapter_line_location(line),
            format!("`{section}` repeats key `{}`", escape_control_characters(key)),
        );
    }
}

fn compare_value(location: &str, expected: &str, actual: &str, errors: &mut ViolationSink) {
    if expected != actual {
        errors.push(
            adapter_location(location),
            format!(
                "expected `{}`, found `{}`",
                escape_control_characters(expected),
                escape_control_characters(actual)
            ),
        );
    }
}

fn compare_map(
    section: &str,
    expected: &BTreeMap<String, String>,
    actual: &BTreeMap<String, String>,
    errors: &mut ViolationSink,
) {
    for (key, value) in expected {
        match actual.get(key) {
            Some(actual) => compare_value(&format!("{section}.{key}"), value, actual, errors),
            None => errors
                .push(adapter_location(&format!("{section}.{key}")), "required field is absent"),
        }
    }
    for key in actual.keys() {
        if !expected.contains_key(key) {
            errors.push(
                adapter_location(&format!("{section}.{key}")),
                "field is not part of the typed semver adapter",
            );
        }
    }
}

fn indentation(line: &str) -> usize {
    line.bytes().take_while(|byte| *byte == b' ').count()
}

fn adapter_location(field: &str) -> String {
    format!("{WORKFLOW_PATH}:{SEMVER_STEP_NAME}.{field}")
}

fn preparation_location(field: &str) -> String {
    format!("{WORKFLOW_PATH}:{PREPARE_STEP_NAME}.{field}")
}

fn adapter_line_location(line: usize) -> String {
    format!("{WORKFLOW_PATH}:{line}")
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

/// A failure reading or validating the live semver adapter.
#[derive(Debug, Error)]
pub enum SemverAdapterAuditError {
    /// Typed policy or live adapter semantics were invalid.
    #[error(transparent)]
    Invalid(#[from] SemverAdapterViolations),
}

/// Deterministically ordered semver-adapter violations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemverAdapterViolations(Vec<SemverAdapterViolation>);

impl SemverAdapterViolations {
    /// Returns every violation in location and message order.
    pub fn violations(&self) -> &[SemverAdapterViolation] {
        &self.0
    }
}

impl fmt::Display for SemverAdapterViolations {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(formatter, "semver GitHub adapter has {} violation(s):", self.0.len())?;
        for error in &self.0 {
            writeln!(formatter, "- {}: {}", error.location, error.message)?;
        }
        Ok(())
    }
}

impl Error for SemverAdapterViolations {}

/// One actionable mismatch in typed policy or live workflow source.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SemverAdapterViolation {
    location: String,
    message: String,
}

impl SemverAdapterViolation {
    /// Returns the policy field or workflow location which must be repaired.
    pub fn location(&self) -> &str {
        &self.location
    }

    /// Returns a plain-language repair diagnostic.
    pub fn message(&self) -> &str {
        &self.message
    }
}

#[derive(Default)]
struct ViolationSink(BTreeSet<SemverAdapterViolation>);

impl ViolationSink {
    fn push(&mut self, location: impl Into<String>, message: impl Into<String>) {
        self.0.insert(SemverAdapterViolation {
            location: escape_control_characters(&location.into()),
            message: escape_control_characters(&message.into()),
        });
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn finish(self) -> SemverAdapterViolations {
        SemverAdapterViolations(self.0.into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use std::{path::Path, sync::OnceLock};

    use super::{
        audit_semver_adapter, audit_source, validate_exact_rust_version_scalar,
        validate_plain_string_scalar, SemverAdapterSpec, ViolationSink, PREPARE_OUTPUT_CONDITION,
        PREPARE_STEP_ID, SEMVER_ACTION, SEMVER_CACHE_PREFIX_INPUT, SEMVER_FEATURE_GROUP,
        SEMVER_MATRIX_TARGET_EXPRESSION, SEMVER_STEP_NAME, SEMVER_TARGET_INPUT,
        SEMVER_WARNING_FLAGS, TRUSTED_SHELL, WORKFLOW_PATH,
    };
    use crate::{inventory::RepositoryInventory, policy::Policy};

    fn checked_inputs() -> &'static (Policy, RepositoryInventory) {
        static INPUTS: OnceLock<(Policy, RepositoryInventory)> = OnceLock::new();
        INPUTS.get_or_init(|| {
            let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
            let policy = Policy::read(root.join("ci/zc.toml")).unwrap();
            let repository = RepositoryInventory::audit(&root, &policy).unwrap();
            (policy, repository)
        })
    }

    fn spec() -> SemverAdapterSpec {
        let (policy, repository) = checked_inputs();
        SemverAdapterSpec::from_checked_inputs(policy, repository).unwrap()
    }

    fn canonical_adapter() -> String {
        let spec = spec();
        let toolchain_version = spec.inputs()["rust-toolchain"].clone();
        let preparation_run = spec.preparation_run().join("\n        ");
        format!(
            r#"jobs:
  semver:
    if: needs.plan_ci.outputs.semver_enabled == 'true'
    runs-on: ubuntu-latest
    needs: [plan_ci]
    permissions:
      contents: read
    strategy:
      fail-fast: false
      matrix: ${{{{ fromJSON(needs.plan_ci.outputs.semver_matrix) }}}}
    name: Semver (${{{{ matrix.target }}}})
    steps:
    - uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1
      with:
        fetch-depth: 2
        persist-credentials: false
    - name: Prepare cargo-semver-checks
      id: {PREPARE_STEP_ID}
      shell: {TRUSTED_SHELL}
      working-directory: zerocopy
      env:
        PR_HEAD_SHA: ${{{{ github.event.pull_request.head.sha }}}}
      run: |
        {preparation_run}
    - name: {SEMVER_STEP_NAME}
      uses: {SEMVER_ACTION} # v2.9
      env:
        # Unstable API is not semver checked.
        RUSTDOCFLAGS: {SEMVER_WARNING_FLAGS}
        RUSTFLAGS: {SEMVER_WARNING_FLAGS}
      with:
        package: zerocopy
        feature-group: {SEMVER_FEATURE_GROUP}
        features: __internal_use_only_features_that_work_on_stable
        manifest-path: zerocopy/Cargo.toml
        prefix-key: ${{{{ matrix.target }}}}
        rust-toolchain: {toolchain_version}
        rust-target: ${{{{ matrix.target }}}}
      if: |
        {PREPARE_OUTPUT_CONDITION}
  next_job:
    runs-on: ubuntu-latest
"#
        )
    }

    #[test]
    fn derives_every_current_adapter_value_from_checked_inputs() {
        let spec = spec();
        assert_eq!(spec.action(), SEMVER_ACTION);
        assert_eq!(
            spec.environment(),
            &[
                ("RUSTDOCFLAGS".to_owned(), "-Dwarnings".to_owned()),
                ("RUSTFLAGS".to_owned(), "-Dwarnings".to_owned()),
            ]
            .into_iter()
            .collect()
        );
        assert_eq!(spec.inputs()["package"], "zerocopy");
        assert_eq!(spec.inputs()["manifest-path"], "zerocopy/Cargo.toml");
        assert_eq!(spec.inputs()["features"], "__internal_use_only_features_that_work_on_stable");
        assert_eq!(spec.inputs()[SEMVER_CACHE_PREFIX_INPUT], SEMVER_MATRIX_TARGET_EXPRESSION);
        assert_eq!(spec.inputs()[SEMVER_TARGET_INPUT], SEMVER_MATRIX_TARGET_EXPRESSION);
        let (policy, repository) = checked_inputs();
        assert_eq!(
            spec.inputs()["rust-toolchain"],
            repository.toolchain_versions()[policy.semver().toolchain().as_str()]
        );
        assert_eq!(spec.inputs()["rust-toolchain"], "1.93.1");
        assert_eq!(
            spec.preparation_environment(),
            &[("PR_HEAD_SHA".to_owned(), "${{ github.event.pull_request.head.sha }}".to_owned(),)]
                .into_iter()
                .collect()
        );
        assert_eq!(spec.condition(), [PREPARE_OUTPUT_CONDITION]);
    }

    #[test]
    fn accepts_the_canonical_adapter_and_the_live_workflow() {
        let spec = spec();
        audit_source(&spec, &canonical_adapter()).unwrap();

        let (policy, repository) = checked_inputs();
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap();
        let source = crate::repository_text::read(&root.join(WORKFLOW_PATH)).unwrap();
        audit_semver_adapter(&source, policy, repository).unwrap();
    }

    #[test]
    fn job_and_checkout_contracts_are_exact() {
        let original = canonical_adapter();
        let cases = [
            (
                "enable gate",
                original
                    .replace("if: needs.plan_ci.outputs.semver_enabled == 'true'", "if: success()"),
                ".job",
            ),
            ("runner", original.replace("runs-on: ubuntu-latest", "runs-on: self-hosted"), ".job"),
            (
                "dependency",
                original.replace("needs: [plan_ci]", "needs: [build_test, plan_ci]"),
                ".job",
            ),
            ("permission", original.replace("contents: read", "contents: write"), ".job"),
            (
                "matrix source",
                original.replace(
                    "needs.plan_ci.outputs.semver_matrix",
                    "needs.plan_ci.outputs.build_matrix",
                ),
                ".job",
            ),
            (
                "job environment",
                original.replace(
                    "    strategy:\n",
                    "    env:\n      RUSTC_WRAPPER: /tmp/wrapper\n    strategy:\n",
                ),
                ".job",
            ),
            (
                "trailing continue on error",
                original.replace("  next_job:\n", "    continue-on-error: true\n  next_job:\n"),
                ".job",
            ),
            (
                "trailing job environment",
                original.replace(
                    "  next_job:\n",
                    "    env:\n      NODE_OPTIONS: --require=/tmp/interceptor.js\n  next_job:\n",
                ),
                ".job",
            ),
            (
                "trailing duplicate steps",
                original.replace("  next_job:\n", "    steps: []\n  next_job:\n"),
                ".job",
            ),
            (
                "checkout identity",
                original.replacen(
                    "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
                    "actions/checkout@0000000000000000000000000000000000000000",
                    1,
                ),
                ".checkout",
            ),
            (
                "checkout depth",
                original.replacen("fetch-depth: 2", "fetch-depth: 1", 1),
                ".checkout",
            ),
            (
                "checkout credentials",
                original.replacen("persist-credentials: false", "persist-credentials: true", 1),
                ".checkout",
            ),
            (
                "checkout ref override",
                original.replacen(
                    "        fetch-depth: 2\n",
                    "        fetch-depth: 2\n        ref: main\n",
                    1,
                ),
                ".checkout",
            ),
        ];

        for (case, source, expected) in cases {
            let error = audit_source(&spec(), &source).unwrap_err();
            assert!(error.to_string().contains(expected), "{case}: {error}");
        }
    }

    #[test]
    fn no_repository_code_can_run_before_the_semver_action() {
        let original = canonical_adapter();
        let preparation = "    - name: Prepare cargo-semver-checks\n";
        let cases = [
            (
                "added producer step",
                original.replacen(
                    preparation,
                    &format!(
                        "    - name: Unreviewed setup\n      run: echo setup\n{preparation}"
                    ),
                    1,
                ),
                ".steps",
            ),
            (
                "GITHUB_ENV producer",
                original.replacen(
                    "        set -euo pipefail\n",
                    "        set -euo pipefail\n        printf 'RUSTC_WRAPPER=other\\n' >> \"$GITHUB_ENV\"\n",
                    1,
                ),
                "GITHUB_ENV",
            ),
            (
                "GITHUB_PATH producer",
                original.replacen(
                    "        set -euo pipefail\n",
                    "        set -euo pipefail\n        printf '/tmp/bin\\n' >> \"$GITHUB_PATH\"\n",
                    1,
                ),
                "GITHUB_PATH",
            ),
            (
                "Actions expression in shell comment",
                original.replacen(
                    "        # Pull request jobs check the head commit rather than GitHub's synthetic\n",
                    "        # ${{ github.event.pull_request.title }}\n",
                    1,
                ),
                ".preparation.run",
            ),
        ];

        for (case, source, expected) in cases {
            let error = audit_source(&spec(), &source).unwrap_err();
            assert!(error.to_string().contains(expected), "{case}: {error}");
        }
    }

    #[test]
    fn rejects_every_behavior_bearing_mutation() {
        let original = canonical_adapter();
        let pinned_toolchain = spec().inputs()["rust-toolchain"].clone();
        let cases = [
            (
                "action identity",
                original.replace(
                    SEMVER_ACTION,
                    "obi1kenobi/cargo-semver-checks-action@0000000000000000000000000000000000000000",
                ),
                ".uses",
            ),
            (
                "rustdoc warning environment",
                original.replacen("RUSTDOCFLAGS: -Dwarnings", "RUSTDOCFLAGS: -Awarnings", 1),
                ".env.RUSTDOCFLAGS",
            ),
            (
                "rust warning environment",
                original.replacen("RUSTFLAGS: -Dwarnings", "RUSTFLAGS: -Awarnings", 1),
                ".env.RUSTFLAGS",
            ),
            (
                "package input",
                original.replace("package: zerocopy", "package: zerocopy-derive"),
                ".with.package",
            ),
            (
                "feature group",
                original.replace(
                    "feature-group: only-explicit-features",
                    "feature-group: all-features",
                ),
                ".with.feature-group",
            ),
            (
                "feature root",
                original.replace(
                    "features: __internal_use_only_features_that_work_on_stable",
                    "features: derive",
                ),
                ".with.features",
            ),
            (
                "manifest",
                original.replace("manifest-path: zerocopy/Cargo.toml", "manifest-path: Cargo.toml"),
                ".with.manifest-path",
            ),
            (
                "cache prefix expression",
                original.replace(
                    "prefix-key: ${{ matrix.target }}",
                    "prefix-key: one-cache-for-every-target",
                ),
                ".with.prefix-key",
            ),
            (
                "target expression",
                original.replace(
                    "rust-target: ${{ matrix.target }}",
                    "rust-target: x86_64-unknown-linux-gnu",
                ),
                ".with.rust-target",
            ),
            (
                "toolchain literal",
                original.replace(
                    &format!("rust-toolchain: {pinned_toolchain}"),
                    "rust-toolchain: ${{ env.ZC_TOOLCHAIN }}",
                ),
                ".with.rust-toolchain",
            ),
            (
                "skip condition",
                original.replace(
                    PREPARE_OUTPUT_CONDITION,
                    "steps.prepare_semver.outputs.run != 'true'",
                ),
                ".if",
            ),
        ];

        for (case, source, expected) in cases {
            let error = audit_source(&spec(), &source).unwrap_err();
            assert!(error.to_string().contains(expected), "{case}: {error}");
        }
    }

    #[test]
    fn rejects_every_skip_producer_escape() {
        let original = canonical_adapter();
        let preparation = original.find("    - name: Prepare cargo-semver-checks\n").unwrap();
        let action = original.find("    - name: Check semver compatibility\n").unwrap();
        let next_job = original.find("  next_job:\n").unwrap();
        let reordered = format!(
            "{}{}{}{}",
            &original[..preparation],
            &original[action..next_job],
            &original[preparation..action],
            &original[next_job..]
        );
        let cases = [
            (
                "unconditional decision",
                original.replacen(
                    "        if /usr/bin/grep -Eq \\\n",
                    "        if true; then\n",
                    1,
                ),
                ".preparation.run",
            ),
            (
                "generated shell wrapper",
                original.replacen(
                    &format!("shell: {TRUSTED_SHELL}"),
                    "shell: /tmp/docker-shell.sh {0}",
                    1,
                ),
                ".preparation.shell",
            ),
            (
                "wrong preparation directory",
                original.replacen("working-directory: zerocopy", "working-directory: .", 1),
                ".preparation.working-directory",
            ),
            (
                "changed producer output",
                original.replacen("printf 'run=false\\n'", "printf 'run=true\\n'", 1),
                ".preparation.run",
            ),
            (
                "comment interrupts continued command",
                original.replacen(
                    "        if /usr/bin/grep -Eq \\\n",
                    "        if /usr/bin/grep -Eq \\\n        # This changes shell continuation.\n",
                    1,
                ),
                "continued shell command",
            ),
            (
                "legacy workflow environment",
                original.replacen("jobs:\n", "env:\n  ZC_SKIP_CARGO_SEMVER_CHECKS: 1\njobs:\n", 1),
                "legacy ambient skip channel",
            ),
            (
                "duplicate preparation ID",
                original.replacen(
                    "    - name: Check semver compatibility\n",
                    "      id: prepare_semver\n    - name: Check semver compatibility\n",
                    1,
                ),
                "prepare_semver",
            ),
            ("reordered steps", reordered, ".order"),
        ];

        for (case, source, expected) in cases {
            let error = audit_source(&spec(), &source).unwrap_err();
            assert!(error.to_string().contains(expected), "{case}: {error}");
        }
    }

    #[test]
    fn treats_indented_condition_comments_as_scalar_content() {
        let original = canonical_adapter();
        let cases = [
            (
                "leading action comment",
                original.replacen(
                    &format!("      if: |\n        {PREPARE_OUTPUT_CONDITION}"),
                    &format!(
                        "      if: |\n        # changed expression\n        {PREPARE_OUTPUT_CONDITION}"
                    ),
                    1,
                ),
                ".if",
            ),
            (
                "trailing action comment",
                original.replacen(
                    &format!("        {PREPARE_OUTPUT_CONDITION}\n  next_job:"),
                    &format!(
                        "        {PREPARE_OUTPUT_CONDITION}\n        # changed expression\n  next_job:"
                    ),
                    1,
                ),
                ".if",
            ),
        ];

        for (case, source, expected) in cases {
            let error = audit_source(&spec(), &source).unwrap_err();
            assert!(error.to_string().contains(expected), "{case}: {error}");
        }
    }

    #[test]
    fn accepts_only_yaml_plain_safe_generated_scalars() {
        for value in ["zerocopy", "stable", "zerocopy/Cargo.toml", "_feature"] {
            let mut errors = ViolationSink::default();
            validate_plain_string_scalar("test", value, &mut errors);
            assert!(errors.is_empty(), "{value:?} should be safe");
        }
        for value in [
            "path with space",
            "path#comment",
            "true",
            "y",
            "n",
            "123",
            "0123",
            "1e3",
            "2026-08-25",
            "'quoted'",
            "-leading",
        ] {
            let mut errors = ViolationSink::default();
            validate_plain_string_scalar("test", value, &mut errors);
            assert!(!errors.is_empty(), "{value:?} should be rejected");
        }

        let mut errors = ViolationSink::default();
        validate_exact_rust_version_scalar("test", "1.93.1", &mut errors);
        assert!(errors.is_empty());
        for value in ["123", "1.93", "1.93.1-beta", "2026-08-25"] {
            let mut errors = ViolationSink::default();
            validate_exact_rust_version_scalar("test", value, &mut errors);
            assert!(!errors.is_empty(), "{value:?} should be rejected");
        }
    }

    #[test]
    fn rejects_an_unchanged_adapter_moved_out_of_semver() {
        let moved = canonical_adapter()
            .replace("  semver:\n", "  semver:\n    steps: []\n  another_job:\n");

        let error = audit_source(&spec(), &moved).unwrap_err().to_string();

        assert!(error.contains("must be inside the `semver` job"), "{error}");
    }

    #[test]
    fn rejects_ambiguous_or_extended_step_shapes() {
        let original = canonical_adapter();
        let cases = [
            ("duplicate step", format!("{original}\n{original}"), "expected exactly one"),
            (
                "extra root field",
                original.replace(
                    &format!("      uses: {SEMVER_ACTION} # v2.9\n      env:\n"),
                    &format!(
                        "      uses: {SEMVER_ACTION} # v2.9\n      timeout-minutes: 5\n      env:\n"
                    ),
                ),
                "unsupported root field",
            ),
            (
                "extra root field after a blank",
                original.replace(
                    "  next_job:",
                    "\n      continue-on-error: true\n  next_job:",
                ),
                "condition content",
            ),
            (
                "second action under another step name",
                original.replace(
                    "  next_job:",
                    &format!(
                        "    - name: A misleading second adapter\n      uses: {SEMVER_ACTION}\n  next_job:"
                    ),
                ),
                "occurrence",
            ),
            (
                "extra input",
                original.replace(
                    "        package: zerocopy\n",
                    "        package: zerocopy\n        extra: value\n",
                ),
                "not part of the typed",
            ),
            (
                "duplicate input",
                original.replace(
                    "        package: zerocopy\n",
                    "        package: zerocopy\n        package: zerocopy\n",
                ),
                "repeats key",
            ),
            (
                "YAML merge",
                original.replace(
                    "      env:\n        # Unstable API is not semver checked.\n",
                    "      env:\n        <<: *shared\n        # Unstable API is not semver checked.\n",
                ),
                "not part of the typed",
            ),
            (
                "quoted uses key",
                original.replace("      uses:", "      \"uses\":"),
                "unsupported root field",
            ),
            (
                "reordered root fields",
                original.replace(
                    &format!("      uses: {SEMVER_ACTION} # v2.9\n      env:\n"),
                    &format!("      env:\n      uses: {SEMVER_ACTION} # v2.9\n"),
                ),
                "root fields must appear exactly",
            ),
            (
                "condition content disguised as a comment",
                original.replace(
                    &format!("        {PREPARE_OUTPUT_CONDITION}"),
                    &format!("        # {PREPARE_OUTPUT_CONDITION}"),
                ),
                PREPARE_STEP_ID,
            ),
            ("CRLF source", original.replace('\n', "\r\n"), "canonical LF"),
        ];

        for (case, source, expected) in cases {
            let error = audit_source(&spec(), &source).unwrap_err();
            assert!(error.to_string().contains(expected), "{case}: {error}");
        }
    }

    #[test]
    fn diagnostics_escape_control_characters() {
        let source = canonical_adapter()
            .replace(SEMVER_ACTION, "obi1kenobi/cargo-semver-checks-action@bad\u{1b}revision");
        let diagnostic = audit_source(&spec(), &source).unwrap_err().to_string();
        assert!(diagnostic.contains("\\u{1b}"));
        assert!(!diagnostic.contains('\u{1b}'));
    }
}
