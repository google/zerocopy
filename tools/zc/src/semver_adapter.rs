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
//! IDs, while [`crate::planned_adapter`] already proves that `build_test`
//! consumes the exact typed projection for each event. Here we recognize one
//! exact canonical preparation/action pair inside that exact job, construct
//! its specification from checked policy and repository inventory, and reject
//! unfamiliar or additional syntax. A broader workflow shape must receive a
//! deliberately reviewed parser change.
//!
//! Keep the following files coordinated:
//!
//! * `ci/zc.toml` owns the semver package, toolchain, profile, target set, and
//!   waivers.
//! * `zerocopy/Cargo.toml` owns the stable aggregate feature and package path
//!   discovered through Cargo metadata.
//! * `.github/workflows/ci.yml` contains the literal action adapter audited
//!   here.
//! * `planned_adapter` proves that `build_test` consumes the exact per-event
//!   projection owned by `github.rs`. This module may therefore prove the
//!   full-event package/toolchain/profile slice without reparsing a second
//!   matrix; reduced events intentionally consume their policy-selected
//!   subset.
//! * `workflow_protocol.rs` owns the workflow path and `build_test` job name
//!   shared with that preceding audit. Keep this module's deliberately narrow
//!   job-range grammar coordinated with `planned_adapter/source.rs`.
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
    fmt, fs, io,
    ops::Range,
    path::{Path, PathBuf},
};

use thiserror::Error;

use crate::{
    inventory::RepositoryInventory,
    policy::{FeatureProfile, Policy},
    workflow_protocol::{BUILD_JOB, REPOSITORY_WORKING_DIRECTORY, TRUSTED_SHELL, WORKFLOW_PATH},
};

/// The pinned action identity shared with the typed execution model.
pub(crate) const SEMVER_ACTION: &str =
    "obi1kenobi/cargo-semver-checks-action@6b69fcf40e9b5fb17adeb57e4b6ecd020649a239";

/// The action's explicit feature-selection mode.
pub(crate) const SEMVER_FEATURE_GROUP: &str = "only-explicit-features";

/// Warnings remain errors, while unstable public API stays hidden from semver.
pub(crate) const SEMVER_WARNING_FLAGS: &str = "-Dwarnings";

const PREPARE_STEP_NAME: &str = "Prepare cargo-semver-checks";
const PREPARE_STEP_MARKER: &str = "    - name: Prepare cargo-semver-checks";
const PREPARE_STEP_ID: &str = "prepare_semver";
const PREPARE_OUTPUT_CONDITION: &str = "steps.prepare_semver.outputs.run == 'true'";
const LEGACY_SKIP_ENVIRONMENT: &str = "ZC_SKIP_CARGO_SEMVER_CHECKS";
const SEMVER_STEP_NAME: &str = "Check semver compatibility";
const SEMVER_STEP_MARKER: &str = "    - name: Check semver compatibility";
const SEMVER_ACTION_MARKER: &str = "cargo-semver-checks-action@";
const MATRIX_TARGET_EXPRESSION: &str = "${{ matrix.target }}";
const PREPARE_ROOT_FIELD_ORDER: [&str; 6] =
    ["id", "shell", "working-directory", "env", "run", "if"];
const ROOT_FIELD_ORDER: [&str; 4] = ["uses", "env", "with", "if"];

const PREPARE_RUN: &[&str] = &[
    "set -euo pipefail",
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
    preparation_condition: Vec<String>,
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

        validate_effective_targets(policy, &mut errors);

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
        for target in semver.waivers().keys() {
            validate_plain_string_scalar(
                &format!("semver.waivers.{target}"),
                target.as_str(),
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
            ("rust-target".to_owned(), MATRIX_TARGET_EXPRESSION.to_owned()),
            ("rust-toolchain".to_owned(), toolchain_version),
        ]);

        let preparation_environment = BTreeMap::from([(
            "PR_HEAD_SHA".to_owned(),
            "${{ github.event.pull_request.head.sha }}".to_owned(),
        )]);
        let preparation_run = PREPARE_RUN.iter().map(|line| (*line).to_owned()).collect();
        let preparation_condition = vec![
            format!("matrix.crate == '{}'", semver.package()),
            format!("matrix.feature_profile == '{}'", semver.profile()),
            format!("matrix.toolchain == '{}'", semver.toolchain()),
        ]
        .into_iter()
        .chain(semver.waivers().keys().map(|target| format!("matrix.target != '{target}'")))
        .collect::<Vec<_>>();
        let condition = preparation_condition
            .iter()
            .cloned()
            .chain(std::iter::once(PREPARE_OUTPUT_CONDITION.to_owned()))
            .collect::<Vec<_>>();
        let preparation_condition = canonical_condition(preparation_condition);
        let condition = canonical_condition(condition);

        Ok(Self {
            preparation_environment,
            preparation_run,
            preparation_condition,
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

    /// Returns the exact preparation selector.
    fn preparation_condition(&self) -> &[String] {
        &self.preparation_condition
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

fn canonical_condition(terms: Vec<String>) -> Vec<String> {
    let final_index = terms.len() - 1;
    terms
        .into_iter()
        .enumerate()
        .map(|(index, term)| if index == final_index { term } else { format!("{term} &&") })
        .collect()
}

/// Checks the literal workflow adapter against its typed specification.
///
/// `repository_root` must be the canonical root already used by the workflow
/// inventory. That earlier pass rejects workflow-directory redirects and
/// non-file entries before this function opens the fixed workflow path.
pub(crate) fn audit_semver_adapter(
    repository_root: &Path,
    policy: &Policy,
    repository: &RepositoryInventory,
) -> Result<(), SemverAdapterAuditError> {
    let path = repository_root.join(WORKFLOW_PATH);
    let source = fs::read_to_string(&path)
        .map_err(|source| SemverAdapterAuditError::Read { path: path.clone(), source })?;
    let expected = SemverAdapterSpec::from_checked_inputs(policy, repository)?;
    audit_source(&expected, &source)?;
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
    if expected.preparation_condition() != preparation.condition {
        errors.push(
            adapter_location("preparation.if"),
            format!(
                "condition must be the exact typed expression {:?}, found {:?}",
                expected.preparation_condition(),
                preparation.condition
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

/// Proves that the canonical condition runs on exactly the typed target set.
///
/// The planned-adapter audit runs before this function and proves that
/// `build_test` consumes the exact typed projection for every event. Equality
/// clauses can therefore select one package/toolchain/profile slice of the
/// full-event projection, and target-waiver clauses subtract every explicit
/// waiver. If the result differs from `semver.target_set`, the visible
/// condition cannot faithfully implement policy even if each individual YAML
/// line looks valid.
fn validate_effective_targets(policy: &Policy, errors: &mut ViolationSink) {
    let semver = policy.semver();
    let Some(toolchain) = policy.toolchains().get(semver.toolchain().as_str()) else {
        errors.push("semver.toolchain", format!("unknown toolchain `{}`", semver.toolchain()));
        return;
    };
    let Some(selected) = policy.target_sets().get(semver.target_set().as_str()) else {
        errors.push("semver.target_set", format!("unknown target set `{}`", semver.target_set()));
        return;
    };

    let mut candidates = BTreeSet::new();
    for scope in toolchain.scopes() {
        if !scope.packages().contains(semver.package())
            || !scope.profiles().contains(semver.profile())
        {
            continue;
        }
        let Some(targets) = policy.target_sets().get(scope.target_set().as_str()) else {
            errors.push(
                "semver.toolchain",
                format!("toolchain scope references unknown target set `{}`", scope.target_set()),
            );
            continue;
        };
        candidates.extend(targets.iter().cloned());
    }

    let effective = candidates
        .iter()
        .filter(|target| !semver.waivers().contains_key(target.as_str()))
        .cloned()
        .collect::<BTreeSet<_>>();
    if &effective == selected {
        return;
    }
    let missing = selected.difference(&effective).map(ToString::to_string).collect::<Vec<_>>();
    let extra = effective.difference(selected).map(ToString::to_string).collect::<Vec<_>>();
    errors.push(
        "semver.target_set",
        format!(
            "the package/toolchain/profile condition plus waiver exclusions differs from the selected target set; missing {missing:?}, extra {extra:?}"
        ),
    );
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
        let build_job = canonical_job_range(&lines, BUILD_JOB, &mut errors);
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
        let Some(build_job) = build_job else {
            return Err(errors.finish());
        };
        if !build_job.contains(&marker) {
            errors.push(
                preparation_location("name"),
                format!("canonical preparation step must be inside the `{BUILD_JOB}` job"),
            );
            return Err(errors.finish());
        }

        let start = marker + 1;
        let end = canonical_step_end(&lines, start, build_job.end);
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
            if line.trim().is_empty() || line.trim_start().starts_with('#') {
                if section == PreparationSection::Run
                    && run.last().is_some_and(|line: &String| line.ends_with('\\'))
                {
                    errors.push(
                        adapter_line_location(line_number),
                        "blank or comment line must not interrupt a continued shell command",
                    );
                }
                continue;
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
        let build_job = canonical_job_range(&lines, BUILD_JOB, &mut errors);
        let action_mentions = source.match_indices(SEMVER_ACTION_MARKER).count();
        if action_mentions != 1 {
            errors.push(
                adapter_location("uses"),
                format!(
                    "expected exactly one `{SEMVER_ACTION_MARKER}` occurrence in the workflow, found {action_mentions}"
                ),
            );
        }
        let markers = lines
            .iter()
            .enumerate()
            .filter_map(|(index, line)| (*line == SEMVER_STEP_MARKER).then_some(index))
            .collect::<Vec<_>>();
        if markers.len() != 1 {
            errors.push(
                adapter_location("name"),
                format!(
                    "expected exactly one canonical `{SEMVER_STEP_MARKER}` declaration, found {}",
                    markers.len()
                ),
            );
            return Err(errors.finish());
        }

        let marker = markers[0];
        let Some(build_job) = build_job else {
            return Err(errors.finish());
        };
        if !build_job.contains(&marker) {
            errors.push(
                adapter_location("name"),
                format!("canonical semver step must be inside the `{BUILD_JOB}` job"),
            );
            return Err(errors.finish());
        }

        let start = marker + 1;
        let end = canonical_step_end(&lines, start, build_job.end);

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
    /// The fixed workflow path could not be read after workflow inventory.
    #[error("failed to read semver adapter workflow `{path}`: {source}")]
    Read {
        /// The fixed workflow path.
        path: PathBuf,
        /// The underlying file-system error.
        #[source]
        source: io::Error,
    },
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
        PREPARE_STEP_ID, SEMVER_ACTION, SEMVER_FEATURE_GROUP, SEMVER_WARNING_FLAGS, TRUSTED_SHELL,
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
            "jobs:\n  build_test:\n    steps:\n    - name: Prepare cargo-semver-checks\n      id: {PREPARE_STEP_ID}\n      shell: {TRUSTED_SHELL}\n      working-directory: zerocopy\n      env:\n        PR_HEAD_SHA: ${{{{ github.event.pull_request.head.sha }}}}\n      run: |\n        {preparation_run}\n      if: |\n        matrix.crate == 'zerocopy' &&\n        matrix.feature_profile == 'stable' &&\n        matrix.toolchain == 'stable' &&\n        matrix.target != 'wasm32-unknown-unknown'\n    - name: Check semver compatibility\n      uses: {SEMVER_ACTION} # v2.9\n      env:\n        # Unstable API is not semver checked.\n        RUSTDOCFLAGS: {SEMVER_WARNING_FLAGS}\n        RUSTFLAGS: {SEMVER_WARNING_FLAGS}\n      with:\n        package: zerocopy\n        feature-group: {SEMVER_FEATURE_GROUP}\n        features: __internal_use_only_features_that_work_on_stable\n        manifest-path: zerocopy/Cargo.toml\n        rust-toolchain: {toolchain_version}\n        rust-target: ${{{{ matrix.target }}}}\n      if: |\n        matrix.crate == 'zerocopy' &&\n        matrix.feature_profile == 'stable' &&\n        matrix.toolchain == 'stable' &&\n        matrix.target != 'wasm32-unknown-unknown' &&\n        {PREPARE_OUTPUT_CONDITION}\n  next_job:\n    runs-on: ubuntu-latest\n"
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
        assert_eq!(
            spec.preparation_condition(),
            [
                "matrix.crate == 'zerocopy' &&",
                "matrix.feature_profile == 'stable' &&",
                "matrix.toolchain == 'stable' &&",
                "matrix.target != 'wasm32-unknown-unknown'",
            ]
        );
        assert_eq!(
            spec.condition(),
            [
                "matrix.crate == 'zerocopy' &&",
                "matrix.feature_profile == 'stable' &&",
                "matrix.toolchain == 'stable' &&",
                "matrix.target != 'wasm32-unknown-unknown' &&",
                PREPARE_OUTPUT_CONDITION,
            ]
        );
    }

    #[test]
    fn accepts_the_canonical_adapter_and_the_live_workflow() {
        let spec = spec();
        audit_source(&spec, &canonical_adapter()).unwrap();

        let (policy, repository) = checked_inputs();
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap();
        audit_semver_adapter(&root, policy, repository).unwrap();
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
                "package condition",
                original.replace(
                    "matrix.crate == 'zerocopy' &&",
                    "matrix.crate == 'zerocopy-derive' &&",
                ),
                ".if",
            ),
            (
                "profile condition",
                original.replace(
                    "matrix.feature_profile == 'stable' &&",
                    "matrix.feature_profile == 'default' &&",
                ),
                ".if",
            ),
            (
                "toolchain condition",
                original.replace(
                    "matrix.toolchain == 'stable' &&",
                    "matrix.toolchain == 'nightly' &&",
                ),
                ".if",
            ),
            (
                "waiver condition",
                original.replace("        matrix.target != 'wasm32-unknown-unknown' &&\n", ""),
                ".if",
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
                "changed preparation selector",
                original.replacen(
                    "matrix.crate == 'zerocopy' &&",
                    "matrix.crate == 'zerocopy-derive' &&",
                    1,
                ),
                ".preparation.if",
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
                "interior preparation comment",
                original.replacen(
                    "        matrix.feature_profile == 'stable' &&\n",
                    "        matrix.feature_profile == 'stable' &&\n        # changed expression\n",
                    1,
                ),
                ".preparation.if",
            ),
            (
                "trailing preparation comment",
                original.replacen(
                    "        matrix.target != 'wasm32-unknown-unknown'\n    - name: Check",
                    "        matrix.target != 'wasm32-unknown-unknown'\n        # changed expression\n    - name: Check",
                    1,
                ),
                ".preparation.if",
            ),
            (
                "interior action comment",
                original.replacen(
                    &format!(
                        "        matrix.target != 'wasm32-unknown-unknown' &&\n        {PREPARE_OUTPUT_CONDITION}"
                    ),
                    &format!(
                        "        matrix.target != 'wasm32-unknown-unknown' &&\n        # changed expression\n        {PREPARE_OUTPUT_CONDITION}"
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
    fn rejects_an_unchanged_adapter_moved_out_of_build_test() {
        let moved = canonical_adapter().replace(
            "  build_test:\n    steps:\n",
            "  build_test:\n    steps: []\n  another_job:\n    steps:\n",
        );

        let error = audit_source(&spec(), &moved).unwrap_err().to_string();

        assert!(error.contains("must be inside the `build_test` job"), "{error}");
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
                    "        matrix.crate == 'zerocopy' &&",
                    "        # matrix.crate == 'zerocopy' &&",
                ),
                ".if",
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
