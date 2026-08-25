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
//! the `uses` field dynamically. That unavoidable adapter is small but
//! load-bearing: changing its action revision, inputs, environment, or
//! condition can silently make the typed semver policy mean something else.
//!
//! This module does not pretend to parse GitHub Actions YAML. The general
//! workflow inventory in [`crate::workflow`] proves only filenames and job IDs;
//! it intentionally knows nothing about steps. Here we recognize one exact,
//! canonical step shape, construct one typed specification from checked policy,
//! repository inventory, and deliberately reviewed adapter constants, and
//! reject any unfamiliar or additional syntax. A broader workflow shape must
//! receive a deliberately reviewed parser change.
//!
//! Keep the following files coordinated:
//!
//! * `ci/zc.toml` owns the semver package, toolchain, profile, target set, and
//!   waivers.
//! * `zerocopy/Cargo.toml` owns the stable aggregate feature and package path
//!   discovered through Cargo metadata.
//! * `.github/workflows/ci.yml` contains the literal action adapter audited
//!   here.
//! * `github.rs` owns the projected matrix field values consumed by
//!   `matrix.crate`, `matrix.feature_profile`, `matrix.toolchain`, and
//!   `matrix.target`. The workflow's "Configure environment variables" and
//!   semver-skip steps turn those values into `env.ZC_TOOLCHAIN` and
//!   `env.ZC_SKIP_CARGO_SEMVER_CHECKS`. This narrow parser fixes the adapter's
//!   consumer expressions; it does not claim to parse those general shell
//!   producers.
//! * `execution.rs` models the same action as legacy command behavior. It must
//!   consume the constants and typed values exported here rather than growing
//!   an independent copy.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt, fs, io,
    path::{Path, PathBuf},
};

use thiserror::Error;

use crate::{
    inventory::RepositoryInventory,
    policy::{FeatureProfile, Policy},
};

/// The one workflow whose semver step remains handwritten.
pub(crate) const SEMVER_WORKFLOW_PATH: &str = ".github/workflows/ci.yml";

/// The pinned action identity shared with the typed execution model.
pub(crate) const SEMVER_ACTION: &str =
    "obi1kenobi/cargo-semver-checks-action@6b69fcf40e9b5fb17adeb57e4b6ecd020649a239";

/// The action's explicit feature-selection mode.
pub(crate) const SEMVER_FEATURE_GROUP: &str = "only-explicit-features";

/// Warnings remain errors, while unstable public API stays hidden from semver.
pub(crate) const SEMVER_WARNING_FLAGS: &str = "-Dwarnings";

/// The local escape hatch whose condition remains visible in workflow YAML.
pub(crate) const SEMVER_SKIP_ENVIRONMENT: &str = "ZC_SKIP_CARGO_SEMVER_CHECKS";

const SEMVER_STEP_NAME: &str = "Check semver compatibility";
const SEMVER_STEP_MARKER: &str = "    - name: Check semver compatibility";
const SEMVER_ACTION_MARKER: &str = "cargo-semver-checks-action@";
const MATRIX_TARGET_EXPRESSION: &str = "${{ matrix.target }}";
const RESOLVED_TOOLCHAIN_EXPRESSION: &str = "${{ env.ZC_TOOLCHAIN }}";
const ROOT_FIELD_ORDER: [&str; 4] = ["uses", "env", "with", "if"];

/// All semantic values expected in the handwritten adapter.
///
/// This type is crate-visible so the typed executor can share this model. Its
/// fields remain private to prevent another module from constructing an
/// unchecked, nearly-identical adapter.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SemverAdapterSpec {
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

        validate_effective_targets(policy, &mut errors);

        if !errors.is_empty() {
            return Err(errors.finish());
        }
        let manifest = manifest.expect("a valid checked package must have a UTF-8 manifest path");
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
            ("rust-toolchain".to_owned(), RESOLVED_TOOLCHAIN_EXPRESSION.to_owned()),
        ]);

        let mut terms = vec![
            format!("matrix.crate == '{}'", semver.package()),
            format!("matrix.feature_profile == '{}'", semver.profile()),
            format!("matrix.toolchain == '{}'", semver.toolchain()),
        ];
        terms.extend(semver.waivers().keys().map(|target| format!("matrix.target != '{target}'")));
        terms.push(format!("env.{SEMVER_SKIP_ENVIRONMENT} != '1'"));
        let final_index = terms.len() - 1;
        let condition = terms
            .into_iter()
            .enumerate()
            .map(|(index, term)| if index == final_index { term } else { format!("{term} &&") })
            .collect();

        Ok(Self { action: SEMVER_ACTION, environment, inputs, condition })
    }

    /// Returns the exact pinned `uses` identity.
    pub(crate) fn action(&self) -> &str {
        self.action
    }

    /// Returns the complete explicit step-level environment.
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
/// `repository_root` must be the canonical root already used by the workflow
/// inventory. That earlier pass rejects workflow-directory redirects and
/// non-file entries before this function opens the fixed workflow path.
pub(crate) fn audit_semver_adapter(
    repository_root: &Path,
    policy: &Policy,
    repository: &RepositoryInventory,
) -> Result<(), SemverAdapterAuditError> {
    let path = repository_root.join(SEMVER_WORKFLOW_PATH);
    let source = fs::read_to_string(&path)
        .map_err(|source| SemverAdapterAuditError::Read { path: path.clone(), source })?;
    let expected = SemverAdapterSpec::from_checked_inputs(policy, repository)?;
    audit_source(&expected, &source)?;
    Ok(())
}

fn audit_source(expected: &SemverAdapterSpec, source: &str) -> Result<(), SemverAdapterViolations> {
    let actual = ParsedAdapter::parse(source)?;
    let mut errors = ViolationSink::default();
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
/// Equality clauses select one package/toolchain/profile slice of the ordinary
/// matrix. Target-waiver clauses then subtract every explicit waiver. If that
/// result differs from `semver.target_set`, the visible condition cannot
/// faithfully implement policy even if each individual YAML line looks valid.
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

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedAdapter {
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

        let start = markers[0] + 1;
        let mut end = lines.len();
        for (index, line) in lines.iter().enumerate().skip(start) {
            if !line.trim().is_empty()
                && !line.trim_start().starts_with('#')
                && indentation(line) <= 4
            {
                end = index;
                break;
            }
        }
        // Blank lines and sibling-level comments between this step and the
        // next sequence item are not part of the adapter. Strip only a trailing
        // run: a blank or comment followed by another semantic field remains
        // inside the block and is rejected, so whitespace cannot hide an
        // unsupported `continue-on-error` or similar field.
        while end > start {
            let line = lines[end - 1];
            if line.trim().is_empty() || line.trim_start().starts_with('#') {
                end -= 1;
            } else {
                break;
            }
        }

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
            Ok(Self { action, environment, inputs, condition })
        } else {
            Err(errors.finish())
        }
    }
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
    format!("{SEMVER_WORKFLOW_PATH}:{SEMVER_STEP_NAME}.{field}")
}

fn adapter_line_location(line: usize) -> String {
    format!("{SEMVER_WORKFLOW_PATH}:{line}")
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
        audit_semver_adapter, audit_source, SemverAdapterSpec, SEMVER_ACTION, SEMVER_FEATURE_GROUP,
        SEMVER_WARNING_FLAGS,
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
        format!(
            "jobs:\n  build_test:\n    steps:\n    - name: Check semver compatibility\n      uses: {SEMVER_ACTION} # v2.9\n      env:\n        # Unstable API is not semver checked.\n        RUSTDOCFLAGS: {SEMVER_WARNING_FLAGS}\n        RUSTFLAGS: {SEMVER_WARNING_FLAGS}\n      with:\n        package: zerocopy\n        feature-group: {SEMVER_FEATURE_GROUP}\n        features: __internal_use_only_features_that_work_on_stable\n        manifest-path: zerocopy/Cargo.toml\n        rust-toolchain: ${{{{ env.ZC_TOOLCHAIN }}}}\n        rust-target: ${{{{ matrix.target }}}}\n      if: |\n        matrix.crate == 'zerocopy' &&\n        matrix.feature_profile == 'stable' &&\n        matrix.toolchain == 'stable' &&\n        matrix.target != 'wasm32-unknown-unknown' &&\n        env.ZC_SKIP_CARGO_SEMVER_CHECKS != '1'\n  next_job:\n    runs-on: ubuntu-latest\n"
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
        assert_eq!(
            spec.condition(),
            [
                "matrix.crate == 'zerocopy' &&",
                "matrix.feature_profile == 'stable' &&",
                "matrix.toolchain == 'stable' &&",
                "matrix.target != 'wasm32-unknown-unknown' &&",
                "env.ZC_SKIP_CARGO_SEMVER_CHECKS != '1'",
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
                "toolchain expression",
                original
                    .replace("rust-toolchain: ${{ env.ZC_TOOLCHAIN }}", "rust-toolchain: stable"),
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
                    "env.ZC_SKIP_CARGO_SEMVER_CHECKS != '1'",
                    "env.ZC_SKIP_CARGO_SEMVER_CHECKS == '1'",
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
    fn rejects_ambiguous_or_extended_step_shapes() {
        let original = canonical_adapter();
        let cases = [
            ("duplicate step", format!("{original}\n{original}"), "expected exactly one"),
            (
                "extra root field",
                original.replace("      env:\n", "      timeout-minutes: 5\n      env:\n"),
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
                original.replace("      env:\n", "      env:\n        <<: *shared\n"),
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
