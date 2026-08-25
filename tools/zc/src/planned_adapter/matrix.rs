// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exact consumption and execution audit for typed build and Miri matrices.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

use super::{
    source::{
        audit_exact_job_fields, audit_exact_scalar_field, audit_host_job_contract,
        audit_read_permissions, audit_step, audit_unique_run_mentions, audited_steps_block,
        compare_map, escape_control_characters, exact_step_lines, find_job, job_field_location,
        job_fields, nested_mapping, parse_needs, unique_field, RunForm, StepExpectation,
    },
    PlannedAdapterAuditError, PlannedAdapterViolations, ViolationSink,
};
use crate::{
    repository_text,
    workflow::WORKFLOW_REGISTRY_PATH,
    workflow_protocol::{
        BUILD_JOB, BUILD_MATRIX_OUTPUT, BUILD_STEP_NAME, CELL_FEATURE_PROFILE_OPTION,
        CELL_MIRI_MODEL_OPTION, CELL_PACKAGE_OPTION, CELL_TARGET_OPTION, CELL_TOOLCHAIN_OPTION,
        CI_EVENT_OPTION, DOCKER_ENTRYPOINT_ARGUMENT, DOCKER_OPTION_TERMINATOR,
        EXECUTE_BUILD_CELL_COMMAND, EXECUTE_MIRI_CELL_COMMAND, HOST_DOCKER_RUN,
        MIRI_ENABLED_OUTPUT, MIRI_JOB, MIRI_MATRIX_OUTPUT, MIRI_STEP_NAME, PLAN_JOB,
        REPOSITORY_WORKING_DIRECTORY, SEMVER_JOB, TRUSTED_SHELL, WORKFLOW_PATH,
    },
};

#[derive(Clone, Copy)]
struct SelectorExpectation {
    environment_name: &'static str,
    matrix_field_name: &'static str,
    cli_option: &'static str,
}

#[derive(Clone, Copy)]
enum JobConditionExpectation {
    Absent,
    MiriEnabled,
}

#[derive(Clone, Copy)]
struct MatrixJobExpectation {
    job_name: &'static str,
    display_name: &'static str,
    top_level_fields: &'static [&'static str],
    matrix_output_name: &'static str,
    executor_step_name: &'static str,
    executor_command: &'static str,
    selectors: &'static [SelectorExpectation],
    forwarded_selector_environment: &'static str,
    condition: JobConditionExpectation,
}

const BUILD_DOCKER_JOB: &str = "build_docker_env";
const DOWNLOAD_ACTION_PATH: &str = ".github/actions/download-artifact-with-retry/action.yml";
const BUILD_JOB_FIELDS: &[&str] = &["runs-on", "needs", "permissions", "strategy", "name", "steps"];
const MIRI_JOB_FIELDS: &[&str] =
    &["if", "runs-on", "needs", "permissions", "strategy", "name", "steps"];
const BUILD_DISPLAY_NAME: &str = "Build & Test (${{ matrix.crate }} / ${{ matrix.toolchain }} / ${{ matrix.feature_profile }} / ${{ matrix.target }})";
const MIRI_DISPLAY_NAME: &str = "Miri (${{ matrix.crate }} / ${{ matrix.toolchain }} / ${{ matrix.feature_profile }} / ${{ matrix.miri_model }} / ${{ matrix.target }})";

// The build job defines these three reusable setup steps, and the Miri job
// consumes the corresponding aliases. Their exact source is part of the typed
// execution boundary: changing checkout identity, artifact selection, or the
// host command which loads the image can make an otherwise-correct executor
// run against different code or a different container.
//
// Keep these definitions synchronized with `&matrix_checkout`,
// `&download_ci_image`, and `&load_ci_image` in `.github/workflows/ci.yml`.
// YAML comments may change without changing behavior; comments inside a block
// scalar are shell content and remain part of the exact comparison. The
// repository-owned download action receives an additional containment and
// cross-step-environment audit below because its `uses` line cannot pin its
// implementation independently of this checkout.
const CHECKOUT_STEP: &[&str] = &[
    "    - &matrix_checkout",
    "      uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1",
    "      with:",
    "        persist-credentials: false",
];
const DOWNLOAD_IMAGE_STEP: &[&str] = &[
    "    - &download_ci_image",
    "      name: Download prebuilt Docker image",
    "      uses: ./.github/actions/download-artifact-with-retry",
    "      with:",
    "        artifact-id: ${{ needs.build_docker_env.outputs.image_artifact_id }}",
    "        path: ${{ runner.temp }}",
    "        expected-file: ${{ env.ZC_CI_IMAGE_ARCHIVE }}",
];
const LOAD_IMAGE_STEP: &[&str] = &[
    "    - &load_ci_image",
    "      name: Load prebuilt Docker image",
    "      shell: bash",
    "      env:",
    "        IMAGE_ARCHIVE: ${{ runner.temp }}/${{ env.ZC_CI_IMAGE_ARCHIVE }}",
    "        IMAGE_NAME: ${{ env.ZC_CI_IMAGE }}",
    "      run: |",
    "        set -euo pipefail",
    "        trap 'rm -f -- \"$IMAGE_ARCHIVE\"' EXIT",
    "        docker load --input \"$IMAGE_ARCHIVE\"",
    "        docker image inspect \"$IMAGE_NAME\" >/dev/null",
    "        docker run --rm \"$IMAGE_NAME\" true",
];

const BUILD_STEP_MARKERS: &[&str] = &[
    "- &matrix_checkout",
    "- &download_ci_image",
    "- &load_ci_image",
    "- name: Execute checked build cell",
];
const MIRI_STEP_MARKERS: &[&str] = &[
    "- *matrix_checkout",
    "- *download_ci_image",
    "- *load_ci_image",
    "- name: Execute checked Miri cell",
];

const BUILD_SELECTORS: [SelectorExpectation; 4] = [
    SelectorExpectation {
        environment_name: "CRATE",
        matrix_field_name: "crate",
        cli_option: CELL_PACKAGE_OPTION,
    },
    SelectorExpectation {
        environment_name: "TOOLCHAIN",
        matrix_field_name: "toolchain",
        cli_option: CELL_TOOLCHAIN_OPTION,
    },
    SelectorExpectation {
        environment_name: "FEATURE_PROFILE",
        matrix_field_name: "feature_profile",
        cli_option: CELL_FEATURE_PROFILE_OPTION,
    },
    SelectorExpectation {
        environment_name: "TARGET",
        matrix_field_name: "target",
        cli_option: CELL_TARGET_OPTION,
    },
];

const MIRI_SELECTORS: [SelectorExpectation; 5] = [
    SelectorExpectation {
        environment_name: "CRATE",
        matrix_field_name: "crate",
        cli_option: CELL_PACKAGE_OPTION,
    },
    SelectorExpectation {
        environment_name: "TOOLCHAIN",
        matrix_field_name: "toolchain",
        cli_option: CELL_TOOLCHAIN_OPTION,
    },
    SelectorExpectation {
        environment_name: "FEATURE_PROFILE",
        matrix_field_name: "feature_profile",
        cli_option: CELL_FEATURE_PROFILE_OPTION,
    },
    SelectorExpectation {
        environment_name: "TARGET",
        matrix_field_name: "target",
        cli_option: CELL_TARGET_OPTION,
    },
    SelectorExpectation {
        environment_name: "MIRI_MODEL",
        matrix_field_name: "miri_model",
        cli_option: CELL_MIRI_MODEL_OPTION,
    },
];

const BUILD_EXPECTATION: MatrixJobExpectation = MatrixJobExpectation {
    job_name: BUILD_JOB,
    display_name: BUILD_DISPLAY_NAME,
    top_level_fields: BUILD_JOB_FIELDS,
    matrix_output_name: BUILD_MATRIX_OUTPUT,
    executor_step_name: BUILD_STEP_NAME,
    executor_command: EXECUTE_BUILD_CELL_COMMAND,
    selectors: &BUILD_SELECTORS,
    forwarded_selector_environment: "  -e TOOLCHAIN -e CRATE -e TARGET -e FEATURE_PROFILE \\",
    condition: JobConditionExpectation::Absent,
};

const MIRI_EXPECTATION: MatrixJobExpectation = MatrixJobExpectation {
    job_name: MIRI_JOB,
    display_name: MIRI_DISPLAY_NAME,
    top_level_fields: MIRI_JOB_FIELDS,
    matrix_output_name: MIRI_MATRIX_OUTPUT,
    executor_step_name: MIRI_STEP_NAME,
    executor_command: EXECUTE_MIRI_CELL_COMMAND,
    selectors: &MIRI_SELECTORS,
    forwarded_selector_environment:
        "  -e TOOLCHAIN -e CRATE -e TARGET -e FEATURE_PROFILE -e MIRI_MODEL \\",
    condition: JobConditionExpectation::MiriEnabled,
};

pub(super) fn audit(
    lines: &[&str],
    reviewed_planned_jobs: &BTreeSet<(String, String)>,
    errors: &mut ViolationSink,
) {
    audit_reviewed_roles(reviewed_planned_jobs, errors);
    audit_anchor_ownership(lines, errors);
    for expected in [BUILD_EXPECTATION, MIRI_EXPECTATION] {
        if let Some(job) = find_job(lines, expected.job_name, errors) {
            audit_matrix_job(lines, job, expected, errors);
        }
        audit_unique_run_mentions(
            lines,
            expected.executor_step_name,
            expected.executor_command,
            errors,
        );
    }
}

fn audit_anchor_ownership(lines: &[&str], errors: &mut ViolationSink) {
    // YAML aliases bind to anchor declarations outside the aliasing step. The
    // exact build definition and Miri alias checks are insufficient if another
    // job can redefine the same anchor between them, so reserve each name for
    // exactly one definition and one use in the whole workflow. Full-line
    // comments remain documentation and do not participate in YAML binding.
    for anchor in ["matrix_checkout", "download_ci_image", "load_ci_image"] {
        for (sigil, role) in [('&', "definition"), ('*', "alias")] {
            let token = format!("{sigil}{anchor}");
            let mentions = lines
                .iter()
                .filter(|line| !line.trim_start().starts_with('#'))
                .map(|line| token_mentions(line, &token))
                .sum::<usize>();
            if mentions != 1 {
                errors.push(
                    WORKFLOW_PATH,
                    format!(
                        "matrix step anchor `{anchor}` must have exactly one {role}, found {mentions}"
                    ),
                );
            }
        }
    }
}

/// Audits the mutable local action used by both planned matrix jobs.
///
/// External actions in the exact step contract are pinned by immutable commit
/// ID. This downloader is repository-owned instead, so its literal `uses`
/// path alone does not constrain the code which runs before the typed
/// executor. Resolve the fixed path through the canonical repository boundary
/// and reject GitHub's two cross-step process-mutation channels in its source.
pub(super) fn audit_download_action(
    repository_root: &Path,
) -> Result<(), PlannedAdapterAuditError> {
    let source = read_download_action(repository_root)?;
    audit_download_action_source(&source)?;
    Ok(())
}

/// Reads the fixed local action without following a redirect out of the repo.
///
/// `repository_root` is the canonical root already established by CI input
/// loading. Canonicalizing the complete action path catches both a symlink at
/// the file itself and a redirect in any ancestor directory. The shared text
/// boundary accepts well-formed CRLF from an older Windows worktree while
/// preserving the source audit's one canonical LF spelling.
fn read_download_action(repository_root: &Path) -> Result<String, PlannedAdapterAuditError> {
    let path = repository_root.join(DOWNLOAD_ACTION_PATH);
    let resolved = path.canonicalize().map_err(|source| {
        PlannedAdapterAuditError::InspectLocalAction { path: path.clone(), source }
    })?;
    if !resolved.starts_with(repository_root) {
        return Err(PlannedAdapterAuditError::LocalActionOutsideRepository {
            path,
            resolved,
            repository_root: repository_root.to_path_buf(),
        });
    }
    let metadata = fs::metadata(&resolved).map_err(|source| {
        PlannedAdapterAuditError::InspectLocalAction { path: resolved.clone(), source }
    })?;
    if !metadata.is_file() {
        return Err(PlannedAdapterAuditError::LocalActionNotFile { path: resolved });
    }
    repository_text::read(&resolved)
        .map_err(|source| PlannedAdapterAuditError::ReadLocalAction { path: resolved, source })
}

/// Rejects direct file-command channel references in the local action.
///
/// GitHub makes `GITHUB_ENV` and `GITHUB_PATH` write-only channels which alter
/// later step processes. Neither is needed to download an artifact, and either
/// could change the checked executor despite its exact workflow step. Full-line
/// comments remain free to document this rule unless they contain an Actions
/// expression. A comment inside a `run` block is scalar content, and GitHub
/// expands such an expression before Bash decides that the line is a comment.
/// Every other token mention fails closed.
///
/// This is deliberately an inherited-environment audit, not a general sandbox
/// around the local action. The action can also reach the checkout and Docker
/// daemon; its functional tests own that artifact behavior. If it ever needs
/// to modify repository files or daemon state beyond downloading the archive,
/// this boundary must grow an explicit contract for that behavior before the
/// change lands. Duplicating the action's complete implementation here would
/// make harmless retry changes require two source edits without strengthening
/// the specific environment invariant this audit owns.
fn audit_download_action_source(source: &str) -> Result<(), PlannedAdapterViolations> {
    let mut errors = ViolationSink::default();
    if source.contains('\r') {
        errors.push(DOWNLOAD_ACTION_PATH, "local action must use canonical LF line endings");
    }
    for (index, line) in source.lines().enumerate() {
        if line.trim_start().starts_with('#') {
            if line.contains("${{") {
                errors.push(
                    format!("{DOWNLOAD_ACTION_PATH}:{}", index + 1),
                    "local action comments must not contain Actions expressions because comments inside `run` blocks are executable scalar content",
                );
            }
            continue;
        }
        for channel in ["GITHUB_ENV", "GITHUB_PATH"] {
            if token_mentions(line, channel) != 0 {
                errors.push(
                    format!("{DOWNLOAD_ACTION_PATH}:{}", index + 1),
                    format!(
                        "local action must not reference `{channel}` because it runs before the typed matrix executor"
                    ),
                );
            }
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors.finish())
    }
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

fn audit_reviewed_roles(reviewed: &BTreeSet<(String, String)>, errors: &mut ViolationSink) {
    // The matrix module directly audits build and Miri below. The standalone
    // semver adapter has its own exact job audit, but its role still belongs in
    // this single ownership equality check so adding or dropping `planned` in
    // the registry cannot fall between the two focused modules.
    let expected = [BUILD_JOB, MIRI_JOB, SEMVER_JOB]
        .into_iter()
        .map(|job| (WORKFLOW_PATH.to_owned(), job.to_owned()))
        .collect::<BTreeSet<_>>();
    for (workflow, job) in expected.difference(reviewed) {
        errors.push(
            format!("{WORKFLOW_REGISTRY_PATH}:{workflow}:{job}"),
            "planned matrix job must have the reviewed `planned` role",
        );
    }
    for (workflow, job) in reviewed.difference(&expected) {
        errors.push(
            format!("{WORKFLOW_REGISTRY_PATH}:{workflow}:{job}"),
            "job has the reviewed `planned` role but no planned-job workflow audit",
        );
    }
}

fn audit_matrix_job(
    lines: &[&str],
    job: std::ops::Range<usize>,
    expected: MatrixJobExpectation,
    errors: &mut ViolationSink,
) {
    let fields = job_fields(lines, job.clone(), expected.job_name, errors);
    audit_exact_job_fields(&fields, expected.job_name, expected.top_level_fields, errors);
    audit_exact_scalar_field(&fields, expected.job_name, "name", expected.display_name, errors);
    audit_needs(&fields, expected.job_name, errors);
    audit_condition(&fields, expected, errors);
    audit_host_job_contract(&fields, expected.job_name, errors);
    audit_read_permissions(lines, job.end, &fields, expected.job_name, errors);
    audit_strategy(lines, job.end, &fields, expected, errors);

    if let Some(steps) = audited_steps_block(&fields, job, expected.job_name, 4, errors) {
        audit_matrix_step_contract(lines, &steps, expected, errors);
        audit_executor_step(lines, &steps, expected, errors);
    }
}

fn audit_matrix_step_contract(
    lines: &[&str],
    steps: &super::source::StepsBlock,
    expected: MatrixJobExpectation,
    errors: &mut ViolationSink,
) {
    let actual = exact_step_lines(lines, steps);
    let expected_markers =
        if expected.job_name == BUILD_JOB { BUILD_STEP_MARKERS } else { MIRI_STEP_MARKERS };
    let actual_markers = actual
        .iter()
        .filter_map(|step| step.first())
        .map(|line| line.strip_prefix("    ").unwrap_or(line).to_owned())
        .collect::<Vec<_>>();
    if actual_markers != expected_markers {
        errors.push(
            job_field_location(expected.job_name, "steps"),
            format!(
                "steps must be exactly {expected_markers:?} in order, found {actual_markers:?}"
            ),
        );
    }

    // `build_test` owns the definitions and Miri must consume those exact
    // aliases. Comparing complete significant steps prevents an extra field,
    // alternate action, or setup command from hiding behind a familiar anchor
    // name. The terminal executor has its richer field-by-field audit below.
    let expected_setup: [&[&str]; 3] = if expected.job_name == BUILD_JOB {
        [CHECKOUT_STEP, DOWNLOAD_IMAGE_STEP, LOAD_IMAGE_STEP]
    } else {
        [&["    - *matrix_checkout"], &["    - *download_ci_image"], &["    - *load_ci_image"]]
    };
    for (index, expected_step) in expected_setup.into_iter().enumerate() {
        if actual.get(index).map(Vec::as_slice) != Some(expected_step) {
            errors.push(
                job_field_location(expected.job_name, "steps"),
                format!(
                    "setup step {} must match the exact canonical contract {:?}",
                    index + 1,
                    expected_step
                ),
            );
        }
    }
}

fn audit_needs(fields: &[super::source::Field<'_>], job: &str, errors: &mut ViolationSink) {
    let Some(needs) = unique_field(fields, "needs", job, errors) else {
        return;
    };
    let dependencies = match parse_needs(needs.value) {
        Ok(dependencies) => dependencies,
        Err(message) => {
            errors.push(job_field_location(job, "needs"), message);
            return;
        }
    };
    let expected = BTreeSet::from([BUILD_DOCKER_JOB, PLAN_JOB]);
    for missing in expected.difference(&dependencies) {
        errors
            .push(job_field_location(job, "needs"), format!("must depend directly on `{missing}`"));
    }
    for extra in dependencies.difference(&expected) {
        errors.push(
            job_field_location(job, "needs"),
            format!("unexpected direct dependency `{extra}`"),
        );
    }
}

fn audit_condition(
    fields: &[super::source::Field<'_>],
    expected: MatrixJobExpectation,
    errors: &mut ViolationSink,
) {
    let conditions = fields.iter().filter(|field| field.key == "if").collect::<Vec<_>>();
    match expected.condition {
        JobConditionExpectation::Absent => {
            if !conditions.is_empty() {
                errors.push(
                    job_field_location(expected.job_name, "if"),
                    "the ordinary build job must run on every planned event",
                );
            }
        }
        JobConditionExpectation::MiriEnabled => {
            let required = miri_job_condition();
            match conditions.as_slice() {
                [condition] if condition.value == required => {}
                [condition] => errors.push(
                    job_field_location(expected.job_name, "if"),
                    format!(
                        "expected `{required}`, found `{}`",
                        escape_control_characters(condition.value)
                    ),
                ),
                [] => errors.push(
                    job_field_location(expected.job_name, "if"),
                    format!("required `{required}` condition is absent"),
                ),
                _ => errors.push(
                    job_field_location(expected.job_name, "if"),
                    "job repeats its condition; use one canonical scalar field",
                ),
            }
        }
    }
}

fn audit_strategy(
    lines: &[&str],
    job_end: usize,
    fields: &[super::source::Field<'_>],
    expected: MatrixJobExpectation,
    errors: &mut ViolationSink,
) {
    let Some(strategy) = unique_field(fields, "strategy", expected.job_name, errors) else {
        return;
    };
    if !strategy.value.is_empty() {
        errors.push(
            job_field_location(expected.job_name, "strategy"),
            "strategy must use the canonical nested mapping form",
        );
        return;
    }

    let actual = nested_mapping(lines, strategy, job_end, expected.job_name, errors);
    let expected_fields = BTreeMap::from([
        ("fail-fast".to_owned(), "false".to_owned()),
        ("matrix".to_owned(), matrix_expression(expected.matrix_output_name)),
    ]);
    compare_map(
        job_field_location(expected.job_name, "strategy"),
        &expected_fields,
        &actual,
        errors,
    );
}

fn audit_executor_step(
    lines: &[&str],
    steps: &super::source::StepsBlock,
    expected: MatrixJobExpectation,
    errors: &mut ViolationSink,
) {
    let scalar_fields = BTreeMap::from([
        ("shell".to_owned(), TRUSTED_SHELL.to_owned()),
        ("working-directory".to_owned(), REPOSITORY_WORKING_DIRECTORY.to_owned()),
    ]);
    let environment = expected
        .selectors
        .iter()
        .map(|selector| {
            (
                selector.environment_name.to_owned(),
                matrix_selector_expression(selector.matrix_field_name),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let run = executor_run(expected);
    audit_step(
        lines,
        steps,
        StepExpectation {
            job: expected.job_name,
            name: expected.executor_step_name,
            root_fields: &["shell", "working-directory", "env", "run"],
            scalar_fields: &scalar_fields,
            environment: &environment,
            run: &run,
            run_form: RunForm::Block,
        },
        errors,
    );
}

fn executor_run(expected: MatrixJobExpectation) -> Vec<String> {
    let mut run = vec![
        "set -euo pipefail".to_owned(),
        HOST_DOCKER_RUN.to_owned(),
        "  --workdir \"$PWD\" \\".to_owned(),
        "  -v /home/runner/work:/home/runner/work \\".to_owned(),
        "  -v /home/runner/.docker-cargo/registry:/root/.cargo/registry \\".to_owned(),
        "  -v /home/runner/.docker-cargo/git:/root/.cargo/git \\".to_owned(),
        // GITHUB_ENV and GITHUB_PATH are intentionally absent. The container
        // must not use GitHub's cross-step file-command channels to alter the
        // host environment. The exact sequence above keeps the executor
        // terminal today; any future later step would first require extending
        // this audit deliberately. Keep this line coordinated with both matrix
        // job run blocks in `.github/workflows/ci.yml` and the local-action
        // environment audit in this module. Summary, output, and workspace
        // paths are step-scoped data channels which the checked executor may
        // still use.
        "  -e GITHUB_STEP_SUMMARY -e GITHUB_OUTPUT -e GITHUB_WORKSPACE \\".to_owned(),
        "  -e CI -e GITHUB_ACTIONS -e GITHUB_ACTOR -e GITHUB_REPOSITORY -e GITHUB_SHA -e GITHUB_REF -e GITHUB_EVENT_NAME \\".to_owned(),
        expected.forwarded_selector_environment.to_owned(),
        "  -e RUSTFLAGS -e RUSTDOCFLAGS -e MIRIFLAGS \\".to_owned(),
        "  -e CARGO_NET_RETRY -e RUSTUP_MAX_RETRIES \\".to_owned(),
        "  -e ZC_NIGHTLY_RUSTFLAGS -e ZC_NIGHTLY_MIRIFLAGS \\".to_owned(),
        "  -e GIT_CONFIG_COUNT=1 \\".to_owned(),
        "  -e GIT_CONFIG_KEY_0=safe.directory \\".to_owned(),
        "  -e \"GIT_CONFIG_VALUE_0=*\" \\".to_owned(),
        DOCKER_ENTRYPOINT_ARGUMENT.to_owned(),
        DOCKER_OPTION_TERMINATOR.to_owned(),
        "  \"$ZC_CI_IMAGE\" \\".to_owned(),
        "  --noprofile \\".to_owned(),
        "  --norc \\".to_owned(),
        "  -p \\".to_owned(),
        format!("  ./cargo.sh ci {} \\", expected.executor_command),
        format!("  {CI_EVENT_OPTION} \"$GITHUB_EVENT_NAME\" \\"),
    ];
    let last_selector = expected.selectors.len() - 1;
    run.extend(expected.selectors.iter().enumerate().map(|(index, selector)| {
        let continuation = if index == last_selector { "" } else { " \\" };
        format!("  {} \"${}\"{continuation}", selector.cli_option, selector.environment_name)
    }));
    run
}

fn miri_job_condition() -> String {
    format!("needs.{PLAN_JOB}.outputs.{MIRI_ENABLED_OUTPUT} == 'true'")
}

fn matrix_expression(output: &str) -> String {
    format!("${{{{ fromJSON(needs.{PLAN_JOB}.outputs.{output}) }}}}")
}

fn matrix_selector_expression(field: &str) -> String {
    format!("${{{{ matrix.{field} }}}}")
}

#[cfg(test)]
mod tests {
    use std::{
        collections::BTreeSet,
        fs,
        path::{Path, PathBuf},
        process,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::{
        audit, audit_download_action_source, executor_run, read_download_action,
        BUILD_DISPLAY_NAME, BUILD_EXPECTATION, CHECKOUT_STEP, DOWNLOAD_ACTION_PATH,
        DOWNLOAD_IMAGE_STEP, LOAD_IMAGE_STEP, MIRI_DISPLAY_NAME, MIRI_EXPECTATION,
    };
    use crate::{
        planned_adapter::{
            audit_planned_adapter,
            test_support::{
                assert_rejected, audit_feature, canonical_planned_jobs, replace_in_job,
            },
        },
        workflow::{ReviewedWorkflowJobs, WORKFLOW_REGISTRY_PATH},
        workflow_protocol::{
            BUILD_JOB, EXECUTE_BUILD_CELL_COMMAND, EXECUTE_MIRI_CELL_COMMAND, MIRI_JOB, SEMVER_JOB,
            TRUSTED_SHELL, WORKFLOW_PATH,
        },
    };

    const CANONICAL_SOURCE: &str = r#"jobs:
  build_test:
    runs-on: ubuntu-latest
    needs: [build_docker_env, plan_ci]
    permissions:
      contents: read
    strategy:
      fail-fast: false
      matrix: ${{ fromJSON(needs.plan_ci.outputs.build_matrix) }}
    name: Build & Test (${{ matrix.crate }} / ${{ matrix.toolchain }} / ${{ matrix.feature_profile }} / ${{ matrix.target }})
    steps:
    - &matrix_checkout
      uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1
      with:
        persist-credentials: false
    - &download_ci_image
      name: Download prebuilt Docker image
      uses: ./.github/actions/download-artifact-with-retry
      with:
        artifact-id: ${{ needs.build_docker_env.outputs.image_artifact_id }}
        path: ${{ runner.temp }}
        expected-file: ${{ env.ZC_CI_IMAGE_ARCHIVE }}
    - &load_ci_image
      name: Load prebuilt Docker image
      shell: bash
      env:
        IMAGE_ARCHIVE: ${{ runner.temp }}/${{ env.ZC_CI_IMAGE_ARCHIVE }}
        IMAGE_NAME: ${{ env.ZC_CI_IMAGE }}
      run: |
        set -euo pipefail
        trap 'rm -f -- "$IMAGE_ARCHIVE"' EXIT
        docker load --input "$IMAGE_ARCHIVE"
        docker image inspect "$IMAGE_NAME" >/dev/null
        docker run --rm "$IMAGE_NAME" true
    - name: Execute checked build cell
      shell: /usr/bin/env -u BASH_ENV -u ENV -u SHELLOPTS -u BASHOPTS /bin/bash --noprofile --norc -p -euo pipefail -- {0}
      working-directory: zerocopy
      env:
        TOOLCHAIN: ${{ matrix.toolchain }}
        CRATE: ${{ matrix.crate }}
        FEATURE_PROFILE: ${{ matrix.feature_profile }}
        TARGET: ${{ matrix.target }}
      run: |
        set -euo pipefail
        /usr/bin/docker run --rm \
          --workdir "$PWD" \
          -v /home/runner/work:/home/runner/work \
          -v /home/runner/.docker-cargo/registry:/root/.cargo/registry \
          -v /home/runner/.docker-cargo/git:/root/.cargo/git \
          -e GITHUB_STEP_SUMMARY -e GITHUB_OUTPUT -e GITHUB_WORKSPACE \
          -e CI -e GITHUB_ACTIONS -e GITHUB_ACTOR -e GITHUB_REPOSITORY -e GITHUB_SHA -e GITHUB_REF -e GITHUB_EVENT_NAME \
          -e TOOLCHAIN -e CRATE -e TARGET -e FEATURE_PROFILE \
          -e RUSTFLAGS -e RUSTDOCFLAGS -e MIRIFLAGS \
          -e CARGO_NET_RETRY -e RUSTUP_MAX_RETRIES \
          -e ZC_NIGHTLY_RUSTFLAGS -e ZC_NIGHTLY_MIRIFLAGS \
          -e GIT_CONFIG_COUNT=1 \
          -e GIT_CONFIG_KEY_0=safe.directory \
          -e "GIT_CONFIG_VALUE_0=*" \
          --entrypoint /bin/bash \
          -- \
          "$ZC_CI_IMAGE" \
          --noprofile \
          --norc \
          -p \
          ./cargo.sh ci execute-build-cell \
          --event "$GITHUB_EVENT_NAME" \
          --package "$CRATE" \
          --toolchain "$TOOLCHAIN" \
          --feature-profile "$FEATURE_PROFILE" \
          --target "$TARGET"
  miri:
    if: needs.plan_ci.outputs.miri_enabled == 'true'
    runs-on: ubuntu-latest
    needs: [build_docker_env, plan_ci]
    permissions:
      contents: read
    strategy:
      fail-fast: false
      matrix: ${{ fromJSON(needs.plan_ci.outputs.miri_matrix) }}
    name: Miri (${{ matrix.crate }} / ${{ matrix.toolchain }} / ${{ matrix.feature_profile }} / ${{ matrix.miri_model }} / ${{ matrix.target }})
    steps:
    - *matrix_checkout
    - *download_ci_image
    - *load_ci_image
    - name: Execute checked Miri cell
      shell: /usr/bin/env -u BASH_ENV -u ENV -u SHELLOPTS -u BASHOPTS /bin/bash --noprofile --norc -p -euo pipefail -- {0}
      working-directory: zerocopy
      env:
        TOOLCHAIN: ${{ matrix.toolchain }}
        CRATE: ${{ matrix.crate }}
        FEATURE_PROFILE: ${{ matrix.feature_profile }}
        TARGET: ${{ matrix.target }}
        MIRI_MODEL: ${{ matrix.miri_model }}
      run: |
        set -euo pipefail
        /usr/bin/docker run --rm \
          --workdir "$PWD" \
          -v /home/runner/work:/home/runner/work \
          -v /home/runner/.docker-cargo/registry:/root/.cargo/registry \
          -v /home/runner/.docker-cargo/git:/root/.cargo/git \
          -e GITHUB_STEP_SUMMARY -e GITHUB_OUTPUT -e GITHUB_WORKSPACE \
          -e CI -e GITHUB_ACTIONS -e GITHUB_ACTOR -e GITHUB_REPOSITORY -e GITHUB_SHA -e GITHUB_REF -e GITHUB_EVENT_NAME \
          -e TOOLCHAIN -e CRATE -e TARGET -e FEATURE_PROFILE -e MIRI_MODEL \
          -e RUSTFLAGS -e RUSTDOCFLAGS -e MIRIFLAGS \
          -e CARGO_NET_RETRY -e RUSTUP_MAX_RETRIES \
          -e ZC_NIGHTLY_RUSTFLAGS -e ZC_NIGHTLY_MIRIFLAGS \
          -e GIT_CONFIG_COUNT=1 \
          -e GIT_CONFIG_KEY_0=safe.directory \
          -e "GIT_CONFIG_VALUE_0=*" \
          --entrypoint /bin/bash \
          -- \
          "$ZC_CI_IMAGE" \
          --noprofile \
          --norc \
          -p \
          ./cargo.sh ci execute-miri-cell \
          --event "$GITHUB_EVENT_NAME" \
          --package "$CRATE" \
          --toolchain "$TOOLCHAIN" \
          --feature-profile "$FEATURE_PROFILE" \
          --target "$TARGET" \
          --miri-model "$MIRI_MODEL"
  next_job:
    runs-on: ubuntu-latest
"#;

    fn audit_source(
        source: &str,
        reviewed: &BTreeSet<(String, String)>,
    ) -> Result<(), super::super::PlannedAdapterViolations> {
        audit_feature(source, |lines, errors| audit(lines, reviewed, errors))
    }

    fn audit_canonical(source: &str) -> Result<(), super::super::PlannedAdapterViolations> {
        audit_source(source, &canonical_planned_jobs())
    }

    fn rejected(label: &str, source: &str, expected: &str) {
        assert_rejected(label, audit_canonical(source), expected);
    }

    fn replace_in_step(source: &str, marker: &str, from: &str, to: &str) -> String {
        let start =
            source.find(marker).unwrap_or_else(|| panic!("missing fixture step marker {marker:?}"));
        let remainder = &source[start + marker.len()..];
        let end = remainder
            .find("\n    - ")
            .map(|offset| start + marker.len() + offset + 1)
            .unwrap_or(source.len());
        let block = &source[start..end];
        assert!(block.contains(from), "step {marker:?} did not contain {from:?}");
        format!("{}{}{}", &source[..start], block.replacen(from, to, 1), &source[end..])
    }

    struct TemporaryRepository {
        directory: PathBuf,
        root: PathBuf,
    }

    impl TemporaryRepository {
        fn new(label: &str) -> Self {
            static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
            let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir()
                .join(format!("zerocopy-planned-matrix-{label}-{}-{unique}", process::id()));
            let root = directory.join("repository");
            fs::create_dir_all(&root).unwrap();
            let root = root.canonicalize().unwrap();
            Self { directory, root }
        }

        fn action_path(&self) -> PathBuf {
            self.root.join(DOWNLOAD_ACTION_PATH)
        }

        fn write_action(&self, source: &str) {
            let action = self.action_path();
            fs::create_dir_all(action.parent().unwrap()).unwrap();
            fs::write(action, source).unwrap();
        }
    }

    impl Drop for TemporaryRepository {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.directory).unwrap();
        }
    }

    #[test]
    fn accepts_the_literal_fixture_and_live_workflow() {
        audit_canonical(CANONICAL_SOURCE).unwrap();

        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap();
        let reviewed = ReviewedWorkflowJobs::read(root.join(WORKFLOW_REGISTRY_PATH)).unwrap();
        audit_planned_adapter(&root, &reviewed).unwrap();
    }

    #[test]
    fn matrix_setup_definitions_are_exact_and_yaml_comments_remain_free() {
        for (step_name, step) in [
            ("checkout", CHECKOUT_STEP),
            ("download", DOWNLOAD_IMAGE_STEP),
            ("load", LOAD_IMAGE_STEP),
        ] {
            for line in step {
                let changed = format!("{line} unexpected");
                let source = replace_in_step(CANONICAL_SOURCE, step[0], line, &changed);
                rejected(&format!("{step_name}: {line}"), &source, "exact canonical contract");
            }
        }

        let comments = replace_in_job(
            CANONICAL_SOURCE,
            BUILD_JOB,
            "    - &download_ci_image\n",
            "    - &download_ci_image\n      # The source audit intentionally ignores documentation.\n",
        );
        audit_canonical(&comments).unwrap();

        let scalar_comment = replace_in_step(
            CANONICAL_SOURCE,
            LOAD_IMAGE_STEP[0],
            "        set -euo pipefail\n",
            "        set -euo pipefail\n        # ${{ github.event.pull_request.title }}\n",
        );
        rejected("run scalar comment", &scalar_comment, "exact canonical contract");
    }

    #[test]
    fn matrix_step_sequences_and_miri_aliases_are_exact() {
        let cases = [
            (
                "build step before checkout",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "    - &matrix_checkout\n",
                    "    - name: Unexpected setup\n      run: true\n    - &matrix_checkout\n",
                ),
            ),
            (
                "build anchor renamed",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "    - &matrix_checkout\n",
                    "    - &wrong_anchor\n",
                ),
            ),
            (
                "Miri setup reordered",
                replace_in_job(
                    CANONICAL_SOURCE,
                    MIRI_JOB,
                    "    - *matrix_checkout\n    - *download_ci_image\n",
                    "    - *download_ci_image\n    - *matrix_checkout\n",
                ),
            ),
            (
                "Miri alias renamed",
                replace_in_job(
                    CANONICAL_SOURCE,
                    MIRI_JOB,
                    "    - *download_ci_image\n",
                    "    - *other_download\n",
                ),
            ),
            (
                "Miri alias extended",
                replace_in_job(
                    CANONICAL_SOURCE,
                    MIRI_JOB,
                    "    - *load_ci_image\n",
                    "    - *load_ci_image\n      if: success()\n",
                ),
            ),
            (
                "Miri setup inserted",
                replace_in_job(
                    CANONICAL_SOURCE,
                    MIRI_JOB,
                    "    - *matrix_checkout\n",
                    "    - *matrix_checkout\n    - name: Unexpected setup\n      run: true\n",
                ),
            ),
        ];
        for (label, source) in cases {
            rejected(label, &source, ".steps");
        }
    }

    #[test]
    fn matrix_anchor_names_cannot_be_redefined_or_reused_elsewhere() {
        for (label, addition, expected) in [
            (
                "second checkout definition",
                "    steps:\n    - &matrix_checkout\n      run: echo replacement\n",
                "exactly one definition",
            ),
            (
                "second downloader alias",
                "    steps:\n    - *download_ci_image\n",
                "exactly one alias",
            ),
        ] {
            let source = CANONICAL_SOURCE.replace(
                "  next_job:\n    runs-on: ubuntu-latest\n",
                &format!("  next_job:\n    runs-on: ubuntu-latest\n{addition}"),
            );
            rejected(label, &source, expected);
        }

        let comments = format!(
            "# &matrix_checkout and *download_ci_image are documentation.\n{CANONICAL_SOURCE}"
        );
        audit_canonical(&comments).unwrap();
    }

    #[test]
    fn local_download_action_rejects_file_command_channel_mentions() {
        let documented_channels = r#"# GITHUB_ENV and GITHUB_PATH are forbidden here.
runs:
  using: composite
  steps:
    # A nested comment may also mention GITHUB_ENV.
    - shell: bash
      run: echo download only
"#;
        audit_download_action_source(documented_channels).unwrap();
        audit_download_action_source(
            "runs:\n  using: composite\n  xNOT_GITHUB_ENV_SUFFIX: documentation\n",
        )
        .unwrap();

        let expression_comment = "runs:\n  using: composite\n  steps:\n    - shell: bash\n      run: |\n        # ${{ github.event.pull_request.title }}\n        true\n";
        let error = audit_download_action_source(expression_comment).unwrap_err().to_string();
        assert!(error.contains("Actions expressions"), "{error}");

        for (channel, source) in [
            (
                "GITHUB_ENV",
                "runs:\n  using: composite\n  steps:\n    - run: echo 'RUSTC_WRAPPER=other' >> \"$GITHUB_ENV\"\n",
            ),
            (
                "GITHUB_PATH",
                "runs:\n  using: composite\n  steps:\n    - env:\n        FILE_COMMAND: ${{ env.GITHUB_PATH }}\n",
            ),
            (
                "GITHUB_ENV",
                "runs:\n  using: composite # GITHUB_ENV is not a full-line comment\n",
            ),
        ] {
            let error = audit_download_action_source(source).unwrap_err().to_string();
            assert!(error.contains(DOWNLOAD_ACTION_PATH), "{channel}: {error}");
            assert!(error.contains(channel), "{channel}: {error}");
        }

        let crlf = documented_channels.replace('\n', "\r\n");
        let error = audit_download_action_source(&crlf).unwrap_err().to_string();
        assert!(error.contains("canonical LF"), "{error}");
    }

    #[test]
    fn local_download_action_read_normalizes_crlf_but_rejects_bare_cr() {
        let repository = TemporaryRepository::new("line-endings");
        repository.write_action("runs:\r\n  using: composite\r\n  steps: []\r\n");
        let source = read_download_action(&repository.root).unwrap();
        assert_eq!(source, "runs:\n  using: composite\n  steps: []\n");
        audit_download_action_source(&source).unwrap();

        repository.write_action("runs:\r  using: composite\n");
        let error = read_download_action(&repository.root).unwrap_err();
        assert!(matches!(error, super::super::PlannedAdapterAuditError::ReadLocalAction { .. }));
        assert!(error.to_string().contains("bare carriage return"), "{error}");
    }

    #[test]
    fn local_download_action_must_be_a_regular_file() {
        let missing = TemporaryRepository::new("missing");
        let error = read_download_action(&missing.root).unwrap_err();
        assert!(matches!(error, super::super::PlannedAdapterAuditError::InspectLocalAction { .. }));

        let repository = TemporaryRepository::new("not-file");
        fs::create_dir_all(repository.action_path()).unwrap();
        let error = read_download_action(&repository.root).unwrap_err();
        assert!(matches!(error, super::super::PlannedAdapterAuditError::LocalActionNotFile { .. }));
    }

    #[cfg(unix)]
    #[test]
    fn local_download_action_cannot_escape_through_file_or_ancestor_symlinks() {
        use std::os::unix::fs::symlink;

        for escape in ["file", "ancestor"] {
            let repository = TemporaryRepository::new(escape);
            let outside = repository.directory.join("outside");
            fs::create_dir_all(&outside).unwrap();
            let outside_action = if escape == "file" {
                outside.join("action.yml")
            } else {
                outside.join("download-artifact-with-retry/action.yml")
            };
            fs::create_dir_all(outside_action.parent().unwrap()).unwrap();
            fs::write(&outside_action, "runs:\n  using: composite\n  steps: []\n").unwrap();

            if escape == "file" {
                fs::create_dir_all(repository.action_path().parent().unwrap()).unwrap();
                symlink(&outside_action, repository.action_path()).unwrap();
            } else {
                fs::create_dir_all(repository.root.join(".github")).unwrap();
                symlink(&outside, repository.root.join(".github/actions")).unwrap();
            }

            let error = read_download_action(&repository.root).unwrap_err();
            assert!(
                matches!(
                    error,
                    super::super::PlannedAdapterAuditError::LocalActionOutsideRepository { .. }
                ),
                "{escape}: {error:?}"
            );
        }
    }

    #[test]
    fn reviewed_planned_roles_equal_all_three_typed_plan_consumers() {
        let mut missing = canonical_planned_jobs();
        missing.remove(&(WORKFLOW_PATH.to_owned(), BUILD_JOB.to_owned()));
        assert_rejected(
            "missing build role",
            audit_source(CANONICAL_SOURCE, &missing),
            "must have the reviewed `planned` role",
        );

        let mut missing = canonical_planned_jobs();
        missing.remove(&(WORKFLOW_PATH.to_owned(), SEMVER_JOB.to_owned()));
        assert_rejected(
            "missing standalone semver role",
            audit_source(CANONICAL_SOURCE, &missing),
            "must have the reviewed `planned` role",
        );

        let mut extra = canonical_planned_jobs();
        extra.insert((WORKFLOW_PATH.to_owned(), "surprise".to_owned()));
        assert_rejected(
            "extra planned role",
            audit_source(CANONICAL_SOURCE, &extra),
            "no planned-job workflow audit",
        );
    }

    #[test]
    fn matrix_jobs_reject_concurrency_and_require_exact_strategies() {
        let cases = [
            (
                "build fail-fast",
                replace_in_job(CANONICAL_SOURCE, BUILD_JOB, "fail-fast: false", "fail-fast: true"),
                ".strategy.fail-fast",
            ),
            (
                "missing fail-fast",
                replace_in_job(CANONICAL_SOURCE, BUILD_JOB, "      fail-fast: false\n", ""),
                ".strategy.fail-fast",
            ),
            (
                "latency serialization",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "      fail-fast: false\n",
                    "      fail-fast: false\n      max-parallel: 1\n",
                ),
                ".strategy.max-parallel",
            ),
            (
                "job-level serialization",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "    strategy:\n",
                    "    concurrency: one-at-a-time\n    strategy:\n",
                ),
                ".concurrency",
            ),
            (
                "wrong build matrix",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "outputs.build_matrix",
                    "outputs.miri_matrix",
                ),
                ".strategy.matrix",
            ),
            (
                "wrong Miri matrix",
                replace_in_job(
                    CANONICAL_SOURCE,
                    MIRI_JOB,
                    "outputs.miri_matrix",
                    "outputs.build_matrix",
                ),
                ".strategy.matrix",
            ),
            (
                "scalar strategy",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "    strategy:\n",
                    "    strategy: fast\n",
                ),
                "canonical nested mapping",
            ),
        ];
        for (label, source, expected) in cases {
            rejected(label, &source, expected);
        }
    }

    #[test]
    fn matrix_jobs_require_the_planner_gate_and_exact_host_contract() {
        let cases = [
            (
                "build dependency",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "[build_docker_env, plan_ci]",
                    "build_docker_env",
                ),
                "must depend directly",
            ),
            (
                "Miri dependency",
                replace_in_job(
                    CANONICAL_SOURCE,
                    MIRI_JOB,
                    "[build_docker_env, plan_ci]",
                    "build_docker_env",
                ),
                "must depend directly",
            ),
            (
                "extra dependency",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "[build_docker_env, plan_ci]",
                    "[build_docker_env, plan_ci, surprise]",
                ),
                "unexpected direct dependency `surprise`",
            ),
            (
                "build condition",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "    runs-on: ubuntu-latest\n",
                    "    if: success()\n    runs-on: ubuntu-latest\n",
                ),
                ".if",
            ),
            (
                "Miri condition",
                replace_in_job(
                    CANONICAL_SOURCE,
                    MIRI_JOB,
                    "miri_enabled == 'true'",
                    "miri_enabled == 'false'",
                ),
                ".if",
            ),
            (
                "changed runner",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "runs-on: ubuntu-latest",
                    "runs-on: self-hosted",
                ),
                ".runs-on",
            ),
            (
                "job container",
                replace_in_job(
                    CANONICAL_SOURCE,
                    MIRI_JOB,
                    "    runs-on: ubuntu-latest\n",
                    "    runs-on: ubuntu-latest\n    container: ignored.invalid/noop\n",
                ),
                ".container",
            ),
            (
                "continue on error",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "    runs-on: ubuntu-latest\n",
                    "    runs-on: ubuntu-latest\n    continue-on-error: true\n",
                ),
                ".continue-on-error",
            ),
        ];
        for (label, source, expected) in cases {
            rejected(label, &source, expected);
        }
    }

    #[test]
    fn matrix_job_fields_permissions_names_and_defaults_are_exact() {
        let additions = [
            ("concurrency", "    concurrency: one-at-a-time\n"),
            ("environment", "    environment: protected\n"),
            ("env", "    env:\n      SURPRISE: value\n"),
            ("services", "    services: {}\n"),
            ("timeout-minutes", "    timeout-minutes: 1\n"),
            ("uses", "    uses: example.invalid/owner/workflow@main\n"),
            ("with", "    with: {}\n"),
            ("secrets", "    secrets: inherit\n"),
        ];
        for expected in [BUILD_EXPECTATION, MIRI_EXPECTATION] {
            for (field, addition) in additions {
                let source = replace_in_job(
                    CANONICAL_SOURCE,
                    expected.job_name,
                    "    runs-on: ubuntu-latest\n",
                    &format!("    runs-on: ubuntu-latest\n{addition}"),
                );
                rejected(
                    &format!("{} {field}", expected.job_name),
                    &source,
                    &format!("{}.{field}", expected.job_name),
                );
            }
        }

        let cases = [
            (
                "build display name",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    BUILD_DISPLAY_NAME,
                    "Build something",
                ),
                "build_test.name",
            ),
            (
                "Miri display omits toolchain",
                replace_in_job(
                    CANONICAL_SOURCE,
                    MIRI_JOB,
                    MIRI_DISPLAY_NAME,
                    "Miri (${{ matrix.crate }} / ${{ matrix.feature_profile }} / ${{ matrix.miri_model }} / ${{ matrix.target }})",
                ),
                "miri.name",
            ),
            (
                "write permission",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "      contents: read",
                    "      contents: write",
                ),
                "build_test.permissions.contents",
            ),
            (
                "extra permission",
                replace_in_job(
                    CANONICAL_SOURCE,
                    MIRI_JOB,
                    "      contents: read\n",
                    "      contents: read\n      id-token: write\n",
                ),
                "miri.permissions.id-token",
            ),
            (
                "build defaults",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "    strategy:\n",
                    "    defaults: {}\n    strategy:\n",
                ),
                "build_test.defaults",
            ),
            (
                "Miri defaults",
                replace_in_job(
                    CANONICAL_SOURCE,
                    MIRI_JOB,
                    "    permissions:\n",
                    "    defaults: {}\n    permissions:\n",
                ),
                "miri.defaults",
            ),
        ];
        for (label, source, expected) in cases {
            rejected(label, &source, expected);
        }
    }

    #[test]
    fn executor_names_are_unique_only_inside_their_job_steps_mapping() {
        let duplicate_mapping = replace_in_job(
            CANONICAL_SOURCE,
            BUILD_JOB,
            "    steps:\n",
            "    steps: []\n    steps:\n",
        );
        rejected("duplicate steps", &duplicate_mapping, ".steps");

        let duplicate_step = replace_in_job(
            CANONICAL_SOURCE,
            BUILD_JOB,
            "    - name: Execute checked build cell\n",
            "    - name: Execute checked build cell\n      run: echo unrelated\n    - name: Execute checked build cell\n",
        );
        rejected("duplicate step", &duplicate_step, "inside `build_test.steps`");

        let same_name_elsewhere = CANONICAL_SOURCE.replace(
            "  next_job:\n    runs-on: ubuntu-latest\n",
            "  next_job:\n    runs-on: ubuntu-latest\n    steps:\n    - name: Execute checked build cell\n      run: echo unrelated\n",
        );
        audit_canonical(&same_name_elsewhere).unwrap();
    }

    #[test]
    fn selector_environments_are_exact_for_each_matrix_role() {
        for expected in [BUILD_EXPECTATION, MIRI_EXPECTATION] {
            for selector in expected.selectors {
                let canonical = format!(
                    "{}: ${{{{ matrix.{} }}}}",
                    selector.environment_name, selector.matrix_field_name
                );
                let changed = format!("{}: ${{{{ matrix.wrong }}}}", selector.environment_name);
                let source =
                    replace_in_job(CANONICAL_SOURCE, expected.job_name, &canonical, &changed);
                rejected(selector.environment_name, &source, ".env.");
            }
        }
    }

    #[test]
    fn both_executor_shells_reject_startup_influence() {
        let mut replacements = vec!["bash".to_owned(), TRUSTED_SHELL.replace(" -p ", " ")];
        for variable in ["BASH_ENV", "ENV", "SHELLOPTS", "BASHOPTS"] {
            replacements.push(TRUSTED_SHELL.replace(&format!("-u {variable} "), ""));
        }
        for expected in [BUILD_EXPECTATION, MIRI_EXPECTATION] {
            for replacement in &replacements {
                let source = replace_in_job(
                    CANONICAL_SOURCE,
                    expected.job_name,
                    &format!("shell: {TRUSTED_SHELL}"),
                    &format!("shell: {replacement}"),
                );
                rejected(expected.job_name, &source, ".fields.shell");
            }
        }
    }

    #[test]
    fn executor_runs_enforce_absolute_docker_and_container_bash_invariants() {
        let cases = [
            (BUILD_JOB, "/usr/bin/docker run --rm", "docker run --rm", "absolute Docker"),
            (BUILD_JOB, "--entrypoint /bin/bash", "--entrypoint /bin/sh", "entrypoint"),
            (BUILD_JOB, "          -- \\\n", "", "option terminator"),
            (MIRI_JOB, "          --noprofile \\\n", "", "no profile"),
            (MIRI_JOB, "          --norc \\\n", "", "no rc"),
            (MIRI_JOB, "          -p \\\n", "", "privileged child"),
            (
                BUILD_JOB,
                "-e TOOLCHAIN -e CRATE -e TARGET -e FEATURE_PROFILE \\",
                "-e TOOLCHAIN -e CRATE -e TARGET -e FEATURE_PROFILE -e MIRI_MODEL \\",
                "build forwarding",
            ),
            (
                MIRI_JOB,
                "-e TOOLCHAIN -e CRATE -e TARGET -e FEATURE_PROFILE -e MIRI_MODEL \\",
                "-e TOOLCHAIN -e CRATE -e TARGET -e FEATURE_PROFILE \\",
                "Miri forwarding",
            ),
            (
                BUILD_JOB,
                "-e GITHUB_STEP_SUMMARY -e GITHUB_OUTPUT -e GITHUB_WORKSPACE \\",
                "-e GITHUB_ENV -e GITHUB_STEP_SUMMARY -e GITHUB_OUTPUT -e GITHUB_WORKSPACE \\",
                "host environment file command",
            ),
            (
                MIRI_JOB,
                "-e GITHUB_STEP_SUMMARY -e GITHUB_OUTPUT -e GITHUB_WORKSPACE \\",
                "-e GITHUB_PATH -e GITHUB_STEP_SUMMARY -e GITHUB_OUTPUT -e GITHUB_WORKSPACE \\",
                "host PATH file command",
            ),
            (BUILD_JOB, EXECUTE_BUILD_CELL_COMMAND, "wrong-build-command", "build command"),
            (MIRI_JOB, EXECUTE_MIRI_CELL_COMMAND, "wrong-miri-command", "Miri command"),
        ];
        for (job, from, to, label) in cases {
            let source = replace_in_job(CANONICAL_SOURCE, job, from, to);
            rejected(label, &source, ".run");
        }
    }

    #[test]
    fn every_executor_run_line_is_load_bearing() {
        for expected in [BUILD_EXPECTATION, MIRI_EXPECTATION] {
            for line in executor_run(expected) {
                let changed = if line.contains(expected.executor_command) {
                    line.replace(expected.executor_command, "wrong-command")
                } else if line == "set -euo pipefail" {
                    "set -eo pipefail".to_owned()
                } else if line.contains('"') {
                    line.replacen('"', "", 1)
                } else if let Some(line) = line.strip_suffix(" \\") {
                    line.to_owned()
                } else {
                    format!("{line} --unexpected")
                };
                let marker = format!("    - name: {}", expected.executor_step_name);
                let source = replace_in_step(CANONICAL_SOURCE, &marker, &line, &changed);
                rejected(&line, &source, ".run");
            }
        }
    }

    #[test]
    fn executor_commands_are_globally_unique_and_comments_are_not_runs() {
        let duplicate = replace_in_job(
            CANONICAL_SOURCE,
            MIRI_JOB,
            "    steps:\n",
            &format!("    steps:\n    - run: ./cargo.sh ci {EXECUTE_BUILD_CELL_COMMAND}\n"),
        );
        rejected("duplicate build command", &duplicate, "command mention");

        let comment = format!(
            "# ./cargo.sh ci {EXECUTE_BUILD_CELL_COMMAND}\n# ./cargo.sh ci {EXECUTE_MIRI_CELL_COMMAND}\n{CANONICAL_SOURCE}"
        );
        audit_canonical(&comment).unwrap();
    }
}
