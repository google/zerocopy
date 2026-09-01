// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exact consumption and execution audit for typed build and Miri matrices.

use std::collections::{BTreeMap, BTreeSet};
#[cfg(test)]
use std::path::Path;

use super::{
    reviewed_source::ReviewedSource,
    source::{
        audit_exact_job_fields, audit_exact_scalar_field, audit_host_job_contract,
        audit_read_permissions, audit_step, audit_unique_run_mentions, audited_steps_block,
        compare_map, escape_control_characters, exact_step_lines, find_job, job_field_location,
        job_fields, nested_fields, nested_mapping, parse_needs, unique_field, RunForm,
        StepExpectation,
    },
    ViolationSink,
};
#[cfg(test)]
use super::{
    reviewed_source::{audit_exact_source, audit_reviewed_sources, read_reviewed_source},
    PlannedAdapterAuditError, PlannedAdapterViolations,
};
use crate::{
    workflow::WORKFLOW_REGISTRY_PATH,
    workflow_protocol::{
        image_artifact_consumer_line, BUILD_JOB, BUILD_MATRIX_OUTPUT, BUILD_STEP_NAME,
        CELL_FEATURE_PROFILE_OPTION, CELL_MIRI_MODEL_OPTION, CELL_PACKAGE_OPTION,
        CELL_TARGET_OPTION, CELL_TOOLCHAIN_OPTION, CI_EVENT_OPTION, DOCKER_ENTRYPOINT_ARGUMENT,
        DOCKER_OPTION_TERMINATOR, EXECUTE_BUILD_CELL_COMMAND, EXECUTE_MIRI_CELL_COMMAND,
        HOST_DOCKER_RUN, IMAGE_JOB, MATRIX_STEP_ANCHORS, MIRI_ENABLED_OUTPUT, MIRI_JOB,
        MIRI_MATRIX_OUTPUT, MIRI_STEP_NAME, PLAN_JOB, REPOSITORY_WORKING_DIRECTORY, TRUSTED_SHELL,
        WORKFLOW_PATH,
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
    run_defaults: Option<RunDefaultsExpectation>,
}

#[derive(Clone, Copy)]
struct RunDefaultsExpectation {
    shell: &'static str,
    working_directory: &'static str,
}

const DOWNLOAD_ACTION_PATH: &str = ".github/actions/download-artifact-with-retry/action.yml";
const DOWNLOAD_ACTION_SNAPSHOT_PATH: &str =
    "tools/zc/testdata/download-artifact-with-retry.action.yml";
// A local `uses` path executes mutable code from the checkout. Keep this
// independent snapshot's complete normalized source coordinated with the
// action above. Any functional or documentary edit must update both
// deliberately, which makes the action's complete pre-executor authority
// visible in the matrix-audit review rather than trying to blacklist
// particular shell forms.
const DOWNLOAD_ACTION_EXPECTED_SOURCE: &str =
    include_str!("../../testdata/download-artifact-with-retry.action.yml");
const REVIEWED_SOURCES: &[ReviewedSource] = &[ReviewedSource {
    live_path: DOWNLOAD_ACTION_PATH,
    snapshot_path: DOWNLOAD_ACTION_SNAPSHOT_PATH,
    expected: DOWNLOAD_ACTION_EXPECTED_SOURCE,
}];
const BUILD_JOB_FIELDS: &[&str] =
    &["runs-on", "needs", "permissions", "defaults", "strategy", "name", "steps"];
const MIRI_JOB_FIELDS: &[&str] =
    &["if", "runs-on", "needs", "permissions", "strategy", "name", "steps"];
const BUILD_DEFAULT_SHELL: &str = "/tmp/docker-shell.sh {0} # zizmor: ignore[misfeature] (CI intentionally routes build matrix commands through the prebuilt Docker image)";
const BUILD_DISPLAY_NAME: &str = "Build & Test (${{ matrix.crate }} / ${{ matrix.toolchain }} / ${{ matrix.feature_profile }} / ${{ matrix.target }})";
const MIRI_DISPLAY_NAME: &str = "Miri (${{ matrix.crate }} / ${{ matrix.toolchain }} / ${{ matrix.feature_profile }} / ${{ matrix.miri_model }} / ${{ matrix.target }})";

// The build job owns the setup definitions used by both typed matrix jobs.
// Their exact source is part of the execution boundary: a preceding step can
// otherwise alter the checkout, selected image, or process environment before
// an exactly audited executor runs. Keep these definitions coordinated with
// the corresponding steps and anchors in `.github/workflows/ci.yml`.
//
// YAML comments outside a run block may change freely. Comments inside a run
// block are shell input, so `exact_step_lines` retains them and the constants
// below include them. The repository-owned downloader receives a separate
// source audit because its local `uses` path cannot pin its implementation.
const CHECKOUT_STEP: &[&str] = &[
    "    - &matrix_checkout",
    "      uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1",
    "      with:",
    "        fetch-depth: 2",
    "        persist-credentials: false",
];
fn download_image_step() -> Vec<String> {
    vec![
        "    - &download_ci_image".to_owned(),
        "      name: Download prebuilt Docker image".to_owned(),
        "      uses: ./.github/actions/download-artifact-with-retry".to_owned(),
        "      with:".to_owned(),
        image_artifact_consumer_line(),
        "        path: ${{ runner.temp }}".to_owned(),
        "        expected-file: ${{ env.ZC_CI_IMAGE_ARCHIVE }}".to_owned(),
    ]
}
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
const CREATE_DOCKER_SHELL_STEP: &[&str] = &[
    "    - name: Create Docker Shell Wrapper",
    "      shell: bash",
    "      run: |",
    "        set -eo pipefail",
    "        mkdir -p /home/runner/.docker-cargo/registry /home/runner/.docker-cargo/git",
    "        cat << 'EOF' > /tmp/docker-shell.sh",
    "        #!/bin/bash",
    "        # Boot an ephemeral container for the step, mounting the workspace and",
    "        # temp dirs. Explicitly forward GitHub Actions internal state and matrix",
    "        # environment variables.",
    "        docker run --rm -i \\",
    "          --workdir \"$PWD\" \\",
    "          -v /home/runner/work:/home/runner/work \\",
    "          -v /home/runner/.docker-cargo/registry:/root/.cargo/registry \\",
    "          -v /home/runner/.docker-cargo/git:/root/.cargo/git \\",
    "          -e GITHUB_ENV -e GITHUB_PATH -e GITHUB_STEP_SUMMARY -e GITHUB_OUTPUT -e GITHUB_WORKSPACE \\",
    "          -e CI -e GITHUB_ACTIONS -e GITHUB_ACTOR -e GITHUB_REPOSITORY -e GITHUB_SHA -e GITHUB_REF -e GITHUB_EVENT_NAME \\",
    "          -e TOOLCHAIN -e CRATE -e TARGET -e FEATURE_PROFILE \\",
    "          -e MIRI_MODEL -e ZC_TOOLCHAIN -e PR_HEAD_SHA \\",
    "          -e RUSTFLAGS -e RUSTDOCFLAGS -e MIRIFLAGS \\",
    "          -e CARGO_NET_RETRY -e RUSTUP_MAX_RETRIES \\",
    "          -e ZC_NIGHTLY_RUSTFLAGS -e ZC_NIGHTLY_MIRIFLAGS \\",
    "          -e ZC_SKIP_CARGO_SEMVER_CHECKS \\",
    "          \"$ZC_CI_IMAGE\" bash -c \"git config --global --add safe.directory '*' && exec bash -e -o pipefail \\\"\\$1\\\"\" -- \"$1\"",
    "        EOF",
    "        chmod +x /tmp/docker-shell.sh",
];
const VERIFY_CHECKOUT_STEP: &[&str] = &[
    "    - &verify_matrix_checkout",
    "      name: Verify matrix checkout is unchanged",
    TRUSTED_SHELL_LINE,
    "      env:",
    "        EXPECTED_COMMIT: ${{ github.sha }}",
    "      run: |",
    "        set -euo pipefail",
    "        builtin cd -- \"$GITHUB_WORKSPACE\"",
    "        readonly -a source_git=(",
    "          /usr/bin/env -i",
    "          GIT_CONFIG_GLOBAL=/dev/null",
    "          GIT_CONFIG_NOSYSTEM=1",
    "          GIT_NO_REPLACE_OBJECTS=1",
    "          HOME=/dev/null",
    "          PATH=/usr/bin:/bin",
    "          /usr/bin/git",
    "          \"--git-dir=$GITHUB_WORKSPACE/.git\"",
    "          \"--work-tree=$GITHUB_WORKSPACE\"",
    "        )",
    "        actual_commit=\"$(\"${source_git[@]}\" rev-parse --verify HEAD^{commit})\"",
    "        if [[ \"$actual_commit\" != \"$EXPECTED_COMMIT\" ]]; then",
    "          printf 'Expected checkout commit %s, found %s\\n' \\",
    "            \"$EXPECTED_COMMIT\" \"$actual_commit\" >&2",
    "          exit 1",
    "        fi",
    "        # Do not trust the checkout's mutable index, local Git config, or",
    "        # attributes. Build a temporary repository whose object store is the",
    "        # checkout's content-addressed store, whose index comes from the",
    "        # expected commit, and whose attributes also come from that commit.",
    "        verification_directory=\"$(",
    "          /usr/bin/mktemp -d \"$RUNNER_TEMP/matrix-checkout.XXXXXX\"",
    "        )\"",
    "        readonly verification_directory",
    "        trap '/usr/bin/rm -rf -- \"$verification_directory\"' EXIT",
    "        /usr/bin/env -i \\",
    "          GIT_CONFIG_GLOBAL=/dev/null \\",
    "          GIT_CONFIG_NOSYSTEM=1 \\",
    "          HOME=/dev/null \\",
    "          PATH=/usr/bin:/bin \\",
    "          /usr/bin/git init --quiet --initial-branch=verified \\",
    "            \"$verification_directory/repository\"",
    "        readonly -a trusted_git=(",
    "          /usr/bin/env -i",
    "          GIT_ATTR_NOSYSTEM=1",
    "          \"GIT_ATTR_SOURCE=$EXPECTED_COMMIT\"",
    "          GIT_CONFIG_GLOBAL=/dev/null",
    "          GIT_CONFIG_NOSYSTEM=1",
    "          \"GIT_INDEX_FILE=$verification_directory/index\"",
    "          GIT_NO_REPLACE_OBJECTS=1",
    "          \"GIT_OBJECT_DIRECTORY=$GITHUB_WORKSPACE/.git/objects\"",
    "          HOME=/dev/null",
    "          PATH=/usr/bin:/bin",
    "          /usr/bin/git",
    "          \"--git-dir=$verification_directory/repository/.git\"",
    "          \"--work-tree=$GITHUB_WORKSPACE\"",
    "          -c core.filemode=true",
    "          -c core.fsmonitor=false",
    "          -c core.ignoreCase=false",
    "          -c core.sparseCheckout=false",
    "          -c core.symlinks=true",
    "          -c core.untrackedCache=false",
    "        )",
    "        \"${trusted_git[@]}\" update-ref HEAD \"$EXPECTED_COMMIT\"",
    "        \"${trusted_git[@]}\" read-tree \"$EXPECTED_COMMIT\"",
    "        checkout_status=\"$(",
    "          \"${trusted_git[@]}\" status \\",
    "            --porcelain=v1 --untracked-files=all --ignored=matching -- \\",
    "            . ':(exclude).git'",
    "        )\"",
    "        if [[ -n \"$checkout_status\" ]]; then",
    "          printf 'Matrix setup modified the checkout:\\n%s\\n' \\",
    "            \"$checkout_status\" >&2",
    "          exit 1",
    "        fi",
];

const TRUSTED_SHELL_LINE: &str = "      shell: /usr/bin/env -u BASH_ENV -u ENV -u SHELLOPTS -u BASHOPTS /bin/bash --noprofile --norc -p -euo pipefail -- {0}";

const BUILD_STEP_MARKERS: &[&str] = &[
    "- &matrix_checkout",
    "- &download_ci_image",
    "- &load_ci_image",
    "- name: Create Docker Shell Wrapper",
    "- &verify_matrix_checkout",
    "- name: Execute checked build cell",
    "- name: Prepare cargo-semver-checks",
    "- name: Check semver compatibility",
];
const MIRI_STEP_MARKERS: &[&str] = &[
    "- *matrix_checkout",
    "- *download_ci_image",
    "- *load_ci_image",
    "- *verify_matrix_checkout",
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
    run_defaults: Some(RunDefaultsExpectation {
        shell: BUILD_DEFAULT_SHELL,
        working_directory: REPOSITORY_WORKING_DIRECTORY,
    }),
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
    run_defaults: None,
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
    for anchor in MATRIX_STEP_ANCHORS {
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

/// Returns mutable downloader source reviewed by the planned-job boundary.
///
/// External actions in the exact step contract are pinned by commit ID. This
/// downloader is repository-owned, so its `uses` path alone does not constrain
/// code which runs before the checkout-integrity gate. The orchestrator joins
/// this source with every image-producer source before checking contents and
/// file identity, so no two supposedly independent review files can alias.
pub(super) fn reviewed_sources() -> &'static [ReviewedSource] {
    REVIEWED_SOURCES
}

#[cfg(test)]
fn audit_download_action(repository_root: &Path) -> Result<(), PlannedAdapterAuditError> {
    audit_reviewed_sources(repository_root, REVIEWED_SOURCES)
}

#[cfg(test)]
fn read_download_action(repository_root: &Path) -> Result<String, PlannedAdapterAuditError> {
    read_reviewed_source(repository_root, DOWNLOAD_ACTION_PATH).map(|(_, source, _)| source)
}

/// Requires the complete local-action source reviewed with this adapter.
#[cfg(test)]
fn audit_download_action_source(source: &str) -> Result<(), PlannedAdapterViolations> {
    audit_exact_source(
        source,
        DOWNLOAD_ACTION_PATH,
        DOWNLOAD_ACTION_EXPECTED_SOURCE,
        DOWNLOAD_ACTION_SNAPSHOT_PATH,
    )
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
    let expected = [BUILD_EXPECTATION, MIRI_EXPECTATION]
        .into_iter()
        .map(|spec| (WORKFLOW_PATH.to_owned(), spec.job_name.to_owned()))
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
    if let Some(defaults) = expected.run_defaults {
        audit_run_defaults(lines, job.end, &fields, expected.job_name, defaults, errors);
    }
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

    // `build_test` owns the definitions and Miri consumes exact aliases. The
    // terminal executors have richer field-by-field audits below. The two
    // semver steps follow the build executor and cannot affect it; their exact
    // behavior remains outside this matrix-execution boundary until the
    // standalone semver audit replaces them later in the stack.
    let owned = |step: &[&str]| step.iter().map(|line| (*line).to_owned()).collect();
    let expected_setup: Vec<Vec<String>> = if expected.job_name == BUILD_JOB {
        vec![
            owned(CHECKOUT_STEP),
            download_image_step(),
            owned(LOAD_IMAGE_STEP),
            owned(CREATE_DOCKER_SHELL_STEP),
            owned(VERIFY_CHECKOUT_STEP),
        ]
    } else {
        vec![
            vec!["    - *matrix_checkout".to_owned()],
            vec!["    - *download_ci_image".to_owned()],
            vec!["    - *load_ci_image".to_owned()],
            vec!["    - *verify_matrix_checkout".to_owned()],
        ]
    };
    for (index, expected_step) in expected_setup.into_iter().enumerate() {
        let matches = actual.get(index).is_some_and(|actual| {
            actual.iter().copied().eq(expected_step.iter().map(String::as_str))
        });
        if !matches {
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
    let expected = BTreeSet::from([IMAGE_JOB, PLAN_JOB]);
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

fn audit_run_defaults(
    lines: &[&str],
    job_end: usize,
    fields: &[super::source::Field<'_>],
    job: &str,
    expected: RunDefaultsExpectation,
    errors: &mut ViolationSink,
) {
    let Some(defaults) = unique_field(fields, "defaults", job, errors) else {
        return;
    };
    let defaults_job = format!("{job}.defaults");
    let Some(default_fields) = nested_fields(lines, defaults, job_end, &defaults_job, errors)
    else {
        return;
    };
    audit_exact_job_fields(&default_fields, &defaults_job, &["run"], errors);

    let Some(run) = unique_field(&default_fields, "run", &defaults_job, errors) else {
        return;
    };
    let run_job = format!("{defaults_job}.run");
    let Some(run_fields) = nested_fields(lines, run, job_end, &run_job, errors) else {
        return;
    };
    audit_exact_job_fields(&run_fields, &run_job, &["shell", "working-directory"], errors);
    audit_exact_scalar_field(&run_fields, &run_job, "shell", expected.shell, errors);
    audit_exact_scalar_field(
        &run_fields,
        &run_job,
        "working-directory",
        expected.working_directory,
        errors,
    );
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
        "  -e GITHUB_ENV -e GITHUB_PATH -e GITHUB_STEP_SUMMARY -e GITHUB_OUTPUT -e GITHUB_WORKSPACE \\".to_owned(),
        "  -e CI -e GITHUB_ACTIONS -e GITHUB_ACTOR -e GITHUB_REPOSITORY -e GITHUB_SHA -e GITHUB_REF -e GITHUB_EVENT_NAME \\".to_owned(),
        expected.forwarded_selector_environment.to_owned(),
        "  -e RUSTFLAGS -e RUSTDOCFLAGS -e MIRIFLAGS \\".to_owned(),
        "  -e CARGO_NET_RETRY -e RUSTUP_MAX_RETRIES \\".to_owned(),
        "  -e ZC_NIGHTLY_RUSTFLAGS -e ZC_NIGHTLY_MIRIFLAGS \\".to_owned(),
        "  -e ZC_SKIP_CARGO_SEMVER_CHECKS \\".to_owned(),
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
        process::{self, Command, Output},
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::{
        audit, audit_download_action, audit_download_action_source, download_image_step,
        executor_run, read_download_action, BUILD_DEFAULT_SHELL, BUILD_DISPLAY_NAME,
        BUILD_EXPECTATION, CHECKOUT_STEP, CREATE_DOCKER_SHELL_STEP,
        DOWNLOAD_ACTION_EXPECTED_SOURCE, DOWNLOAD_ACTION_PATH, DOWNLOAD_ACTION_SNAPSHOT_PATH,
        LOAD_IMAGE_STEP, MIRI_DISPLAY_NAME, MIRI_EXPECTATION, TRUSTED_SHELL_LINE,
        VERIFY_CHECKOUT_STEP,
    };
    use crate::{
        ci::POLICY_PATH,
        inventory::RepositoryInventory,
        planned_adapter::{
            audit_planned_adapter,
            test_support::{
                assert_rejected, audit_feature, canonical_planned_jobs, replace_in_job,
            },
        },
        policy::Policy,
        workflow::{ReviewedWorkflowJobs, WORKFLOW_REGISTRY_PATH},
        workflow_protocol::{
            BUILD_JOB, EXECUTE_BUILD_CELL_COMMAND, EXECUTE_MIRI_CELL_COMMAND, MIRI_JOB,
            TRUSTED_SHELL, WORKFLOW_PATH,
        },
    };

    const CANONICAL_SOURCE: &str = r#"jobs:
  build_test:
    runs-on: ubuntu-latest
    needs: [build_docker_env, plan_ci]
    permissions:
      contents: read
    defaults:
      run:
        shell: /tmp/docker-shell.sh {0} # zizmor: ignore[misfeature] (CI intentionally routes build matrix commands through the prebuilt Docker image)
        working-directory: zerocopy
    strategy:
      fail-fast: false
      matrix: ${{ fromJSON(needs.plan_ci.outputs.build_matrix) }}
    name: Build & Test (${{ matrix.crate }} / ${{ matrix.toolchain }} / ${{ matrix.feature_profile }} / ${{ matrix.target }})
    steps:
    - &matrix_checkout
      uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1
      with:
        fetch-depth: 2
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
    - name: Create Docker Shell Wrapper
      shell: bash
      run: |
        set -eo pipefail
        mkdir -p /home/runner/.docker-cargo/registry /home/runner/.docker-cargo/git
        cat << 'EOF' > /tmp/docker-shell.sh
        #!/bin/bash
        # Boot an ephemeral container for the step, mounting the workspace and
        # temp dirs. Explicitly forward GitHub Actions internal state and matrix
        # environment variables.
        docker run --rm -i \
          --workdir "$PWD" \
          -v /home/runner/work:/home/runner/work \
          -v /home/runner/.docker-cargo/registry:/root/.cargo/registry \
          -v /home/runner/.docker-cargo/git:/root/.cargo/git \
          -e GITHUB_ENV -e GITHUB_PATH -e GITHUB_STEP_SUMMARY -e GITHUB_OUTPUT -e GITHUB_WORKSPACE \
          -e CI -e GITHUB_ACTIONS -e GITHUB_ACTOR -e GITHUB_REPOSITORY -e GITHUB_SHA -e GITHUB_REF -e GITHUB_EVENT_NAME \
          -e TOOLCHAIN -e CRATE -e TARGET -e FEATURE_PROFILE \
          -e MIRI_MODEL -e ZC_TOOLCHAIN -e PR_HEAD_SHA \
          -e RUSTFLAGS -e RUSTDOCFLAGS -e MIRIFLAGS \
          -e CARGO_NET_RETRY -e RUSTUP_MAX_RETRIES \
          -e ZC_NIGHTLY_RUSTFLAGS -e ZC_NIGHTLY_MIRIFLAGS \
          -e ZC_SKIP_CARGO_SEMVER_CHECKS \
          "$ZC_CI_IMAGE" bash -c "git config --global --add safe.directory '*' && exec bash -e -o pipefail \"\$1\"" -- "$1"
        EOF
        chmod +x /tmp/docker-shell.sh
    - &verify_matrix_checkout
      name: Verify matrix checkout is unchanged
      shell: /usr/bin/env -u BASH_ENV -u ENV -u SHELLOPTS -u BASHOPTS /bin/bash --noprofile --norc -p -euo pipefail -- {0}
      env:
        EXPECTED_COMMIT: ${{ github.sha }}
      run: |
        set -euo pipefail
        builtin cd -- "$GITHUB_WORKSPACE"
        readonly -a source_git=(
          /usr/bin/env -i
          GIT_CONFIG_GLOBAL=/dev/null
          GIT_CONFIG_NOSYSTEM=1
          GIT_NO_REPLACE_OBJECTS=1
          HOME=/dev/null
          PATH=/usr/bin:/bin
          /usr/bin/git
          "--git-dir=$GITHUB_WORKSPACE/.git"
          "--work-tree=$GITHUB_WORKSPACE"
        )
        actual_commit="$("${source_git[@]}" rev-parse --verify HEAD^{commit})"
        if [[ "$actual_commit" != "$EXPECTED_COMMIT" ]]; then
          printf 'Expected checkout commit %s, found %s\n' \
            "$EXPECTED_COMMIT" "$actual_commit" >&2
          exit 1
        fi
        # Do not trust the checkout's mutable index, local Git config, or
        # attributes. Build a temporary repository whose object store is the
        # checkout's content-addressed store, whose index comes from the
        # expected commit, and whose attributes also come from that commit.
        verification_directory="$(
          /usr/bin/mktemp -d "$RUNNER_TEMP/matrix-checkout.XXXXXX"
        )"
        readonly verification_directory
        trap '/usr/bin/rm -rf -- "$verification_directory"' EXIT
        /usr/bin/env -i \
          GIT_CONFIG_GLOBAL=/dev/null \
          GIT_CONFIG_NOSYSTEM=1 \
          HOME=/dev/null \
          PATH=/usr/bin:/bin \
          /usr/bin/git init --quiet --initial-branch=verified \
            "$verification_directory/repository"
        readonly -a trusted_git=(
          /usr/bin/env -i
          GIT_ATTR_NOSYSTEM=1
          "GIT_ATTR_SOURCE=$EXPECTED_COMMIT"
          GIT_CONFIG_GLOBAL=/dev/null
          GIT_CONFIG_NOSYSTEM=1
          "GIT_INDEX_FILE=$verification_directory/index"
          GIT_NO_REPLACE_OBJECTS=1
          "GIT_OBJECT_DIRECTORY=$GITHUB_WORKSPACE/.git/objects"
          HOME=/dev/null
          PATH=/usr/bin:/bin
          /usr/bin/git
          "--git-dir=$verification_directory/repository/.git"
          "--work-tree=$GITHUB_WORKSPACE"
          -c core.filemode=true
          -c core.fsmonitor=false
          -c core.ignoreCase=false
          -c core.sparseCheckout=false
          -c core.symlinks=true
          -c core.untrackedCache=false
        )
        "${trusted_git[@]}" update-ref HEAD "$EXPECTED_COMMIT"
        "${trusted_git[@]}" read-tree "$EXPECTED_COMMIT"
        checkout_status="$(
          "${trusted_git[@]}" status \
            --porcelain=v1 --untracked-files=all --ignored=matching -- \
            . ':(exclude).git'
        )"
        if [[ -n "$checkout_status" ]]; then
          printf 'Matrix setup modified the checkout:\n%s\n' \
            "$checkout_status" >&2
          exit 1
        fi
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
          -e GITHUB_ENV -e GITHUB_PATH -e GITHUB_STEP_SUMMARY -e GITHUB_OUTPUT -e GITHUB_WORKSPACE \
          -e CI -e GITHUB_ACTIONS -e GITHUB_ACTOR -e GITHUB_REPOSITORY -e GITHUB_SHA -e GITHUB_REF -e GITHUB_EVENT_NAME \
          -e TOOLCHAIN -e CRATE -e TARGET -e FEATURE_PROFILE \
          -e RUSTFLAGS -e RUSTDOCFLAGS -e MIRIFLAGS \
          -e CARGO_NET_RETRY -e RUSTUP_MAX_RETRIES \
          -e ZC_NIGHTLY_RUSTFLAGS -e ZC_NIGHTLY_MIRIFLAGS \
          -e ZC_SKIP_CARGO_SEMVER_CHECKS \
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
    - name: Prepare cargo-semver-checks
      run: echo audited separately later
    - name: Check semver compatibility
      run: echo audited separately later
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
    - *verify_matrix_checkout
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
          -e GITHUB_ENV -e GITHUB_PATH -e GITHUB_STEP_SUMMARY -e GITHUB_OUTPUT -e GITHUB_WORKSPACE \
          -e CI -e GITHUB_ACTIONS -e GITHUB_ACTOR -e GITHUB_REPOSITORY -e GITHUB_SHA -e GITHUB_REF -e GITHUB_EVENT_NAME \
          -e TOOLCHAIN -e CRATE -e TARGET -e FEATURE_PROFILE -e MIRI_MODEL \
          -e RUSTFLAGS -e RUSTDOCFLAGS -e MIRIFLAGS \
          -e CARGO_NET_RETRY -e RUSTUP_MAX_RETRIES \
          -e ZC_NIGHTLY_RUSTFLAGS -e ZC_NIGHTLY_MIRIFLAGS \
          -e ZC_SKIP_CARGO_SEMVER_CHECKS \
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

    #[cfg(target_os = "linux")]
    fn checkout_verification_script() -> String {
        let run = VERIFY_CHECKOUT_STEP
            .iter()
            .position(|line| *line == "      run: |")
            .expect("verification step must have a run block");
        VERIFY_CHECKOUT_STEP[run + 1..]
            .iter()
            .map(|line| {
                line.strip_prefix("        ")
                    .expect("verification script lines must have block indentation")
            })
            .collect::<Vec<_>>()
            .join("\n")
            + "\n"
    }

    #[cfg(target_os = "linux")]
    fn run_git(repository: &Path, arguments: &[&str]) -> Output {
        let output =
            Command::new("/usr/bin/git").current_dir(repository).args(arguments).output().unwrap();
        assert!(
            output.status.success(),
            "git {arguments:?} failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        output
    }

    #[cfg(target_os = "linux")]
    fn run_checkout_verification(
        repository: &TemporaryRepository,
        expected_commit: &str,
    ) -> Output {
        let runner_temp = repository.directory.join("runner-temp");
        fs::create_dir_all(&runner_temp).unwrap();
        Command::new("/bin/bash")
            .args([
                "--noprofile",
                "--norc",
                "-p",
                "-euo",
                "pipefail",
                "-c",
                &checkout_verification_script(),
            ])
            .env_clear()
            .env("EXPECTED_COMMIT", expected_commit)
            .env("GITHUB_WORKSPACE", &repository.root)
            .env("RUNNER_TEMP", runner_temp)
            .output()
            .unwrap()
    }

    struct TemporaryRepository {
        directory: PathBuf,
        root: PathBuf,
    }

    impl TemporaryRepository {
        fn new(label: &str) -> Self {
            static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
            let directory = loop {
                let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
                let candidate = std::env::temp_dir()
                    .join(format!("zerocopy-planned-matrix-{label}-{}-{unique}", process::id()));
                match fs::create_dir(&candidate) {
                    Ok(()) => break candidate,
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => {
                        panic!("failed to reserve {}: {error}", candidate.display());
                    }
                }
            };
            let root = directory.join("repository");
            fs::create_dir(&root).unwrap();
            let root = root.canonicalize().unwrap();
            Self { directory, root }
        }

        fn action_path(&self) -> PathBuf {
            self.root.join(DOWNLOAD_ACTION_PATH)
        }

        fn snapshot_path(&self) -> PathBuf {
            self.root.join(DOWNLOAD_ACTION_SNAPSHOT_PATH)
        }

        fn write_action(&self, source: &str) {
            let action = self.action_path();
            fs::create_dir_all(action.parent().unwrap()).unwrap();
            fs::write(action, source).unwrap();
        }

        fn write_snapshot(&self, source: &str) {
            let snapshot = self.snapshot_path();
            fs::create_dir_all(snapshot.parent().unwrap()).unwrap();
            fs::write(snapshot, source).unwrap();
        }
    }

    impl Drop for TemporaryRepository {
        fn drop(&mut self) {
            if let Err(error) = fs::remove_dir_all(&self.directory) {
                if !std::thread::panicking() {
                    panic!("failed to remove {}: {error}", self.directory.display());
                }
            }
        }
    }

    #[test]
    fn accepts_the_literal_fixture_and_live_workflow() {
        audit_canonical(CANONICAL_SOURCE).unwrap();

        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap();
        let reviewed = ReviewedWorkflowJobs::read(root.join(WORKFLOW_REGISTRY_PATH)).unwrap();
        let policy = Policy::read(root.join(POLICY_PATH)).unwrap();
        let repository = RepositoryInventory::audit(&root, &policy).unwrap();
        let workflow = crate::repository_text::read(&root.join(WORKFLOW_PATH)).unwrap();
        audit_planned_adapter(&root, &workflow, &reviewed, &repository).unwrap();
    }

    #[test]
    fn matrix_setup_definitions_are_exact() {
        assert_eq!(TRUSTED_SHELL_LINE, format!("      shell: {TRUSTED_SHELL}"));
        let owned = |step: &[&str]| step.iter().map(|line| (*line).to_owned()).collect();
        for (step_name, step) in [
            ("checkout", owned(CHECKOUT_STEP)),
            ("download", download_image_step()),
            ("load", owned(LOAD_IMAGE_STEP)),
            ("Docker shell", owned(CREATE_DOCKER_SHELL_STEP)),
            ("checkout verification", owned(VERIFY_CHECKOUT_STEP)),
        ] {
            for line in &step {
                let changed = format!("{line} unexpected");
                let source = replace_in_step(CANONICAL_SOURCE, &step[0], line, &changed);
                rejected(&format!("{step_name}: {line}"), &source, "exact canonical contract");
            }
        }
    }

    #[test]
    fn prerequisite_checkout_overwrites_are_rejected() {
        let overwrite_from_wrapper = replace_in_step(
            CANONICAL_SOURCE,
            CREATE_DOCKER_SHELL_STEP[0],
            "        set -eo pipefail\n",
            "        set -eo pipefail\n        printf malicious > zerocopy/cargo.sh\n",
        );
        rejected(
            "wrapper overwrites cargo.sh",
            &overwrite_from_wrapper,
            "exact canonical contract",
        );

        let inserted_overwrite = replace_in_job(
            CANONICAL_SOURCE,
            BUILD_JOB,
            "    - &verify_matrix_checkout\n",
            "    - name: Replace the executor\n      run: printf malicious > zerocopy/cargo.sh\n    - &verify_matrix_checkout\n",
        );
        rejected("inserted checkout overwrite", &inserted_overwrite, ".steps");

        let weakened_gate = replace_in_step(
            CANONICAL_SOURCE,
            VERIFY_CHECKOUT_STEP[0],
            "--untracked-files=all --ignored=matching",
            "--untracked-files=no",
        );
        rejected("weakened checkout gate", &weakened_gate, "exact canonical contract");
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn checkout_verifier_ignores_mutable_index_config_and_attributes() {
        let repository = TemporaryRepository::new("checkout-verifier");
        let cargo = repository.root.join("cargo.sh");
        fs::write(&cargo, "trusted\n").unwrap();
        run_git(&repository.root, &["init", "--quiet", "--initial-branch=main"]);
        run_git(&repository.root, &["add", "--", "cargo.sh"]);
        run_git(
            &repository.root,
            &[
                "-c",
                "user.name=CI",
                "-c",
                "user.email=ci@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "initial",
            ],
        );
        let expected = run_git(&repository.root, &["rev-parse", "HEAD"]);
        let expected = String::from_utf8(expected.stdout).unwrap();
        let expected = expected.trim();

        let clean = run_checkout_verification(&repository, expected);
        assert!(clean.status.success(), "{}", String::from_utf8_lossy(&clean.stderr));

        fs::write(&cargo, "skip-worktree replacement\n").unwrap();
        run_git(&repository.root, &["update-index", "--skip-worktree", "cargo.sh"]);
        let skipped = run_checkout_verification(&repository, expected);
        assert!(!skipped.status.success(), "skip-worktree concealed the overwrite");
        assert!(
            String::from_utf8_lossy(&skipped.stderr).contains("Matrix setup modified the checkout"),
            "{}",
            String::from_utf8_lossy(&skipped.stderr)
        );

        run_git(&repository.root, &["update-index", "--no-skip-worktree", "cargo.sh"]);
        fs::write(&cargo, "trusted\n").unwrap();
        run_git(&repository.root, &["add", "--", "cargo.sh"]);
        fs::write(repository.root.join(".git/trusted-cargo"), "trusted\n").unwrap();
        fs::write(repository.root.join(".git/info/attributes"), "cargo.sh filter=hide\n").unwrap();
        run_git(&repository.root, &["config", "filter.hide.clean", "cat .git/trusted-cargo"]);
        fs::write(&cargo, "filtered replacement\n").unwrap();
        run_git(&repository.root, &["add", "--", "cargo.sh"]);
        let concealed = run_git(
            &repository.root,
            &[
                "status",
                "--porcelain=v1",
                "--untracked-files=all",
                "--ignored=matching",
                "--",
                ".",
                ":(exclude).git",
            ],
        );
        assert!(concealed.stdout.is_empty(), "filter bypass setup was not concealed");

        let filtered = run_checkout_verification(&repository, expected);
        assert!(!filtered.status.success(), "local clean filter concealed the overwrite");
        assert!(
            String::from_utf8_lossy(&filtered.stderr)
                .contains("Matrix setup modified the checkout"),
            "{}",
            String::from_utf8_lossy(&filtered.stderr)
        );
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
                "Miri setup reordered",
                replace_in_job(
                    CANONICAL_SOURCE,
                    MIRI_JOB,
                    "    - *matrix_checkout\n    - *download_ci_image\n",
                    "    - *download_ci_image\n    - *matrix_checkout\n",
                ),
            ),
            (
                "Miri alias extended",
                replace_in_job(
                    CANONICAL_SOURCE,
                    MIRI_JOB,
                    "    - *verify_matrix_checkout\n",
                    "    - *verify_matrix_checkout\n      if: success()\n",
                ),
            ),
            (
                "step after Miri executor",
                replace_in_job(
                    CANONICAL_SOURCE,
                    MIRI_JOB,
                    "          --miri-model \"$MIRI_MODEL\"\n",
                    "          --miri-model \"$MIRI_MODEL\"\n    - name: Unexpected tail\n      run: true\n",
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
                "second verification alias",
                "    steps:\n    - *verify_matrix_checkout\n",
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
            "# &matrix_checkout and *verify_matrix_checkout are documentation.\n{CANONICAL_SOURCE}"
        );
        audit_canonical(&comments).unwrap();
    }

    #[test]
    fn local_download_action_source_is_exact() {
        audit_download_action_source(DOWNLOAD_ACTION_EXPECTED_SOURCE).unwrap();

        for (label, source) in [
            (
                "workspace overwrite",
                DOWNLOAD_ACTION_EXPECTED_SOURCE.replacen(
                    "        set -eu\n",
                    "        set -eu\n        printf malicious > zerocopy/cargo.sh\n",
                    1,
                ),
            ),
            (
                "delayed overwrite",
                DOWNLOAD_ACTION_EXPECTED_SOURCE.replacen(
                    "        set -eu\n",
                    "        set -eu\n        (sleep 1; printf malicious > zerocopy/cargo.sh) &\n",
                    1,
                ),
            ),
            (
                "environment file command",
                DOWNLOAD_ACTION_EXPECTED_SOURCE.replacen(
                    "        set -eu\n",
                    "        set -eu\n        echo 'RUSTFLAGS=other' >> \"$GITHUB_ENV\"\n",
                    1,
                ),
            ),
            (
                "transitive local action",
                DOWNLOAD_ACTION_EXPECTED_SOURCE.replacen(
                    "uses: actions/download-artifact@3e5f45b2cfb9172054b4087a40e8e0b5a5461e7c # v8.0.1",
                    "uses: ../mutable-download",
                    1,
                ),
            ),
        ] {
            let error = audit_download_action_source(&source).unwrap_err().to_string();
            assert!(error.contains(DOWNLOAD_ACTION_PATH), "{label}: {error}");
            assert!(error.contains("complete compiled source"), "{label}: {error}");
        }
    }

    #[test]
    fn local_download_action_path_is_contained_and_regular() {
        let missing = TemporaryRepository::new("missing");
        let error = read_download_action(&missing.root).unwrap_err();
        assert!(matches!(
            error,
            super::super::PlannedAdapterAuditError::InspectReviewedSource { .. }
        ));

        let repository = TemporaryRepository::new("valid");
        repository.write_action(DOWNLOAD_ACTION_EXPECTED_SOURCE);
        repository.write_snapshot(DOWNLOAD_ACTION_EXPECTED_SOURCE);
        audit_download_action(&repository.root).unwrap();

        let directory = TemporaryRepository::new("not-file");
        fs::create_dir_all(directory.action_path()).unwrap();
        let error = read_download_action(&directory.root).unwrap_err();
        assert!(matches!(
            error,
            super::super::PlannedAdapterAuditError::ReviewedSourceNotFile { .. }
        ));
    }

    #[test]
    fn runtime_snapshot_must_match_the_compiled_snapshot() {
        let repository = TemporaryRepository::new("changed-snapshot");
        repository.write_action(DOWNLOAD_ACTION_EXPECTED_SOURCE);
        repository.write_snapshot(&format!("{DOWNLOAD_ACTION_EXPECTED_SOURCE}# changed\n"));

        let error = audit_download_action(&repository.root).unwrap_err().to_string();
        assert!(error.contains(DOWNLOAD_ACTION_SNAPSHOT_PATH), "{error}");
        assert!(error.contains("complete compiled source"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn local_download_action_rejects_a_symlink() {
        use std::os::unix::fs::symlink;

        let repository = TemporaryRepository::new("symlink");
        let outside = repository.directory.join("outside/action.yml");
        fs::create_dir_all(outside.parent().unwrap()).unwrap();
        fs::write(&outside, "runs:\n  using: composite\n  steps: []\n").unwrap();
        fs::create_dir_all(repository.action_path().parent().unwrap()).unwrap();
        symlink(&outside, repository.action_path()).unwrap();

        let error = read_download_action(&repository.root).unwrap_err();
        assert!(matches!(
            error,
            super::super::PlannedAdapterAuditError::ReviewedSourceSymlink { .. }
        ));
    }

    #[cfg(unix)]
    #[test]
    fn local_action_and_snapshot_cannot_alias_each_other() {
        use std::os::unix::fs::symlink;

        for direction in ["action-to-snapshot", "snapshot-to-action"] {
            let repository = TemporaryRepository::new(direction);
            if direction == "action-to-snapshot" {
                repository.write_snapshot(DOWNLOAD_ACTION_EXPECTED_SOURCE);
                fs::create_dir_all(repository.action_path().parent().unwrap()).unwrap();
                symlink(repository.snapshot_path(), repository.action_path()).unwrap();
            } else {
                repository.write_action(DOWNLOAD_ACTION_EXPECTED_SOURCE);
                fs::create_dir_all(repository.snapshot_path().parent().unwrap()).unwrap();
                symlink(repository.action_path(), repository.snapshot_path()).unwrap();
            }

            let error = audit_download_action(&repository.root).unwrap_err();
            assert!(
                matches!(
                    error,
                    super::super::PlannedAdapterAuditError::ReviewedSourceSymlink { .. }
                ),
                "{direction}: {error:?}"
            );
        }
    }

    #[test]
    fn local_action_and_snapshot_cannot_be_hard_links() {
        let repository = TemporaryRepository::new("hard-link");
        repository.write_action(DOWNLOAD_ACTION_EXPECTED_SOURCE);
        fs::create_dir_all(repository.snapshot_path().parent().unwrap()).unwrap();
        fs::hard_link(repository.action_path(), repository.snapshot_path()).unwrap();

        let error = audit_download_action(&repository.root).unwrap_err();
        assert!(
            matches!(error, super::super::PlannedAdapterAuditError::DuplicateReviewedSource { .. }),
            "{error:?}"
        );
    }

    #[test]
    fn reviewed_planned_roles_equal_the_two_audited_jobs() {
        let mut missing = canonical_planned_jobs();
        missing.remove(&(WORKFLOW_PATH.to_owned(), BUILD_JOB.to_owned()));
        assert_rejected(
            "missing build role",
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
                "default shell",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    BUILD_DEFAULT_SHELL,
                    "/tmp/other-shell.sh {0}",
                ),
                "build_test.defaults.run.shell",
            ),
            (
                "default working directory",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "        working-directory: zerocopy",
                    "        working-directory: .",
                ),
                "build_test.defaults.run.working-directory",
            ),
            (
                "extra run default",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "        working-directory: zerocopy\n",
                    "        working-directory: zerocopy\n        timeout-minutes: 1\n",
                ),
                "build_test.defaults.run.timeout-minutes",
            ),
            (
                "scalar defaults",
                replace_in_job(
                    CANONICAL_SOURCE,
                    BUILD_JOB,
                    "    defaults:\n",
                    "    defaults: {}\n",
                ),
                "canonical nested mapping",
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
                let marker = format!("    - name: {}", expected.executor_step_name);
                let source = replace_in_step(
                    CANONICAL_SOURCE,
                    &marker,
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
            (BUILD_JOB, EXECUTE_BUILD_CELL_COMMAND, "wrong-build-command", "build command"),
            (MIRI_JOB, EXECUTE_MIRI_CELL_COMMAND, "wrong-miri-command", "Miri command"),
        ];
        for (job, from, to, label) in cases {
            let marker = if job == BUILD_JOB {
                "    - name: Execute checked build cell"
            } else {
                "    - name: Execute checked Miri cell"
            };
            let source = replace_in_step(CANONICAL_SOURCE, marker, from, to);
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
