// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exact consumption and execution audit for typed build and Miri matrices.

use std::collections::{BTreeMap, BTreeSet};

use super::{
    source::{
        audit_exact_job_fields, audit_exact_scalar_field, audit_host_job_contract,
        audit_read_permissions, audit_step, audit_unique_run_mentions, audited_steps_block,
        compare_map, escape_control_characters, find_job, job_field_location, job_fields,
        nested_mapping, parse_needs, unique_field, RunForm, StepExpectation,
    },
    ViolationSink,
};
use crate::{
    workflow::WORKFLOW_REGISTRY_PATH,
    workflow_protocol::{
        BUILD_JOB, BUILD_MATRIX_OUTPUT, BUILD_STEP_NAME, CELL_FEATURE_PROFILE_OPTION,
        CELL_MIRI_MODEL_OPTION, CELL_PACKAGE_OPTION, CELL_TARGET_OPTION, CELL_TOOLCHAIN_OPTION,
        CI_EVENT_OPTION, DOCKER_ENTRYPOINT_ARGUMENT, DOCKER_OPTION_TERMINATOR,
        EXECUTE_BUILD_CELL_COMMAND, EXECUTE_MIRI_CELL_COMMAND, HOST_DOCKER_RUN,
        MIRI_ENABLED_OUTPUT, MIRI_JOB, MIRI_MATRIX_OUTPUT, MIRI_STEP_NAME, PLAN_JOB,
        REPOSITORY_WORKING_DIRECTORY, TRUSTED_SHELL, WORKFLOW_PATH,
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
const BUILD_JOB_FIELDS: &[&str] = &["runs-on", "needs", "permissions", "strategy", "name", "steps"];
const MIRI_JOB_FIELDS: &[&str] =
    &["if", "runs-on", "needs", "permissions", "strategy", "name", "steps"];
const BUILD_DISPLAY_NAME: &str = "Build & Test (${{ matrix.crate }} / ${{ matrix.toolchain }} / ${{ matrix.feature_profile }} / ${{ matrix.target }})";
const MIRI_DISPLAY_NAME: &str = "Miri (${{ matrix.crate }} / ${{ matrix.toolchain }} / ${{ matrix.feature_profile }} / ${{ matrix.miri_model }} / ${{ matrix.target }})";

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
    audit_strategy(lines, job.end, &fields, expected, errors);

    if let Some(steps) = audited_steps_block(&fields, job, expected.job_name, 4, errors) {
        audit_executor_step(lines, &steps, expected, errors);
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
        "  -e GITHUB_ENV -e GITHUB_PATH -e GITHUB_STEP_SUMMARY -e GITHUB_OUTPUT -e GITHUB_WORKSPACE \\".to_owned(),
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
    use std::{collections::BTreeSet, path::Path};

    use super::{
        audit, executor_run, BUILD_DISPLAY_NAME, BUILD_EXPECTATION, MIRI_DISPLAY_NAME,
        MIRI_EXPECTATION,
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
    strategy:
      fail-fast: false
      matrix: ${{ fromJSON(needs.plan_ci.outputs.build_matrix) }}
    name: Build & Test (${{ matrix.crate }} / ${{ matrix.toolchain }} / ${{ matrix.feature_profile }} / ${{ matrix.target }})
    steps:
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

    #[test]
    fn accepts_the_literal_fixture_and_live_workflow() {
        audit_canonical(CANONICAL_SOURCE).unwrap();

        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap();
        let reviewed = ReviewedWorkflowJobs::read(root.join(WORKFLOW_REGISTRY_PATH)).unwrap();
        audit_planned_adapter(&root, &reviewed).unwrap();
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

        let same_name_elsewhere = replace_in_job(
            CANONICAL_SOURCE,
            MIRI_JOB,
            "    - name: Execute checked Miri cell\n",
            "    - name: Execute checked build cell\n      run: echo unrelated\n    - name: Execute checked Miri cell\n",
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
                let source = replace_in_job(CANONICAL_SOURCE, expected.job_name, &line, &changed);
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
