// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exact required-check portion of the planned-job workflow bridge.

use std::collections::BTreeMap;

use super::{
    source::{
        audit_exact_job_fields, audit_exact_scalar_field, audit_exact_step_sequence,
        audit_singleton_job_contract, audit_step, audited_steps_block, find_job,
        job_field_location, job_fields, parse_needs, unique_field, RunForm, StepExpectation,
    },
    ViolationSink,
};
use crate::workflow_protocol::{
    AGGREGATE_DISPLAY_NAME, AGGREGATE_JOB, AGGREGATE_JOB_CONDITION, AGGREGATE_STEP_NAME, BUILD_JOB,
    BUILD_MATRIX_OUTPUT, CANCELLATION_STEP_NAME, CHECK_JOB_DEPENDENCIES_JOB, MIRI_ENABLED_OUTPUT,
    MIRI_JOB, MIRI_MATRIX_OUTPUT, PLAN_JOB, PUBLISHED_OUTPUTS_STEP_NAME, TRUSTED_SHELL,
};

const AGGREGATE_JOB_FIELDS: &[&str] = &["name", "if", "runs-on", "permissions", "needs", "steps"];

pub(super) fn audit(lines: &[&str], errors: &mut ViolationSink) {
    let Some(job) = find_job(lines, AGGREGATE_JOB, errors) else {
        return;
    };
    let fields = job_fields(lines, job.clone(), AGGREGATE_JOB, errors);
    audit_exact_job_fields(&fields, AGGREGATE_JOB, AGGREGATE_JOB_FIELDS, errors);
    audit_exact_scalar_field(&fields, AGGREGATE_JOB, "name", AGGREGATE_DISPLAY_NAME, errors);
    audit_exact_scalar_field(&fields, AGGREGATE_JOB, "if", AGGREGATE_JOB_CONDITION, errors);
    audit_exact_scalar_field(&fields, AGGREGATE_JOB, "permissions", "{}", errors);
    audit_minimum_dependencies(&fields, errors);
    audit_singleton_job_contract(&fields, AGGREGATE_JOB, errors);

    let gate_scalars = BTreeMap::from([
        ("if".to_owned(), published_outputs_condition()),
        ("shell".to_owned(), TRUSTED_SHELL.to_owned()),
    ]);
    let aggregate_scalars = BTreeMap::from([("shell".to_owned(), TRUSTED_SHELL.to_owned())]);
    let aggregate_environment = BTreeMap::from([
        ("RESULTS_JSON".to_owned(), "${{ toJSON(needs.*.result) }}".to_owned()),
        (
            "MIRI_ENABLED".to_owned(),
            format!("${{{{ needs.{PLAN_JOB}.outputs.{MIRI_ENABLED_OUTPUT} }}}}"),
        ),
        ("MIRI_RESULT".to_owned(), format!("${{{{ needs.{MIRI_JOB}.result }}}}")),
    ]);
    let cancellation_scalars = BTreeMap::from([
        ("if".to_owned(), "${{ cancelled() }}".to_owned()),
        ("shell".to_owned(), TRUSTED_SHELL.to_owned()),
    ]);
    let cancellation_run = ["exit 1".to_owned()];
    let gate_run = ["exit 1".to_owned()];
    let aggregate_run = aggregate_run();
    if let Some(steps) = audited_steps_block(&fields, job, AGGREGATE_JOB, 6, errors) {
        audit_exact_step_sequence(
            lines,
            &steps,
            AGGREGATE_JOB,
            &[CANCELLATION_STEP_NAME, PUBLISHED_OUTPUTS_STEP_NAME, AGGREGATE_STEP_NAME],
            errors,
        );
        audit_step(
            lines,
            &steps,
            StepExpectation {
                job: AGGREGATE_JOB,
                name: CANCELLATION_STEP_NAME,
                root_fields: &["if", "shell", "run"],
                scalar_fields: &cancellation_scalars,
                environment: &BTreeMap::new(),
                run: &cancellation_run,
                run_form: RunForm::Inline,
            },
            errors,
        );
        audit_step(
            lines,
            &steps,
            StepExpectation {
                job: AGGREGATE_JOB,
                name: PUBLISHED_OUTPUTS_STEP_NAME,
                root_fields: &["if", "shell", "run"],
                scalar_fields: &gate_scalars,
                environment: &BTreeMap::new(),
                run: &gate_run,
                run_form: RunForm::Inline,
            },
            errors,
        );
        audit_step(
            lines,
            &steps,
            StepExpectation {
                job: AGGREGATE_JOB,
                name: AGGREGATE_STEP_NAME,
                root_fields: &["shell", "env", "run"],
                scalar_fields: &aggregate_scalars,
                environment: &aggregate_environment,
                run: &aggregate_run,
                run_form: RunForm::Block,
            },
            errors,
        );
    }
}

fn audit_minimum_dependencies(fields: &[super::source::Field<'_>], errors: &mut ViolationSink) {
    let Some(needs) = unique_field(fields, "needs", AGGREGATE_JOB, errors) else {
        return;
    };
    let dependencies = match parse_needs(needs.value) {
        Ok(dependencies) => dependencies,
        Err(message) => {
            errors.push(job_field_location(AGGREGATE_JOB, "needs"), message);
            return;
        }
    };

    // These are only the edges needed to prove that the planned-job workflow
    // bridge reaches the required check. `check_job_dependencies.sh` remains
    // the single owner of every other job in the complete dependency list.
    for dependency in [PLAN_JOB, BUILD_JOB, MIRI_JOB, CHECK_JOB_DEPENDENCIES_JOB] {
        if !dependencies.contains(dependency) {
            errors.push(
                job_field_location(AGGREGATE_JOB, "needs"),
                format!(
                    "must depend directly on `{dependency}` as part of the minimum planned-job workflow bridge into the required check"
                ),
            );
        }
    }
}

fn published_outputs_condition() -> String {
    format!(
        "${{{{ needs.{PLAN_JOB}.result == 'success' && (needs.{PLAN_JOB}.outputs.{BUILD_MATRIX_OUTPUT} == '' || needs.{PLAN_JOB}.outputs.{MIRI_MATRIX_OUTPUT} == '' || (needs.{PLAN_JOB}.outputs.{MIRI_ENABLED_OUTPUT} != 'true' && needs.{PLAN_JOB}.outputs.{MIRI_ENABLED_OUTPUT} != 'false')) }}}}"
    )
}

fn aggregate_run() -> Vec<String> {
    vec![
        "set -euo pipefail".to_owned(),
        "/usr/bin/jq -e --arg enabled \"$MIRI_ENABLED\" --arg miri \"$MIRI_RESULT\" '".to_owned(),
        "  type == \"array\" and length > 0 and".to_owned(),
        "  if $enabled == \"false\"".to_owned(),
        "  then $miri == \"skipped\" and".to_owned(),
        "       ([.[] | select(. == \"skipped\")] | length) == 1 and".to_owned(),
        "       all(.[]; . == \"success\" or . == \"skipped\")".to_owned(),
        "  else $enabled == \"true\" and".to_owned(),
        "       $miri == \"success\" and".to_owned(),
        "       all(.[]; . == \"success\")".to_owned(),
        "  end".to_owned(),
        "' <<< \"$RESULTS_JSON\"".to_owned(),
    ]
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::{aggregate_run, audit};
    use crate::{
        planned_adapter::{
            audit_planned_adapter,
            test_support::{assert_rejected, audit_feature, replace_in_job},
        },
        workflow::{ReviewedWorkflowJobs, WORKFLOW_REGISTRY_PATH},
        workflow_protocol::{
            AGGREGATE_DISPLAY_NAME, AGGREGATE_JOB, AGGREGATE_STEP_NAME, CANCELLATION_STEP_NAME,
            CHECK_JOB_DEPENDENCIES_JOB, PLAN_JOB, PUBLISHED_OUTPUTS_STEP_NAME, TRUSTED_SHELL,
        },
    };

    const CANONICAL_SOURCE: &str = r#"jobs:
  all-jobs-succeed:
    name: All checks succeeded (ci.yml)
    if: ${{ always() }}
    runs-on: ubuntu-latest
    permissions: {}
    needs: [build_test, miri, check-job-dependencies, plan_ci]
    steps:
      - name: Reject workflow cancellation
        if: ${{ cancelled() }}
        shell: /usr/bin/env -u BASH_ENV -u ENV -u SHELLOPTS -u BASHOPTS /bin/bash --noprofile --norc -p -euo pipefail -- {0}
        run: exit 1
      - name: Require published planner outputs
        if: ${{ needs.plan_ci.result == 'success' && (needs.plan_ci.outputs.build_matrix == '' || needs.plan_ci.outputs.miri_matrix == '' || (needs.plan_ci.outputs.miri_enabled != 'true' && needs.plan_ci.outputs.miri_enabled != 'false')) }}
        shell: /usr/bin/env -u BASH_ENV -u ENV -u SHELLOPTS -u BASHOPTS /bin/bash --noprofile --norc -p -euo pipefail -- {0}
        run: exit 1
      - name: Require every dependency to succeed
        shell: /usr/bin/env -u BASH_ENV -u ENV -u SHELLOPTS -u BASHOPTS /bin/bash --noprofile --norc -p -euo pipefail -- {0}
        env:
          RESULTS_JSON: ${{ toJSON(needs.*.result) }}
          MIRI_ENABLED: ${{ needs.plan_ci.outputs.miri_enabled }}
          MIRI_RESULT: ${{ needs.miri.result }}
        run: |
          set -euo pipefail
          /usr/bin/jq -e --arg enabled "$MIRI_ENABLED" --arg miri "$MIRI_RESULT" '
            type == "array" and length > 0 and
            if $enabled == "false"
            then $miri == "skipped" and
                 ([.[] | select(. == "skipped")] | length) == 1 and
                 all(.[]; . == "success" or . == "skipped")
            else $enabled == "true" and
                 $miri == "success" and
                 all(.[]; . == "success")
            end
          ' <<< "$RESULTS_JSON"
  next_job:
    runs-on: ubuntu-latest
"#;

    fn audit_source(source: &str) -> Result<(), super::super::PlannedAdapterViolations> {
        audit_feature(source, audit)
    }

    fn rejected(label: &str, source: &str, expected: &str) {
        assert_rejected(label, audit_source(source), expected);
    }

    fn swap_first_two_step_blocks(source: &str) -> String {
        let first = format!("      - name: {CANCELLATION_STEP_NAME}\n");
        let second = format!("      - name: {PUBLISHED_OUTPUTS_STEP_NAME}\n");
        let third = format!("      - name: {AGGREGATE_STEP_NAME}\n");
        let first_start = source.find(&first).unwrap();
        let second_start = source.find(&second).unwrap();
        let third_start = source.find(&third).unwrap();
        assert!(first_start < second_start && second_start < third_start);
        format!(
            "{}{}{}{}",
            &source[..first_start],
            &source[second_start..third_start],
            &source[first_start..second_start],
            &source[third_start..]
        )
    }

    #[test]
    fn accepts_the_literal_fixture_and_live_workflow() {
        audit_source(CANONICAL_SOURCE).unwrap();

        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap();
        let reviewed = ReviewedWorkflowJobs::read(root.join(WORKFLOW_REGISTRY_PATH)).unwrap();
        audit_planned_adapter(&root, &reviewed).unwrap();
    }

    #[test]
    fn required_check_name_and_singleton_host_contract_are_exact() {
        let cases = [
            (
                "display name",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    AGGREGATE_DISPLAY_NAME,
                    "Almost all checks succeeded",
                ),
                ".name",
            ),
            (
                "condition",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    "if: ${{ always() }}",
                    "if: success()",
                ),
                ".if",
            ),
            (
                "runner",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    "runs-on: ubuntu-latest",
                    "runs-on: self-hosted",
                ),
                ".runs-on",
            ),
            (
                "missing permissions",
                replace_in_job(CANONICAL_SOURCE, AGGREGATE_JOB, "    permissions: {}\n", ""),
                ".permissions",
            ),
            (
                "expanded permissions",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    "    permissions: {}\n",
                    "    permissions:\n      contents: read\n",
                ),
                ".permissions",
            ),
            (
                "container",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    "    runs-on: ubuntu-latest\n",
                    "    runs-on: ubuntu-latest\n    container: ignored.invalid/noop\n",
                ),
                ".container",
            ),
            (
                "strategy",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    "    runs-on: ubuntu-latest\n",
                    "    runs-on: ubuntu-latest\n    strategy:\n      matrix:\n        include: []\n",
                ),
                ".strategy",
            ),
            (
                "continue on error",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
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
    fn aggregate_rejects_every_unreviewed_top_level_job_field() {
        let additions = [
            ("concurrency", "    concurrency: one-at-a-time\n"),
            ("environment", "    environment: protected\n"),
            ("env", "    env:\n      SURPRISE: value\n"),
            ("services", "    services: {}\n"),
            ("timeout-minutes", "    timeout-minutes: 1\n"),
            ("defaults", "    defaults: {}\n"),
            ("outputs", "    outputs: {}\n"),
            ("uses", "    uses: example.invalid/owner/workflow@main\n"),
            ("with", "    with: {}\n"),
            ("secrets", "    secrets: inherit\n"),
        ];
        for (field, addition) in additions {
            let source = replace_in_job(
                CANONICAL_SOURCE,
                AGGREGATE_JOB,
                "    runs-on: ubuntu-latest\n",
                &format!("    runs-on: ubuntu-latest\n{addition}"),
            );
            rejected(field, &source, &format!("all-jobs-succeed.{field}"));
        }
    }

    #[test]
    fn aggregate_requires_the_minimum_planned_job_dependency_bridge() {
        let canonical = "[build_test, miri, check-job-dependencies, plan_ci]";
        let cases = [
            ("build_test", "[miri, check-job-dependencies, plan_ci]"),
            ("miri", "[build_test, check-job-dependencies, plan_ci]"),
            (CHECK_JOB_DEPENDENCIES_JOB, "[build_test, miri, plan_ci]"),
            (PLAN_JOB, "[build_test, miri, check-job-dependencies]"),
        ];
        for (dependency, replacement) in cases {
            let source = replace_in_job(CANONICAL_SOURCE, AGGREGATE_JOB, canonical, replacement);
            rejected(dependency, &source, "must depend directly");
        }

        let extra = replace_in_job(
            CANONICAL_SOURCE,
            AGGREGATE_JOB,
            canonical,
            "[build_test, miri, codegen, check-job-dependencies, plan_ci]",
        );
        audit_source(&extra).unwrap();

        let duplicate = replace_in_job(
            CANONICAL_SOURCE,
            AGGREGATE_JOB,
            canonical,
            "[build_test, miri, miri, check-job-dependencies, plan_ci]",
        );
        rejected("duplicate dependency", &duplicate, "repeats job `miri`");
    }

    #[test]
    fn published_output_gate_is_exact_and_uses_every_typed_output() {
        let cases = [
            (
                "step name",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    PUBLISHED_OUTPUTS_STEP_NAME,
                    "Maybe require planner outputs",
                ),
                "canonical step declaration",
            ),
            (
                "build output",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    "outputs.build_matrix == ''",
                    "outputs.build_matrix != ''",
                ),
                ".fields.if",
            ),
            (
                "Miri output",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    "outputs.miri_matrix == ''",
                    "outputs.miri_matrix != ''",
                ),
                ".fields.if",
            ),
            (
                "Miri gate",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    "outputs.miri_enabled != 'false'",
                    "outputs.miri_enabled == 'false'",
                ),
                ".fields.if",
            ),
            (
                "successful no-op",
                replace_in_job(CANONICAL_SOURCE, AGGREGATE_JOB, "run: exit 1", "run: exit 0"),
                ".run",
            ),
            (
                "gate shell",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    &format!("shell: {TRUSTED_SHELL}\n        run: exit 1"),
                    "shell: bash\n        run: exit 1",
                ),
                ".fields.shell",
            ),
        ];
        for (label, source, expected) in cases {
            rejected(label, &source, expected);
        }
    }

    #[test]
    fn dependency_assertion_environment_and_absolute_jq_run_are_exact() {
        let cases = [
            (
                "results",
                "RESULTS_JSON: ${{ toJSON(needs.*.result) }}",
                "RESULTS_JSON: ${{ toJSON(needs) }}",
            ),
            (
                "Miri enabled",
                "MIRI_ENABLED: ${{ needs.plan_ci.outputs.miri_enabled }}",
                "MIRI_ENABLED: ${{ needs.miri.outputs.miri_enabled }}",
            ),
            (
                "Miri result",
                "MIRI_RESULT: ${{ needs.miri.result }}",
                "MIRI_RESULT: ${{ needs.build_test.result }}",
            ),
            ("absolute jq", "/usr/bin/jq -e", "jq -e"),
        ];
        for (label, from, to) in cases {
            let source = replace_in_job(CANONICAL_SOURCE, AGGREGATE_JOB, from, to);
            rejected(label, &source, if label == "absolute jq" { ".run" } else { ".env." });
        }

        let aggregate_header =
            format!("      - name: {AGGREGATE_STEP_NAME}\n        shell: {TRUSTED_SHELL}\n");
        let weakened = replace_in_job(
            CANONICAL_SOURCE,
            AGGREGATE_JOB,
            &aggregate_header,
            &format!("      - name: {AGGREGATE_STEP_NAME}\n        shell: bash\n"),
        );
        rejected("assertion shell", &weakened, ".fields.shell");

        for line in aggregate_run() {
            let changed = if line == "set -euo pipefail" {
                "set -eo pipefail".to_owned()
            } else if line.contains('"') {
                line.replacen('"', "", 1)
            } else {
                format!("{line} and true")
            };
            let source = replace_in_job(CANONICAL_SOURCE, AGGREGATE_JOB, &line, &changed);
            rejected(&line, &source, ".run");
        }
    }

    #[test]
    fn both_aggregate_shells_reject_startup_influence() {
        let mut replacements = vec!["bash".to_owned(), TRUSTED_SHELL.replace(" -p ", " ")];
        for variable in ["BASH_ENV", "ENV", "SHELLOPTS", "BASHOPTS"] {
            replacements.push(TRUSTED_SHELL.replace(&format!("-u {variable} "), ""));
        }

        let gate_shell = format!("        shell: {TRUSTED_SHELL}\n        run: exit 1");
        let aggregate_header =
            format!("      - name: {AGGREGATE_STEP_NAME}\n        shell: {TRUSTED_SHELL}\n");
        for replacement in replacements {
            let gate = replace_in_job(
                CANONICAL_SOURCE,
                AGGREGATE_JOB,
                &gate_shell,
                &format!("        shell: {replacement}\n        run: exit 1"),
            );
            rejected("published-output gate", &gate, ".fields.shell");

            let assertion = replace_in_job(
                CANONICAL_SOURCE,
                AGGREGATE_JOB,
                &aggregate_header,
                &format!("      - name: {AGGREGATE_STEP_NAME}\n        shell: {replacement}\n"),
            );
            rejected("dependency assertion", &assertion, ".fields.shell");
        }
    }

    #[test]
    fn ordered_steps_and_cancellation_guard_are_exact() {
        let cancellation = format!(
            "      - name: {CANCELLATION_STEP_NAME}\n        if: ${{{{ cancelled() }}}}\n        shell: {TRUSTED_SHELL}\n        run: exit 1\n"
        );
        let cases = [
            (
                "inserted privileged step",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    &cancellation,
                    &format!(
                        "      - name: Replace jq\n        run: sudo install ./fake-jq /usr/bin/jq\n{cancellation}"
                    ),
                ),
                "steps must be exactly",
            ),
            (
                "reordered steps",
                swap_first_two_step_blocks(CANONICAL_SOURCE),
                "steps must be exactly",
            ),
            (
                "cancellation condition",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    "if: ${{ cancelled() }}",
                    "if: success()",
                ),
                ".fields.if",
            ),
            (
                "cancellation no-op",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    &cancellation,
                    &format!(
                        "      - name: {CANCELLATION_STEP_NAME}\n        if: ${{{{ cancelled() }}}}\n        run: exit 0\n"
                    ),
                ),
                ".run",
            ),
            (
                "conditional guard shell",
                replace_in_job(
                    CANONICAL_SOURCE,
                    AGGREGATE_JOB,
                    &cancellation,
                    &format!(
                        "      - name: {CANCELLATION_STEP_NAME}\n        if: ${{{{ cancelled() }}}}\n        shell: bash\n        run: exit 1\n"
                    ),
                ),
                ".fields.shell",
            ),
        ];
        for (label, source, expected) in cases {
            rejected(label, &source, expected);
        }
    }

    #[test]
    fn aggregate_steps_are_bounded_by_one_steps_mapping() {
        let duplicate_mapping = replace_in_job(
            CANONICAL_SOURCE,
            AGGREGATE_JOB,
            "    steps:\n",
            "    steps: []\n    steps:\n",
        );
        rejected("duplicate steps", &duplicate_mapping, ".steps");

        let duplicate_step = replace_in_job(
            CANONICAL_SOURCE,
            AGGREGATE_JOB,
            &format!("      - name: {AGGREGATE_STEP_NAME}\n"),
            &format!(
                "      - name: {AGGREGATE_STEP_NAME}\n        run: echo unrelated\n      - name: {AGGREGATE_STEP_NAME}\n"
            ),
        );
        rejected("duplicate assertion", &duplicate_step, "inside `all-jobs-succeed.steps`");

        let same_name_elsewhere = CANONICAL_SOURCE.replace(
            "  next_job:\n",
            &format!(
                "  next_job:\n    steps:\n      - name: {AGGREGATE_STEP_NAME}\n        run: echo unrelated\n"
            ),
        );
        audit_source(&same_name_elsewhere).unwrap();
    }
}
