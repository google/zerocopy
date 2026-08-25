// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exact publication audit for the typed CI plan producer.

use std::collections::BTreeMap;

use super::{
    source::{
        audit_exact_job_fields, audit_exact_mapping, audit_exact_scalar_field,
        audit_read_permissions, audit_singleton_job_contract, audit_step,
        audit_unique_run_mentions, audited_steps_block, compare_map, find_job, job_field_location,
        job_fields, nested_mapping, step_field_location, unique_field, MappingExpectation, RunForm,
        StepExpectation,
    },
    ViolationSink,
};
use crate::workflow_protocol::{
    BUILD_MATRIX_OUTPUT, CI_EVENT_OPTION, GITHUB_OUTPUT_OPTION, GITHUB_PLAN_COMMAND,
    MIRI_ENABLED_OUTPUT, MIRI_MATRIX_OUTPUT, PLANNER_PATH, PLAN_ARTIFACT_OPTION, PLAN_JOB,
    PLAN_STEP_ID, PLAN_STEP_NAME, REPOSITORY_WORKING_DIRECTORY, TRUSTED_SHELL,
};

const PLAN_JOB_FIELDS: &[&str] = &["name", "runs-on", "permissions", "outputs", "env", "steps"];
const PLAN_DISPLAY_NAME: &str = "Plan ordinary CI work";
const PLAN_ARTIFACT_ENVIRONMENT: &str = "CI_PLAN_ARTIFACT";
const PLAN_ARTIFACT_NAME: &str = "ci-plan.json";

pub(super) fn audit(lines: &[&str], errors: &mut ViolationSink) {
    if let Some(job) = find_job(lines, PLAN_JOB, errors) {
        let fields = job_fields(lines, job.clone(), PLAN_JOB, errors);
        audit_exact_job_fields(&fields, PLAN_JOB, PLAN_JOB_FIELDS, errors);
        audit_exact_scalar_field(&fields, PLAN_JOB, "name", PLAN_DISPLAY_NAME, errors);
        audit_read_permissions(lines, job.end, &fields, PLAN_JOB, errors);
        let environment =
            BTreeMap::from([(PLAN_ARTIFACT_ENVIRONMENT.to_owned(), PLAN_ARTIFACT_NAME.to_owned())]);
        audit_exact_mapping(
            lines,
            job.end,
            &fields,
            MappingExpectation { job: PLAN_JOB, field: "env", values: &environment },
            errors,
        );
        audit_outputs(lines, job.end, &fields, errors);
        audit_job(lines, job, &fields, errors);
    }
    audit_unique_run_mentions(lines, PLAN_STEP_NAME, GITHUB_PLAN_COMMAND, errors);
}

fn audit_outputs(
    lines: &[&str],
    job_end: usize,
    fields: &[super::source::Field<'_>],
    errors: &mut ViolationSink,
) {
    let Some(outputs) = unique_field(fields, "outputs", PLAN_JOB, errors) else {
        return;
    };
    if !outputs.value.is_empty() {
        errors.push(
            job_field_location(PLAN_JOB, "outputs"),
            "outputs must use the canonical nested mapping form",
        );
        return;
    }

    let actual = nested_mapping(lines, outputs, job_end, PLAN_JOB, errors);
    let expected = [BUILD_MATRIX_OUTPUT, MIRI_MATRIX_OUTPUT, MIRI_ENABLED_OUTPUT]
        .into_iter()
        .map(|output| (output.to_owned(), plan_output_expression(output)))
        .collect::<BTreeMap<_, _>>();
    compare_map(job_field_location(PLAN_JOB, "outputs"), &expected, &actual, errors);
}

fn audit_job(
    lines: &[&str],
    job: std::ops::Range<usize>,
    fields: &[super::source::Field<'_>],
    errors: &mut ViolationSink,
) {
    if fields.iter().any(|field| field.key == "if") {
        errors.push(
            job_field_location(PLAN_JOB, "if"),
            "the checked planner must run on every workflow event",
        );
    }
    audit_singleton_job_contract(fields, PLAN_JOB, errors);

    let scalar_fields = BTreeMap::from([
        ("id".to_owned(), PLAN_STEP_ID.to_owned()),
        ("shell".to_owned(), TRUSTED_SHELL.to_owned()),
        ("working-directory".to_owned(), REPOSITORY_WORKING_DIRECTORY.to_owned()),
    ]);
    let environment =
        BTreeMap::from([("EVENT_NAME".to_owned(), "${{ github.event_name }}".to_owned())]);
    let run = planner_run();
    if let Some(steps) = audited_steps_block(fields, job, PLAN_JOB, 6, errors) {
        audit_step(
            lines,
            &steps,
            StepExpectation {
                job: PLAN_JOB,
                name: PLAN_STEP_NAME,
                root_fields: &["id", "shell", "working-directory", "env", "run"],
                scalar_fields: &scalar_fields,
                environment: &environment,
                run: &run,
                run_form: RunForm::Block,
            },
            errors,
        );

        let canonical_id = format!("        id: {PLAN_STEP_ID}");
        let id_count = lines
            .iter()
            .enumerate()
            .filter(|(index, line)| steps.range.contains(index) && **line == canonical_id)
            .count();
        if id_count != 1 {
            errors.push(
                step_field_location(PLAN_STEP_NAME, "id"),
                format!(
                    "expected exactly one canonical `{PLAN_STEP_ID}` step ID, found {id_count}"
                ),
            );
        }
    }
}

fn planner_run() -> Vec<String> {
    vec![
        "set -euo pipefail".to_owned(),
        format!("PATH={PLANNER_PATH} \\"),
        format!("/bin/bash --noprofile --norc -p ./cargo.sh ci {GITHUB_PLAN_COMMAND} \\"),
        format!("  {CI_EVENT_OPTION} \"$EVENT_NAME\" \\"),
        format!("  {GITHUB_OUTPUT_OPTION} \"$GITHUB_OUTPUT\" \\"),
        format!("  {PLAN_ARTIFACT_OPTION} \"$RUNNER_TEMP/$CI_PLAN_ARTIFACT\""),
    ]
}

fn plan_output_expression(output: &str) -> String {
    format!("${{{{ steps.{PLAN_STEP_ID}.outputs.{output} }}}}")
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::{
        super::{audit_planned_adapter, test_support::audit_feature, PlannedAdapterViolations},
        audit,
    };
    use crate::{
        workflow::{ReviewedWorkflowJobs, WORKFLOW_REGISTRY_PATH},
        workflow_protocol::{GITHUB_PLAN_COMMAND, PLAN_JOB, PLAN_STEP_NAME, TRUSTED_SHELL},
    };

    const CANONICAL_SOURCE: &str = r#"jobs:
  plan_ci:
    name: Plan ordinary CI work
    runs-on: ubuntu-latest
    permissions:
      contents: read
    outputs:
      build_matrix: ${{ steps.plan.outputs.build_matrix }}
      miri_matrix: ${{ steps.plan.outputs.miri_matrix }}
      miri_enabled: ${{ steps.plan.outputs.miri_enabled }}
    env:
      CI_PLAN_ARTIFACT: ci-plan.json
    steps:
      - name: Validate inputs and project the plan
        id: plan
        shell: /usr/bin/env -u BASH_ENV -u ENV -u SHELLOPTS -u BASHOPTS /bin/bash --noprofile --norc -p -euo pipefail -- {0}
        working-directory: zerocopy
        env:
          EVENT_NAME: ${{ github.event_name }}
        run: |
          set -euo pipefail
          PATH=/home/runner/.cargo/bin:/usr/local/bin:/usr/bin:/bin \
          /bin/bash --noprofile --norc -p ./cargo.sh ci github-plan \
            --event "$EVENT_NAME" \
            --github-output "$GITHUB_OUTPUT" \
            --artifact "$RUNNER_TEMP/$CI_PLAN_ARTIFACT"
  next_job:
    runs-on: ubuntu-latest
"#;

    fn audit_source(source: &str) -> Result<(), PlannedAdapterViolations> {
        audit_feature(source, audit)
    }

    fn rejected(label: &str, source: &str, expected: &str) {
        let error = match audit_source(source) {
            Ok(()) => panic!("{label}: mutation was accepted"),
            Err(error) => error,
        };
        assert!(error.to_string().contains(expected), "{label}: {error}");
    }

    fn replace_once(source: &str, from: &str, to: &str) -> String {
        assert_eq!(source.matches(from).count(), 1, "fixture occurrence for {from:?}");
        source.replacen(from, to, 1)
    }

    #[test]
    fn accepts_the_literal_fixture_and_live_workflow() {
        audit_source(CANONICAL_SOURCE).unwrap();

        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap();
        let reviewed = ReviewedWorkflowJobs::read(root.join(WORKFLOW_REGISTRY_PATH)).unwrap();
        audit_planned_adapter(&root, &reviewed).unwrap();
    }

    #[test]
    fn outputs_are_exact_and_come_from_the_bounded_producer() {
        let cases = [
            (
                "wrong build producer",
                replace_once(
                    CANONICAL_SOURCE,
                    "steps.plan.outputs.build_matrix",
                    "steps.other.outputs.build_matrix",
                ),
                "plan_ci.outputs.build_matrix",
            ),
            (
                "missing Miri output",
                replace_once(
                    CANONICAL_SOURCE,
                    "      miri_matrix: ${{ steps.plan.outputs.miri_matrix }}\n",
                    "",
                ),
                "plan_ci.outputs.miri_matrix",
            ),
            (
                "extra output",
                replace_once(
                    CANONICAL_SOURCE,
                    "      miri_enabled: ${{ steps.plan.outputs.miri_enabled }}\n",
                    "      miri_enabled: ${{ steps.plan.outputs.miri_enabled }}\n      surprise: ${{ steps.plan.outputs.surprise }}\n",
                ),
                "plan_ci.outputs.surprise",
            ),
            (
                "scalar outputs",
                replace_once(CANONICAL_SOURCE, "    outputs:\n", "    outputs: disabled\n"),
                "canonical nested mapping",
            ),
        ];
        for (label, source, expected) in cases {
            rejected(label, &source, expected);
        }
    }

    #[test]
    fn producer_is_an_unconditional_host_singleton_with_one_steps_mapping() {
        let header = "  plan_ci:\n    name: Plan ordinary CI work\n    runs-on: ubuntu-latest\n";
        let cases = [
            (
                "changed runner",
                replace_once(
                    CANONICAL_SOURCE,
                    header,
                    "  plan_ci:\n    name: Plan ordinary CI work\n    runs-on: self-hosted\n",
                ),
                ".runs-on",
            ),
            (
                "job container",
                replace_once(
                    CANONICAL_SOURCE,
                    header,
                    "  plan_ci:\n    name: Plan ordinary CI work\n    runs-on: ubuntu-latest\n    container: ignored.invalid/noop\n",
                ),
                ".container",
            ),
            (
                "strategy",
                replace_once(
                    CANONICAL_SOURCE,
                    header,
                    "  plan_ci:\n    name: Plan ordinary CI work\n    runs-on: ubuntu-latest\n    strategy:\n      matrix:\n        include: []\n",
                ),
                ".strategy",
            ),
            (
                "job condition",
                replace_once(
                    CANONICAL_SOURCE,
                    header,
                    "  plan_ci:\n    name: Plan ordinary CI work\n    runs-on: ubuntu-latest\n    if: github.ref == 'refs/heads/main'\n",
                ),
                ".if",
            ),
            (
                "continue on error",
                replace_once(
                    CANONICAL_SOURCE,
                    header,
                    "  plan_ci:\n    name: Plan ordinary CI work\n    runs-on: ubuntu-latest\n    continue-on-error: true\n",
                ),
                ".continue-on-error",
            ),
            (
                "duplicate steps mapping",
                replace_once(
                    CANONICAL_SOURCE,
                    "    steps:\n",
                    "    steps: []\n    steps:\n",
                ),
                ".steps",
            ),
            (
                "scalar steps mapping",
                replace_once(CANONICAL_SOURCE, "    steps:\n", "    steps: []\n"),
                "nested sequence",
            ),
        ];
        for (label, source, expected) in cases {
            rejected(label, &source, expected);
        }
    }

    #[test]
    fn producer_top_level_fields_permissions_and_environment_are_exact() {
        let header = "  plan_ci:\n    name: Plan ordinary CI work\n    runs-on: ubuntu-latest\n";
        let additions = [
            ("needs", "    needs: build_docker_env\n"),
            ("concurrency", "    concurrency: one-at-a-time\n"),
            ("environment", "    environment: protected\n"),
            ("services", "    services: {}\n"),
            ("timeout-minutes", "    timeout-minutes: 1\n"),
            ("defaults", "    defaults: {}\n"),
            ("uses", "    uses: example.invalid/owner/workflow@main\n"),
            ("with", "    with: {}\n"),
            ("secrets", "    secrets: inherit\n"),
        ];
        for (field, addition) in additions {
            let source = replace_once(CANONICAL_SOURCE, header, &format!("{header}{addition}"));
            rejected(field, &source, &format!("plan_ci.{field}"));
        }

        let cases = [
            (
                "missing name",
                replace_once(CANONICAL_SOURCE, "    name: Plan ordinary CI work\n", ""),
                "plan_ci.name",
            ),
            (
                "changed name",
                replace_once(
                    CANONICAL_SOURCE,
                    "name: Plan ordinary CI work",
                    "name: Maybe plan ordinary CI work",
                ),
                "plan_ci.name",
            ),
            (
                "write permissions",
                replace_once(CANONICAL_SOURCE, "      contents: read", "      contents: write"),
                "plan_ci.permissions.contents",
            ),
            (
                "extra permission",
                replace_once(
                    CANONICAL_SOURCE,
                    "      contents: read\n",
                    "      contents: read\n      id-token: write\n",
                ),
                "plan_ci.permissions.id-token",
            ),
            (
                "scalar permissions",
                replace_once(CANONICAL_SOURCE, "    permissions:\n", "    permissions: read-all\n"),
                "canonical nested mapping",
            ),
            (
                "artifact name",
                replace_once(CANONICAL_SOURCE, "CI_PLAN_ARTIFACT: ci-plan.json", "CI_PLAN_ARTIFACT: other.json"),
                "plan_ci.env.CI_PLAN_ARTIFACT",
            ),
            (
                "extra environment",
                replace_once(
                    CANONICAL_SOURCE,
                    "      CI_PLAN_ARTIFACT: ci-plan.json\n",
                    "      CI_PLAN_ARTIFACT: ci-plan.json\n      SURPRISE: value\n",
                ),
                "plan_ci.env.SURPRISE",
            ),
            (
                "duplicate environment field",
                replace_once(
                    CANONICAL_SOURCE,
                    "    env:\n      CI_PLAN_ARTIFACT: ci-plan.json\n",
                    "    env:\n      CI_PLAN_ARTIFACT: ci-plan.json\n    env:\n      CI_PLAN_ARTIFACT: ci-plan.json\n",
                ),
                "plan_ci.env",
            ),
        ];
        for (label, source, expected) in cases {
            rejected(label, &source, expected);
        }
    }

    #[test]
    fn producer_step_fields_environment_and_run_lines_are_exact() {
        let cases = [
            (
                "name",
                replace_once(CANONICAL_SOURCE, PLAN_STEP_NAME, "Maybe project the plan"),
                "canonical step declaration",
            ),
            (
                "ID",
                replace_once(CANONICAL_SOURCE, "        id: plan\n", "        id: other\n"),
                ".fields.id",
            ),
            (
                "duplicate ID",
                replace_once(
                    CANONICAL_SOURCE,
                    "        id: plan\n",
                    "        id: plan\n        id: plan\n",
                ),
                "exactly one canonical `plan` step ID",
            ),
            (
                "working directory",
                replace_once(
                    CANONICAL_SOURCE,
                    "        working-directory: zerocopy\n",
                    "        working-directory: .\n",
                ),
                ".fields.working-directory",
            ),
            (
                "event source",
                replace_once(
                    CANONICAL_SOURCE,
                    "EVENT_NAME: ${{ github.event_name }}",
                    "EVENT_NAME: ${{ github.ref }}",
                ),
                ".env.EVENT_NAME",
            ),
            (
                "conditional step",
                replace_once(
                    CANONICAL_SOURCE,
                    "        id: plan\n",
                    "        id: plan\n        if: success()\n",
                ),
                ".shape",
            ),
            (
                "weakened strict mode",
                replace_once(
                    CANONICAL_SOURCE,
                    "          set -euo pipefail\n",
                    "          set -eo pipefail\n",
                ),
                ".run",
            ),
            (
                "renamed command",
                replace_once(CANONICAL_SOURCE, "ci github-plan", "ci wrong-command"),
                ".run",
            ),
            (
                "unquoted event",
                replace_once(CANONICAL_SOURCE, "\"$EVENT_NAME\"", "$EVENT_NAME"),
                ".run",
            ),
        ];
        for (label, source, expected) in cases {
            rejected(label, &source, expected);
        }
    }

    #[test]
    fn producer_rejects_startup_controls_ambient_path_and_shebang_dispatch() {
        let shell = format!("        shell: {TRUSTED_SHELL}\n");
        let mut cases = vec![
            ("bare Bash", replace_once(CANONICAL_SOURCE, &shell, "        shell: bash\n")),
            (
                "unprivileged shell",
                replace_once(CANONICAL_SOURCE, " -p -euo pipefail", " -euo pipefail"),
            ),
            (
                "ambient PATH",
                replace_once(
                    CANONICAL_SOURCE,
                    "PATH=/home/runner/.cargo/bin:/usr/local/bin:/usr/bin:/bin",
                    "PATH=\"$PATH\"",
                ),
            ),
            (
                "cargo shebang",
                replace_once(
                    CANONICAL_SOURCE,
                    "/bin/bash --noprofile --norc -p ./cargo.sh",
                    "./cargo.sh",
                ),
            ),
        ];
        for variable in ["BASH_ENV", "ENV", "SHELLOPTS", "BASHOPTS"] {
            cases.push((variable, replace_once(CANONICAL_SOURCE, &format!("-u {variable} "), "")));
        }
        for (label, source) in cases {
            rejected(
                label,
                &source,
                if label == "ambient PATH" || label == "cargo shebang" {
                    ".run"
                } else {
                    ".fields.shell"
                },
            );
        }
    }

    #[test]
    fn command_is_globally_unique_but_step_names_are_scoped_to_steps() {
        for (label, run) in [
            ("canonical run key", format!("run: ./cargo.sh ci {GITHUB_PLAN_COMMAND}")),
            ("spaced run key", format!("run : ./cargo.sh ci {GITHUB_PLAN_COMMAND}")),
            ("quoted run key", format!("\"run\": ./cargo.sh ci {GITHUB_PLAN_COMMAND}")),
            ("trailing whitespace", format!("run: ./cargo.sh ci {GITHUB_PLAN_COMMAND}   ")),
        ] {
            let duplicate_command = replace_once(
                CANONICAL_SOURCE,
                "  next_job:\n",
                &format!("  next_job:\n    steps:\n      - {run}\n"),
            );
            rejected(label, &duplicate_command, "command mention");
        }

        let duplicate_name = replace_once(
            CANONICAL_SOURCE,
            "  next_job:\n",
            &format!(
                "  next_job:\n    steps:\n      - name: {PLAN_STEP_NAME}\n        run: echo unrelated\n"
            ),
        );
        audit_source(&duplicate_name).unwrap();

        let comment = format!("# ./cargo.sh ci {GITHUB_PLAN_COMMAND}\n{CANONICAL_SOURCE}");
        audit_source(&comment).unwrap();
    }

    #[test]
    fn line_endings_and_diagnostics_fail_closed() {
        rejected("CRLF", &CANONICAL_SOURCE.replace('\n', "\r\n"), "LF line endings");

        let source = CANONICAL_SOURCE.replace(PLAN_JOB, "plan_ci\u{7}");
        let error: PlannedAdapterViolations = audit_source(&source).unwrap_err();
        assert!(!error.to_string().contains('\u{7}'));
    }
}
