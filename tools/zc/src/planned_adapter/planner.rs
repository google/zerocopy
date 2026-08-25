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
        audit_unique_run_mentions, audited_steps_block, compare_map, exact_step_lines, find_job,
        indentation, job_field_location, job_fields, nested_mapping, step_field_location,
        unique_field, Field, MappingExpectation, RunForm, StepExpectation,
    },
    ViolationSink,
};
use crate::workflow_protocol::{
    BUILD_MATRIX_OUTPUT, CI_EVENT_OPTION, GITHUB_OUTPUT_OPTION, GITHUB_PLAN_COMMAND,
    MIRI_ENABLED_OUTPUT, MIRI_MATRIX_OUTPUT, PLANNER_PATH, PLAN_ARTIFACT_OPTION, PLAN_JOB,
    PLAN_STEP_ID, PLAN_STEP_NAME, REPOSITORY_WORKING_DIRECTORY, TRUSTED_SHELL, WORKFLOW_PATH,
};

const PLAN_JOB_FIELDS: &[&str] = &["name", "runs-on", "permissions", "outputs", "env", "steps"];
const PLAN_DISPLAY_NAME: &str = "Plan ordinary CI work";
const PLAN_ARTIFACT_ENVIRONMENT: &str = "CI_PLAN_ARTIFACT";
const PLAN_ARTIFACT_NAME: &str = "ci-plan.json";
// GitHub merges the workflow-level environment into every job. Require one
// canonical spelling and position for every top-level declaration so a second
// YAML spelling such as `'env':` cannot override the mapping which the narrower
// environment audit below sees. This also makes a new root-level `defaults` or
// merge key fail review instead of silently changing command behavior.
//
// Keep this list synchronized with the indentation-zero declarations in
// `.github/workflows/ci.yml`. This list deliberately fixes only the root
// grammar and order; the complete `env` contents are audited below. Other
// nested root mappings retain their existing workflow checks.
const WORKFLOW_ROOT_DECLARATIONS: &[&str] =
    &["name: Build & Tests", "'on':", "permissions:", "concurrency:", "env:", "jobs:"];
// These three steps are a source-level contract with the Rust planner and the
// local upload action. Keep this list synchronized with `.github/workflows/ci.yml`:
// changing the artifact name, checkout credential behavior, or step order here
// without changing that workflow would make the audit describe a different
// bridge than the one GitHub executes.
const CHECKOUT_STEP: &[&str] = &[
    "      - uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1",
    "        with:",
    "          persist-credentials: false",
];
const UPLOAD_STEP: &[&str] = &[
    "      - name: Upload detailed plan for review",
    "        uses: ./.github/actions/upload-file-artifact",
    "        with:",
    "          name: ${{ env.CI_PLAN_ARTIFACT }}",
    "          path: ${{ runner.temp }}/${{ env.CI_PLAN_ARTIFACT }}",
    "          retention-days: 14",
];

pub(super) fn audit(lines: &[&str], errors: &mut ViolationSink) {
    audit_workflow_environment(lines, errors);
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

/// Audits every value inherited from the workflow by the planner and actions.
///
/// Step- and job-level audits already reject unmodeled environment entries in
/// the jobs they own. The workflow mapping is the remaining merge layer. Check
/// the complete map rather than a list of dangerous variable names: Cargo,
/// rustup, compilers, shells, and third-party actions can all acquire new
/// behavior-bearing variables over time.
fn audit_workflow_environment(lines: &[&str], errors: &mut ViolationSink) {
    // Do not try to recognize all equivalent YAML key spellings. Instead,
    // require the workflow's small root grammar exactly. This rejects duplicate
    // keys even when a YAML parser would normalize a quoted or tagged key to
    // `env`, and it keeps future root-level defaults inside this review
    // boundary.
    let root_declarations = lines
        .iter()
        .filter(|line| {
            indentation(line) == 0 && !line.trim().is_empty() && !line.trim_start().starts_with('#')
        })
        .copied()
        .collect::<Vec<_>>();
    if root_declarations != WORKFLOW_ROOT_DECLARATIONS {
        errors.push(
            WORKFLOW_PATH,
            format!(
                "top-level declarations must be exactly {WORKFLOW_ROOT_DECLARATIONS:?} in order, found {root_declarations:?}"
            ),
        );
    }

    // The root check above proves that this is the only workflow-level `env`
    // declaration. Use the same exact nested-mapping audit as job and step
    // environments for its complete contents.
    let mut fields = Vec::new();
    for (line_number, line) in lines.iter().enumerate() {
        if indentation(line) != 0 || line.trim_start().starts_with('#') {
            continue;
        }
        let Some((key, remainder)) = line.split_once(':') else {
            continue;
        };
        if key != "env" {
            continue;
        }
        if line.trim_end() != *line {
            errors.push(
                format!(".github/workflows/ci.yml:{}", line_number + 1),
                "the workflow environment declaration must not trail spaces",
            );
        }
        let value = if remainder.is_empty() {
            ""
        } else {
            remainder.strip_prefix(' ').unwrap_or(remainder)
        };
        fields.push(Field { line: line_number, indent: 0, key, value });
    }
    let expected = BTreeMap::from([
        ("CARGO_NET_RETRY".to_owned(), "\"10\"".to_owned()),
        ("CARGO_TERM_COLOR".to_owned(), "always".to_owned()),
        ("CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN".to_owned(), "1".to_owned()),
        ("RUSTDOCFLAGS".to_owned(), "-Dwarnings --cfg=zerocopy_unstable_ptr".to_owned()),
        ("RUSTFLAGS".to_owned(), "-Dwarnings".to_owned()),
        ("RUSTUP_MAX_RETRIES".to_owned(), "\"10\"".to_owned()),
        ("ZC_CI_IMAGE".to_owned(), "zerocopy-ci:local".to_owned()),
        ("ZC_CI_IMAGE_ARCHIVE".to_owned(), "zerocopy-ci.tar".to_owned()),
        (
            "ZC_NIGHTLY_MIRIFLAGS".to_owned(),
            "\"-Zmiri-strict-provenance -Zmiri-backtrace=full\"".to_owned(),
        ),
        ("ZC_NIGHTLY_RUSTFLAGS".to_owned(), "-Zrandomize-layout".to_owned()),
    ]);
    audit_exact_mapping(
        lines,
        lines.len(),
        &fields,
        MappingExpectation { job: "workflow", field: "env", values: &expected },
        errors,
    );
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
        let actual_steps = exact_step_lines(lines, &steps);
        if actual_steps.len() != 3 {
            errors.push(
                job_field_location(PLAN_JOB, "steps"),
                format!(
                    "plan_ci.steps must contain exactly three steps, found {}",
                    actual_steps.len()
                ),
            );
        } else {
            // The first and last steps are intentionally checked as complete
            // source snippets. This makes additions, reordering, action-pin
            // changes, and artifact-path drift fail closed at the handwritten
            // workflow/Rust protocol boundary.
            for (actual, expected, label) in [
                (&actual_steps[0], CHECKOUT_STEP, "checkout"),
                (&actual_steps[2], UPLOAD_STEP, "upload"),
            ] {
                if actual != expected {
                    errors.push(
                        job_field_location(PLAN_JOB, "steps"),
                        format!("{label} step must match the exact canonical contract"),
                    );
                }
            }
        }
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
        ci::POLICY_PATH,
        inventory::RepositoryInventory,
        policy::Policy,
        workflow::{ReviewedWorkflowJobs, WORKFLOW_REGISTRY_PATH},
        workflow_protocol::{GITHUB_PLAN_COMMAND, PLAN_JOB, PLAN_STEP_NAME, TRUSTED_SHELL},
    };

    const CANONICAL_SOURCE: &str = r#"name: Build & Tests
'on':
  pull_request:
permissions:
  contents: read
concurrency:
  group: test
env:
  CARGO_TERM_COLOR: always
  CARGO_NET_RETRY: "10"
  RUSTUP_MAX_RETRIES: "10"
  ZC_CI_IMAGE: zerocopy-ci:local
  ZC_CI_IMAGE_ARCHIVE: zerocopy-ci.tar
  RUSTFLAGS: -Dwarnings
  RUSTDOCFLAGS: -Dwarnings --cfg=zerocopy_unstable_ptr
  ZC_NIGHTLY_RUSTFLAGS: -Zrandomize-layout
  ZC_NIGHTLY_MIRIFLAGS: "-Zmiri-strict-provenance -Zmiri-backtrace=full"
  CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN: 1
jobs:
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
      - uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1
        with:
          persist-credentials: false

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

      - name: Upload detailed plan for review
        uses: ./.github/actions/upload-file-artifact
        with:
          name: ${{ env.CI_PLAN_ARTIFACT }}
          path: ${{ runner.temp }}/${{ env.CI_PLAN_ARTIFACT }}
          retention-days: 14
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

    fn reorder_plan_steps(source: &str, order: [usize; 3]) -> String {
        let starts = [
            source.find("      - uses: actions/checkout@").unwrap(),
            source.find("      - name: Validate inputs and project the plan").unwrap(),
            source.find("      - name: Upload detailed plan for review").unwrap(),
        ];
        let end = source.find("  next_job:").unwrap();
        let mut chunks = Vec::new();
        for start in &starts {
            let chunk_end =
                starts.iter().copied().filter(|candidate| *candidate > *start).min().unwrap_or(end);
            chunks.push(&source[*start..chunk_end]);
        }
        format!(
            "{}{}{}{}{}",
            &source[..starts[0]],
            chunks[order[0]],
            chunks[order[1]],
            chunks[order[2]],
            &source[end..]
        )
    }

    #[test]
    fn accepts_the_literal_fixture_and_live_workflow() {
        audit_source(CANONICAL_SOURCE).unwrap();

        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap();
        let reviewed = ReviewedWorkflowJobs::read(root.join(WORKFLOW_REGISTRY_PATH)).unwrap();
        let policy = Policy::read(root.join(POLICY_PATH)).unwrap();
        let repository = RepositoryInventory::audit(&root, &policy).unwrap();
        audit_planned_adapter(&root, &reviewed, &repository).unwrap();
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
    fn workflow_environment_is_a_complete_inherited_contract() {
        let cases = [
            (
                "added behavior variable",
                replace_once(
                    CANONICAL_SOURCE,
                    "  CARGO_TERM_COLOR: always\n",
                    "  CARGO_TERM_COLOR: always\n  LD_PRELOAD: /tmp/interceptor.so\n",
                ),
                "workflow.env.LD_PRELOAD",
            ),
            (
                "changed behavior variable",
                replace_once(
                    CANONICAL_SOURCE,
                    "  RUSTFLAGS: -Dwarnings\n",
                    "  RUSTFLAGS: -Awarnings\n",
                ),
                "workflow.env.RUSTFLAGS",
            ),
            (
                "removed behavior variable",
                replace_once(
                    CANONICAL_SOURCE,
                    "  RUSTDOCFLAGS: -Dwarnings --cfg=zerocopy_unstable_ptr\n",
                    "",
                ),
                "workflow.env.RUSTDOCFLAGS",
            ),
            (
                "duplicate workflow environment",
                replace_once(
                    CANONICAL_SOURCE,
                    "jobs:\n",
                    "env:\n  RUSTC_WRAPPER: /tmp/wrapper\njobs:\n",
                ),
                "workflow.env",
            ),
            (
                "quoted duplicate workflow environment",
                replace_once(
                    CANONICAL_SOURCE,
                    "jobs:\n",
                    "'env':\n  RUSTC_WRAPPER: /tmp/wrapper\njobs:\n",
                ),
                "top-level declarations",
            ),
            (
                "root-level defaults",
                replace_once(
                    CANONICAL_SOURCE,
                    "jobs:\n",
                    "defaults:\n  run:\n    shell: bash\njobs:\n",
                ),
                "top-level declarations",
            ),
            (
                "scalar workflow environment",
                replace_once(
                    CANONICAL_SOURCE,
                    "env:\n  CARGO_TERM_COLOR",
                    "env: inherited\n  CARGO_TERM_COLOR",
                ),
                "canonical nested mapping",
            ),
            (
                "scalar continuation",
                replace_once(
                    CANONICAL_SOURCE,
                    "env:\n  CARGO_TERM_COLOR",
                    "env: inherited\n  RUSTC_WRAPPER: /tmp/wrapper\n  CARGO_TERM_COLOR",
                ),
                "canonical nested mapping",
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

    #[test]
    fn scalar_fields_reject_indented_continuations_but_mappings_remain_valid() {
        let source = replace_once(
            CANONICAL_SOURCE,
            "    name: Plan ordinary CI work\n    runs-on: ubuntu-latest\n",
            "    name: Plan ordinary CI work\n    runs-on: ubuntu-latest\n      accidentally-nested\n",
        );
        rejected("scalar continuation", &source, "indented scalar continuation");
        audit_source(CANONICAL_SOURCE).unwrap();
    }

    #[test]
    fn plan_steps_are_an_exact_three_step_contract() {
        let bare_item_before_checkout = replace_once(
            CANONICAL_SOURCE,
            "    steps:\n      - uses: actions/checkout@",
            "    steps:\n      -\n        name: Unexpected hidden step\n        run: echo unexpected\n      - uses: actions/checkout@",
        );
        rejected("bare item before checkout", &bare_item_before_checkout, "exactly three steps");

        // The field-by-field planner audit stops at the bare item's
        // indentation. The exact sequence audit must still see the item,
        // rather than silently assigning it to the preceding planner block.
        let bare_item_after_planner = replace_once(
            CANONICAL_SOURCE,
            "            --artifact \"$RUNNER_TEMP/$CI_PLAN_ARTIFACT\"\n\n      - name: Upload detailed plan for review",
            "            --artifact \"$RUNNER_TEMP/$CI_PLAN_ARTIFACT\"\n\n      -\n        name: Unexpected hidden step\n        run: echo unexpected\n\n      - name: Upload detailed plan for review",
        );
        rejected("bare item after planner", &bare_item_after_planner, "exactly three steps");

        let extra = replace_once(
            CANONICAL_SOURCE,
            "      - name: Validate inputs and project the plan\n",
            "      - name: Unexpected extra step\n        run: echo unexpected\n\n      - name: Validate inputs and project the plan\n",
        );
        rejected("extra planner step", &extra, "exactly three steps");

        let inserted_run = replace_once(
            CANONICAL_SOURCE,
            "      - name: Validate inputs and project the plan\n",
            "      - run: echo unexpected\n\n      - name: Validate inputs and project the plan\n",
        );
        rejected("inserted run step", &inserted_run, "exactly three steps");

        let inserted_uses = replace_once(
            CANONICAL_SOURCE,
            "      - name: Validate inputs and project the plan\n",
            "      - uses: ./unexpected-action\n\n      - name: Validate inputs and project the plan\n",
        );
        rejected("inserted uses step", &inserted_uses, "exactly three steps");

        let reordered = reorder_plan_steps(CANONICAL_SOURCE, [1, 2, 0]);
        rejected("reordered planner steps", &reordered, "checkout step");

        let changed_checkout = replace_once(
            CANONICAL_SOURCE,
            "          persist-credentials: false",
            "          persist-credentials: true",
        );
        rejected("checkout credentials", &changed_checkout, "checkout step");

        let changed_checkout_pin = replace_once(
            CANONICAL_SOURCE,
            "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
            "actions/checkout@0000000000000000000000000000000000000000",
        );
        rejected("checkout action pin", &changed_checkout_pin, "checkout step");

        let changed_upload_action = replace_once(
            CANONICAL_SOURCE,
            "./.github/actions/upload-file-artifact",
            "./.github/actions/other-upload-action",
        );
        rejected("upload action", &changed_upload_action, "upload step");

        let changed_artifact_name = replace_once(
            CANONICAL_SOURCE,
            "          name: ${{ env.CI_PLAN_ARTIFACT }}",
            "          name: unexpected-artifact",
        );
        rejected("artifact name", &changed_artifact_name, "upload step");

        let changed_artifact_path = replace_once(
            CANONICAL_SOURCE,
            "path: ${{ runner.temp }}/${{ env.CI_PLAN_ARTIFACT }}",
            "path: unexpected-path",
        );
        rejected("artifact path", &changed_artifact_path, "upload step");

        let changed_upload_retention = replace_once(
            CANONICAL_SOURCE,
            "          retention-days: 14",
            "          retention-days: 7",
        );
        rejected("upload retention", &changed_upload_retention, "upload step");
    }
}
