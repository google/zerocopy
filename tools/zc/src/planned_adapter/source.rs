// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Private canonical-source scanner used by the focused bridge audits.

use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Range,
};

use super::{yaml_source, ViolationSink};
use crate::workflow_protocol::{HOST_RUNNER, WORKFLOW_PATH};

#[derive(Clone)]
pub(super) struct StepsBlock {
    pub range: Range<usize>,
    marker_indent: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum RunForm {
    Block,
    Inline,
}

pub(super) struct StepExpectation<'a> {
    pub job: &'a str,
    pub name: &'a str,
    pub root_fields: &'a [&'a str],
    pub scalar_fields: &'a BTreeMap<String, String>,
    pub environment: &'a BTreeMap<String, String>,
    pub run: &'a [String],
    pub run_form: RunForm,
}

pub(super) struct MappingExpectation<'a> {
    pub job: &'a str,
    pub field: &'a str,
    pub values: &'a BTreeMap<String, String>,
}

#[derive(Clone, Copy)]
pub(super) struct Field<'a> {
    pub line: usize,
    pub indent: usize,
    pub key: &'a str,
    pub value: &'a str,
}

/// Splits workflow source only after proving that Rust and YAML see the same
/// line boundaries.
///
/// The bridge scanners deliberately accept one canonical source spelling.
/// YAML additionally treats carriage return, next-line, line-separator, and
/// paragraph-separator characters as line breaks, while [`str::lines`] does
/// not split all of them. If one were allowed through, executable YAML could
/// follow a scanner-visible comment on what Rust considers the same line.
/// Repository reads normalize well-formed CRLF before this boundary, so every
/// remaining non-LF YAML line break is rejected rather than normalized here.
pub(super) fn canonical_workflow_lines<'a>(
    source: &'a str,
    errors: &mut ViolationSink,
) -> Option<Vec<&'a str>> {
    if source
        .chars()
        .any(|character| matches!(character, '\r' | '\u{85}' | '\u{2028}' | '\u{2029}'))
    {
        errors.push(WORKFLOW_PATH, "workflow must use LF as its only YAML line break");
        return None;
    }
    if let Err(violation) = yaml_source::require_line_local_flow_nodes(source) {
        let location =
            violation.line.map(line_location).unwrap_or_else(|| WORKFLOW_PATH.to_owned());
        errors.push(location, violation.message);
        // Continue only to aggregate useful source-level diagnostics. The
        // recorded violation is never removed, so downstream scanners cannot
        // turn this source into an accepted workflow even though their
        // indentation assumptions are no longer authoritative.
    }
    let lines = source.lines().collect::<Vec<_>>();

    // The source audits below deliberately recognize a small block-style YAML
    // grammar instead of implementing YAML. Before indentation can establish
    // structure, prove that no earlier token could have opened a multiline
    // quoted or flow scalar. YAML permits scalar content to deindent all the
    // way to column zero, so merely finding `jobs:` at column zero is not a
    // sufficient boundary: it could be inert text inside such a scalar.
    //
    // The complete workflow starts with its exact `name` entry. Focused unit
    // fixtures start directly with `jobs:`. Blank lines and source comments
    // cannot open YAML structure and may precede either anchor. Once one of
    // these exact first entries establishes a root block mapping at column
    // zero, `planner::WORKFLOW_ROOT_DECLARATIONS` proves the complete root
    // grammar for production, and `canonical_jobs_block` below proves the
    // complete tail grammar shared with focused fixtures. Keep all three
    // checks coordinated if either accepted source form changes.
    let anchor = lines
        .iter()
        .copied()
        .find(|line| !line.trim().is_empty() && !line.trim_start().starts_with('#'));
    if !matches!(anchor, Some("name: Build & Tests" | "jobs:")) {
        errors.push(
            WORKFLOW_PATH,
            "the first significant line must establish the canonical root block mapping with `name: Build & Tests` or `jobs:`",
        );
        return None;
    }

    Some(lines)
}

pub(super) fn find_job(
    lines: &[&str],
    job: &str,
    errors: &mut ViolationSink,
) -> Option<Range<usize>> {
    let jobs = canonical_jobs_block(lines, errors)?;
    let marker = format!("  {job}:");
    let starts = lines
        .iter()
        .enumerate()
        .take(jobs.end)
        .skip(jobs.start)
        .filter_map(|(index, line)| (*line == marker).then_some(index))
        .collect::<Vec<_>>();
    if starts.len() != 1 {
        errors.push(
            job_location(job),
            format!(
                "expected exactly one canonical job declaration inside the root `jobs` mapping, found {}",
                starts.len()
            ),
        );
        return None;
    }
    let start = starts[0];
    let end = lines
        .iter()
        .enumerate()
        .take(jobs.end)
        .skip(start + 1)
        .find_map(|(index, line)| {
            (!line.trim().is_empty()
                && !line.trim_start().starts_with('#')
                && indentation(line) == 2)
                .then_some(index)
        })
        .unwrap_or(jobs.end);
    Some(start..end)
}

fn canonical_jobs_block(lines: &[&str], errors: &mut ViolationSink) -> Option<Range<usize>> {
    // A canonical-looking job declaration elsewhere in the document is not a
    // job. In particular, a scalar in another root field may contain an exact
    // textual copy of the reviewed job. `canonical_workflow_lines` first
    // proves that the document began as a root block mapping; only after that
    // precondition can this exact indentation-zero `jobs:` line establish the
    // real root boundary without reproducing YAML's scalar grammar.
    let jobs_starts = lines
        .iter()
        .enumerate()
        .filter_map(|(index, line)| (*line == "jobs:").then_some(index))
        .collect::<Vec<_>>();
    if jobs_starts.len() != 1 {
        errors.push(
            WORKFLOW_PATH,
            format!(
                "expected exactly one canonical root `jobs:` declaration, found {}",
                jobs_starts.len()
            ),
        );
        return None;
    }
    let jobs_start = jobs_starts[0];
    // `jobs` is the final root entry. Scanning through EOF is intentional: a
    // later alternate spelling such as `'jobs':` must be rejected rather than
    // ending this range and overriding the mapping which the focused audit
    // inspected. In the full workflow, this invariant is also coordinated
    // with `planner::WORKFLOW_ROOT_DECLARATIONS`, where `jobs:` is last.
    let jobs_end = lines.len();
    let jobs = jobs_start + 1..jobs_end;

    // Binding only to the root range is not enough. YAML permits a direct job
    // at one or three spaces, and a multiline quoted scalar in such a job can
    // contain a two-space canonical-looking decoy. Fix the complete direct
    // child grammar: every job header has exactly two spaces, an unquoted safe
    // identifier, an empty value, and no trailing text. All nested job content
    // begins at four spaces. This makes any two-space marker found below a real
    // YAML job key rather than scalar content.
    let mut valid = true;
    let mut saw_job = false;
    for (index, line) in lines.iter().enumerate().take(jobs.end).skip(jobs.start) {
        if line.trim().is_empty() || line.trim_start().starts_with('#') {
            continue;
        }
        let indent = indentation(line);
        if indent == 2 {
            let canonical = line.trim_end() == *line
                && parse_mapping(&line[2..])
                    .is_some_and(|(job, value)| is_job_id(job) && value.is_empty());
            if canonical {
                saw_job = true;
            } else {
                valid = false;
                errors.push(
                    line_location(index + 1),
                    "direct jobs must use canonical unquoted `  job_id:` declarations",
                );
            }
        } else if indent < 4 {
            valid = false;
            errors.push(
                line_location(index + 1),
                "the root `jobs` mapping permits significant lines only at canonical two-space job headers or inside their four-space content",
            );
        } else if !saw_job {
            valid = false;
            errors.push(
                line_location(index + 1),
                "nested job content must follow a canonical two-space job declaration",
            );
        }
    }

    valid.then_some(jobs)
}

pub(super) fn job_fields<'a>(
    lines: &'a [&'a str],
    job: Range<usize>,
    job_name: &str,
    errors: &mut ViolationSink,
) -> Vec<Field<'a>> {
    job_fields_at_indent(lines, job, job_name, 4, errors)
}

pub(super) fn job_fields_at_indent<'a>(
    lines: &'a [&'a str],
    job: Range<usize>,
    job_name: &str,
    field_indent: usize,
    errors: &mut ViolationSink,
) -> Vec<Field<'a>> {
    let mut fields: Vec<Field<'a>> = Vec::new();
    for (index, line) in lines.iter().enumerate().take(job.end).skip(job.start + 1) {
        if line.trim().is_empty() || line.trim_start().starts_with('#') {
            continue;
        }
        let indent = indentation(line);
        // A direct child mapping may choose any indentation greater than its
        // parent in YAML. This scanner intentionally recognizes only the
        // reviewed four-space spelling. A shallower valid mapping could make
        // canonical-looking lines into multiline scalar content, causing the
        // scanner to audit a decoy while Actions executes the shallower job.
        // Deeper lines remain valid children of canonical mapping and sequence
        // fields and are checked by their dedicated audits below.
        if indent < field_indent {
            errors.push(
                line_location(index + 1),
                format!(
                    "job `{job_name}` contains significant content shallower than its canonical {field_indent}-space field indentation"
                ),
            );
            continue;
        }
        // A scalar field cannot acquire an indented continuation without
        // changing its meaning.  We must reject that ambiguity, while still
        // allowing children of mapping-valued fields such as `permissions:`.
        // The latter have an empty value and are therefore deliberately left
        // alone for the dedicated nested-mapping audit below.
        if indent > field_indent
            && fields.last().map(|field| !field.value.is_empty()).unwrap_or(false)
        {
            errors.push(
                line_location(index + 1),
                format!(
                    "field `{}` cannot have an indented scalar continuation",
                    fields.last().unwrap().key
                ),
            );
            continue;
        }
        if indent != field_indent || line[field_indent..].starts_with("- ") {
            continue;
        }
        if line.trim_end() != *line {
            errors.push(line_location(index + 1), "semantic bridge lines must not trail spaces");
            continue;
        }
        let Some((key, value)) = parse_mapping(&line[field_indent..]) else {
            errors.push(
                line_location(index + 1),
                format!("job `{job_name}` fields must use canonical unquoted `key: value` form"),
            );
            continue;
        };
        fields.push(Field { line: index, indent: field_indent, key, value });
    }
    fields
}

pub(super) fn unique_field<'a>(
    fields: &'a [Field<'a>],
    key: &str,
    job: &str,
    errors: &mut ViolationSink,
) -> Option<&'a Field<'a>> {
    let found = fields.iter().filter(|field| field.key == key).collect::<Vec<_>>();
    match found.as_slice() {
        [field] => Some(field),
        [] => {
            errors.push(job_field_location(job, key), "required field is absent");
            None
        }
        _ => {
            errors.push(
                job_field_location(job, key),
                format!("field appears {} times; expected exactly once", found.len()),
            );
            None
        }
    }
}

pub(super) fn audit_exact_job_fields(
    fields: &[Field<'_>],
    job: &str,
    expected: &[&str],
    errors: &mut ViolationSink,
) {
    let expected = expected.iter().copied().collect::<BTreeSet<_>>();
    let mut counts = BTreeMap::new();
    for field in fields {
        *counts.entry(field.key).or_insert(0usize) += 1;
    }

    for field in &expected {
        match counts.get(field) {
            None => errors.push(job_field_location(job, field), "required field is absent"),
            Some(1) => {}
            Some(count) => errors.push(
                job_field_location(job, field),
                format!("field appears {count} times; expected exactly once"),
            ),
        }
    }
    for field in counts.keys() {
        if !expected.contains(field) {
            errors.push(
                job_field_location(job, field),
                "field is not part of the exact planned-job workflow bridge",
            );
        }
    }
}

pub(super) fn audit_exact_scalar_field(
    fields: &[Field<'_>],
    job: &str,
    field: &str,
    expected: &str,
    errors: &mut ViolationSink,
) {
    let Some(actual) = unique_field(fields, field, job, errors) else {
        return;
    };
    if actual.value != expected {
        errors.push(
            job_field_location(job, field),
            format!("expected `{expected}`, found `{}`", escape_control_characters(actual.value)),
        );
    }
}

pub(super) fn audit_exact_mapping(
    lines: &[&str],
    block_end: usize,
    fields: &[Field<'_>],
    expected: MappingExpectation<'_>,
    errors: &mut ViolationSink,
) {
    let Some(parent) = unique_field(fields, expected.field, expected.job, errors) else {
        return;
    };
    if !parent.value.is_empty() {
        errors.push(
            job_field_location(expected.job, expected.field),
            format!("{} must use the canonical nested mapping form", expected.field),
        );
        return;
    }
    let actual = nested_mapping(lines, parent, block_end, expected.job, errors);
    compare_map(job_field_location(expected.job, expected.field), expected.values, &actual, errors);
}

pub(super) fn audit_read_permissions(
    lines: &[&str],
    block_end: usize,
    fields: &[Field<'_>],
    job: &str,
    errors: &mut ViolationSink,
) {
    let expected = BTreeMap::from([("contents".to_owned(), "read".to_owned())]);
    audit_exact_mapping(
        lines,
        block_end,
        fields,
        MappingExpectation { job, field: "permissions", values: &expected },
        errors,
    );
}

pub(super) fn nested_mapping(
    lines: &[&str],
    parent: &Field<'_>,
    block_end: usize,
    job: &str,
    errors: &mut ViolationSink,
) -> BTreeMap<String, String> {
    let end = nested_block_end(lines, parent, block_end);
    let child_indent = parent.indent + 2;
    let mut mapping = BTreeMap::new();
    for (index, line) in lines.iter().enumerate().take(end).skip(parent.line + 1) {
        if line.trim().is_empty() || line.trim_start().starts_with('#') {
            continue;
        }
        if indentation(line) != child_indent || line.trim_end() != *line {
            errors.push(
                line_location(index + 1),
                format!("`{job}.{}` must contain only canonical scalar entries", parent.key),
            );
            continue;
        }
        let Some((key, value)) = parse_mapping(&line[child_indent..]) else {
            errors.push(
                line_location(index + 1),
                format!("`{job}.{}` entries must use canonical `key: value` form", parent.key),
            );
            continue;
        };
        if value.is_empty() {
            errors.push(
                line_location(index + 1),
                format!("`{job}.{}.{key}` must have one scalar value", parent.key),
            );
        } else if mapping.insert(key.to_owned(), value.to_owned()).is_some() {
            errors.push(
                line_location(index + 1),
                format!("`{job}.{}` repeats key `{key}`", parent.key),
            );
        }
    }
    mapping
}

pub(super) fn audited_steps_block(
    fields: &[Field<'_>],
    job: Range<usize>,
    job_name: &str,
    marker_indent: usize,
    errors: &mut ViolationSink,
) -> Option<StepsBlock> {
    let steps = unique_field(fields, "steps", job_name, errors)?;
    if !steps.value.is_empty() {
        errors.push(
            job_field_location(job_name, "steps"),
            "steps must use the canonical nested sequence form",
        );
        return None;
    }
    let end = fields
        .iter()
        .filter_map(|field| (field.line > steps.line).then_some(field.line))
        .min()
        .unwrap_or(job.end);
    Some(StepsBlock { range: steps.line + 1..end, marker_indent })
}

/// Returns the significant source lines for each top-level item in `steps`.
///
/// This is intentionally source-oriented rather than a general YAML parser:
/// the planner workflow is a reviewed bridge whose exact checkout, planner,
/// and artifact-upload steps must remain coordinated with the Rust protocol.
/// Full-line YAML comments remain free, but a comment indented beneath any
/// block scalar is data rather than a YAML comment. Preserve those lines. In
/// particular, Actions expands `${{ ... }}` in a `run: |` scalar before
/// invoking the shell, even on a line Bash will otherwise treat as a comment;
/// non-shell scalars such as `cache-from: |` also treat the line literally.
pub(super) fn exact_step_lines<'a>(lines: &'a [&'a str], steps: &StepsBlock) -> Vec<Vec<&'a str>> {
    let starts = lines
        .iter()
        .enumerate()
        .filter_map(|(index, line)| {
            // Treat every significant line at item indentation as a boundary,
            // including syntax other than the canonical `- ...` form. YAML
            // permits a bare `-` followed by an indented mapping; filtering
            // only for `- ` would make that entire step disappear before the
            // callers compare exact counts and markers. Unfamiliar syntax is
            // therefore returned as its own block and rejected explicitly.
            (steps.range.contains(&index)
                && !line.trim().is_empty()
                && !line.trim_start().starts_with('#')
                && indentation(line) == steps.marker_indent)
                .then_some(index)
        })
        .collect::<Vec<_>>();
    starts
        .iter()
        .enumerate()
        .map(|(position, start)| {
            let end = starts.get(position + 1).copied().unwrap_or(steps.range.end);
            let mut exact = Vec::new();
            let mut block_scalar_indent = None;
            for line in &lines[*start..end] {
                // Empty scalar lines cannot contain Actions expressions. Keep
                // ignoring them here; field-by-field run audits preserve them
                // where shell continuation semantics matter.
                if line.trim().is_empty() {
                    continue;
                }
                let indent = indentation(line);
                if block_scalar_indent.is_some_and(|parent| indent > parent) {
                    exact.push(*line);
                    continue;
                }
                block_scalar_indent = None;
                if line.trim_start().starts_with('#') {
                    continue;
                }
                exact.push(*line);
                if is_block_scalar_header(&line[indent..]) {
                    block_scalar_indent = Some(indent);
                }
            }
            exact
        })
        .collect()
}

/// Recognizes the complete YAML block-scalar indicator grammar.
///
/// Exact callers accept only their canonical source lines, so this helper is
/// not a general YAML key parser. It only determines whether following
/// comment-looking lines are scalar data which must remain visible to the
/// exact comparison. YAML permits `|` or `>` followed by at most one chomping
/// indicator and at most one nonzero indentation indicator, in either order.
fn is_block_scalar_header(line: &str) -> bool {
    let Some((_, value)) = line.split_once(':') else {
        return false;
    };
    let mut characters = value.trim().chars();
    if !matches!(characters.next(), Some('|' | '>')) {
        return false;
    }

    let mut saw_chomping = false;
    let mut saw_indentation = false;
    for character in characters {
        match character {
            '+' | '-' if !saw_chomping => saw_chomping = true,
            '1'..='9' if !saw_indentation => saw_indentation = true,
            _ => return false,
        }
    }
    true
}

pub(super) fn audit_step(
    lines: &[&str],
    steps: &StepsBlock,
    expected: StepExpectation<'_>,
    errors: &mut ViolationSink,
) {
    let marker = format!("{}- name: {}", " ".repeat(steps.marker_indent), expected.name);
    let markers = lines
        .iter()
        .enumerate()
        .filter_map(|(index, line)| {
            (steps.range.contains(&index) && *line == marker).then_some(index)
        })
        .collect::<Vec<_>>();
    if markers.len() != 1 {
        errors.push(
            step_location(expected.name),
            format!(
                "expected exactly one canonical step declaration inside `{}.steps`, found {}",
                expected.job,
                markers.len()
            ),
        );
        return;
    }
    let start = markers[0];

    let root_indent = steps.marker_indent + 2;
    let nested_indent = root_indent + 2;
    let end = step_end(lines, start + 1, steps.range.end, steps.marker_indent);
    let mut section = StepSection::Root;
    let mut root_fields = Vec::new();
    let mut scalar_fields = BTreeMap::new();
    let mut environment = BTreeMap::new();
    let mut run = Vec::new();
    let mut run_form = None;

    for (index, line) in lines.iter().enumerate().take(end).skip(start + 1) {
        let line_number = index + 1;
        if line.trim().is_empty() {
            if section == StepSection::Run {
                run.push(String::new());
            }
            continue;
        }
        if line.trim_start().starts_with('#') {
            if section == StepSection::Run {
                run.push(line.get(nested_indent..).unwrap_or(line).to_owned());
            }
            continue;
        }
        if line.trim_end() != *line {
            errors.push(line_location(line_number), "semantic bridge lines must not trail spaces");
            continue;
        }

        match indentation(line) {
            indent if indent == root_indent => {
                let Some((key, value)) = parse_mapping(&line[root_indent..]) else {
                    errors.push(
                        line_location(line_number),
                        "step fields must use canonical unquoted `key: value` form",
                    );
                    section = StepSection::Root;
                    continue;
                };
                root_fields.push(key.to_owned());
                match (key, value) {
                    ("env", "") => section = StepSection::Environment,
                    ("run", "|") => {
                        run_form = Some(RunForm::Block);
                        section = StepSection::Run;
                    }
                    ("run", value) if !value.is_empty() => {
                        run_form = Some(RunForm::Inline);
                        run.push(value.to_owned());
                        section = StepSection::Root;
                    }
                    (_, "") => {
                        errors.push(
                            line_location(line_number),
                            format!("step scalar field `{key}` must not be empty"),
                        );
                        section = StepSection::Root;
                    }
                    _ => {
                        if scalar_fields.insert(key.to_owned(), value.to_owned()).is_some() {
                            errors.push(
                                line_location(line_number),
                                format!("step repeats scalar field `{key}`"),
                            );
                        }
                        section = StepSection::Root;
                    }
                }
            }
            indent if indent == nested_indent && section == StepSection::Environment => {
                let Some((key, value)) = parse_mapping(&line[nested_indent..]) else {
                    errors.push(
                        line_location(line_number),
                        "step environment must use canonical `key: value` form",
                    );
                    continue;
                };
                if value.is_empty() {
                    errors.push(line_location(line_number), "step environment value is empty");
                } else if environment.insert(key.to_owned(), value.to_owned()).is_some() {
                    errors.push(
                        line_location(line_number),
                        format!("step environment repeats `{key}`"),
                    );
                }
            }
            indent if indent >= nested_indent && section == StepSection::Run => {
                run.push(line[nested_indent..].to_owned());
            }
            _ => errors.push(
                line_location(line_number),
                format!(
                    "unsupported audited-step indentation in `{}`",
                    escape_control_characters(line)
                ),
            ),
        }
    }

    if root_fields != expected.root_fields {
        errors.push(
            step_field_location(expected.name, "shape"),
            format!(
                "root fields must appear exactly as {:?}, found {root_fields:?}",
                expected.root_fields
            ),
        );
    }
    compare_map(
        step_field_location(expected.name, "fields"),
        expected.scalar_fields,
        &scalar_fields,
        errors,
    );
    compare_map(
        step_field_location(expected.name, "env"),
        expected.environment,
        &environment,
        errors,
    );
    if run_form != Some(expected.run_form) {
        errors.push(
            step_field_location(expected.name, "run"),
            format!(
                "run field must use canonical {:?} form, found {run_form:?}",
                expected.run_form
            ),
        );
    }
    if run != expected.run {
        errors.push(
            step_field_location(expected.name, "run"),
            format!(
                "run block must match line-for-line: expected {:?}, found {run:?}",
                expected.run
            ),
        );
    }
}

pub(super) fn audit_unique_run_mentions(
    lines: &[&str],
    step: &str,
    command: &str,
    errors: &mut ViolationSink,
) {
    let command_mentions = run_mentions(lines, command);
    if command_mentions != 1 {
        errors.push(
            step_field_location(step, "run"),
            format!(
                "expected exactly one `{command}` command mention on non-comment workflow lines, found {command_mentions}"
            ),
        );
    }
}

pub(super) fn audit_singleton_job_contract(
    fields: &[Field<'_>],
    job: &str,
    errors: &mut ViolationSink,
) {
    audit_host_job_contract(fields, job, errors);
    if fields.iter().any(|field| field.key == "strategy") {
        errors.push(
            job_field_location(job, "strategy"),
            "audited singleton jobs must run exactly once, without a strategy",
        );
    }
}

pub(super) fn audit_host_job_contract(fields: &[Field<'_>], job: &str, errors: &mut ViolationSink) {
    if let Some(runner) = unique_field(fields, "runs-on", job, errors) {
        if runner.value != HOST_RUNNER {
            errors.push(
                job_field_location(job, "runs-on"),
                format!(
                    "expected `{HOST_RUNNER}` for audited absolute host paths, found `{}`",
                    escape_control_characters(runner.value)
                ),
            );
        }
    }
    if fields.iter().any(|field| field.key == "container") {
        errors.push(
            job_field_location(job, "container"),
            "audited absolute host paths must not resolve inside a job container",
        );
    }
    if fields.iter().any(|field| field.key == "continue-on-error") {
        errors.push(
            job_field_location(job, "continue-on-error"),
            "audited jobs must not turn failures into successful conclusions",
        );
    }
}

pub(super) fn parse_needs(value: &str) -> Result<BTreeSet<&str>, String> {
    let dependencies = if is_job_id(value) {
        vec![value]
    } else {
        let Some(value) = value.strip_prefix('[').and_then(|value| value.strip_suffix(']')) else {
            return Err("needs must be one job ID or a canonical inline list".into());
        };
        if value.is_empty() {
            return Err("needs list must not be empty".into());
        }
        value.split(", ").collect()
    };
    let mut unique = BTreeSet::new();
    for dependency in dependencies {
        if !is_job_id(dependency) {
            return Err(format!("needs contains unsupported job ID `{dependency}`"));
        }
        if !unique.insert(dependency) {
            return Err(format!("needs repeats job `{dependency}`"));
        }
    }
    Ok(unique)
}

pub(super) fn compare_map(
    location: String,
    expected: &BTreeMap<String, String>,
    actual: &BTreeMap<String, String>,
    errors: &mut ViolationSink,
) {
    for (key, value) in expected {
        match actual.get(key) {
            Some(actual) if actual == value => {}
            Some(actual) => errors
                .push(format!("{location}.{key}"), format!("expected `{value}`, found `{actual}`")),
            None => errors.push(format!("{location}.{key}"), "required field is absent"),
        }
    }
    for key in actual.keys() {
        if !expected.contains_key(key) {
            errors.push(
                format!("{location}.{key}"),
                "field is not part of the planned-job workflow bridge",
            );
        }
    }
}

pub(super) fn job_field_location(job: &str, field: &str) -> String {
    format!("{WORKFLOW_PATH}:{job}.{field}")
}

pub(super) fn step_field_location(step: &str, field: &str) -> String {
    format!("{WORKFLOW_PATH}:{step}.{field}")
}

pub(super) fn escape_control_characters(value: &str) -> String {
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

fn run_mentions(lines: &[&str], command: &str) -> usize {
    lines
        .iter()
        .filter(|line| !line.trim_start().starts_with('#'))
        .map(|line| token_mentions(line, command))
        .sum()
}

fn nested_block_end(lines: &[&str], parent: &Field<'_>, block_end: usize) -> usize {
    lines
        .iter()
        .enumerate()
        .take(block_end)
        .skip(parent.line + 1)
        .find_map(|(index, line)| {
            (!line.trim().is_empty()
                && !line.trim_start().starts_with('#')
                && indentation(line) <= parent.indent)
                .then_some(index)
        })
        .unwrap_or(block_end)
}

fn token_mentions(text: &str, token: &str) -> usize {
    text.match_indices(token)
        .filter(|(start, _)| {
            let end = start + token.len();
            let before = text[..*start].bytes().next_back();
            let after = text[end..].bytes().next();
            !before.is_some_and(is_token_byte) && !after.is_some_and(is_token_byte)
        })
        .count()
}

fn is_token_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-')
}

fn parse_mapping(declaration: &str) -> Option<(&str, &str)> {
    let (key, remainder) = declaration.split_once(':')?;
    if key.is_empty()
        || !key.bytes().all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'))
    {
        return None;
    }
    if remainder.is_empty() {
        Some((key, ""))
    } else {
        remainder.strip_prefix(' ').map(|value| (key, value))
    }
}

fn is_job_id(value: &str) -> bool {
    let mut bytes = value.bytes();
    matches!(bytes.next(), Some(byte) if byte.is_ascii_alphabetic() || byte == b'_')
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'))
}

fn step_end(lines: &[&str], start: usize, block_end: usize, marker_indent: usize) -> usize {
    // A canonical block scalar's content begins four spaces beneath the step
    // marker: two for the `run` field and two more for its content. A
    // hash-prefixed line at or below that indentation is scalar data, not a
    // YAML comment. In particular, GitHub expands `${{ ... }}` before the
    // scalar becomes a shell script, so discarding such a line here could hide
    // executable text from the exact run comparison below. Comments above the
    // content indentation remain free workflow documentation.
    let block_scalar_content_indent = marker_indent + 4;
    let mut end = lines
        .iter()
        .enumerate()
        .take(block_end)
        .skip(start)
        .find_map(|(index, line)| {
            (!line.trim().is_empty()
                && !line.trim_start().starts_with('#')
                && indentation(line) <= marker_indent)
                .then_some(index)
        })
        .unwrap_or(block_end);
    while end > start {
        let line = lines[end - 1];
        if line.trim().is_empty()
            || (line.trim_start().starts_with('#')
                && indentation(line) < block_scalar_content_indent)
        {
            end -= 1;
        } else {
            break;
        }
    }
    end
}

pub(super) fn indentation(line: &str) -> usize {
    line.bytes().take_while(|byte| *byte == b' ').count()
}

fn line_location(line: usize) -> String {
    format!("{WORKFLOW_PATH}:{line}")
}

fn job_location(job: &str) -> String {
    format!("{WORKFLOW_PATH}:{job}")
}

fn step_location(step: &str) -> String {
    format!("{WORKFLOW_PATH}:{step}")
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum StepSection {
    Root,
    Environment,
    Run,
}
