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

use super::ViolationSink;
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

pub(super) fn find_job(
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
            job_location(job),
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
        // A scalar field cannot acquire an indented continuation without
        // changing its meaning.  We must reject that ambiguity, while still
        // allowing children of mapping-valued fields such as `permissions:`.
        // The latter have an empty value and are therefore deliberately left
        // alone for the dedicated nested-mapping audit below.
        if indentation(line) > field_indent
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
        if indentation(line) != field_indent || line[field_indent..].starts_with("- ") {
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

pub(super) fn nested_fields<'a>(
    lines: &'a [&'a str],
    parent: &Field<'_>,
    block_end: usize,
    job: &str,
    errors: &mut ViolationSink,
) -> Option<Vec<Field<'a>>> {
    if !parent.value.is_empty() {
        errors.push(
            job_field_location(job, parent.key),
            format!("{} must use the canonical nested mapping form", parent.key),
        );
        return None;
    }
    let end = nested_block_end(lines, parent, block_end);
    Some(job_fields_at_indent(lines, parent.line..end, job, parent.indent + 2, errors))
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
pub(super) fn exact_step_lines<'a>(lines: &'a [&'a str], steps: &StepsBlock) -> Vec<Vec<&'a str>> {
    let starts = lines
        .iter()
        .enumerate()
        .filter_map(|(index, line)| {
            (steps.range.contains(&index)
                && !line.trim().is_empty()
                && !line.trim_start().starts_with('#')
                && indentation(line) == steps.marker_indent
                && line[steps.marker_indent..].starts_with("- "))
            .then_some(index)
        })
        .collect::<Vec<_>>();
    starts
        .iter()
        .enumerate()
        .map(|(position, start)| {
            let end = starts.get(position + 1).copied().unwrap_or(steps.range.end);
            lines[*start..end]
                .iter()
                .filter(|line| !line.trim().is_empty() && !line.trim_start().starts_with('#'))
                .copied()
                .collect()
        })
        .collect()
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
        if line.trim().is_empty() || line.trim_start().starts_with('#') {
            end -= 1;
        } else {
            break;
        }
    }
    end
}

fn indentation(line: &str) -> usize {
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
