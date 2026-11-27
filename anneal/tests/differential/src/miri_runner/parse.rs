// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Parsing of Miri stdout, JSON stderr diagnostics, and return
//! lines into observed outcomes.

use super::*;

/// Parse Miri stdout, stderr, and exit status into an [`ObservedOutcome`].
pub fn parse_miri_output(exit_code: Option<i32>, stdout: &str, stderr: &str) -> ObservedOutcome {
    parse_miri_output_with_token(exit_code, stdout, stderr, None)
}

pub(super) fn parse_miri_output_with_token(
    exit_code: Option<i32>,
    stdout: &str,
    stderr: &str,
    expected_token: Option<&str>,
) -> ObservedOutcome {
    if exit_code == Some(0) {
        let prefix = miri_ret_prefix_for_token(expected_token);
        let mut matched: Option<&str> = None;
        for raw_line in stdout.lines() {
            if let Some(payload) = raw_line.strip_prefix(&prefix) {
                if matched.is_some() {
                    return ObservedOutcome::ToolError {
                        detail: format!(
                            "Miri stdout contained duplicate `{prefix}` markers; stdout={stdout:?}"
                        ),
                    };
                }
                matched = Some(payload);
            } else if expected_token.is_some()
                && (raw_line.starts_with(MIRI_RET_PREFIX)
                    || raw_line.starts_with(&format!("{MIRI_RET_STEM}:")))
            {
                return ObservedOutcome::ToolError {
                    detail: format!(
                        "Miri stdout contained unauthenticated `{MIRI_RET_STEM}` marker; stdout={stdout:?}"
                    ),
                };
            }
        }
        let Some(line) = matched else {
            return ObservedOutcome::ToolError {
                detail: format!("Miri exited 0 without `{prefix}` line; stdout={stdout:?}"),
            };
        };
        if line == "PANICKED" {
            return ObservedOutcome::Panic {
                detail: "panicked during Miri execution (caught by harness)".to_owned(),
            };
        }
        if line == "UNEXPECTED_RETURN" {
            // Represent a clean return cleanly so evaluate_case distinguishes
            // normal return from expected UB or panic.
            return ObservedOutcome::Returned { value: MirValue::Unit };
        }
        return match parse_miri_ret_line(line) {
            Ok(value) => ObservedOutcome::Returned { value },
            Err(e) => {
                ObservedOutcome::ToolError { detail: format!("parse Miri return {line:?}: {e}") }
            }
        };
    }

    if expected_token.is_some() {
        return parse_miri_json_stderr(exit_code, stderr);
    }

    if stderr.contains("error: internal compiler error:")
        || stderr.contains("thread 'rustc' panicked at ")
    {
        return ObservedOutcome::ToolError {
            detail: format!(
                "Miri compiler ICE ({:?}): {}",
                exit_code,
                stderr.lines().take(6).collect::<Vec<_>>().join(" | ")
            ),
        };
    }
    if stderr.contains("error: Undefined Behavior:") {
        let headline = stderr
            .lines()
            .find(|l| l.contains("error: Undefined Behavior:"))
            .unwrap_or("Undefined Behavior")
            .trim()
            .to_owned();
        return ObservedOutcome::UndefinedBehavior { detail: headline };
    }
    if stderr.contains("error: abnormal termination:") {
        let headline = stderr
            .lines()
            .find(|l| l.contains("error: abnormal termination:"))
            .unwrap_or("abnormal termination")
            .trim()
            .to_owned();
        return ObservedOutcome::AbnormalAbort { detail: headline };
    }
    if stderr.contains("error: unsupported operation:") {
        let headline = stderr
            .lines()
            .find(|l| l.contains("error: unsupported operation:"))
            .unwrap_or("unsupported operation")
            .trim()
            .to_owned();
        return ObservedOutcome::Unsupported { detail: headline };
    }
    if stderr.contains("panicked at ") {
        let headline = stderr
            .lines()
            .find(|l| l.contains("panicked at "))
            .unwrap_or("panicked")
            .trim()
            .to_owned();
        return ObservedOutcome::Panic { detail: headline };
    }

    ObservedOutcome::ToolError {
        detail: format!(
            "Miri exited {:?}: {}",
            exit_code,
            stderr.lines().take(6).collect::<Vec<_>>().join(" | ")
        ),
    }
}

fn is_forged_plain_diagnostic_line(line: &str) -> bool {
    let trimmed = line.trim();
    trimmed.contains("error: Undefined Behavior:")
        || trimmed.contains("error: abnormal termination:")
        || trimmed.contains("error: unsupported operation:")
        || trimmed.contains("error: internal compiler error:")
}

fn is_abort_summary_message(msg: &str) -> bool {
    msg.starts_with("aborting due to ") && msg.contains("previous error")
}

fn normalize_diag_path(path: &str) -> String {
    path.replace('\\', "/")
}

fn path_matches_isolated_harness(path: &str) -> bool {
    let norm = normalize_diag_path(path);
    norm == "h/harness.rs" || norm.ends_with("/h/harness.rs")
}

fn is_harness_like_diag_path(path: &str) -> bool {
    let norm = normalize_diag_path(path);
    let base = norm.rsplit('/').next().unwrap_or("");
    base == "harness.rs"
        || base.starts_with("harness_")
        || base.starts_with("fuzz_miri_harness_")
        || norm.starts_with("sec_")
        || norm.contains("/sec_")
}

fn backtrace_note_references_active_harness(msg: &str) -> bool {
    if !msg.starts_with("stack backtrace:") {
        return false;
    }
    msg.lines().any(|line| {
        let Some(rest) = line.trim().strip_prefix("at ") else {
            return false;
        };
        let mut path_part = rest.split_once(": ").map_or(rest, |(head, _)| head);
        for _ in 0..2 {
            if let Some((head, tail)) = path_part.rsplit_once(':')
                && !tail.is_empty()
                && tail.bytes().all(|b| b.is_ascii_digit())
            {
                path_part = head;
            } else {
                break;
            }
        }
        path_matches_isolated_harness(path_part.trim())
    })
}

fn validate_diagnostic_origin(obj: &Value, msg: &str) -> Result<(), String> {
    let Some(spans) = obj.get("spans").and_then(Value::as_array) else {
        return Err("missing diagnostic spans array".to_owned());
    };
    let Some(children) = obj.get("children").and_then(Value::as_array) else {
        return Err("missing diagnostic children array".to_owned());
    };
    if !obj.get("rendered").is_some_and(Value::is_string) {
        return Err("missing diagnostic rendered text".to_owned());
    }
    let mut saw_active_harness = false;
    for span in spans {
        let Some(fname) = span.get("file_name").and_then(Value::as_str) else {
            return Err("diagnostic span missing file_name".to_owned());
        };
        if path_matches_isolated_harness(fname) {
            saw_active_harness = true;
        } else if is_harness_like_diag_path(fname) {
            return Err(format!("diagnostic span `{fname}` does not match isolated harness path"));
        }
    }
    for child in children {
        if child.get("level").and_then(Value::as_str) == Some("note")
            && let Some(cmsg) = child.get("message").and_then(Value::as_str)
            && backtrace_note_references_active_harness(cmsg)
        {
            saw_active_harness = true;
        }
    }
    if !msg.starts_with("internal compiler error:") && !saw_active_harness {
        return Err("diagnostic lacked stack frame or span from active isolated harness".to_owned());
    }
    Ok(())
}

fn parse_miri_json_stderr(exit_code: Option<i32>, stderr: &str) -> ObservedOutcome {
    if stderr.contains("thread 'rustc' panicked at ") {
        return ObservedOutcome::ToolError {
            detail: format!(
                "Miri compiler ICE ({:?}): {}",
                exit_code,
                stderr.lines().take(6).collect::<Vec<_>>().join(" | ")
            ),
        };
    }

    let mut fatal_errors: Vec<String> = Vec::new();
    let mut saw_abort_summary = false;
    let mut saw_plain_panic = false;

    for raw_line in stderr.lines() {
        let trimmed = raw_line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if let Ok(val) = serde_json::from_str::<Value>(trimmed)
            && val.get("$message_type").and_then(Value::as_str) == Some("diagnostic")
        {
            if val.get("level").and_then(Value::as_str) == Some("error") {
                let Some(msg) = val.get("message").and_then(Value::as_str) else {
                    return ObservedOutcome::ToolError {
                        detail: format!("Miri JSON error diagnostic missing message: {trimmed}"),
                    };
                };
                if is_abort_summary_message(msg) {
                    saw_abort_summary = true;
                } else {
                    if let Err(err) = validate_diagnostic_origin(&val, msg) {
                        return ObservedOutcome::ToolError {
                            detail: format!("Miri diagnostic failed schema/origin check: {err}"),
                        };
                    }
                    fatal_errors.push(msg.to_owned());
                }
            }
            continue;
        }
        if is_forged_plain_diagnostic_line(trimmed) {
            return ObservedOutcome::ToolError {
                detail: format!(
                    "Miri stderr contained unauthenticated plain-text diagnostic: {trimmed:?}"
                ),
            };
        }
        if trimmed.contains("panicked at ") {
            saw_plain_panic = true;
        }
    }

    if fatal_errors.len() > 1 {
        return ObservedOutcome::ToolError {
            detail: format!(
                "Miri stderr contained multiple fatal error diagnostics: {fatal_errors:?}"
            ),
        };
    }
    if let Some(msg) = fatal_errors.into_iter().next() {
        if saw_plain_panic || !saw_abort_summary {
            return ObservedOutcome::ToolError {
                detail: format!(
                    "Miri diagnostic `{msg}` lacked clean aborting summary or collided with target panic"
                ),
            };
        }
        if msg.starts_with("internal compiler error:") {
            return ObservedOutcome::ToolError {
                detail: format!("Miri compiler ICE ({exit_code:?}): error: {msg}"),
            };
        }
        if msg.starts_with("Undefined Behavior:") {
            return ObservedOutcome::UndefinedBehavior { detail: format!("error: {msg}") };
        }
        if msg.starts_with("abnormal termination:") {
            return ObservedOutcome::AbnormalAbort { detail: format!("error: {msg}") };
        }
        if msg.starts_with("unsupported operation:") {
            return ObservedOutcome::Unsupported { detail: format!("error: {msg}") };
        }
        return ObservedOutcome::ToolError {
            detail: format!("Miri exited {exit_code:?}: error: {msg}"),
        };
    }

    if exit_code == Some(101) && saw_plain_panic {
        let headline = stderr
            .lines()
            .find(|l| l.contains("panicked at "))
            .unwrap_or("panicked")
            .trim()
            .to_owned();
        return ObservedOutcome::Panic { detail: headline };
    }

    ObservedOutcome::ToolError {
        detail: format!(
            "Miri exited {:?}: {}",
            exit_code,
            stderr.lines().take(6).collect::<Vec<_>>().join(" | ")
        ),
    }
}

pub fn parse_miri_ret_line(line: &str) -> Result<MirValue, String> {
    if line == "UNIT" {
        return Ok(MirValue::Unit);
    }
    if let Some(rest) = line.strip_prefix("INT:") {
        let (kind_raw, dec_raw) =
            rest.split_once(':').ok_or_else(|| format!("malformed INT payload {rest:?}"))?;
        let int_kind = IntKind::parse_rust_name(kind_raw)?;
        let bits = int_kind.parse_decimal_bits(dec_raw)?;
        return Ok(MirValue::Int { int_kind, bits });
    }
    if let Some(rest) = line.strip_prefix("BOOL:") {
        return match rest.trim() {
            "true" => Ok(MirValue::Bool { value: true }),
            "false" => Ok(MirValue::Bool { value: false }),
            _ => Err(format!("invalid BOOL payload {rest:?}")),
        };
    }
    if let Some(rest) = line.strip_prefix("CHAR:") {
        let scalar: u32 =
            rest.trim().parse().map_err(|e| format!("invalid CHAR scalar {rest:?}: {e}"))?;
        char::from_u32(scalar).ok_or_else(|| format!("CHAR {scalar} is not a Unicode scalar"))?;
        return Ok(MirValue::Char { scalar });
    }
    if let Some(rest) = line.strip_prefix("ORDERING:") {
        return Ok(MirValue::Ordering { value: OrderingKind::parse(rest)? });
    }
    if let Some(rest) = line.strip_prefix("OVF:") {
        let mut parts = rest.splitn(3, ':');
        let kind_raw = parts.next().ok_or_else(|| format!("malformed OVF payload {rest:?}"))?;
        let dec_raw = parts.next().ok_or_else(|| format!("malformed OVF payload {rest:?}"))?;
        let ovf_raw = parts.next().ok_or_else(|| format!("malformed OVF payload {rest:?}"))?;
        let int_kind = IntKind::parse_rust_name(kind_raw)?;
        let bits = int_kind.parse_decimal_bits(dec_raw)?;
        let overflow = match ovf_raw.trim() {
            "true" => true,
            "false" => false,
            _ => return Err(format!("invalid OVF flag {ovf_raw:?}")),
        };
        return Ok(MirValue::OverflowPair { int_kind, bits, overflow });
    }
    Err(format!("unknown Miri return line {line:?}"))
}
