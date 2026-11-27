// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Miri `--error-format=json` diagnostic parsing, remap-token
//! authentication, and run-output classification.

use super::*;

pub(super) fn generate_miri_auth_token(canon_tmp: &Path) -> String {
    static MIRI_AUTH_COUNTER: AtomicU64 = AtomicU64::new(0);
    let seq = MIRI_AUTH_COUNTER.fetch_add(1, Ordering::Relaxed);
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_nanos();
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-miri-auth-v1\0");
    hasher.update(std::process::id().to_le_bytes());
    hasher.update(seq.to_le_bytes());
    hasher.update(nanos.to_le_bytes());
    hasher.update(canon_tmp.to_string_lossy().as_bytes());
    let hex = sha256_hex(&hasher.finalize());
    format!("__anneal_miri_auth_{}__", &hex[..24])
}

#[derive(Deserialize)]
struct RawMiriSpan {
    #[serde(default)]
    file_name: String,
}

#[derive(Deserialize)]
struct RawMiriChild {
    #[serde(default)]
    level: String,
    #[serde(default)]
    message: String,
    #[serde(default)]
    spans: Vec<RawMiriSpan>,
}

#[derive(Deserialize)]
struct RawMiriDiagnostic {
    #[serde(rename = "$message_type", default)]
    message_type: String,
    #[serde(default)]
    level: String,
    #[serde(default)]
    message: String,
    #[serde(default)]
    spans: Vec<RawMiriSpan>,
    #[serde(default)]
    children: Vec<RawMiriChild>,
    #[serde(default)]
    rendered: Option<String>,
}

fn diagnostic_mentions_token(diag: &RawMiriDiagnostic, token: &str) -> bool {
    diag.spans.iter().any(|s| s.file_name.contains(token))
        || diag.children.iter().any(|c| {
            c.message.contains(token) || c.spans.iter().any(|s| s.file_name.contains(token))
        })
        || diag.rendered.as_deref().is_some_and(|r| r.contains(token))
}

/// Parse Miri exit status, signal, stdout, and `--error-format=json` stderr
/// into an [`AuthorityRunResult`].
pub fn parse_miri_run_output(
    auth_name: &str,
    exit_code: Option<i32>,
    signal: Option<i32>,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
) -> AuthorityRunResult {
    parse_miri_run_output_authenticated(
        auth_name, exit_code, signal, stdout, stderr, elapsed_ms, None, None,
    )
}

/// Entry-count-checked variant of [`parse_miri_run_output`].
#[allow(clippy::too_many_arguments)]
pub fn parse_miri_run_output_with_expected_args(
    auth_name: &str,
    exit_code: Option<i32>,
    signal: Option<i32>,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
    expected_entry_slots: Option<usize>,
) -> AuthorityRunResult {
    parse_miri_run_output_authenticated(
        auth_name,
        exit_code,
        signal,
        stdout,
        stderr,
        elapsed_ms,
        expected_entry_slots,
        None,
    )
}

/// Authenticated variant of [`parse_miri_run_output_with_expected_args`] that
/// additionally requires Miri's structured `--error-format=json` diagnostic to
/// reference the per-invocation `--remap-path-prefix` `expected_remap_token`
/// (which interpreted guest code under Miri isolation cannot observe or forge).
#[allow(clippy::too_many_arguments)]
pub fn parse_miri_run_output_authenticated(
    auth_name: &str,
    exit_code: Option<i32>,
    signal: Option<i32>,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
    expected_entry_slots: Option<usize>,
    expected_remap_token: Option<&str>,
) -> AuthorityRunResult {
    let exited_zero = exit_code == Some(0) && signal.is_none();

    // Require Miri's nonzero exit code (without a fatal signal crash) AND an
    // authenticated `--error-format=json` Miri compiler diagnostic (carrying
    // Miri's UB help child, the companion `aborting due to ...` compiler
    // summary, and `expected_remap_token` when provided) so subject `eprintln!`
    // + `std::process::exit(1)` can never spoof Undefined Behavior.
    if !exited_zero
        && exit_code.is_some()
        && signal.is_none()
        && let Some(ub_line) = detect_authenticated_miri_ub_line(stderr, expected_remap_token)
    {
        let entry_mem_digest = match parse_pre_entry_slots_stdout(
            auth_name,
            stdout,
            stderr,
            expected_entry_slots,
        ) {
            Ok(Some(slots)) => Some(crate::outcome::compute_boundary_mem_digest(&slots)),
            Ok(None) if expected_entry_slots.is_some() => {
                return AuthorityRunResult::tool_error(
                    auth_name,
                    format!(
                        "{auth_name} UB output missing `{PRE_ENTRY_JSON_PREFIX}` line; stdout={stdout:?}, stderr={stderr:?}"
                    ),
                );
            }
            Ok(None) => None,
            Err(detail) => return AuthorityRunResult::tool_error(auth_name, detail),
        };
        return AuthorityRunResult {
            authority: auth_name.to_string(),
            outcome: TerminalOutcome::FaultUb { detail: ub_line },
            spine: ObservableSpine::default(),
            caller_frame_law: CallerFrameLaw::all_satisfied(),
            tool_error: None,
            raw_diagnostics: stderr.to_string(),
            elapsed_ms,
            post_only_mem_digest: false,
            entry_mem_digest,
        };
    }

    if exited_zero {
        return match parse_trace_json_stdout_with_expected_args(
            auth_name,
            stdout,
            stderr,
            elapsed_ms,
            expected_entry_slots,
        ) {
            Ok(res) => res,
            Err(detail) => AuthorityRunResult::tool_error(auth_name, detail),
        };
    }

    // Scheduled `std::process::abort()` inside Miri flushes
    // `ANNEAL_ITREE_PRE_ABORT:` before Miri reports abnormal termination.
    let miri_aborted_diag = detect_authenticated_miri_abort(stderr, expected_remap_token);
    if (miri_aborted_diag || signal == Some(6))
        && stdout.lines().any(|l| l.trim().starts_with(PRE_ABORT_JSON_PREFIX))
    {
        return match parse_pre_abort_stdout_with_expected_args(
            auth_name,
            stdout,
            stderr,
            elapsed_ms,
            expected_entry_slots,
        ) {
            Ok(res) => res,
            Err(detail) => AuthorityRunResult::tool_error(auth_name, detail),
        };
    }

    AuthorityRunResult::tool_error(
        auth_name,
        format!(
            "Miri failed (exit={exit_code:?}, signal={signal:?}): stdout={stdout:?}, stderr={stderr:?}"
        ),
    )
}

/// Detect Miri Undefined Behavior strictly from `--error-format=json`
/// compiler diagnostics, never accepting raw plain-text
/// `error: Undefined Behavior:` lines printed by guest code.
pub fn detect_miri_ub_line(stderr: &str) -> Option<String> {
    detect_authenticated_miri_ub_line(stderr, None)
}

fn parse_miri_json_diagnostics(stderr: &str) -> Vec<RawMiriDiagnostic> {
    let mut parsed_diags = Vec::new();
    for line in stderr.lines() {
        let trimmed = line.trim();
        let candidate = if trimmed.starts_with('{') {
            Some(trimmed)
        } else {
            // If guest code called `eprint!(...)` without a trailing newline
            // immediately before UB/abort, Miri appends its JSON diagnostic at
            // the end of that partial line.
            trimmed.find(r#"{"$message_type":"#).map(|idx| &trimmed[idx..])
        };
        if let Some(json_slice) = candidate
            && let Ok(diag) = serde_json::from_str::<RawMiriDiagnostic>(json_slice)
            && diag.message_type == "diagnostic"
        {
            parsed_diags.push(diag);
        }
    }
    parsed_diags
}

/// Token-authenticated variant of [`detect_miri_ub_line`].
pub fn detect_authenticated_miri_ub_line(
    stderr: &str,
    expected_remap_token: Option<&str>,
) -> Option<String> {
    if let Some(tok) = expected_remap_token
        && tok.trim().is_empty()
    {
        return None;
    }
    let parsed_diags = parse_miri_json_diagnostics(stderr);
    let has_compiler_abort_summary = parsed_diags
        .iter()
        .any(|d| d.level == "error" && d.message.starts_with("aborting due to "));
    if !has_compiler_abort_summary {
        return None;
    }
    for diag in &parsed_diags {
        let has_miri_ub_help = diag.children.iter().any(|c| {
            c.level == "help"
                && c.message
                    .contains("performed an invalid operation, and caused Undefined Behavior")
        });
        let token_ok = match expected_remap_token {
            Some(tok) => diagnostic_mentions_token(diag, tok),
            None => true,
        };
        if diag.level == "error"
            && diag.message.starts_with("Undefined Behavior:")
            && has_miri_ub_help
            && token_ok
        {
            return Some(format!("error: {}", diag.message.trim_end()));
        }
    }
    None
}

fn detect_authenticated_miri_abort(stderr: &str, expected_remap_token: Option<&str>) -> bool {
    let parsed_diags = parse_miri_json_diagnostics(stderr);
    let has_summary = parsed_diags
        .iter()
        .any(|d| d.level == "error" && d.message.starts_with("aborting due to "));
    if has_summary {
        for diag in &parsed_diags {
            let is_abort = diag.level == "error"
                && (diag.message.starts_with("abnormal termination:")
                    || diag.message.contains("the program aborted execution"));
            let token_ok = match expected_remap_token {
                Some(tok) => !tok.trim().is_empty() && diagnostic_mentions_token(diag, tok),
                None => true,
            };
            if is_abort && token_ok {
                return true;
            }
        }
    }
    false
}
