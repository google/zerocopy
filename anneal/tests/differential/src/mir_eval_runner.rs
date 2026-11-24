// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Optional Leg 3 differential runner against `tools/anneal-mir-eval`.

use std::{env, ffi::OsString, fs, path::Path, time::Duration};

use anneal_testkit::{Invocation, ProcessSupervisor, Termination};
use serde::Deserialize;

use crate::{
    corpus::LitmusCase,
    lean_runner::effective_timeout_secs,
    verdict::{IntKind, MirValue, ObservedOutcome, OrderingKind},
};

const MIR_EVAL_TIMEOUT_SECS: u64 = 120;

fn build_eval_args(
    capture_json: &Path,
    body_id: usize,
    case: &LitmusCase,
) -> Result<Vec<OsString>, String> {
    let mut args = vec![
        OsString::from("eval"),
        capture_json.as_os_str().to_os_string(),
        OsString::from("--body"),
        OsString::from(body_id.to_string()),
        OsString::from("--fuel"),
        OsString::from(case.fuel.to_string()),
        OsString::from("--json"),
    ];
    for arg in &case.args {
        args.push(OsString::from("--arg"));
        args.push(OsString::from(format_eval_arg(arg)?));
    }
    Ok(args)
}

/// Execute `anneal-mir-eval eval <capture.json> --body <body_id> --arg ...`
/// (`--json`) for one case against an already-captured `capture.json` under
/// bounded [`ProcessSupervisor`] timeout supervision.
pub fn run_mir_eval_case(
    mir_eval_bin: &Path,
    capture_json: &Path,
    body_id: usize,
    case: &LitmusCase,
) -> ObservedOutcome {
    let Ok(canon_bin) = fs::canonicalize(mir_eval_bin) else {
        return ObservedOutcome::ToolError {
            detail: format!("cannot resolve anneal-mir-eval binary {}", mir_eval_bin.display()),
        };
    };

    let args = match build_eval_args(capture_json, body_id, case) {
        Ok(args) => args,
        Err(detail) => return ObservedOutcome::ToolError { detail },
    };
    let mut inv = Invocation::new(canon_bin, &[]);
    for arg in args {
        inv = inv.arg(arg);
    }

    if let Some(path) = env::var_os("PATH") {
        inv = inv.env("PATH", path);
    }
    if let Some(ld) = env::var_os("LD_LIBRARY_PATH") {
        inv = inv.env("LD_LIBRARY_PATH", ld);
    }

    let tmp_dir = match tempfile::tempdir() {
        Ok(d) => d,
        Err(e) => {
            return ObservedOutcome::ToolError {
                detail: format!("create anneal-mir-eval log dir: {e}"),
            };
        }
    };
    let work_root = match fs::canonicalize(tmp_dir.path()) {
        Ok(p) => p,
        Err(e) => {
            return ObservedOutcome::ToolError {
                detail: format!("canonicalize anneal-mir-eval work dir: {e}"),
            };
        }
    };

    let timeout_secs = match effective_timeout_secs(MIR_EVAL_TIMEOUT_SECS) {
        Ok(secs) => secs,
        Err(detail) => return ObservedOutcome::ToolError { detail },
    };
    let supervisor = match ProcessSupervisor::new(Duration::from_secs(timeout_secs)) {
        Ok(s) => s,
        Err(detail) => return ObservedOutcome::ToolError { detail },
    };
    let out = match supervisor.run(&inv, &work_root, &work_root.join("log"), &work_root) {
        Ok(o) => o,
        Err(detail) => return ObservedOutcome::ToolError { detail },
    };

    let code = match out.termination {
        Termination::Exited(status) => status.code(),
        Termination::TimedOut(status) => {
            return ObservedOutcome::ToolError {
                detail: format!("anneal-mir-eval timed out after {timeout_secs}s ({status})"),
            };
        }
        Termination::LaunchFailed(err) => {
            return ObservedOutcome::ToolError {
                detail: format!("spawn {}: {err}", mir_eval_bin.display()),
            };
        }
    };

    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    parse_mir_eval_output(code, &stdout, &stderr)
}

fn format_eval_arg(val: &MirValue) -> Result<String, String> {
    match val {
        MirValue::Int { int_kind, bits } => Ok(int_kind.to_mir_eval_arg(*bits)),
        MirValue::Bool { value } => Ok(format!("bool:{value}")),
        MirValue::Char { scalar } => Ok(format!("char:U+{scalar:04X}")),
        MirValue::Ordering { value } => Ok(format!("ordering:{}", value.as_str())),
        MirValue::Unit => Ok("unit:()".to_owned()),
        MirValue::Enum { variant_index, .. } => Ok(format!("variant:{variant_index}")),
        MirValue::OverflowPair { .. } => {
            Err("OverflowPair argument formatting is unsupported in Stage 1".to_owned())
        }
    }
}

#[derive(Deserialize)]
struct RawStepTrace {
    outcome: RawOutcome,
}

#[derive(Deserialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
enum RawOutcome {
    Returned(RawTerminalOut),
    Aborted {},
    Fault(RawFaultDetail),
    OutOfFuel,
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum RawTerminalOut {
    Returned { ret: RawVal },
    Unwound {},
}

#[derive(Deserialize)]
struct RawFaultDetail {
    kind: String,
    reason: String,
}

#[derive(Deserialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
enum RawVal {
    Scalar(RawScalarVal),
    Bool(bool),
    Char(char),
    Ordering(String),
    Unit,
    EnumVal {
        variant: usize,
    },
    Tuple(Vec<RawVal>),
    #[serde(other)]
    Other,
}

#[derive(Deserialize)]
struct RawScalarVal {
    width: String,
    signed: bool,
    bits: String,
}

/// Parse `anneal-mir-eval eval --json` output into an [`ObservedOutcome`],
/// cross-checking exit codes (`0` Returned, `2` Undefined, `3`
/// Unsupported/OutOfFuel, `4` Aborted).
pub fn parse_mir_eval_output(
    exit_code: Option<i32>,
    stdout: &str,
    stderr: &str,
) -> ObservedOutcome {
    if !matches!(exit_code, Some(0 | 2 | 3 | 4)) {
        return ObservedOutcome::ToolError {
            detail: format!("anneal-mir-eval failed (exit {exit_code:?}): {}", stderr.trim()),
        };
    }

    let trace: RawStepTrace = match serde_json::from_str(stdout) {
        Ok(parsed) => parsed,
        Err(e) => {
            return ObservedOutcome::ToolError {
                detail: format!("parse anneal-mir-eval JSON: {e}"),
            };
        }
    };

    match trace.outcome {
        RawOutcome::Returned(RawTerminalOut::Returned { ret }) => {
            if exit_code != Some(0) {
                return ObservedOutcome::ToolError {
                    detail: format!(
                        "anneal-mir-eval protocol mismatch: Returned JSON with exit code {exit_code:?}"
                    ),
                };
            }
            match convert_val(ret) {
                Ok(value) => ObservedOutcome::Returned { value },
                Err(detail) => ObservedOutcome::ToolError { detail },
            }
        }
        RawOutcome::Returned(RawTerminalOut::Unwound {}) => {
            if exit_code != Some(0) {
                return ObservedOutcome::ToolError {
                    detail: format!(
                        "anneal-mir-eval protocol mismatch: Unwound JSON with exit code {exit_code:?}"
                    ),
                };
            }
            ObservedOutcome::AbnormalAbort { detail: "anneal-mir-eval unwound".to_owned() }
        }
        RawOutcome::Aborted {} => {
            if exit_code != Some(4) {
                return ObservedOutcome::ToolError {
                    detail: format!(
                        "anneal-mir-eval protocol mismatch: Aborted JSON with exit code {exit_code:?} (expected 4)"
                    ),
                };
            }
            ObservedOutcome::AbnormalAbort {
                detail: "anneal-mir-eval aborted (UnwindAction::Terminate)".to_owned(),
            }
        }
        RawOutcome::Fault(f) => match f.kind.as_str() {
            "undefined" => {
                if exit_code != Some(2) {
                    return ObservedOutcome::ToolError {
                        detail: format!(
                            "anneal-mir-eval protocol mismatch: undefined JSON with exit code {exit_code:?} (expected 2)"
                        ),
                    };
                }
                ObservedOutcome::UndefinedBehavior { detail: f.reason }
            }
            "unsupported" => {
                if exit_code != Some(3) {
                    return ObservedOutcome::ToolError {
                        detail: format!(
                            "anneal-mir-eval protocol mismatch: unsupported JSON with exit code {exit_code:?} (expected 3)"
                        ),
                    };
                }
                ObservedOutcome::Unsupported { detail: f.reason }
            }
            other => ObservedOutcome::ToolError {
                detail: format!("unknown anneal-mir-eval fault kind {other:?}: {}", f.reason),
            },
        },
        RawOutcome::OutOfFuel => {
            if exit_code != Some(3) {
                return ObservedOutcome::ToolError {
                    detail: format!(
                        "anneal-mir-eval protocol mismatch: out_of_fuel JSON with exit code {exit_code:?} (expected 3)"
                    ),
                };
            }
            ObservedOutcome::OutOfFuel { detail: "anneal-mir-eval hit fuel limit".to_owned() }
        }
    }
}

fn check_canonical_bits(int_kind: IntKind, raw_bits: &str) -> Result<u128, String> {
    let bits =
        raw_bits.parse::<u128>().map_err(|e| format!("invalid scalar bits {raw_bits:?}: {e}"))?;
    if bits > int_kind.mask() {
        return Err(format!(
            "non-canonical bits {bits} exceed {} mask {} in anneal-mir-eval result",
            int_kind.rust_name(),
            int_kind.mask()
        ));
    }
    Ok(bits)
}

fn convert_val(val: RawVal) -> Result<MirValue, String> {
    match val {
        RawVal::Scalar(sv) => {
            let int_kind = IntKind::from_lean_parts(&sv.width, sv.signed)?;
            let bits = check_canonical_bits(int_kind, &sv.bits)?;
            Ok(MirValue::Int { int_kind, bits })
        }
        RawVal::Bool(value) => Ok(MirValue::Bool { value }),
        RawVal::Char(c) => Ok(MirValue::Char { scalar: c as u32 }),
        RawVal::Ordering(raw) => Ok(MirValue::Ordering { value: OrderingKind::parse(&raw)? }),
        RawVal::Unit => Ok(MirValue::Unit),
        RawVal::EnumVal { variant } => Ok(MirValue::Enum {
            enum_type: String::new(),
            variant: format!("variant#{variant}"),
            variant_index: variant,
        }),
        RawVal::Tuple(fields) if fields.len() == 2 => {
            let mut it = fields.into_iter();
            match (it.next(), it.next()) {
                (Some(RawVal::Scalar(sv)), Some(RawVal::Bool(overflow))) => {
                    let int_kind = IntKind::from_lean_parts(&sv.width, sv.signed)?;
                    let bits = check_canonical_bits(int_kind, &sv.bits)?;
                    Ok(MirValue::OverflowPair { int_kind, bits, overflow })
                }
                _ => Err("unsupported non-OverflowPair tuple in anneal-mir-eval result".to_owned()),
            }
        }
        RawVal::Tuple(_) | RawVal::Other => {
            Err("unsupported return value variant from anneal-mir-eval".to_owned())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_mir_eval_json_variants_and_rejects_unmasked_or_exit_mismatch() {
        let ret_json = r#"{
            "body_id": 0,
            "identity": "rust-path-v1::demo",
            "steps_executed": 3,
            "fuel_limit": 200,
            "outcome": {
                "kind": "returned",
                "value": {
                    "kind": "returned",
                    "ret": { "kind": "scalar", "value": { "width": "i32", "signed": false, "bits": "42" } },
                    "caller_mem": { "allocations": [] }
                }
            },
            "events": []
        }"#;
        assert_eq!(
            parse_mir_eval_output(Some(0), ret_json, ""),
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 42 } }
        );
        assert!(matches!(
            parse_mir_eval_output(Some(2), ret_json, ""),
            ObservedOutcome::ToolError { .. }
        ));

        let non_canonical_json = r#"{
            "outcome": {
                "kind": "returned",
                "value": {
                    "kind": "returned",
                    "ret": { "kind": "scalar", "value": { "width": "i32", "signed": false, "bits": "4294967300" } }
                }
            }
        }"#;
        assert!(matches!(
            parse_mir_eval_output(Some(0), non_canonical_json, ""),
            ObservedOutcome::ToolError { .. }
        ));

        let ovf_json = r#"{
            "outcome": {
                "kind": "returned",
                "value": {
                    "kind": "returned",
                    "ret": {
                        "kind": "tuple",
                        "value": [
                            { "kind": "scalar", "value": { "width": "i64", "signed": false, "bits": "4" } },
                            { "kind": "bool", "value": true }
                        ]
                    }
                }
            }
        }"#;
        assert_eq!(
            parse_mir_eval_output(Some(0), ovf_json, ""),
            ObservedOutcome::Returned {
                value: MirValue::OverflowPair { int_kind: IntKind::U64, bits: 4, overflow: true }
            }
        );

        let ub_json = r#"{
            "outcome": {
                "kind": "fault",
                "value": { "kind": "undefined", "reason": "division by zero" }
            }
        }"#;
        assert!(matches!(
            parse_mir_eval_output(Some(2), ub_json, ""),
            ObservedOutcome::UndefinedBehavior { .. }
        ));
        assert!(matches!(
            parse_mir_eval_output(Some(0), ub_json, ""),
            ObservedOutcome::ToolError { .. }
        ));

        let unsup_json = r#"{
            "outcome": {
                "kind": "fault",
                "value": { "kind": "unsupported", "reason": "unsupported terminator" }
            }
        }"#;
        assert!(matches!(
            parse_mir_eval_output(Some(3), unsup_json, ""),
            ObservedOutcome::Unsupported { .. }
        ));
        assert!(matches!(
            parse_mir_eval_output(Some(2), unsup_json, ""),
            ObservedOutcome::ToolError { .. }
        ));

        let aborted_json = r#"{
            "outcome": {
                "kind": "aborted",
                "value": { "caller_mem": { "slots": [] } }
            }
        }"#;
        assert!(matches!(
            parse_mir_eval_output(Some(4), aborted_json, ""),
            ObservedOutcome::AbnormalAbort { .. }
        ));
        assert!(matches!(
            parse_mir_eval_output(Some(0), aborted_json, ""),
            ObservedOutcome::ToolError { .. }
        ));
    }

    #[test]
    fn build_eval_args_passes_resolved_body_index() {
        let case = LitmusCase {
            id: "c1".to_owned(),
            source_rel: std::path::PathBuf::from("src/a.rs"),
            source_abs: std::path::PathBuf::from("/tmp/src/a.rs"),
            function: "fn_name".to_owned(),
            category: "arith".to_owned(),
            expected: crate::verdict::Expectation::Pass,
            miri_ub_contains: None,
            expected_miri: None,
            args: vec![MirValue::Int { int_kind: IntKind::U32, bits: 7 }],
            expected_return: Some(MirValue::Int { int_kind: IntKind::U32, bits: 8 }),
            fuel: 42,
        };
        let args = build_eval_args(Path::new("/tmp/cap.json"), 7, &case).unwrap();
        let strings: Vec<String> =
            args.into_iter().map(|s| s.to_string_lossy().into_owned()).collect();
        assert_eq!(
            strings,
            vec![
                "eval",
                "/tmp/cap.json",
                "--body",
                "7",
                "--fuel",
                "42",
                "--json",
                "--arg",
                "u32:7"
            ]
        );
    }
}
