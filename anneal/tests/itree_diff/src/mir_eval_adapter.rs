// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Optional pluggable adapter for external `anneal-mir-eval` binaries.
//!
//! Probes `ANNEAL_MIR_EVAL_BIN` and `PATH`, returning
//! [`MirEvalAvailability::Unavailable`] cleanly when `ANNEAL_MIR_EVAL_BIN` is
//! unset and no executable is on `PATH`, failing closed with
//! [`MirEvalAvailability::InvalidConfig`] whenever an explicit
//! `ANNEAL_MIR_EVAL_BIN` override is invalid, and validating exit-code / JSON
//! protocol invariants strictly when invoked.

use std::{
    env,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use anneal_testkit::{Invocation, Termination};
use serde::Deserialize;

use crate::{
    outcome::{
        AuthorityRunResult, CallerFrameLaw, IntKind, OrderingVal, TerminalOutcome, TraceVal,
        compute_boundary_mem_digest, validate_boundary_slots_for_outcome,
    },
    rustc_runner::{
        DYLIB_PATH_ENV_VAR, exe_name_for_suffix, forward_env_keys_with_env,
        forward_platform_temp_and_profile_env_with_env, resolve_explicit_or_path_exe_with_suffix,
        run_supervised_with_prefix,
    },
    spec::ReturnShape,
    trace_observer::ObservableSpine,
};

const MIR_EVAL_TIMEOUT_SECS: u64 = 120;

/// Probe result for an optional `anneal-mir-eval` executable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MirEvalAvailability {
    Available(MirEvalAdapter),
    Unavailable { reason: String },
    InvalidConfig { reason: String },
}

/// Pluggable CLI/JSON adapter for `anneal-mir-eval`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MirEvalAdapter {
    pub binary: PathBuf,
}

fn check_executable_file(path: &Path) -> Result<(), String> {
    let meta = fs::metadata(path).map_err(|e| format!("stat {}: {e}", path.display()))?;
    if !meta.is_file() {
        return Err(format!("{} is not a regular file", path.display()));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = meta.permissions().mode();
        if (mode & 0o111) == 0 {
            return Err(format!("{} is not executable (mode {:o})", path.display(), mode));
        }
    }
    Ok(())
}

/// Build the clean-environment `anneal-mir-eval` [`Invocation`], preserving
/// `PATH`, platform dynamic-library search paths, and host temporary/profile
/// variables while falling back to `fallback_temp` if no temp variable is set.
pub fn build_mir_eval_invocation_with_env(
    binary: &Path,
    cli_args: &[OsString],
    fallback_temp: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Invocation {
    let mut inv = Invocation::new(binary, &[]);
    for a in cli_args {
        inv = inv.arg(a);
    }
    inv = forward_env_keys_with_env(inv, &[DYLIB_PATH_ENV_VAR, "PATH"], &get_env);
    forward_platform_temp_and_profile_env_with_env(inv, fallback_temp, get_env)
}

impl MirEvalAdapter {
    /// Probe `ANNEAL_MIR_EVAL_BIN` and `PATH` for an `anneal-mir-eval` binary.
    pub fn probe() -> MirEvalAvailability {
        Self::probe_with_env(|k| env::var_os(k))
    }

    /// Deterministic probe variant accepting a custom environment lookup
    /// closure for unit tests.
    pub fn probe_with_env(get_env: impl Fn(&str) -> Option<OsString>) -> MirEvalAvailability {
        Self::probe_with_env_and_suffix(get_env, env::consts::EXE_SUFFIX)
    }

    /// Suffix-parameterized variant of [`Self::probe_with_env`] so unit tests
    /// can verify Windows `.exe` discovery on Unix hosts.
    pub fn probe_with_env_and_suffix(
        get_env: impl Fn(&str) -> Option<OsString>,
        exe_suffix: &str,
    ) -> MirEvalAvailability {
        if let Some(raw) = get_env("ANNEAL_MIR_EVAL_BIN") {
            if raw.is_empty() {
                return MirEvalAvailability::InvalidConfig {
                    reason: "ANNEAL_MIR_EVAL_BIN is set to an empty path".to_string(),
                };
            }
            let path_var = get_env("PATH");
            let raw_path = PathBuf::from(&raw);
            let Some(p) =
                resolve_explicit_or_path_exe_with_suffix(&raw, path_var.as_deref(), exe_suffix)
            else {
                return MirEvalAvailability::InvalidConfig {
                    reason: format!(
                        "ANNEAL_MIR_EVAL_BIN={} does not point to an existing regular file",
                        raw_path.display()
                    ),
                };
            };
            let canon = match fs::canonicalize(&p) {
                Ok(c) => c,
                Err(e) => {
                    return MirEvalAvailability::InvalidConfig {
                        reason: format!(
                            "cannot canonicalize ANNEAL_MIR_EVAL_BIN ({}): {e}",
                            p.display()
                        ),
                    };
                }
            };
            if let Err(reason) = check_executable_file(&canon) {
                return MirEvalAvailability::InvalidConfig {
                    reason: format!("ANNEAL_MIR_EVAL_BIN invalid: {reason}"),
                };
            }
            return MirEvalAvailability::Available(Self { binary: canon });
        }

        let eval_exe = exe_name_for_suffix("anneal-mir-eval", exe_suffix);
        if let Some(path_var) = get_env("PATH") {
            for dir in env::split_paths(&path_var) {
                let candidate = dir.join(&eval_exe);
                if candidate.is_file()
                    && let Ok(canon) = fs::canonicalize(&candidate)
                    && check_executable_file(&canon).is_ok()
                {
                    return MirEvalAvailability::Available(Self { binary: canon });
                }
            }
        }

        MirEvalAvailability::Unavailable {
            reason: "anneal-mir-eval binary not found in ANNEAL_MIR_EVAL_BIN or PATH".to_string(),
        }
    }

    /// Invoke `anneal-mir-eval eval <capture.json> --body <body_id> --fuel
    /// <fuel> [--arg ...] --json`.
    pub fn eval_captured(
        &self,
        capture_json: &Path,
        body_id: usize,
        fuel: u64,
        args: &[TraceVal],
    ) -> AuthorityRunResult {
        self.eval_captured_for_shape(capture_json, body_id, fuel, args, None)
    }

    /// Shape-aware variant of [`Self::eval_captured`] normalizing `Val::Ptr`
    /// results consistently with [`ReturnShape::OpaquePtr`] and conservatively
    /// skipping unmodeled `Val::Bytes` / non-`OpaquePtr` pointer return shapes
    /// rather than faulting with `ToolError`.
    pub fn eval_captured_for_shape(
        &self,
        capture_json: &Path,
        body_id: usize,
        fuel: u64,
        args: &[TraceVal],
        ret_shape: Option<&ReturnShape>,
    ) -> AuthorityRunResult {
        let start = Instant::now();
        let mut cli_args = vec![
            OsString::from("eval"),
            capture_json.as_os_str().to_os_string(),
            OsString::from("--body"),
            OsString::from(body_id.to_string()),
            OsString::from("--fuel"),
            OsString::from(fuel.to_string()),
            OsString::from("--json"),
        ];
        for arg in args {
            match format_eval_arg(arg) {
                Ok(formatted) => {
                    cli_args.push(OsString::from("--arg"));
                    cli_args.push(OsString::from(formatted));
                }
                Err(reason) => {
                    return AuthorityRunResult {
                        authority: "anneal-mir-eval".to_string(),
                        outcome: TerminalOutcome::CaptureRefused { reason },
                        spine: ObservableSpine::default(),
                        caller_frame_law: CallerFrameLaw::all_satisfied(),
                        tool_error: None,
                        raw_diagnostics: String::new(),
                        elapsed_ms: start.elapsed().as_millis() as u64,
                        post_only_mem_digest: false,
                        entry_mem_digest: None,
                    };
                }
            }
        }

        let inv =
            build_mir_eval_invocation_with_env(&self.binary, &cli_args, None, |k| env::var_os(k));
        let out = match run_supervised_with_prefix(
            "anneal-itree-mireval-",
            &inv,
            None,
            MIR_EVAL_TIMEOUT_SECS,
        ) {
            Ok(o) => o,
            Err(e) => return AuthorityRunResult::tool_error("anneal-mir-eval", e),
        };
        let elapsed_ms = start.elapsed().as_millis() as u64;

        let exit_code = match out.termination {
            Termination::Exited(status) => status.code(),
            Termination::TimedOut(status) => {
                return AuthorityRunResult::tool_error(
                    "anneal-mir-eval",
                    format!("timed out after {MIR_EVAL_TIMEOUT_SECS}s ({status})"),
                );
            }
            Termination::LaunchFailed(err) => {
                return AuthorityRunResult::tool_error(
                    "anneal-mir-eval",
                    format!("spawn {}: {err}", self.binary.display()),
                );
            }
        };
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        parse_mir_eval_output_with_fuel_and_shape(
            exit_code,
            &stdout,
            &stderr,
            fuel,
            elapsed_ms,
            ret_shape,
            Some(args.len()),
        )
    }
}

fn format_eval_arg(val: &TraceVal) -> Result<String, String> {
    match val {
        TraceVal::Scalar { kind, bits } => Ok(kind.to_mir_eval_arg(*bits)),
        TraceVal::Bool { value } => Ok(format!("bool:{value}")),
        TraceVal::Char { scalar } => Ok(format!("char:U+{scalar:04X}")),
        TraceVal::Ordering { value } => Ok(format!("ordering:{}", value.as_str())),
        TraceVal::Unit => Ok("unit:()".to_string()),
        TraceVal::Enum { variant_index, .. } => Ok(format!("variant:{variant_index}")),
        TraceVal::Tuple { .. } | TraceVal::PaddedBytes { .. } => {
            Err(format!("unsupported anneal-mir-eval CLI argument shape: {val:?}"))
        }
    }
}

#[derive(Deserialize)]
struct RawEvalTrace {
    outcome: RawEvalOutcome,
    #[serde(default)]
    boundary_slots: Option<Vec<Vec<Option<u8>>>>,
}

#[derive(Deserialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
enum RawEvalOutcome {
    Returned(RawEvalTerminal),
    Aborted(serde::de::IgnoredAny),
    Fault(RawEvalFault),
    OutOfFuel,
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum RawEvalTerminal {
    Returned { ret: RawEvalVal },
    Unwound {},
}

#[derive(Deserialize)]
struct RawEvalFault {
    kind: String,
    reason: String,
}

#[derive(Deserialize)]
struct RawEvalPtr {
    alloc_id: Option<u64>,
    offset_bytes: u64,
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum RawEvalTagRepr {
    ZeroSized,
    Scalar { width: String },
}

#[derive(Deserialize)]
struct RawEvalEnumTy {
    #[serde(default)]
    discriminants: Vec<String>,
    #[serde(default)]
    tag_repr: Option<RawEvalTagRepr>,
}

#[derive(Deserialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
enum RawEvalVal {
    Scalar(RawEvalScalar),
    Ptr(RawEvalPtr),
    Bool(bool),
    Char(char),
    Ordering(String),
    Unit,
    EnumVal {
        #[serde(default)]
        ty: Option<RawEvalEnumTy>,
        variant: usize,
    },
    Tuple(Vec<RawEvalVal>),
    Bytes(serde::de::IgnoredAny),
    #[serde(other)]
    Other,
}

#[derive(Deserialize)]
struct RawEvalScalar {
    width: String,
    signed: bool,
    bits: String,
}

/// Parse `anneal-mir-eval eval --json` output into an [`AuthorityRunResult`],
/// cross-checking exit codes (`0` Returned/Unwound, `2` Undefined, `3`
/// Unsupported/OutOfFuel, `4` Aborted) and deriving `mem_digest` strictly from
/// `mir_eval`'s own JSON output (never synthesizing from harness inputs).
pub fn parse_mir_eval_output(
    exit_code: Option<i32>,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
) -> AuthorityRunResult {
    parse_mir_eval_output_with_fuel_and_shape(exit_code, stdout, stderr, 0, elapsed_ms, None, None)
}

/// Entry-count- and shape-parameterized variant of [`parse_mir_eval_output`].
#[allow(clippy::too_many_arguments)]
pub fn parse_mir_eval_output_with_expected_args(
    exit_code: Option<i32>,
    stdout: &str,
    stderr: &str,
    fuel: u64,
    elapsed_ms: u64,
    ret_shape: Option<&ReturnShape>,
    expected_entry_slots: Option<usize>,
) -> AuthorityRunResult {
    parse_mir_eval_output_with_fuel_and_shape(
        exit_code,
        stdout,
        stderr,
        fuel,
        elapsed_ms,
        ret_shape,
        expected_entry_slots,
    )
}

#[allow(clippy::too_many_arguments)]
fn parse_mir_eval_output_with_fuel_and_shape(
    exit_code: Option<i32>,
    stdout: &str,
    stderr: &str,
    fuel: u64,
    elapsed_ms: u64,
    ret_shape: Option<&ReturnShape>,
    expected_entry_slots: Option<usize>,
) -> AuthorityRunResult {
    let trimmed_err = stderr.trim();
    if !matches!(exit_code, Some(0 | 2 | 3 | 4)) {
        return AuthorityRunResult::tool_error(
            "anneal-mir-eval",
            format!("unexpected exit code {exit_code:?}: {trimmed_err}"),
        );
    }

    let trace: RawEvalTrace = match serde_json::from_str(stdout) {
        Ok(t) => t,
        Err(e) => {
            return AuthorityRunResult::tool_error(
                "anneal-mir-eval",
                format!("malformed JSON: {e}; raw={stdout:?}"),
            );
        }
    };

    let explicit_slots = trace.boundary_slots;
    let mut post_only_mem_digest = false;
    let mut entry_mem_digest = None;

    let outcome = match trace.outcome {
        RawEvalOutcome::Returned(RawEvalTerminal::Returned { ret }) => {
            if exit_code != Some(0) {
                return AuthorityRunResult::tool_error(
                    "anneal-mir-eval",
                    format!("protocol mismatch: Returned JSON with exit code {exit_code:?}"),
                );
            }
            match convert_eval_val(ret, ret_shape) {
                Ok(Some(v)) => {
                    let mem_digest = if let Some(slots) = &explicit_slots {
                        if let Err(detail) = validate_boundary_slots_for_outcome(
                            "anneal-mir-eval",
                            "returned",
                            Some(&v),
                            expected_entry_slots,
                            slots,
                        ) {
                            return AuthorityRunResult::tool_error("anneal-mir-eval", detail);
                        }
                        let entry_len = slots.len().saturating_sub(1);
                        if expected_entry_slots.is_some() || entry_len > 0 {
                            entry_mem_digest =
                                Some(compute_boundary_mem_digest(&slots[..entry_len]));
                        }
                        compute_boundary_mem_digest(slots)
                    } else {
                        post_only_mem_digest = true;
                        let rb = v.encode_boundary_bytes();
                        let mut post_slot = Vec::with_capacity(1 + rb.len());
                        post_slot.push(Some(0x10));
                        post_slot.extend(rb);
                        compute_boundary_mem_digest(&[post_slot])
                    };
                    TerminalOutcome::Returned { ret: v, mem_digest }
                }
                Ok(None) => {
                    if let Some(slots) = &explicit_slots {
                        if let Err(detail) = validate_boundary_slots_for_outcome(
                            "anneal-mir-eval",
                            "returned",
                            None,
                            expected_entry_slots,
                            slots,
                        ) {
                            return AuthorityRunResult::tool_error("anneal-mir-eval", detail);
                        }
                        let entry_len = slots.len().saturating_sub(1);
                        if expected_entry_slots.is_some() || entry_len > 0 {
                            entry_mem_digest =
                                Some(compute_boundary_mem_digest(&slots[..entry_len]));
                        }
                    }
                    TerminalOutcome::CaptureRefused {
                        reason: "unsupported return value shape in anneal-mir-eval output"
                            .to_string(),
                    }
                }
                Err(detail) => return AuthorityRunResult::tool_error("anneal-mir-eval", detail),
            }
        }
        RawEvalOutcome::Returned(RawEvalTerminal::Unwound {}) => {
            if exit_code != Some(0) {
                return AuthorityRunResult::tool_error(
                    "anneal-mir-eval",
                    format!("protocol mismatch: Unwound JSON with exit code {exit_code:?}"),
                );
            }
            let mem_digest = if let Some(slots) = &explicit_slots {
                if let Err(detail) = validate_boundary_slots_for_outcome(
                    "anneal-mir-eval",
                    "unwound",
                    None,
                    expected_entry_slots,
                    slots,
                ) {
                    return AuthorityRunResult::tool_error("anneal-mir-eval", detail);
                }
                let entry_len = slots.len().saturating_sub(1);
                if expected_entry_slots.is_some() || entry_len > 0 {
                    entry_mem_digest = Some(compute_boundary_mem_digest(&slots[..entry_len]));
                }
                compute_boundary_mem_digest(slots)
            } else {
                post_only_mem_digest = true;
                compute_boundary_mem_digest(&[vec![Some(0x20)]])
            };
            TerminalOutcome::Unwound { mem_digest }
        }
        RawEvalOutcome::Aborted(_) => {
            if exit_code != Some(4) {
                return AuthorityRunResult::tool_error(
                    "anneal-mir-eval",
                    format!(
                        "protocol mismatch: Aborted JSON with exit code {exit_code:?} (expected 4)"
                    ),
                );
            }
            let mem_digest = if let Some(slots) = &explicit_slots {
                if let Err(detail) = validate_boundary_slots_for_outcome(
                    "anneal-mir-eval",
                    "aborted",
                    None,
                    expected_entry_slots,
                    slots,
                ) {
                    return AuthorityRunResult::tool_error("anneal-mir-eval", detail);
                }
                let entry_len = slots.len().saturating_sub(1);
                if expected_entry_slots.is_some() || entry_len > 0 {
                    entry_mem_digest = Some(compute_boundary_mem_digest(&slots[..entry_len]));
                }
                compute_boundary_mem_digest(slots)
            } else {
                post_only_mem_digest = true;
                compute_boundary_mem_digest(&[vec![Some(0x30)]])
            };
            TerminalOutcome::Aborted { mem_digest }
        }
        RawEvalOutcome::Fault(f) => match f.kind.as_str() {
            "undefined" => {
                if exit_code != Some(2) {
                    return AuthorityRunResult::tool_error(
                        "anneal-mir-eval",
                        format!(
                            "protocol mismatch: undefined JSON with exit code {exit_code:?} (expected 2)"
                        ),
                    );
                }
                if let Some(slots) = &explicit_slots {
                    if let Err(detail) = validate_boundary_slots_for_outcome(
                        "anneal-mir-eval",
                        "fault_undefined",
                        None,
                        expected_entry_slots,
                        slots,
                    ) {
                        return AuthorityRunResult::tool_error("anneal-mir-eval", detail);
                    }
                    if expected_entry_slots.is_some() || !slots.is_empty() {
                        entry_mem_digest = Some(compute_boundary_mem_digest(slots));
                    }
                } else {
                    post_only_mem_digest = true;
                }
                TerminalOutcome::FaultUb { detail: f.reason }
            }
            "unsupported" => {
                if exit_code != Some(3) {
                    return AuthorityRunResult::tool_error(
                        "anneal-mir-eval",
                        format!(
                            "protocol mismatch: unsupported JSON with exit code {exit_code:?} (expected 3)"
                        ),
                    );
                }
                if let Some(slots) = &explicit_slots
                    && let Err(detail) = validate_boundary_slots_for_outcome(
                        "anneal-mir-eval",
                        "fault_unsupported",
                        None,
                        expected_entry_slots,
                        slots,
                    )
                {
                    return AuthorityRunResult::tool_error("anneal-mir-eval", detail);
                }
                TerminalOutcome::CaptureRefused { reason: f.reason }
            }
            other => {
                return AuthorityRunResult::tool_error(
                    "anneal-mir-eval",
                    format!("unknown fault kind {other:?}"),
                );
            }
        },
        RawEvalOutcome::OutOfFuel => {
            if exit_code != Some(3) {
                return AuthorityRunResult::tool_error(
                    "anneal-mir-eval",
                    format!(
                        "protocol mismatch: OutOfFuel JSON with exit code {exit_code:?} (expected 3)"
                    ),
                );
            }
            if let Some(slots) = &explicit_slots
                && let Err(detail) = validate_boundary_slots_for_outcome(
                    "anneal-mir-eval",
                    "diverged",
                    None,
                    expected_entry_slots,
                    slots,
                )
            {
                return AuthorityRunResult::tool_error("anneal-mir-eval", detail);
            }
            TerminalOutcome::Diverged { fuel }
        }
    };

    AuthorityRunResult {
        authority: "anneal-mir-eval".to_string(),
        outcome,
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: stderr.to_string(),
        elapsed_ms,
        post_only_mem_digest,
        entry_mem_digest,
    }
}

fn convert_eval_val(
    val: RawEvalVal,
    ret_shape: Option<&ReturnShape>,
) -> Result<Option<TraceVal>, String> {
    match val {
        RawEvalVal::Scalar(s) => {
            let kind = IntKind::from_width_signed(&s.width, s.signed).ok_or_else(|| {
                format!("unknown scalar width/signed ({}, {})", s.width, s.signed)
            })?;
            let bits = parse_bits_string(&s.bits)?;
            Ok(Some(TraceVal::Scalar { kind, bits: kind.mask_bits(bits) }))
        }
        RawEvalVal::Ptr(p) => match ret_shape {
            None | Some(ReturnShape::OpaquePtr) => match p.alloc_id {
                Some(_) if p.offset_bytes <= isize::MAX as u64 => {
                    Ok(Some(TraceVal::Scalar { kind: IntKind::Usize, bits: 1 }))
                }
                Some(_) => Ok(None),
                None => Ok(Some(TraceVal::Scalar {
                    kind: IntKind::Usize,
                    bits: u128::from(p.offset_bytes != 0),
                })),
            },
            Some(_) => Ok(None),
        },
        RawEvalVal::Bool(value) => Ok(Some(TraceVal::Bool { value })),
        RawEvalVal::Char(c) => Ok(Some(TraceVal::Char { scalar: c as u32 })),
        RawEvalVal::Ordering(s) => {
            let value = match s.as_str() {
                "less" | "Less" => OrderingVal::Less,
                "equal" | "Equal" => OrderingVal::Equal,
                "greater" | "Greater" => OrderingVal::Greater,
                other => return Err(format!("unknown Ordering variant {other:?}")),
            };
            Ok(Some(TraceVal::Ordering { value }))
        }
        RawEvalVal::Unit => Ok(Some(TraceVal::Unit)),
        RawEvalVal::EnumVal { ty, variant } => {
            let tag_bytes = ty.as_ref().and_then(|ety| match &ety.tag_repr {
                Some(RawEvalTagRepr::ZeroSized) => Some(0),
                Some(RawEvalTagRepr::Scalar { width }) => {
                    IntKind::from_width_signed(width, false).map(IntKind::byte_width)
                }
                None => None,
            });
            let discriminant = match ty {
                Some(ety) if !ety.discriminants.is_empty() => {
                    let raw = ety.discriminants.get(variant).ok_or_else(|| {
                        format!(
                            "out-of-bounds EnumVal variant {variant} (len={})",
                            ety.discriminants.len()
                        )
                    })?;
                    parse_bits_string(raw)?
                }
                _ => variant as u128,
            };
            Ok(Some(TraceVal::Enum {
                type_name: String::new(),
                variant_name: String::new(),
                variant_index: variant,
                discriminant,
                tag_bytes,
            }))
        }
        RawEvalVal::Tuple(fields) => {
            let mut converted = Vec::with_capacity(fields.len());
            for f in fields {
                match convert_eval_val(f, Some(&ReturnShape::Unit))? {
                    Some(v) => converted.push(v),
                    None => return Ok(None),
                }
            }
            Ok(Some(TraceVal::Tuple { fields: converted }))
        }
        RawEvalVal::Bytes(_) => Ok(None),
        RawEvalVal::Other => Err("unsupported value variant in anneal-mir-eval output".to_string()),
    }
}

fn parse_bits_string(raw: &str) -> Result<u128, String> {
    let trimmed = raw.trim();
    if let Some(hex) = trimmed.strip_prefix("0x").or_else(|| trimmed.strip_prefix("0X")) {
        u128::from_str_radix(hex, 16).map_err(|e| format!("parse hex bits {raw:?}: {e}"))
    } else {
        trimmed.parse::<u128>().map_err(|e| format!("parse decimal bits {raw:?}: {e}"))
    }
}
