// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Host `rustc` differential execution authority compiling and running each
//! defined-behavior test case at BOTH `-C opt-level=0` AND `-C opt-level=2` and
//! asserting `O0 == O2` parity across `TerminalOutcome`, `ObservableSpine`, and
//! `CallerFrameLaw`.

use std::{
    env,
    ffi::{OsStr, OsString},
    fs,
    io::Write,
    path::{Path, PathBuf},
    process::ExitStatus,
    time::{Duration, Instant},
};

use anneal_testkit::{Invocation, ProcessOutcome, ProcessSupervisor, Termination};
use serde::{Deserialize, Serialize};

use crate::{
    outcome::{AuthorityRunResult, compare_spines},
    spec::{
        TraceTestCase, parse_pre_abort_stdout_with_expected_args,
        parse_trace_json_stdout_with_expected_args, render_standalone_rust_harness,
    },
    trace_observer::PRE_ABORT_JSON_PREFIX,
};

mod discovery;
mod invocation;

pub use discovery::*;
pub use invocation::*;

const RUSTC_COMPILE_TIMEOUT_SECS: u64 = 90;
const RUSTC_RUN_TIMEOUT_SECS: u64 = 30;

/// Combined result of running a trace case under `rustc -C opt-level=0` and
/// `rustc -C opt-level=2`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RustcDualResult {
    pub o0: AuthorityRunResult,
    pub o2: AuthorityRunResult,
    pub parity_ok: bool,
    pub skipped_for_ub: bool,
    pub mismatch_detail: Option<String>,
}

impl RustcDualResult {
    /// Construct a clean placeholder when host `rustc` execution is skipped
    /// because Miri proved UB or the case is an explicit `expected_ub` probe.
    pub fn skipped_for_ub(reason: &str) -> Self {
        Self {
            o0: AuthorityRunResult::skipped_for_ub("rustc-O0", reason),
            o2: AuthorityRunResult::skipped_for_ub("rustc-O2", reason),
            parity_ok: false,
            skipped_for_ub: true,
            mismatch_detail: None,
        }
    }
}

/// Prepared host `rustc` session bound to a consistent compiler sysroot and
/// validated 64-bit little-endian native host target triple.
#[derive(Clone, Debug)]
pub struct RustcRunner {
    pub rustc_bin: PathBuf,
    pub sysroot: Option<PathBuf>,
    pub host_target: String,
}

impl RustcRunner {
    /// Locate `rustc` consistently with Anneal's toolchain environment:
    /// 1. `ANNEAL_ITREE_RUSTC` or `RUSTC` environment override (verifying its
    ///    queried `--print sysroot` matches `expected_sysroot` whenever Lean /
    ///    capture pinned a sysroot),
    /// 2. `<expected_sysroot>/bin/rustc` from `ToolchainEnv::resolve` (failing
    ///    closed rather than falling back to ambient `PATH` when requested), or
    /// 3. `rustc` on `PATH` when `expected_sysroot` is `None` (`--no-lean`).
    pub fn discover(expected_sysroot: Option<&Path>) -> Result<Self, String> {
        Self::discover_with_env(expected_sysroot, |k| env::var_os(k))
    }

    /// Deterministic environment-injected variant of [`Self::discover`] for
    /// unit-testing toolchain skew rejection without mutating process env vars.
    pub fn discover_with_env(
        expected_sysroot: Option<&Path>,
        get_env: impl Fn(&str) -> Option<OsString>,
    ) -> Result<Self, String> {
        Self::discover_with_env_and_suffix(expected_sysroot, get_env, env::consts::EXE_SUFFIX)
    }

    /// Suffix-parameterized variant of [`Self::discover_with_env`] so unit
    /// tests can exercise Windows `.exe` toolchain and `PATH` resolution on
    /// Unix hosts as well.
    pub fn discover_with_env_and_suffix(
        expected_sysroot: Option<&Path>,
        get_env: impl Fn(&str) -> Option<OsString>,
        exe_suffix: &str,
    ) -> Result<Self, String> {
        let canon_expected = match expected_sysroot {
            Some(sr) => Some(
                fs::canonicalize(sr)
                    .map_err(|e| format!("canonicalize expected sysroot {}: {e}", sr.display()))?,
            ),
            None => None,
        };

        let expected_os = expected_native_os_for_suffix(exe_suffix);
        let path_var = get_env("PATH");
        for key in ["ANNEAL_ITREE_RUSTC", "RUSTC"] {
            if let Some(explicit) = get_env(key).filter(|v| !v.is_empty()) {
                let p = resolve_rustc_override_with_path_and_suffix(
                    &explicit,
                    path_var.as_deref(),
                    exe_suffix,
                )
                .map_err(|e| format!("resolve {key}: {e}"))?;
                let actual_sr = query_rustc_sysroot(&p)?;
                if let Some(exp_sr) = &canon_expected
                    && !sysroots_equivalent_with_suffix(exp_sr, &actual_sr, exe_suffix)?
                {
                    return Err(format!(
                        "toolchain version skew: explicit {key} ({}) resolves sysroot {}, which differs from Lean/capture sysroot {}",
                        p.display(),
                        actual_sr.display(),
                        exp_sr.display(),
                    ));
                }
                let rustc_bin =
                    pin_toolchain_rustc_if_rustup_proxy_with_suffix(p, &actual_sr, exe_suffix)?;
                if let Some(exp_sr) = &canon_expected
                    && !compiler_matches_pinned_sysroot_with_suffix(&rustc_bin, exp_sr, exe_suffix)?
                {
                    return Err(format!(
                        "toolchain compiler mismatch: explicit {key} ({}) is not the pinned sysroot compiler for {}",
                        rustc_bin.display(),
                        exp_sr.display(),
                    ));
                }
                let host_target = query_rustc_host_target_for_platform(
                    &rustc_bin,
                    Some(&actual_sr),
                    env::consts::ARCH,
                    expected_os,
                )?;
                return Ok(Self { rustc_bin, sysroot: Some(actual_sr), host_target });
            }
        }

        let rustc_exe = exe_name_for_suffix("rustc", exe_suffix);
        if let Some(exp_sr) = canon_expected {
            let candidate = exp_sr.join("bin").join(&rustc_exe);
            if !candidate.is_file() {
                return Err(format!(
                    "expected sysroot {} is missing `bin/{rustc_exe}` (refusing to fall back to ambient PATH `rustc`)",
                    exp_sr.display()
                ));
            }
            let p = resolve_rustc_executable_path_with_suffix(&candidate, exe_suffix)
                .map_err(|e| format!("resolve sysroot rustc {}: {e}", candidate.display()))?;
            let actual_sr = query_rustc_sysroot(&p)?;
            if !sysroots_equivalent_with_suffix(&exp_sr, &actual_sr, exe_suffix)? {
                return Err(format!(
                    "toolchain version skew: sysroot `rustc` ({}) resolves sysroot {}, which differs from expected sysroot {}",
                    p.display(),
                    actual_sr.display(),
                    exp_sr.display(),
                ));
            }
            let rustc_bin =
                pin_toolchain_rustc_if_rustup_proxy_with_suffix(p, &actual_sr, exe_suffix)?;
            let host_target = query_rustc_host_target_for_platform(
                &rustc_bin,
                Some(&actual_sr),
                env::consts::ARCH,
                expected_os,
            )?;
            return Ok(Self { rustc_bin, sysroot: Some(actual_sr), host_target });
        }

        if let Some(path_var) = get_env("PATH") {
            for dir in env::split_paths(&path_var) {
                let candidate = dir.join(&rustc_exe);
                if candidate.is_file() {
                    let p = resolve_rustc_executable_path_with_suffix(&candidate, exe_suffix)
                        .map_err(|e| format!("resolve PATH rustc: {e}"))?;
                    let actual_sr = query_rustc_sysroot(&p)?;
                    let rustc_bin =
                        pin_toolchain_rustc_if_rustup_proxy_with_suffix(p, &actual_sr, exe_suffix)?;
                    let host_target = query_rustc_host_target_for_platform(
                        &rustc_bin,
                        Some(&actual_sr),
                        env::consts::ARCH,
                        expected_os,
                    )?;
                    return Ok(Self { rustc_bin, sysroot: Some(actual_sr), host_target });
                }
            }
        }
        Err("cannot locate `rustc` binary (set RUSTC or ANNEAL_SYSROOT)".to_string())
    }

    /// Compile and run `case` at both `-C opt-level=0` and `-C opt-level=2`.
    pub fn run_dual(&self, case: &TraceTestCase) -> RustcDualResult {
        let tmp = match tempfile::Builder::new().prefix("anneal-itree-rustc-").tempdir() {
            Ok(d) => d,
            Err(e) => {
                let err = format!("create temp dir for rustc runner: {e}");
                return RustcDualResult {
                    o0: AuthorityRunResult::tool_error("rustc-O0", &err),
                    o2: AuthorityRunResult::tool_error("rustc-O2", &err),
                    parity_ok: false,
                    skipped_for_ub: false,
                    mismatch_detail: Some(err),
                };
            }
        };

        let harness_src = render_standalone_rust_harness(case);
        let src_path = tmp.path().join("harness.rs");
        if let Err(e) = fs::write(&src_path, &harness_src) {
            let err = format!("write harness {}: {e}", src_path.display());
            return RustcDualResult {
                o0: AuthorityRunResult::tool_error("rustc-O0", &err),
                o2: AuthorityRunResult::tool_error("rustc-O2", &err),
                parity_ok: false,
                skipped_for_ub: false,
                mismatch_detail: Some(err),
            };
        }

        let expected_entry_slots = case.rust_arg_exprs.len();
        let o0 = self.compile_and_run_opt(tmp.path(), &src_path, 0, Some(expected_entry_slots));
        let o2 = self.compile_and_run_opt(tmp.path(), &src_path, 2, Some(expected_entry_slots));

        let (parity_ok, mismatch_detail) = if o0.tool_error.is_some() || o2.tool_error.is_some() {
            (false, Some(format!("tool error: O0={:?}, O2={:?}", o0.tool_error, o2.tool_error)))
        } else if !o0.outcome.semantically_eq(&o2.outcome) {
            (
                false,
                Some(format!(
                    "O0 vs O2 outcome mismatch: O0={:?}, O2={:?}",
                    o0.outcome, o2.outcome
                )),
            )
        } else if let Err(msg) =
            compare_spines("rustc-O0", &o0.spine, "rustc-O2", &o2.spine, case.spine_mode)
        {
            (false, Some(msg))
        } else if !o0.caller_frame_law.is_satisfied() || !o2.caller_frame_law.is_satisfied() {
            (
                false,
                Some(format!(
                    "caller frame law failed: O0={:?}, O2={:?}",
                    o0.caller_frame_law.violations, o2.caller_frame_law.violations
                )),
            )
        } else {
            (true, None)
        };

        RustcDualResult { o0, o2, parity_ok, skipped_for_ub: false, mismatch_detail }
    }

    fn compile_and_run_opt(
        &self,
        work_dir: &Path,
        src_path: &Path,
        opt_level: u8,
        expected_entry_slots: Option<usize>,
    ) -> AuthorityRunResult {
        let auth_name = format!("rustc-O{opt_level}");
        let start = Instant::now();
        let bin_path = work_dir.join(exe_name(&format!("harness_o{opt_level}")));

        let sysroot_child_path = match &self.sysroot {
            Some(sr) => match build_child_path(&sr.join("bin")) {
                Ok(p) => Some(p),
                Err(detail) => return AuthorityRunResult::tool_error(&auth_name, detail),
            },
            None => env::var_os("PATH"),
        };

        let scratch_tmp = work_dir.join("tmp");
        if let Err(e) = fs::create_dir_all(&scratch_tmp) {
            return AuthorityRunResult::tool_error(
                &auth_name,
                format!("create rustc scratch temp {}: {e}", scratch_tmp.display()),
            );
        }

        let compile_inv = build_rustc_compile_invocation_with_env(
            &self.rustc_bin,
            &self.host_target,
            opt_level,
            src_path,
            &bin_path,
            self.sysroot.as_deref(),
            sysroot_child_path.as_deref(),
            Some(&scratch_tmp),
            |k| env::var_os(k),
        );

        let compile_out = match run_supervised(&compile_inv, work_dir, RUSTC_COMPILE_TIMEOUT_SECS) {
            Ok(out) => out,
            Err(detail) => return AuthorityRunResult::tool_error(&auth_name, detail),
        };
        match compile_out.termination {
            Termination::Exited(status) if status.success() => {}
            other => {
                return AuthorityRunResult::tool_error(
                    &auth_name,
                    format!(
                        "rustc -O{opt_level} compile failed ({}): {}",
                        other.describe(),
                        String::from_utf8_lossy(&compile_out.stderr)
                    ),
                );
            }
        }

        let run_inv = build_rustc_run_invocation_with_env(
            &bin_path,
            self.sysroot.as_deref(),
            sysroot_child_path.as_deref(),
            Some(&scratch_tmp),
            |k| env::var_os(k),
        );
        let run_out = match run_supervised(&run_inv, work_dir, RUSTC_RUN_TIMEOUT_SECS) {
            Ok(out) => out,
            Err(detail) => return AuthorityRunResult::tool_error(&auth_name, detail),
        };
        let elapsed_ms = start.elapsed().as_millis() as u64;
        let stdout = String::from_utf8_lossy(&run_out.stdout);
        let stderr = String::from_utf8_lossy(&run_out.stderr);

        match run_out.termination {
            Termination::Exited(status) => {
                #[cfg(unix)]
                let signal = {
                    use std::os::unix::process::ExitStatusExt;
                    status.signal()
                };
                #[cfg(not(unix))]
                let signal: Option<i32> = None;

                parse_rustc_run_output_with_expected_args(
                    &auth_name,
                    status.code(),
                    signal,
                    &stdout,
                    &stderr,
                    elapsed_ms,
                    expected_entry_slots,
                )
            }
            Termination::TimedOut(status) => AuthorityRunResult::tool_error(
                &auth_name,
                format!("timed out after {RUSTC_RUN_TIMEOUT_SECS}s ({status})"),
            ),
            Termination::LaunchFailed(err) => {
                AuthorityRunResult::tool_error(&auth_name, format!("launch failed: {err}"))
            }
        }
    }
}

/// Map native `rustc` binary exit code and Unix signal into an
/// [`AuthorityRunResult`].
///
/// Only exit code `0` with a unique `ANNEAL_ITREE_TRACE_JSON:` line or the
/// platform's `std::process::abort()` termination (`SIGABRT` `6` on Unix, or
/// Windows/CRT fast-fail abort exit codes on non-Unix hosts) paired with a
/// unique `ANNEAL_ITREE_PRE_ABORT:` sentinel maps to a domain outcome;
/// `exit(101)`, `SIGKILL` (`9`), `SIGSEGV` (`11`), `SIGBUS` (`7`), `SIGILL`
/// (`4`), and un-marked aborts all fail closed as `ToolError`.
pub fn parse_rustc_run_output(
    auth_name: &str,
    exit_code: Option<i32>,
    signal: Option<i32>,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
) -> AuthorityRunResult {
    parse_rustc_run_output_with_expected_args(
        auth_name, exit_code, signal, stdout, stderr, elapsed_ms, None,
    )
}

/// Entry-count-checked variant of [`parse_rustc_run_output`].
#[allow(clippy::too_many_arguments)]
pub fn parse_rustc_run_output_with_expected_args(
    auth_name: &str,
    exit_code: Option<i32>,
    signal: Option<i32>,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
    expected_entry_slots: Option<usize>,
) -> AuthorityRunResult {
    parse_rustc_run_output_for_platform_and_args(
        auth_name,
        exit_code,
        signal,
        stdout,
        stderr,
        elapsed_ms,
        cfg!(unix),
        expected_entry_slots,
    )
}

/// Platform-parameterized variant of [`parse_rustc_run_output`] so unit tests
/// can verify both Unix (`SIGABRT`) and non-Unix (Windows/CRT abort exit code)
/// scheduled-abort classification deterministically.
pub fn parse_rustc_run_output_for_platform(
    auth_name: &str,
    exit_code: Option<i32>,
    signal: Option<i32>,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
    is_unix: bool,
) -> AuthorityRunResult {
    parse_rustc_run_output_for_platform_and_args(
        auth_name, exit_code, signal, stdout, stderr, elapsed_ms, is_unix, None,
    )
}

#[allow(clippy::too_many_arguments)]
fn parse_rustc_run_output_for_platform_and_args(
    auth_name: &str,
    exit_code: Option<i32>,
    signal: Option<i32>,
    stdout: &str,
    stderr: &str,
    elapsed_ms: u64,
    is_unix: bool,
    expected_entry_slots: Option<usize>,
) -> AuthorityRunResult {
    if exit_code == Some(0) && signal.is_none() {
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

    let is_platform_abort = if is_unix {
        signal == Some(6)
    } else {
        signal.is_none() && is_non_unix_abort_exit_code(exit_code)
    };
    if is_platform_abort && stdout.lines().any(|l| l.trim().starts_with(PRE_ABORT_JSON_PREFIX)) {
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
            "unexpected host binary termination (exit={exit_code:?}, signal={signal:?}): stdout={stdout:?}, stderr={stderr:?}"
        ),
    )
}

fn is_non_unix_abort_exit_code(exit_code: Option<i32>) -> bool {
    const WIN_STATUS_STACK_BUFFER_OVERRUN: i32 = 0xC000_0409u32 as i32;
    const WIN_STATUS_ILLEGAL_INSTRUCTION: i32 = 0xC000_001Du32 as i32;
    const WIN_STATUS_BREAKPOINT: i32 = 0x8000_0003u32 as i32;
    const CRT_ABORT_EXIT_CODE: i32 = 3;
    matches!(
        exit_code,
        Some(
            WIN_STATUS_STACK_BUFFER_OVERRUN
                | WIN_STATUS_ILLEGAL_INSTRUCTION
                | WIN_STATUS_BREAKPOINT
                | CRT_ABORT_EXIT_CODE
        )
    )
}
