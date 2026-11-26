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

/// Bounded timeout (seconds) for toolchain discovery subprocesses
/// (`--print sysroot`, `-vV`, `--version --verbose`, `rustup run`).
pub const DISCOVERY_PROBE_TIMEOUT_SECS: u64 = 30;

/// Status and captured output streams returned by [`run_probe_supervised`].
#[derive(Clone, Debug)]
pub struct SupervisedProbeOutput {
    pub status: ExitStatus,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

fn is_bare_executable_name(path: &Path) -> bool {
    let raw_lossy = path.as_os_str().to_string_lossy();
    !raw_lossy.contains('/')
        && !raw_lossy.contains('\\')
        && matches!(
            path.components().collect::<Vec<_>>().as_slice(),
            [std::path::Component::Normal(_)]
        )
}

/// Supervise a short-lived toolchain discovery command under
/// [`ProcessSupervisor`] with bounded wall-clock timeout and `ETXTBSY` launch
/// retries, forwarding standard toolchain and platform environment variables.
pub fn run_probe_supervised(
    executable: &Path,
    args: &[&str],
    dylib_search_path: Option<&OsStr>,
    forward_rustup_toolchain: bool,
) -> Result<SupervisedProbeOutput, String> {
    run_probe_supervised_with_timeout(
        executable,
        args,
        dylib_search_path,
        forward_rustup_toolchain,
        DISCOVERY_PROBE_TIMEOUT_SECS,
    )
}

/// Timeout-parameterized variant of [`run_probe_supervised`].
pub fn run_probe_supervised_with_timeout(
    executable: &Path,
    args: &[&str],
    dylib_search_path: Option<&OsStr>,
    forward_rustup_toolchain: bool,
    timeout_secs: u64,
) -> Result<SupervisedProbeOutput, String> {
    run_probe_supervised_with_env_and_timeout(
        executable,
        args,
        dylib_search_path,
        forward_rustup_toolchain,
        timeout_secs,
        |k| env::var_os(k),
    )
}

/// Environment- and timeout-parameterized variant of [`run_probe_supervised`].
pub fn run_probe_supervised_with_env_and_timeout(
    executable: &Path,
    args: &[&str],
    dylib_search_path: Option<&OsStr>,
    forward_rustup_toolchain: bool,
    timeout_secs: u64,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Result<SupervisedProbeOutput, String> {
    let resolved = if is_bare_executable_name(executable) {
        resolve_explicit_or_path_exe_with_suffix(
            executable.as_os_str(),
            get_env("PATH").as_deref(),
            env::consts::EXE_SUFFIX,
        )
        .ok_or_else(|| format!("executable `{}` not found on PATH", executable.display()))?
    } else {
        executable.to_path_buf()
    };
    let abs_candidate = if resolved.is_absolute() {
        resolved
    } else {
        env::current_dir()
            .map_err(|e| format!("resolve current dir for `{}`: {e}", resolved.display()))?
            .join(&resolved)
    };
    let abs_exe = match (abs_candidate.parent(), abs_candidate.file_name()) {
        (Some(parent), Some(leaf)) => fs::canonicalize(parent)
            .map(|canon_parent| canon_parent.join(leaf))
            .unwrap_or(abs_candidate),
        _ => abs_candidate,
    };
    let mut inv = Invocation::new(&abs_exe, args);
    if let Some(dylib) = dylib_search_path {
        inv = inv.env(DYLIB_PATH_ENV_VAR, dylib);
    } else {
        inv = forward_env_keys_with_env(inv, &[DYLIB_PATH_ENV_VAR], &get_env);
    }
    inv = forward_standard_tool_env_with_env(inv, None, &get_env);
    if forward_rustup_toolchain {
        inv = forward_env_keys_with_env(inv, &["RUSTUP_TOOLCHAIN"], &get_env);
    }
    let out = run_supervised_with_prefix("anneal-itree-probe-", &inv, None, timeout_secs)?;
    match out.termination {
        Termination::Exited(status) => {
            Ok(SupervisedProbeOutput { status, stdout: out.stdout, stderr: out.stderr })
        }
        Termination::TimedOut(status) => Err(format!("timed out after {timeout_secs}s ({status})")),
        Termination::LaunchFailed(err) => Err(err),
    }
}

/// Query `<rustc_bin> --print sysroot` with a bounded timeout and return its
/// canonicalized directory path so wrapper scripts, `rustup` shims, and
/// standalone sysroot compilers report their true backing sysroot.
pub fn query_rustc_sysroot(rustc_bin: &Path) -> Result<PathBuf, String> {
    query_rustc_sysroot_with_timeout(rustc_bin, DISCOVERY_PROBE_TIMEOUT_SECS)
}

/// Timeout-parameterized variant of [`query_rustc_sysroot`].
pub fn query_rustc_sysroot_with_timeout(
    rustc_bin: &Path,
    timeout_secs: u64,
) -> Result<PathBuf, String> {
    if !rustc_bin.is_file() {
        return Err(format!("missing `rustc` executable at {}", rustc_bin.display()));
    }
    let dylib = infer_sysroot_from_rustc(rustc_bin).map(|sr| join_dylib_path(&sr.join("lib")));
    let out = run_probe_supervised_with_timeout(
        rustc_bin,
        &["--print", "sysroot"],
        dylib.as_deref(),
        true,
        timeout_secs,
    )
    .map_err(|e| format!("invoke `{} --print sysroot`: {e}", rustc_bin.display()))?;
    if !out.status.success() {
        return Err(format!(
            "`{} --print sysroot` failed ({}): {}",
            rustc_bin.display(),
            out.status,
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    let stdout = String::from_utf8(out.stdout).map_err(|e| {
        format!("invalid UTF-8 from `{} --print sysroot`: {e}", rustc_bin.display())
    })?;
    let trimmed = stdout.trim();
    if trimmed.is_empty() {
        return Err(format!("`{} --print sysroot` returned empty stdout", rustc_bin.display()));
    }
    fs::canonicalize(trimmed).map_err(|e| {
        format!("canonicalize sysroot `{trimmed}` reported by `{}`: {e}", rustc_bin.display())
    })
}

/// If `sysroot` is a `pkgs.symlinkJoin`-style wrapper directory whose
/// `bin/rustc<exe_suffix>` wrapper script delegates `--print sysroot` to a
/// distinct backing compiler store path AND whose `lib` tree links into that
/// backing sysroot without escaping outside either root, return `Ok(Some(b))`.
/// Returns `Ok(None)` when `sysroot` is already a direct sysroot or does not
/// structurally delegate to its queried compiler sysroot.
pub fn resolve_verified_backing_sysroot_with_suffix(
    sysroot: &Path,
    exe_suffix: &str,
) -> Result<Option<PathBuf>, String> {
    let canon = fs::canonicalize(sysroot)
        .map_err(|e| format!("canonicalize sysroot {}: {e}", sysroot.display()))?;
    let rustc_cand = canon.join("bin").join(exe_name_for_suffix("rustc", exe_suffix));
    if !rustc_cand.is_file() {
        return Ok(None);
    }
    let canon_rustc = fs::canonicalize(&rustc_cand)
        .map_err(|e| format!("canonicalize {}: {e}", rustc_cand.display()))?;
    if canon_rustc.file_name().is_some_and(is_rustup_executable_name) {
        return Ok(None);
    }
    let wrapper_lib = canon.join("lib");
    if !wrapper_lib.is_dir() {
        return Ok(None);
    }

    let mut external_targets = Vec::new();
    let mut dirs_to_scan = vec![wrapper_lib.clone()];
    let wrapper_rustlib = wrapper_lib.join("rustlib");
    if let Ok(meta) = fs::symlink_metadata(&wrapper_rustlib)
        && meta.file_type().is_dir()
    {
        dirs_to_scan.push(wrapper_rustlib);
    }
    for dir in dirs_to_scan {
        let entries = fs::read_dir(&dir).map_err(|e| format!("read_dir {}: {e}", dir.display()))?;
        for entry in entries {
            let entry = entry.map_err(|e| format!("iterate {}: {e}", dir.display()))?;
            let path = entry.path();
            let meta = fs::symlink_metadata(&path)
                .map_err(|e| format!("inspect {}: {e}", path.display()))?;
            if meta.file_type().is_symlink() {
                let target = fs::canonicalize(&path)
                    .map_err(|e| format!("resolve symlink {}: {e}", path.display()))?;
                if !target.starts_with(&canon) {
                    external_targets.push(target);
                }
            }
        }
    }
    if external_targets.is_empty() {
        for probe in [
            "lib/rustlib/src/rust/Cargo.lock",
            "lib/rustlib/src/rust/library/Cargo.lock",
            "lib/rustlib/src/rust/library/core/Cargo.toml",
        ] {
            let p = canon.join(probe);
            if let Ok(meta) = fs::symlink_metadata(&p)
                && meta.file_type().is_symlink()
                && let Ok(target) = fs::canonicalize(&p)
                && !target.starts_with(&canon)
            {
                external_targets.push(target);
                break;
            }
        }
    }
    if external_targets.is_empty() {
        return Ok(None);
    }

    let queried = query_rustc_sysroot(&rustc_cand)?;
    if queried == canon || !queried.join("lib").is_dir() {
        return Ok(None);
    }
    if external_targets.iter().all(|t| t.starts_with(&queried)) {
        Ok(Some(queried))
    } else {
        Ok(None)
    }
}

/// Return `true` when `expected_sr` and `actual_sr` canonicalize to the same
/// directory OR when one is a verified `pkgs.symlinkJoin` wrapper sysroot (such
/// as `anneal/flake.nix`'s `testSysroot`) delegating to the other.
pub fn sysroots_equivalent_with_suffix(
    expected_sr: &Path,
    actual_sr: &Path,
    exe_suffix: &str,
) -> Result<bool, String> {
    let canon_exp = fs::canonicalize(expected_sr)
        .map_err(|e| format!("canonicalize sysroot {}: {e}", expected_sr.display()))?;
    let canon_act = fs::canonicalize(actual_sr)
        .map_err(|e| format!("canonicalize sysroot {}: {e}", actual_sr.display()))?;
    if canon_exp == canon_act {
        return Ok(true);
    }
    if resolve_verified_backing_sysroot_with_suffix(&canon_exp, exe_suffix)?.as_deref()
        == Some(canon_act.as_path())
    {
        return Ok(true);
    }
    if resolve_verified_backing_sysroot_with_suffix(&canon_act, exe_suffix)?.as_deref()
        == Some(canon_exp.as_path())
    {
        return Ok(true);
    }
    Ok(false)
}

/// Verify that `rustc_bin` is canonically the pinned `rustc` executable in
/// `exp_sr` (or its verified `symlinkJoin` backing sysroot) so custom
/// wrappers injecting flags cannot diverge from `rustc_driver` capture.
pub fn compiler_matches_pinned_sysroot_with_suffix(
    rustc_bin: &Path,
    exp_sr: &Path,
    exe_suffix: &str,
) -> Result<bool, String> {
    let rustc_exe = exe_name_for_suffix("rustc", exe_suffix);
    let canon_bin = fs::canonicalize(rustc_bin)
        .map_err(|e| format!("canonicalize compiler {}: {e}", rustc_bin.display()))?;
    let expected_rustc = exp_sr.join("bin").join(&rustc_exe);
    if expected_rustc.is_file() && fs::canonicalize(&expected_rustc).is_ok_and(|c| c == canon_bin) {
        return Ok(true);
    }
    if let Some(backing_sr) = resolve_verified_backing_sysroot_with_suffix(exp_sr, exe_suffix)? {
        let backing_rustc = backing_sr.join("bin").join(&rustc_exe);
        if backing_rustc.is_file() && fs::canonicalize(&backing_rustc).is_ok_and(|c| c == canon_bin)
        {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Platform-default wrapper around [`sysroots_equivalent_with_suffix`].
pub fn sysroots_equivalent(expected_sr: &Path, actual_sr: &Path) -> Result<bool, String> {
    sysroots_equivalent_with_suffix(expected_sr, actual_sr, env::consts::EXE_SUFFIX)
}

/// Format an executable stem with an explicit platform suffix (such as `""`
/// on Unix or `".exe"` on Windows).
pub fn exe_name_for_suffix(stem: &str, exe_suffix: &str) -> String {
    format!("{stem}{exe_suffix}")
}

/// Format an executable stem with [`std::env::consts::EXE_SUFFIX`].
pub fn exe_name(stem: &str) -> String {
    exe_name_for_suffix(stem, env::consts::EXE_SUFFIX)
}

/// Resolve an explicit executable path `path`, falling back to `<path><suffix>`
/// when `suffix` is non-empty and `path` has no extension (for example when a
/// Windows caller specifies `C:\toolchain\bin\rustc` without `.exe`).
pub fn resolve_candidate_exe_with_suffix(path: &Path, exe_suffix: &str) -> Option<PathBuf> {
    if path.is_file() {
        return Some(path.to_path_buf());
    }
    if !exe_suffix.is_empty() && path.extension().is_none() {
        let mut raw = path.as_os_str().to_os_string();
        raw.push(exe_suffix);
        let with_suffix = PathBuf::from(raw);
        if with_suffix.is_file() {
            return Some(with_suffix);
        }
    }
    None
}

/// Resolve an explicit executable path using [`std::env::consts::EXE_SUFFIX`].
pub fn resolve_candidate_exe(path: &Path) -> Option<PathBuf> {
    resolve_candidate_exe_with_suffix(path, env::consts::EXE_SUFFIX)
}

/// Return `true` when `name` is the `rustup` multicall proxy filename on Unix
/// (`rustup`) or Windows (`rustup.exe`).
pub fn is_rustup_executable_name(name: &std::ffi::OsStr) -> bool {
    name == "rustup" || name.to_str().is_some_and(|s| s.eq_ignore_ascii_case("rustup.exe"))
}

/// Return `true` when `path` canonicalizes to a `rustup` multicall proxy.
pub fn is_rustup_proxy_executable(path: &Path) -> bool {
    fs::canonicalize(path)
        .ok()
        .and_then(|canon| canon.file_name().map(is_rustup_executable_name))
        .unwrap_or(false)
}

fn infer_rustup_home_and_toolchain(sysroot: &Path) -> Option<(PathBuf, OsString)> {
    let mut candidates = Vec::new();
    if let Ok(canon) = fs::canonicalize(sysroot) {
        candidates.push(canon);
    }
    if let Ok(Some(backing)) =
        resolve_verified_backing_sysroot_with_suffix(sysroot, env::consts::EXE_SUFFIX)
        && !candidates.iter().any(|c| c == &backing)
    {
        candidates.push(backing);
    }
    if !candidates.iter().any(|c| c == sysroot) {
        candidates.push(sysroot.to_path_buf());
    }
    for cand in candidates {
        if let Some(toolchains_dir) = cand.parent()
            && toolchains_dir.file_name() == Some(std::ffi::OsStr::new("toolchains"))
            && let (Some(home), Some(tc)) = (toolchains_dir.parent(), cand.file_name())
            && !home.as_os_str().is_empty()
            && !tc.is_empty()
        {
            return Some((home.to_path_buf(), tc.to_os_string()));
        }
    }
    None
}

/// Resolve `(RUSTUP_HOME, RUSTUP_TOOLCHAIN)` selection state pinning `rustup`
/// proxy invocations to `rust_sysroot` (preferring `<rustup_home>/toolchains`
/// `<tc>` inferred from `rust_sysroot` before falling back to ambient
/// environment overrides).
pub fn resolve_rustup_env_for_sysroot_with_env(
    rust_sysroot: &Path,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> (Option<OsString>, Option<OsString>) {
    if let Some((home, tc)) = infer_rustup_home_and_toolchain(rust_sysroot) {
        return (Some(home.into_os_string()), Some(tc));
    }
    let rustup_home = get_env("RUSTUP_HOME").filter(|v| !v.is_empty()).or_else(|| {
        get_env("HOME")
            .filter(|v| !v.is_empty())
            .map(|h| PathBuf::from(h).join(".rustup"))
            .filter(|p| p.is_dir())
            .map(PathBuf::into_os_string)
    });
    let rustup_toolchain = get_env("RUSTUP_TOOLCHAIN").filter(|v| !v.is_empty());
    (rustup_home, rustup_toolchain)
}

/// Canonicalize `found`, pinning to `<sysroot>/bin/<stem><exe_suffix>` when
/// `found` is a `rustup` multicall proxy (`~/.cargo/bin/<stem> -> rustup`) and
/// `sysroot` bundles a concrete non-proxy binary, or otherwise preserving
/// `<canonical_parent>/<found_leaf>` so `argv[0]` dispatches as `<stem>` rather
/// than `rustup`.
pub fn canonicalize_preserving_rustup_proxy_with_suffix(
    found: &Path,
    sysroot: Option<&Path>,
    stem: &str,
    exe_suffix: &str,
) -> Result<PathBuf, String> {
    let canon =
        fs::canonicalize(found).map_err(|e| format!("canonicalize {}: {e}", found.display()))?;
    if canon.file_name().is_some_and(is_rustup_executable_name) {
        if let Some(sr) = sysroot {
            let direct = sr.join("bin").join(exe_name_for_suffix(stem, exe_suffix));
            if direct.is_file() {
                let direct_canon = fs::canonicalize(&direct)
                    .map_err(|e| format!("canonicalize {}: {e}", direct.display()))?;
                if !direct_canon.file_name().is_some_and(is_rustup_executable_name) {
                    return Ok(direct_canon);
                }
            }
        }
        if let (Some(parent), Some(leaf)) = (found.parent(), found.file_name())
            && !is_rustup_executable_name(leaf)
        {
            let canon_parent = fs::canonicalize(if parent.as_os_str().is_empty() {
                Path::new(".")
            } else {
                parent
            })
            .map_err(|e| format!("canonicalize parent of {}: {e}", found.display()))?;
            return Ok(canon_parent.join(leaf));
        }
    }
    Ok(canon)
}

/// Platform-default wrapper around
/// [`canonicalize_preserving_rustup_proxy_with_suffix`].
pub fn canonicalize_preserving_rustup_proxy(
    found: &Path,
    sysroot: Option<&Path>,
    stem: &str,
) -> Result<PathBuf, String> {
    canonicalize_preserving_rustup_proxy_with_suffix(found, sysroot, stem, env::consts::EXE_SUFFIX)
}

/// Resolve an explicit executable override `raw`, searching `path_var` when
/// `raw` is a bare command name without any path separator (such as
/// `RUSTC=rustc` or `ANNEAL_ITREE_RUSTC=rustc`) and checking filesystem paths
/// directly otherwise.
pub fn resolve_explicit_or_path_exe_with_suffix(
    raw: &std::ffi::OsStr,
    path_var: Option<&std::ffi::OsStr>,
    exe_suffix: &str,
) -> Option<PathBuf> {
    let raw_path = Path::new(raw);
    let raw_lossy = raw.to_string_lossy();
    let is_bare_name = !raw_lossy.contains('/')
        && !raw_lossy.contains('\\')
        && matches!(
            raw_path.components().collect::<Vec<_>>().as_slice(),
            [std::path::Component::Normal(_)]
        );
    if is_bare_name {
        if let Some(pv) = path_var {
            for dir in env::split_paths(pv) {
                if dir.as_os_str().is_empty() {
                    continue;
                }
                if let Some(found) =
                    resolve_candidate_exe_with_suffix(&dir.join(raw_path), exe_suffix)
                {
                    return Some(found);
                }
            }
        }
        None
    } else {
        resolve_candidate_exe_with_suffix(raw_path, exe_suffix)
    }
}

fn resolve_rustc_override_with_path_and_suffix(
    raw: &std::ffi::OsStr,
    path_var: Option<&std::ffi::OsStr>,
    exe_suffix: &str,
) -> Result<PathBuf, String> {
    let found = resolve_explicit_or_path_exe_with_suffix(raw, path_var, exe_suffix)
        .ok_or_else(|| format!("not an executable file: {}", Path::new(raw).display()))?;
    canonicalize_preserving_rustup_proxy_with_suffix(&found, None, "rustc", exe_suffix)
}

fn resolve_rustc_executable_path_with_suffix(
    path: &Path,
    exe_suffix: &str,
) -> Result<PathBuf, String> {
    let found = resolve_candidate_exe_with_suffix(path, exe_suffix)
        .ok_or_else(|| format!("not an executable file: {}", path.display()))?;
    canonicalize_preserving_rustup_proxy_with_suffix(&found, None, "rustc", exe_suffix)
}

/// When `rustc_bin` is a `rustup` multicall proxy
/// (`~/.cargo/bin/rustc -> rustup`), replace it with the concrete
/// `<sysroot>/bin/rustc` binary so supervised subprocess invocations (which
/// scrub `RUSTUP_TOOLCHAIN`) always execute the exact toolchain matching
/// `sysroot`.
fn pin_toolchain_rustc_if_rustup_proxy_with_suffix(
    rustc_bin: PathBuf,
    sysroot: &Path,
    exe_suffix: &str,
) -> Result<PathBuf, String> {
    canonicalize_preserving_rustup_proxy_with_suffix(&rustc_bin, Some(sysroot), "rustc", exe_suffix)
}

fn infer_sysroot_from_rustc(rustc_bin: &Path) -> Option<PathBuf> {
    let bin_dir = rustc_bin.parent()?;
    if bin_dir.file_name().and_then(|s| s.to_str()) != Some("bin") {
        return None;
    }
    let sr = bin_dir.parent()?;
    if sr.join("lib").is_dir() { Some(sr.to_path_buf()) } else { None }
}

/// Parse `rustc -vV` output for its `host: <triple>` line and verify that the
/// target architecture is a supported 64-bit little-endian target matching
/// `Anneal.MirTotal` (`mirTyBeqAt 64`).
pub fn parse_and_validate_host_target_triple(rustc_vv: &str) -> Result<String, String> {
    let raw_triple = rustc_vv
        .lines()
        .find_map(|l| l.strip_prefix("host:"))
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .ok_or_else(|| "missing `host:` triple in `rustc -vV` output".to_string())?;
    if raw_triple.chars().any(|c| c.is_whitespace() || c == '/' || c == '\\' || c.is_control()) {
        return Err(format!("invalid characters in `rustc -vV` host triple `{raw_triple}`"));
    }
    let arch = raw_triple.split('-').next().unwrap_or("");
    let is_supported_64bit_le = matches!(
        arch,
        "x86_64" | "aarch64" | "riscv64gc" | "riscv64imac" | "loongarch64" | "powerpc64le"
    );
    if !is_supported_64bit_le {
        return Err(format!(
            "unsupported host target `{raw_triple}`: Anneal.MirTotal ITree differential authority requires a 64-bit little-endian target"
        ));
    }
    Ok(raw_triple.to_string())
}

fn expected_native_os_for_suffix(exe_suffix: &str) -> &'static str {
    if exe_suffix.eq_ignore_ascii_case(".exe") && !cfg!(windows) {
        "windows"
    } else {
        env::consts::OS
    }
}

/// Extract Rust `std::env::consts::OS`-compatible OS identifier from a target
/// triple (`x86_64-unknown-linux-gnu` -> `"linux"`, `x86_64-pc-windows-msvc`
/// -> `"windows"`, `aarch64-apple-darwin` -> `"macos"`).
pub fn target_os_from_triple(target: &str) -> Option<&'static str> {
    let mut parts = target.split('-');
    let _arch = parts.next()?;
    let rest: Vec<&str> = parts.collect();
    if rest.is_empty() {
        return None;
    }
    if rest.iter().any(|p| *p == "android" || p.starts_with("android")) {
        return Some("android");
    }
    const OS_TOKENS: &[(&str, &str)] = &[
        ("darwin", "macos"),
        ("ios", "ios"),
        ("windows", "windows"),
        ("linux", "linux"),
        ("freebsd", "freebsd"),
        ("netbsd", "netbsd"),
        ("openbsd", "openbsd"),
        ("dragonfly", "dragonfly"),
        ("fuchsia", "fuchsia"),
        ("solaris", "solaris"),
        ("illumos", "illumos"),
        ("redox", "redox"),
        ("haiku", "haiku"),
    ];
    OS_TOKENS.iter().find_map(|&(token, os)| rest.contains(&token).then_some(os))
}

/// Verify that `target` matches both `native_arch` and `native_os` on a
/// 64-bit little-endian platform.
pub fn validate_host_target_matches_platform(
    target: &str,
    native_arch: &str,
    native_os: &str,
) -> Result<(), String> {
    if !cfg!(target_pointer_width = "64") || !cfg!(target_endian = "little") {
        return Err(
            "unsupported host platform: native execution requires a 64-bit little-endian host"
                .to_string(),
        );
    }
    let target_arch_norm = match target.split('-').next().unwrap_or("") {
        "riscv64gc" | "riscv64imac" => "riscv64",
        "powerpc64le" => "powerpc64",
        other => other,
    };
    if target_arch_norm != native_arch {
        return Err(format!(
            "toolchain target architecture mismatch: selected `rustc` host target `{target}` ({target_arch_norm}) cannot execute natively on `{native_arch}` host"
        ));
    }
    let Some(target_os) = target_os_from_triple(target) else {
        return Err(format!(
            "toolchain target OS mismatch: cannot confirm host target `{target}` executes natively on `{native_os}`"
        ));
    };
    if target_os != native_os {
        return Err(format!(
            "toolchain target OS mismatch: selected `rustc` host target `{target}` ({target_os}) cannot execute natively on `{native_os}` host"
        ));
    }
    Ok(())
}

/// Verify that `target` is runnable natively on the current host OS and CPU so
/// `RustcRunner` executes the exact target analyzed by Miri and capture.
pub fn validate_host_target_matches_native_arch(target: &str) -> Result<(), String> {
    validate_host_target_matches_platform(target, env::consts::ARCH, env::consts::OS)
}

/// Query `<rustc_bin> -vV` with a bounded timeout, parse its `host:` target
/// triple, and verify 64-bit little-endian compatibility and native parity.
pub fn query_rustc_host_target(rustc_bin: &Path, sysroot: Option<&Path>) -> Result<String, String> {
    query_rustc_host_target_with_timeout(rustc_bin, sysroot, DISCOVERY_PROBE_TIMEOUT_SECS)
}

fn query_rustc_host_target_for_platform(
    rustc_bin: &Path,
    sysroot: Option<&Path>,
    native_arch: &str,
    native_os: &str,
) -> Result<String, String> {
    query_rustc_host_target_for_platform_with_timeout(
        rustc_bin,
        sysroot,
        native_arch,
        native_os,
        DISCOVERY_PROBE_TIMEOUT_SECS,
    )
}

/// Timeout-parameterized variant of [`query_rustc_host_target`].
pub fn query_rustc_host_target_with_timeout(
    rustc_bin: &Path,
    sysroot: Option<&Path>,
    timeout_secs: u64,
) -> Result<String, String> {
    query_rustc_host_target_for_platform_with_timeout(
        rustc_bin,
        sysroot,
        env::consts::ARCH,
        env::consts::OS,
        timeout_secs,
    )
}

fn query_rustc_host_target_for_platform_with_timeout(
    rustc_bin: &Path,
    sysroot: Option<&Path>,
    native_arch: &str,
    native_os: &str,
    timeout_secs: u64,
) -> Result<String, String> {
    let dylib = sysroot
        .map(Path::to_path_buf)
        .or_else(|| infer_sysroot_from_rustc(rustc_bin))
        .map(|sr| sr.join("lib"))
        .filter(|lib_dir| lib_dir.is_dir())
        .map(|lib_dir| join_dylib_path(&lib_dir));
    let out = run_probe_supervised_with_timeout(
        rustc_bin,
        &["-vV"],
        dylib.as_deref(),
        true,
        timeout_secs,
    )
    .map_err(|e| format!("invoke `{} -vV`: {e}", rustc_bin.display()))?;
    if !out.status.success() {
        return Err(format!(
            "`{} -vV` failed ({}): {}",
            rustc_bin.display(),
            out.status,
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    let stdout = String::from_utf8(out.stdout)
        .map_err(|e| format!("invalid UTF-8 from `{} -vV`: {e}", rustc_bin.display()))?;
    let triple = parse_and_validate_host_target_triple(&stdout)?;
    validate_host_target_matches_platform(&triple, native_arch, native_os)?;
    Ok(triple)
}

/// Platform dynamic-library loader search-path variable matching
/// `anneal_testkit::Workspace::run_capture` (`DYLD_LIBRARY_PATH` on macOS,
/// `LD_LIBRARY_PATH` on other platforms).
#[cfg(target_os = "macos")]
pub const DYLIB_PATH_ENV_VAR: &str = "DYLD_LIBRARY_PATH";
/// Platform dynamic-library loader search-path variable matching
/// `anneal_testkit::Workspace::run_capture` (`DYLD_LIBRARY_PATH` on macOS,
/// `LD_LIBRARY_PATH` on other platforms).
#[cfg(not(target_os = "macos"))]
pub const DYLIB_PATH_ENV_VAR: &str = "LD_LIBRARY_PATH";

/// Prepend `primary` to any existing [`DYLIB_PATH_ENV_VAR`] entries using the
/// host platform's native path-list separator.
pub fn join_dylib_path(primary: &Path) -> OsString {
    join_dylib_path_with_existing(primary, env::var_os(DYLIB_PATH_ENV_VAR).as_deref())
}

/// Pure testable helper for [`join_dylib_path`].
pub fn join_dylib_path_with_existing(
    primary: &Path,
    existing: Option<&std::ffi::OsStr>,
) -> OsString {
    join_path_list_with_existing(primary, existing)
        .unwrap_or_else(|_| primary.as_os_str().to_os_string())
}

/// Prepend `primary_dir` to any existing `PATH` entries using the host
/// platform's native path-list separator so clean-environment subprocesses find
/// selected toolchain binaries and `<sysroot>/bin` `rustc_private` DLLs on
/// Windows ahead of ambient fallback directories.
pub fn build_child_path(primary_dir: &Path) -> Result<OsString, String> {
    join_path_list_with_existing(primary_dir, env::var_os("PATH").as_deref())
}

/// Pure testable helper for prepending `primary_dir` to an optional path-list
/// environment value.
pub fn join_path_list_with_existing(
    primary_dir: &Path,
    existing: Option<&std::ffi::OsStr>,
) -> Result<OsString, String> {
    let mut entries = vec![primary_dir.to_path_buf()];
    if let Some(ex) = existing.filter(|v| !v.is_empty()) {
        entries.extend(env::split_paths(ex));
    }
    env::join_paths(entries).map_err(|e| format!("join PATH: {e}"))
}

/// Platform temporary-directory environment variables checked across Unix and
/// Windows toolchains (`TMPDIR` on Unix; `TEMP`/`TMP` on Windows).
pub const PLATFORM_TEMP_ENV_KEYS: &[&str] = &["TMPDIR", "TEMP", "TMP"];

/// User profile and core OS directory variables required by native Windows and
/// Unix compilers, runtimes, Cargo, and Lean subprocesses under `env_clear()`.
pub const PLATFORM_PROFILE_ENV_KEYS: &[&str] =
    &["HOME", "USERPROFILE", "LOCALAPPDATA", "APPDATA", "SystemRoot", "WINDIR"];

/// Toolchain locator variables (`PATH`, `RUSTUP_HOME`, `CARGO_HOME`).
pub const STANDARD_TOOL_ENV_KEYS: &[&str] = &["PATH", "RUSTUP_HOME", "CARGO_HOME"];

/// Copy each non-empty environment variable in `keys` from `get_env` into
/// `inv` unless `inv.environment` already defines that key explicitly.
pub fn forward_env_keys_with_env(
    mut inv: Invocation,
    keys: &[&str],
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Invocation {
    for &key in keys {
        if !inv.environment.contains_key(OsStr::new(key))
            && let Some(val) = get_env(key).filter(|v| !v.is_empty())
        {
            inv = inv.env(key, val);
        }
    }
    inv
}

fn first_non_empty_temp_env(inv: &Invocation) -> Option<OsString> {
    PLATFORM_TEMP_ENV_KEYS
        .iter()
        .find_map(|key| inv.environment.get(OsStr::new(*key)).filter(|v| !v.is_empty()).cloned())
}

/// Ensure every variable in [`PLATFORM_TEMP_ENV_KEYS`] is populated cleanly on
/// `inv`, mirroring any already-set platform temp variable or assigning
/// `scratch_tmp` when all three (`TMPDIR`, `TEMP`, `TMP`) are absent.
pub fn ensure_invocation_temp_env(mut inv: Invocation, scratch_tmp: Option<&Path>) -> Invocation {
    let resolved = first_non_empty_temp_env(&inv)
        .or_else(|| scratch_tmp.map(|p| p.as_os_str().to_os_string()));
    if let Some(dir) = resolved {
        for &key in PLATFORM_TEMP_ENV_KEYS {
            if !inv.environment.get(OsStr::new(key)).is_some_and(|v| !v.is_empty()) {
                inv = inv.env(key, &dir);
            }
        }
    }
    inv
}

/// Write `contents` into `dest` atomically via a temporary file in `dest`'s
/// parent directory so crash/interruption never leaves a truncated stamp.
pub fn atomic_write_file(dest: &Path, contents: &[u8]) -> Result<(), String> {
    let parent = dest
        .parent()
        .ok_or_else(|| format!("destination path has no parent: {}", dest.display()))?;
    let mut tmp_file = tempfile::Builder::new()
        .prefix(".anneal-tmp-")
        .tempfile_in(parent)
        .map_err(|e| format!("create temp file in {}: {e}", parent.display()))?;
    tmp_file
        .write_all(contents)
        .and_then(|_| tmp_file.flush())
        .map_err(|e| format!("write temp file for {}: {e}", dest.display()))?;
    tmp_file.persist(dest).map_err(|e| format!("persist {}: {}", dest.display(), e.error))?;
    Ok(())
}

/// Preserve host temporary (`TMPDIR`, `TEMP`, `TMP`), user-profile, and core
/// Windows directory variables across `env_clear()`, assigning `fallback_temp`
/// when no temporary-directory variable is present.
pub fn forward_platform_temp_and_profile_env_with_env(
    inv: Invocation,
    fallback_temp: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Invocation {
    let inv = forward_env_keys_with_env(inv, PLATFORM_TEMP_ENV_KEYS, &get_env);
    let inv = forward_env_keys_with_env(inv, PLATFORM_PROFILE_ENV_KEYS, &get_env);
    ensure_invocation_temp_env(inv, fallback_temp)
}

/// Forward platform temporary/profile variables alongside standard toolchain
/// variables (`PATH`, `RUSTUP_HOME`, `CARGO_HOME`), skipping keys already set
/// explicitly on `inv`.
pub fn forward_standard_tool_env_with_env(
    inv: Invocation,
    fallback_temp: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Invocation {
    let inv = forward_platform_temp_and_profile_env_with_env(inv, fallback_temp, &get_env);
    forward_env_keys_with_env(inv, STANDARD_TOOL_ENV_KEYS, get_env)
}

/// Build the clean-environment `rustc` compilation [`Invocation`], preserving
/// platform temporary/profile/Windows OS variables and falling back to
/// `fallback_temp`.
#[allow(clippy::too_many_arguments)]
pub fn build_rustc_compile_invocation_with_env(
    rustc_bin: &Path,
    host_target: &str,
    opt_level: u8,
    src_path: &Path,
    bin_path: &Path,
    sysroot: Option<&Path>,
    child_path: Option<&OsStr>,
    fallback_temp: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Invocation {
    let mut compile_inv = Invocation::new(rustc_bin, &["--edition=2024"])
        .arg("--target")
        .arg(host_target)
        .arg("-C")
        .arg(format!("opt-level={opt_level}"))
        .arg("-C")
        .arg("overflow-checks=no")
        .arg("-C")
        .arg("debug-assertions=no")
        .arg("-o")
        .arg(bin_path)
        .arg(src_path);
    if let Some(sr) = sysroot {
        compile_inv = compile_inv.env(DYLIB_PATH_ENV_VAR, join_dylib_path(&sr.join("lib")));
    }
    if let Some(path) = child_path {
        compile_inv = compile_inv.env("PATH", path);
    }
    forward_platform_temp_and_profile_env_with_env(compile_inv, fallback_temp, get_env)
}

/// Build the clean-environment compiled-binary execution [`Invocation`],
/// preserving platform temporary/profile/Windows OS variables and falling back
/// to `fallback_temp`.
pub fn build_rustc_run_invocation_with_env(
    bin_path: &Path,
    sysroot: Option<&Path>,
    child_path: Option<&OsStr>,
    fallback_temp: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Invocation {
    let mut run_inv = Invocation::new(bin_path, &[]);
    if let Some(sr) = sysroot {
        run_inv = run_inv.env(DYLIB_PATH_ENV_VAR, join_dylib_path(&sr.join("lib")));
    }
    if let Some(path) = child_path {
        run_inv = run_inv.env("PATH", path);
    }
    forward_platform_temp_and_profile_env_with_env(run_inv, fallback_temp, get_env)
}

fn is_executable_file_busy_msg(msg: &str) -> bool {
    msg.contains("Text file busy") || msg.contains("ETXTBSY") || msg.contains("os error 26")
}

/// Execute `sup.run`, retrying transient Linux `ExecutableFileBusy` (`ETXTBSY`)
/// spawn errors caused when another test thread forks while a freshly written
/// mock executable fd is closing.
pub fn run_supervised_retrying_busy(
    sup: &ProcessSupervisor,
    inv: &Invocation,
    work_dir: &Path,
    log_dir: &Path,
    run_root: &Path,
) -> Result<ProcessOutcome, String> {
    for attempt in 0..20 {
        if attempt > 0 {
            let _ = fs::remove_dir_all(log_dir);
        }
        match sup.run(inv, work_dir, log_dir, run_root) {
            Err(e) if is_executable_file_busy_msg(&e) && attempt < 19 => {
                std::thread::sleep(Duration::from_millis(10));
            }
            Ok(out)
                if matches!(
                    &out.termination,
                    Termination::LaunchFailed(msg) if is_executable_file_busy_msg(msg)
                ) && attempt < 19 =>
            {
                std::thread::sleep(Duration::from_millis(10));
            }
            other => return other,
        }
    }
    unreachable!("attempt == 19 always returns in `other => return other`")
}

/// Supervise `inv` with a fresh temporary run/log root, automatically supplying
/// a writable child scratch temporary directory if `inv` has no `TMPDIR`,
/// `TEMP`, or `TMP` variable and retrying transient `ETXTBSY` launch failures.
pub fn run_supervised_with_prefix(
    prefix: &str,
    inv: &Invocation,
    work_dir: Option<&Path>,
    timeout_secs: u64,
) -> Result<ProcessOutcome, String> {
    let tmp = tempfile::Builder::new()
        .prefix(prefix)
        .tempdir()
        .map_err(|e| format!("create supervisor tempdir: {e}"))?;
    let canon_tmp = fs::canonicalize(tmp.path())
        .map_err(|e| format!("canonicalize supervisor tempdir: {e}"))?;
    let canon_work = match work_dir {
        Some(dir) => fs::canonicalize(dir).map_err(|e| format!("canonicalize work dir: {e}"))?,
        None => canon_tmp.clone(),
    };
    let effective_inv = if PLATFORM_TEMP_ENV_KEYS
        .iter()
        .all(|k| inv.environment.get(OsStr::new(*k)).is_some_and(|v| !v.is_empty()))
    {
        inv.clone()
    } else {
        let fallback = if first_non_empty_temp_env(inv).is_some() {
            None
        } else {
            let child_tmp = canon_tmp.join("tmp");
            fs::create_dir_all(&child_tmp)
                .map_err(|e| format!("create child scratch temp {}: {e}", child_tmp.display()))?;
            Some(child_tmp)
        };
        ensure_invocation_temp_env(inv.clone(), fallback.as_deref())
    };
    let sup = ProcessSupervisor::new(Duration::from_secs(timeout_secs))?;
    run_supervised_retrying_busy(
        &sup,
        &effective_inv,
        &canon_work,
        &canon_tmp.join("log"),
        &canon_tmp,
    )
}

fn run_supervised(
    inv: &Invocation,
    work_dir: &Path,
    timeout_secs: u64,
) -> Result<ProcessOutcome, String> {
    run_supervised_with_prefix("anneal-itree-sup-", inv, Some(work_dir), timeout_secs)
}
