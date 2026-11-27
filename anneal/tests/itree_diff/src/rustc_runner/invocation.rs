// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Child-process environment forwarding, dynamic-library and `PATH`
//! construction, and supervised `rustc` compile and run invocations.

use super::*;

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

pub(super) fn run_supervised(
    inv: &Invocation,
    work_dir: &Path,
    timeout_secs: u64,
) -> Result<ProcessOutcome, String> {
    run_supervised_with_prefix("anneal-itree-sup-", inv, Some(work_dir), timeout_secs)
}
