// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Supervised toolchain probes and `rustc`, sysroot, `rustup`, executable,
//! and host-target discovery and validation.

use super::*;

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

pub(super) fn resolve_rustc_override_with_path_and_suffix(
    raw: &std::ffi::OsStr,
    path_var: Option<&std::ffi::OsStr>,
    exe_suffix: &str,
) -> Result<PathBuf, String> {
    let found = resolve_explicit_or_path_exe_with_suffix(raw, path_var, exe_suffix)
        .ok_or_else(|| format!("not an executable file: {}", Path::new(raw).display()))?;
    canonicalize_preserving_rustup_proxy_with_suffix(&found, None, "rustc", exe_suffix)
}

pub(super) fn resolve_rustc_executable_path_with_suffix(
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
pub(super) fn pin_toolchain_rustc_if_rustup_proxy_with_suffix(
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

pub(super) fn expected_native_os_for_suffix(exe_suffix: &str) -> &'static str {
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

pub(super) fn query_rustc_host_target_for_platform(
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
