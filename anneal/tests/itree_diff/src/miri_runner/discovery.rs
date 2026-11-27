// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Miri, `cargo`, and sysroot coordinate discovery from explicit overrides,
//! the active toolchain, and `rustup`, rejecting toolchain skew.

use super::*;

/// Query `<miri_bin> --print sysroot` with a bounded timeout and return its
/// canonicalized compiler sysroot directory path so explicit Miri overrides
/// never silently pair with a skewed compiler or capture sysroot.
pub fn query_miri_sysroot(miri_bin: &Path) -> Result<PathBuf, String> {
    query_miri_sysroot_with_timeout(miri_bin, crate::rustc_runner::DISCOVERY_PROBE_TIMEOUT_SECS)
}

/// Timeout-parameterized variant of [`query_miri_sysroot`].
pub fn query_miri_sysroot_with_timeout(
    miri_bin: &Path,
    timeout_secs: u64,
) -> Result<PathBuf, String> {
    if !miri_bin.is_file() {
        return Err(format!("missing `miri` executable at {}", miri_bin.display()));
    }
    let dylib = miri_bin
        .parent()
        .and_then(Path::parent)
        .map(|p| p.join("lib"))
        .filter(|p| p.is_dir())
        .map(|lib_dir| join_dylib_path(&lib_dir));
    let out = run_probe_supervised_with_timeout(
        miri_bin,
        &["--print", "sysroot"],
        dylib.as_deref(),
        true,
        timeout_secs,
    )
    .map_err(|e| format!("invoke `{} --print sysroot`: {e}", miri_bin.display()))?;
    if !out.status.success() {
        return Err(format!(
            "`{} --print sysroot` failed ({}): {}",
            miri_bin.display(),
            out.status,
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    let stdout = String::from_utf8(out.stdout)
        .map_err(|e| format!("invalid UTF-8 from `{} --print sysroot`: {e}", miri_bin.display()))?;
    let trimmed = stdout.trim();
    if trimmed.is_empty() {
        return Err(format!("`{} --print sysroot` returned empty stdout", miri_bin.display()));
    }
    fs::canonicalize(trimmed).map_err(|e| {
        format!("canonicalize sysroot `{trimmed}` reported by `{}`: {e}", miri_bin.display())
    })
}

fn resolve_miri_override_with_path_and_suffix(
    raw: &std::ffi::OsStr,
    path_var: Option<&std::ffi::OsStr>,
    exe_suffix: &str,
) -> Result<PathBuf, String> {
    let found = resolve_explicit_or_path_exe_with_suffix(raw, path_var, exe_suffix)
        .ok_or_else(|| format!("not an executable file: {}", Path::new(raw).display()))?;
    canonicalize_preserving_rustup_proxy_with_suffix(&found, None, "miri", exe_suffix)
}

fn pin_toolchain_miri_if_rustup_proxy_with_suffix(
    miri_bin: PathBuf,
    sysroot: &Path,
    exe_suffix: &str,
) -> Result<PathBuf, String> {
    canonicalize_preserving_rustup_proxy_with_suffix(&miri_bin, Some(sysroot), "miri", exe_suffix)
}

/// Resolve `(label, rust_sysroot, miri_bin, cargo_bin)` from process
/// environment variables, rejecting explicit Miri toolchain skew against
/// `active_sysroot`.
pub fn resolve_miri_coordinates(
    active_sysroot: Option<&Path>,
) -> Result<(String, PathBuf, PathBuf, Option<PathBuf>), MiriProbeError> {
    resolve_miri_coordinates_with_env(active_sysroot, |k| env::var_os(k))
}

/// Deterministic environment-injected variant of [`resolve_miri_coordinates`]
/// for unit-testing all Miri discovery and toolchain-skew branches without
/// mutating process environment variables.
pub fn resolve_miri_coordinates_with_env(
    active_sysroot: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Result<(String, PathBuf, PathBuf, Option<PathBuf>), MiriProbeError> {
    resolve_miri_coordinates_with_env_and_suffix(active_sysroot, get_env, env::consts::EXE_SUFFIX)
}

/// Suffix-parameterized variant of [`resolve_miri_coordinates_with_env`] so
/// unit tests can verify Windows `.exe` executable discovery on Unix hosts.
pub fn resolve_miri_coordinates_with_env_and_suffix(
    active_sysroot: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
    exe_suffix: &str,
) -> Result<(String, PathBuf, PathBuf, Option<PathBuf>), MiriProbeError> {
    let miri_exe = exe_name_for_suffix("miri", exe_suffix);
    let canon_active = active_sysroot
        .map(|p| {
            fs::canonicalize(p).map_err(|e| {
                MiriProbeError::InvalidConfig(format!(
                    "canonicalize active sysroot {}: {e}",
                    p.display()
                ))
            })
        })
        .transpose()?;

    let raw_bin = get_env("ANNEAL_ITREE_MIRI_BIN").filter(|v| !v.is_empty());
    let raw_tc = match get_env("ANNEAL_ITREE_MIRI_TOOLCHAIN") {
        Some(v) => {
            let s = v.into_string().map_err(|_| {
                MiriProbeError::InvalidConfig(
                    "ANNEAL_ITREE_MIRI_TOOLCHAIN contains invalid UTF-8".to_string(),
                )
            })?;
            let trimmed = s.trim().to_string();
            if trimmed.is_empty() { None } else { Some(trimmed) }
        }
        None => None,
    };
    if raw_bin.is_some() && raw_tc.is_some() {
        return Err(MiriProbeError::InvalidConfig(
            "conflicting Miri configuration: both ANNEAL_ITREE_MIRI_BIN and ANNEAL_ITREE_MIRI_TOOLCHAIN are set".to_string(),
        ));
    }

    // 1. Explicit `ANNEAL_ITREE_MIRI_BIN` override.
    let path_var = get_env("PATH");
    if let Some(raw_bin) = raw_bin {
        let miri_exec =
            resolve_miri_override_with_path_and_suffix(&raw_bin, path_var.as_deref(), exe_suffix)
                .map_err(|e| {
                MiriProbeError::InvalidConfig(format!("canonicalize ANNEAL_ITREE_MIRI_BIN: {e}"))
            })?;
        let miri_sr = query_miri_sysroot(&miri_exec).map_err(MiriProbeError::InvalidConfig)?;
        if let Some(exp_sr) = &canon_active
            && !sysroots_equivalent_with_suffix(exp_sr, &miri_sr, exe_suffix)
                .map_err(MiriProbeError::InvalidConfig)?
        {
            return Err(MiriProbeError::InvalidConfig(format!(
                "Miri toolchain version skew: explicit ANNEAL_ITREE_MIRI_BIN ({}) resolves compiler sysroot {}, which differs from active sysroot {}",
                miri_exec.display(),
                miri_sr.display(),
                exp_sr.display()
            )));
        }
        let miri_bin =
            pin_toolchain_miri_if_rustup_proxy_with_suffix(miri_exec, &miri_sr, exe_suffix)
                .map_err(MiriProbeError::InvalidConfig)?;
        let cargo_bin =
            resolve_cargo_for_sysroot_with_env_and_suffix(&miri_sr, &get_env, exe_suffix)
                .map_err(MiriProbeError::InvalidConfig)?;
        return Ok(("explicit-miri-bin".to_string(), miri_sr, miri_bin, cargo_bin));
    }

    // 2. Explicit `ANNEAL_ITREE_MIRI_TOOLCHAIN` override via `rustup`.
    if let Some(tc) = raw_tc {
        let raw_sr = query_rustup_sysroot(&tc).map_err(MiriProbeError::InvalidConfig)?;
        let tc_sr = fs::canonicalize(&raw_sr).map_err(|e| {
            MiriProbeError::InvalidConfig(format!(
                "canonicalize `{tc}` sysroot {}: {e}",
                raw_sr.display()
            ))
        })?;
        let miri_cand = tc_sr.join("bin").join(&miri_exe);
        if !miri_cand.is_file() {
            return Err(MiriProbeError::InvalidConfig(format!(
                "ANNEAL_ITREE_MIRI_TOOLCHAIN `{tc}` lacks `bin/{miri_exe}` at {}",
                miri_cand.display()
            )));
        }
        let miri_bin = fs::canonicalize(&miri_cand)
            .map_err(|e| MiriProbeError::InvalidConfig(format!("canonicalize miri: {e}")))?;
        let miri_sr = query_miri_sysroot(&miri_bin).map_err(MiriProbeError::InvalidConfig)?;
        if !sysroots_equivalent_with_suffix(&tc_sr, &miri_sr, exe_suffix)
            .map_err(MiriProbeError::InvalidConfig)?
        {
            return Err(MiriProbeError::InvalidConfig(format!(
                "Miri toolchain version skew: ANNEAL_ITREE_MIRI_TOOLCHAIN `{tc}` miri ({}) resolves compiler sysroot {}, which differs from toolchain sysroot {}",
                miri_bin.display(),
                miri_sr.display(),
                tc_sr.display()
            )));
        }
        if let Some(exp_sr) = &canon_active
            && !sysroots_equivalent_with_suffix(exp_sr, &tc_sr, exe_suffix)
                .map_err(MiriProbeError::InvalidConfig)?
        {
            return Err(MiriProbeError::InvalidConfig(format!(
                "Miri toolchain version skew: explicit ANNEAL_ITREE_MIRI_TOOLCHAIN `{tc}` resolves compiler sysroot {}, which differs from active sysroot {}",
                tc_sr.display(),
                exp_sr.display()
            )));
        }
        let cargo_bin = resolve_cargo_for_sysroot_with_env_and_suffix(&tc_sr, &get_env, exe_suffix)
            .map_err(MiriProbeError::InvalidConfig)?;
        return Ok((tc, tc_sr, miri_bin, cargo_bin));
    }

    // 3. Explicit `ANNEAL_ITREE_MIRI_CARGO` override when provided (checked
    //    before falling back to `active_sysroot` so a skewed explicit
    //    `ANNEAL_ITREE_MIRI_CARGO` is not masked by `active_sysroot/bin/miri`).
    if let Some(raw_cargo) = get_env("ANNEAL_ITREE_MIRI_CARGO").filter(|v| !v.is_empty()) {
        let found_cargo =
            resolve_explicit_or_path_exe_with_suffix(&raw_cargo, path_var.as_deref(), exe_suffix)
                .unwrap_or_else(|| PathBuf::from(&raw_cargo));
        let cargo_bin = canonicalize_preserving_rustup_proxy_with_suffix(
            &found_cargo,
            canon_active.as_deref(),
            "cargo",
            exe_suffix,
        )
        .map_err(|e| {
            MiriProbeError::InvalidConfig(format!("canonicalize ANNEAL_ITREE_MIRI_CARGO: {e}"))
        })?;
        let is_proxy = fs::canonicalize(&cargo_bin)
            .ok()
            .and_then(|c| c.file_name().map(is_rustup_executable_name))
            .unwrap_or(false);
        let sr = if is_proxy && let Some(exp_sr) = &canon_active {
            exp_sr.clone()
        } else {
            let Some(raw_sr) = cargo_bin.parent().and_then(Path::parent) else {
                return Err(MiriProbeError::InvalidConfig(format!(
                    "cannot derive sysroot parent for ANNEAL_ITREE_MIRI_CARGO at {}",
                    cargo_bin.display()
                )));
            };
            fs::canonicalize(raw_sr).map_err(|e| {
                MiriProbeError::InvalidConfig(format!(
                    "canonicalize ANNEAL_ITREE_MIRI_CARGO sysroot {}: {e}",
                    raw_sr.display()
                ))
            })?
        };
        let miri_cand = sr.join("bin").join(&miri_exe);
        if !miri_cand.is_file() {
            return Err(MiriProbeError::InvalidConfig(format!(
                "ANNEAL_ITREE_MIRI_CARGO at {} has no sibling `bin/{miri_exe}`",
                cargo_bin.display()
            )));
        }
        let miri_bin = fs::canonicalize(&miri_cand)
            .map_err(|e| MiriProbeError::InvalidConfig(format!("canonicalize miri: {e}")))?;
        let miri_sr = query_miri_sysroot(&miri_bin).map_err(MiriProbeError::InvalidConfig)?;
        if !sysroots_equivalent_with_suffix(&sr, &miri_sr, exe_suffix)
            .map_err(MiriProbeError::InvalidConfig)?
        {
            return Err(MiriProbeError::InvalidConfig(format!(
                "Miri toolchain version skew: ANNEAL_ITREE_MIRI_CARGO sibling miri ({}) resolves compiler sysroot {}, which differs from cargo sysroot {}",
                miri_bin.display(),
                miri_sr.display(),
                sr.display()
            )));
        }
        if let Some(exp_sr) = &canon_active
            && !sysroots_equivalent_with_suffix(exp_sr, &miri_sr, exe_suffix)
                .map_err(MiriProbeError::InvalidConfig)?
        {
            return Err(MiriProbeError::InvalidConfig(format!(
                "Miri toolchain version skew: explicit ANNEAL_ITREE_MIRI_CARGO ({}) resolves compiler sysroot {}, which differs from active sysroot {}",
                cargo_bin.display(),
                miri_sr.display(),
                exp_sr.display()
            )));
        }
        return Ok(("explicit-miri-cargo".to_string(), sr, miri_bin, Some(cargo_bin)));
    }

    // 4. Active sysroot (`ANNEAL_SYSROOT` / `ANNEAL_TEST_INSTALL_ROOT/rust` /
    //    `ToolchainEnv.sysroot`) without explicit `ANNEAL_ITREE_MIRI_*`
    //    overrides — guarantees zero compiler skew with `rustc` and
    //    `anneal-rustc-capture` while allowing trimmed omnibus archives
    //    lacking `bin/miri` to run cleanly in `DegradedNoMiri` mode.
    if let Some(canon_sr) = &canon_active {
        let miri_cand = canon_sr.join("bin").join(&miri_exe);
        if miri_cand.is_file() {
            let miri_bin = fs::canonicalize(&miri_cand)
                .map_err(|e| MiriProbeError::InvalidConfig(format!("canonicalize miri: {e}")))?;
            let miri_sr = query_miri_sysroot(&miri_bin).map_err(MiriProbeError::InvalidConfig)?;
            if !sysroots_equivalent_with_suffix(canon_sr, &miri_sr, exe_suffix)
                .map_err(MiriProbeError::InvalidConfig)?
            {
                return Err(MiriProbeError::InvalidConfig(format!(
                    "Miri toolchain version skew: active sysroot `bin/{miri_exe}` ({}) resolves compiler sysroot {}, which differs from active sysroot {}",
                    miri_bin.display(),
                    miri_sr.display(),
                    canon_sr.display()
                )));
            }
            let cargo_bin =
                resolve_cargo_for_sysroot_with_env_and_suffix(canon_sr, &get_env, exe_suffix)
                    .map_err(MiriProbeError::InvalidConfig)?;
            return Ok(("active-sysroot".to_string(), canon_sr.clone(), miri_bin, cargo_bin));
        }
    }

    Err(MiriProbeError::Unavailable(match active_sysroot {
        Some(sr) => format!(
            "active sysroot {} does not bundle `bin/{miri_exe}` (set ANNEAL_ITREE_MIRI_BIN or ANNEAL_ITREE_MIRI_TOOLCHAIN to opt into a matching Miri toolchain)",
            sr.display()
        ),
        None => "no Miri binary found in active sysroot or environment overrides".to_string(),
    }))
}

fn resolve_cargo_for_sysroot_with_env_and_suffix(
    sysroot: &Path,
    get_env: &impl Fn(&str) -> Option<OsString>,
    exe_suffix: &str,
) -> Result<Option<PathBuf>, String> {
    if let Some(explicit) = get_env("ANNEAL_ITREE_MIRI_CARGO").filter(|v| !v.is_empty()) {
        let path_var = get_env("PATH");
        let found =
            resolve_explicit_or_path_exe_with_suffix(&explicit, path_var.as_deref(), exe_suffix)
                .unwrap_or_else(|| PathBuf::from(&explicit));
        let raw_canon = fs::canonicalize(&found)
            .map_err(|e| format!("canonicalize ANNEAL_ITREE_MIRI_CARGO: {e}"))?;
        if !raw_canon.is_file() {
            return Err(format!("ANNEAL_ITREE_MIRI_CARGO is not a file: {}", raw_canon.display()));
        }
        let is_proxy = raw_canon.file_name().is_some_and(is_rustup_executable_name);
        if !is_proxy
            && let Some(cargo_sr) =
                raw_canon.parent().and_then(Path::parent).filter(|p| p.join("lib/rustlib").is_dir())
        {
            let canon_cargo_sr = fs::canonicalize(cargo_sr)
                .map_err(|e| format!("canonicalize ANNEAL_ITREE_MIRI_CARGO sysroot: {e}"))?;
            if !sysroots_equivalent_with_suffix(sysroot, &canon_cargo_sr, exe_suffix)? {
                return Err(format!(
                    "Miri toolchain version skew: explicit ANNEAL_ITREE_MIRI_CARGO ({}) belongs to sysroot {}, which differs from Miri sysroot {}",
                    raw_canon.display(),
                    canon_cargo_sr.display(),
                    sysroot.display()
                ));
            }
        }
        let resolved = canonicalize_preserving_rustup_proxy_with_suffix(
            &found,
            Some(sysroot),
            "cargo",
            exe_suffix,
        )
        .map_err(|e| format!("resolve ANNEAL_ITREE_MIRI_CARGO: {e}"))?;
        return Ok(Some(resolved));
    }
    let cargo_exe = exe_name_for_suffix("cargo", exe_suffix);
    let bundled = sysroot.join("bin").join(&cargo_exe);
    if bundled.is_file() {
        return Ok(canonicalize_preserving_rustup_proxy_with_suffix(
            &bundled,
            Some(sysroot),
            "cargo",
            exe_suffix,
        )
        .ok());
    }
    if let Some(env_cargo) = get_env("CARGO").filter(|v| !v.is_empty()) {
        let p = PathBuf::from(&env_cargo);
        if let Some(found) = resolve_candidate_exe_with_suffix(&p, exe_suffix) {
            return Ok(canonicalize_preserving_rustup_proxy_with_suffix(
                &found,
                Some(sysroot),
                "cargo",
                exe_suffix,
            )
            .ok());
        }
        if p.components().count() == 1
            && let Some(path_var) = get_env("PATH")
        {
            let name_with_ext = if !exe_suffix.is_empty() && p.extension().is_none() {
                let mut raw = env_cargo;
                raw.push(exe_suffix);
                PathBuf::from(raw)
            } else {
                p
            };
            for dir in env::split_paths(&path_var) {
                let cand = dir.join(&name_with_ext);
                if cand.is_file() {
                    return Ok(canonicalize_preserving_rustup_proxy_with_suffix(
                        &cand,
                        Some(sysroot),
                        "cargo",
                        exe_suffix,
                    )
                    .ok());
                }
            }
        }
    }
    if let Some(path_var) = get_env("PATH") {
        for dir in env::split_paths(&path_var) {
            let cand = dir.join(&cargo_exe);
            if cand.is_file() {
                return Ok(canonicalize_preserving_rustup_proxy_with_suffix(
                    &cand,
                    Some(sysroot),
                    "cargo",
                    exe_suffix,
                )
                .ok());
            }
        }
    }
    Ok(None)
}

fn query_rustup_sysroot(toolchain: &str) -> Result<PathBuf, String> {
    let out = run_probe_supervised(
        Path::new("rustup"),
        &["run", toolchain, "rustc", "--print", "sysroot"],
        None,
        false,
    )
    .map_err(|e| format!("invoke rustup for `{toolchain}`: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "rustup toolchain `{toolchain}` unavailable: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    let text = String::from_utf8(out.stdout)
        .map_err(|e| format!("invalid UTF-8 from rustup sysroot: {e}"))?;
    fs::canonicalize(text.trim()).map_err(|e| format!("canonicalize `{toolchain}` sysroot: {e}"))
}

pub(super) fn run_version_cmd(
    bin: &Path,
    args: &[&str],
    dylib_search_path: &std::ffi::OsStr,
) -> Result<String, String> {
    if !bin.is_file() {
        return Err(format!("missing executable {}", bin.display()));
    }
    let out = run_probe_supervised(bin, args, Some(dylib_search_path), true)
        .map_err(|e| format!("run `{} {}`: {e}", bin.display(), args.join(" ")))?;
    if !out.status.success() {
        return Err(format!(
            "`{} {}` failed: {}",
            bin.display(),
            args.join(" "),
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}
