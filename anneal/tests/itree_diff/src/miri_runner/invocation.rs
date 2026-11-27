// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Offline `cargo miri setup` sysroot builds and clean-environment `miri`
//! child-process invocations.

use super::*;

#[derive(Serialize)]
struct ScratchCargoConfig {
    source: ScratchCargoSources,
}

#[derive(Serialize)]
struct ScratchCargoSources {
    #[serde(rename = "crates-io")]
    crates_io: ScratchCratesIoReplace,
    #[serde(rename = "vendored-sources")]
    vendored_sources: ScratchVendorDir,
}

#[derive(Serialize)]
struct ScratchCratesIoReplace {
    #[serde(rename = "replace-with")]
    replace_with: &'static str,
}

#[derive(Serialize)]
struct ScratchVendorDir {
    directory: String,
}

pub(super) fn build_offline_miri_sysroot(
    rust_sysroot: &Path,
    cargo_bin: &Path,
    miri_bin: &Path,
    target_triple: &str,
    target_dir: &Path,
) -> Result<(), String> {
    let rustc = fs::canonicalize(rust_sysroot.join("bin").join(exe_name("rustc")))
        .map_err(|e| format!("canonicalize rustc: {e}"))?;
    let vendor_dir = rust_sysroot.join("lib/rustlib/src/rust/library/vendor");
    if !vendor_dir.is_dir() {
        return Err(format!("missing vendored rust-src deps at {}", vendor_dir.display()));
    }
    let canon_vendor = fs::canonicalize(&vendor_dir)
        .map_err(|e| format!("canonicalize vendored rust-src: {e}"))?;

    let parent = target_dir
        .parent()
        .ok_or_else(|| format!("target dir has no parent: {}", target_dir.display()))?;
    let staging = tempfile::Builder::new()
        .prefix("itree-miri-staging-")
        .tempdir_in(parent)
        .map_err(|e| format!("create Miri staging dir: {e}"))?;
    let scratch_cargo_home = tempfile::Builder::new()
        .prefix("itree-miri-cargo-")
        .tempdir()
        .map_err(|e| format!("create Miri CARGO_HOME: {e}"))?;
    let scratch_home = tempfile::Builder::new()
        .prefix("itree-miri-home-")
        .tempdir()
        .map_err(|e| format!("create Miri HOME: {e}"))?;
    let cfg = ScratchCargoConfig {
        source: ScratchCargoSources {
            crates_io: ScratchCratesIoReplace { replace_with: "vendored-sources" },
            vendored_sources: ScratchVendorDir {
                directory: canon_vendor.to_string_lossy().into_owned(),
            },
        },
    };
    let toml_text = toml::to_string(&cfg).map_err(|e| format!("serialize Miri config: {e}"))?;
    fs::write(scratch_cargo_home.path().join("config.toml"), toml_text)
        .map_err(|e| format!("write offline Miri Cargo config: {e}"))?;

    let scratch_tmp = scratch_home.path().join("tmp");
    fs::create_dir_all(&scratch_tmp).map_err(|e| format!("create Miri scratch tmp: {e}"))?;
    let path_var = env::var_os("PATH");
    let setup_dirs =
        miri_setup_search_dirs(rust_sysroot, miri_bin, Some(cargo_bin), path_var.as_deref());
    let joined_path = env::join_paths(&setup_dirs).map_err(|e| format!("join Miri PATH: {e}"))?;
    let cargo_miri_bin = resolve_cargo_miri_binary_with_path_and_suffix(
        rust_sysroot,
        miri_bin,
        Some(cargo_bin),
        path_var.as_deref(),
        env::consts::EXE_SUFFIX,
    )
    .ok_or_else(|| {
        format!("cannot locate `cargo-miri` executable across setup search paths {:?}", setup_dirs)
    })?;

    let inv = build_miri_setup_invocation_with_env(
        rust_sysroot,
        &rustc,
        cargo_bin,
        miri_bin,
        &cargo_miri_bin,
        target_triple,
        staging.path(),
        scratch_home.path(),
        scratch_cargo_home.path(),
        &scratch_tmp,
        &joined_path,
        |k| env::var_os(k),
    )?;

    let out = run_supervised(&inv, scratch_home.path(), MIRI_SETUP_TIMEOUT_SECS)?;
    match out.termination {
        Termination::Exited(status) if status.success() => {}
        other => {
            return Err(format!(
                "`cargo miri setup` failed ({}):\nstdout:\n{}\nstderr:\n{}",
                other.describe(),
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
    }

    if target_dir.exists() {
        fs::remove_dir_all(target_dir)
            .map_err(|e| format!("clean stale {}: {e}", target_dir.display()))?;
    }
    let staged = staging.keep();
    fs::rename(&staged, target_dir).map_err(|e| {
        let _ = fs::remove_dir_all(&staged);
        format!("promote Miri sysroot: {e}")
    })?;
    Ok(())
}

/// Build the clean-environment direct `miri` execution [`Invocation`],
/// preserving host temporary/profile/Windows OS variables and falling back to
/// `fallback_temp` if no temp variable is set.
#[allow(clippy::too_many_arguments)]
pub fn build_miri_run_invocation_with_env(
    miri_bin: &Path,
    target_triple: &str,
    remap_arg: &str,
    miri_sysroot: &Path,
    harness_path: &Path,
    dylib_path: &OsStr,
    path_env: &OsStr,
    fallback_temp: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Invocation {
    let inv = Invocation::new(
        miri_bin,
        &["--edition=2024", "--error-format=json", "--target", target_triple],
    )
    .arg("--remap-path-prefix")
    .arg(remap_arg)
    .arg("--remap-path-scope=diagnostics")
    .arg("--sysroot")
    .arg(miri_sysroot)
    .arg("-C")
    .arg("opt-level=0")
    .arg("-C")
    .arg("debug-assertions=no")
    .arg("-C")
    .arg("overflow-checks=no")
    .arg("-Zmiri-tree-borrows")
    .arg("-Zmiri-backtrace=1")
    .arg(harness_path)
    .env(DYLIB_PATH_ENV_VAR, dylib_path)
    .env("PATH", path_env);
    forward_platform_temp_and_profile_env_with_env(inv, fallback_temp, get_env)
}

/// Build the clean-environment `cargo miri setup` invocation, preserving
/// resolved `RUSTUP_HOME` / `RUSTUP_TOOLCHAIN` state (or failing closed if a
/// `rustup` proxy toolchain cannot be pinned to `rust_sysroot`).
#[allow(clippy::too_many_arguments)]
pub fn build_miri_setup_invocation_with_env(
    rust_sysroot: &Path,
    rustc: &Path,
    cargo_bin: &Path,
    miri_bin: &Path,
    cargo_miri_bin: &Path,
    target_triple: &str,
    miri_sysroot_staging: &Path,
    scratch_home: &Path,
    scratch_cargo_home: &Path,
    scratch_tmp: &Path,
    joined_path: &std::ffi::OsStr,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Result<Invocation, String> {
    let mut inv = Invocation::new(cargo_miri_bin, &["miri", "setup", "--target", target_triple])
        .env("CARGO", cargo_bin)
        .env("PATH", joined_path)
        .env("HOME", scratch_home)
        .env("USERPROFILE", scratch_home)
        .env("CARGO_HOME", scratch_cargo_home)
        .env("TMPDIR", scratch_tmp)
        .env("TEMP", scratch_tmp)
        .env("TMP", scratch_tmp)
        .env("RUSTC", rustc)
        .env("MIRI", miri_bin)
        .env("MIRI_SYSROOT", miri_sysroot_staging)
        .env("CARGO_NET_OFFLINE", "true")
        .env(DYLIB_PATH_ENV_VAR, join_dylib_path(&rust_sysroot.join("lib")));
    inv = forward_env_keys_with_env(inv, &["SystemRoot", "WINDIR"], &get_env);

    if is_rustup_proxy_executable(cargo_miri_bin) || is_rustup_proxy_executable(cargo_bin) {
        let (rustup_home, rustup_toolchain) =
            resolve_rustup_env_for_sysroot_with_env(rust_sysroot, get_env);
        if let Some(rh) = rustup_home {
            inv = inv.env("RUSTUP_HOME", rh);
        }
        match rustup_toolchain {
            Some(rt) => {
                inv = inv.env("RUSTUP_TOOLCHAIN", rt);
            }
            None => {
                return Err(format!(
                    "cannot pin rustup-backed `cargo-miri` setup ({}) to selected sysroot {}: sysroot is not under `toolchains/` and RUSTUP_TOOLCHAIN is unset",
                    cargo_miri_bin.display(),
                    rust_sysroot.display(),
                ));
            }
        }
    }
    Ok(inv)
}

pub(super) fn run_supervised(
    inv: &Invocation,
    work_dir: &Path,
    timeout_secs: u64,
) -> Result<ProcessOutcome, String> {
    run_supervised_with_prefix("anneal-itree-miri-sup-", inv, Some(work_dir), timeout_secs)
}
