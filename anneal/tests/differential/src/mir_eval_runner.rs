// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Optional Leg 3 differential runner against `tools/anneal-mir-eval`.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    env,
    ffi::{OsStr, OsString},
    fs::{self, File},
    io::{self, Read as _, Seek as _, SeekFrom, Write as _},
    path::{Component, Path, PathBuf},
    sync::Arc,
    time::{Duration, Instant},
};

use anneal_testkit::{Invocation, ProcessSupervisor, Termination};
use serde::Deserialize;
use sha2::{Digest as _, Sha256};

use crate::{
    corpus::LitmusCase,
    lean_runner::{effective_timeout_duration, effective_timeout_secs},
    verdict::{IntKind, MirValue, ObservedOutcome, OrderingKind},
};

const MIR_EVAL_TIMEOUT_SECS: u64 = 120;
const MIR_EVAL_BUILD_TIMEOUT_SECS: u64 = 300;

fn segment_glob_matches(pat: &[char], text: &[char]) -> bool {
    if pat.is_empty() {
        return text.is_empty();
    }
    match pat[0] {
        '*' => {
            segment_glob_matches(&pat[1..], text)
                || (!text.is_empty() && segment_glob_matches(pat, &text[1..]))
        }
        '?' => !text.is_empty() && segment_glob_matches(&pat[1..], &text[1..]),
        '[' => {
            if text.is_empty() {
                return false;
            }
            let mut idx = 1usize;
            let negate = idx < pat.len() && (pat[idx] == '!' || pat[idx] == '^');
            if negate {
                idx += 1;
            }
            let mut matched = false;
            let ch = text[0];
            while idx < pat.len() && pat[idx] != ']' {
                if idx + 2 < pat.len() && pat[idx + 1] == '-' && pat[idx + 2] != ']' {
                    if ch >= pat[idx] && ch <= pat[idx + 2] {
                        matched = true;
                    }
                    idx += 3;
                } else {
                    if ch == pat[idx] {
                        matched = true;
                    }
                    idx += 1;
                }
            }
            if idx >= pat.len() || pat[idx] != ']' {
                return pat[0] == text[0] && segment_glob_matches(&pat[1..], &text[1..]);
            }
            let ok = if negate { !matched } else { matched };
            ok && segment_glob_matches(&pat[idx + 1..], &text[1..])
        }
        c => !text.is_empty() && c == text[0] && segment_glob_matches(&pat[1..], &text[1..]),
    }
}

fn path_components_glob_match(pat_segs: &[&str], rel_segs: &[String]) -> bool {
    if pat_segs.is_empty() {
        return rel_segs.is_empty();
    }
    if pat_segs[0] == "**" {
        return path_components_glob_match(&pat_segs[1..], rel_segs)
            || (!rel_segs.is_empty() && path_components_glob_match(pat_segs, &rel_segs[1..]));
    }
    if rel_segs.is_empty() {
        return false;
    }
    let pat_chars: Vec<char> = pat_segs[0].chars().collect();
    let txt_chars: Vec<char> = rel_segs[0].chars().collect();
    segment_glob_matches(&pat_chars, &txt_chars)
        && path_components_glob_match(&pat_segs[1..], &rel_segs[1..])
}

fn normalize_lexical_path(path: &Path) -> Option<PathBuf> {
    let mut out = PathBuf::new();
    for comp in path.components() {
        match comp {
            Component::Prefix(_) | Component::RootDir => out.push(comp.as_os_str()),
            Component::CurDir => {}
            Component::Normal(s) => out.push(s),
            Component::ParentDir => {
                if !out.pop() {
                    return None;
                }
            }
        }
    }
    Some(out)
}

fn workspace_pattern_matches_dir(ws_dir: &Path, pattern: &str, cand_dir: &Path) -> bool {
    let trimmed = pattern.trim();
    if trimmed.is_empty() {
        return false;
    }
    let has_glob = trimmed.contains(['*', '?', '[']);
    if !has_glob {
        if trimmed.contains('\0') || Path::new(trimmed).is_absolute() {
            return false;
        }
        let Some(norm_pat) = normalize_lexical_path(&ws_dir.join(trimmed)) else {
            return false;
        };
        return normalize_lexical_path(cand_dir).is_some_and(|norm_cand| norm_cand == norm_pat);
    }
    let Ok(rel) = cand_dir.strip_prefix(ws_dir) else {
        return false;
    };
    let rel_segs: Vec<String> = rel
        .components()
        .filter_map(|c| match c {
            std::path::Component::Normal(s) => Some(s.to_string_lossy().into_owned()),
            _ => None,
        })
        .collect();
    let pat_segs: Vec<&str> = trimmed.split('/').filter(|s| !s.is_empty() && *s != ".").collect();
    path_components_glob_match(&pat_segs, &rel_segs)
}

enum ManifestMatchContext<'a> {
    Staged {
        staging: &'a crate::rustc_runner::ImmutableStagingDir,
        rel_target: PathBuf,
        raw_toml: String,
    },
    Direct {
        ws_dir: &'a Path,
        target_manifest: &'a Path,
        raw_toml: Option<String>,
    },
}

fn manifest_matches_target_with_toml(
    cand_manifest: &Path,
    target_manifest: &Path,
    raw_toml: Option<&str>,
) -> bool {
    let Some(raw_toml) = raw_toml else {
        return cand_manifest == target_manifest;
    };
    let Ok(parsed) = raw_toml.parse::<toml::Table>() else {
        return cand_manifest == target_manifest;
    };
    let Some(workspace) = parsed.get("workspace").and_then(toml::Value::as_table) else {
        return cand_manifest == target_manifest;
    };
    let has_package = parsed.contains_key("package");
    let patterns = match workspace.get("default-members") {
        Some(val) => {
            let Some(arr) = val.as_array() else {
                return false;
            };
            arr
        }
        None if has_package => return cand_manifest == target_manifest,
        None => {
            let Some(arr) = workspace.get("members").and_then(toml::Value::as_array) else {
                return false;
            };
            arr
        }
    };
    let Some(ws_dir) = target_manifest.parent() else {
        return false;
    };
    let Some(cand_dir) = cand_manifest.parent() else {
        return false;
    };
    if let Some(excludes) = workspace.get("exclude").and_then(toml::Value::as_array) {
        for ex in excludes.iter().filter_map(toml::Value::as_str) {
            if cand_dir
                .ancestors()
                .take_while(|a| a.starts_with(ws_dir) || !ex.contains(['*', '?', '[']))
                .any(|anc| workspace_pattern_matches_dir(ws_dir, ex, anc))
            {
                return false;
            }
        }
    }
    patterns
        .iter()
        .filter_map(toml::Value::as_str)
        .any(|pat| workspace_pattern_matches_dir(ws_dir, pat, cand_dir))
}

#[cfg_attr(not(test), allow(dead_code))]
fn extract_built_executable(
    stdout_text: &str,
    bin_name: &str,
    canon_manifest: &Path,
) -> Result<PathBuf, String> {
    extract_built_executable_with_staging(stdout_text, bin_name, canon_manifest, None)
}

fn extract_built_executable_with_staging(
    stdout_text: &str,
    bin_name: &str,
    canon_manifest: &Path,
    src_staging: Option<&crate::rustc_runner::ImmutableStagingDir>,
) -> Result<PathBuf, String> {
    let ctx = if let Some(staging) = src_staging {
        let Some(rel_target) = staging.resolve_staged_rel(canon_manifest) else {
            return Err(format!(
                "--mir-eval-manifest is outside pinned staging root: {}",
                canon_manifest.display()
            ));
        };
        let mut f =
            staging.open_verified_rel_file(&rel_target, "--mir-eval-manifest Cargo.toml")?;
        let mut raw_toml = String::new();
        f.read_to_string(&mut raw_toml).map_err(|e| {
            format!("read staged --mir-eval-manifest {}: {e}", rel_target.display())
        })?;
        ManifestMatchContext::Staged { staging, rel_target, raw_toml }
    } else {
        let Some(ws_dir) = canon_manifest.parent() else {
            return Err(format!("--mir-eval-manifest has no parent: {}", canon_manifest.display()));
        };
        let raw_toml = fs::read_to_string(canon_manifest).ok();
        ManifestMatchContext::Direct { ws_dir, target_manifest: canon_manifest, raw_toml }
    };
    let mut found: Option<PathBuf> = None;
    for line in stdout_text.lines() {
        let Ok(val) = serde_json::from_str::<serde_json::Value>(line) else {
            continue;
        };
        if val.get("reason").and_then(|v| v.as_str()) != Some("compiler-artifact") {
            continue;
        }
        let Some(raw_msg_manifest) = val.get("manifest_path").and_then(|v| v.as_str()) else {
            continue;
        };
        let matched = match &ctx {
            ManifestMatchContext::Staged { staging, rel_target, raw_toml } => {
                let Some(rel_msg) = staging.resolve_staged_rel(Path::new(raw_msg_manifest)) else {
                    continue;
                };
                if staging
                    .open_verified_rel_file(&rel_msg, "compiler-artifact manifest_path")
                    .is_err()
                {
                    continue;
                }
                manifest_matches_target_with_toml(&rel_msg, rel_target, Some(raw_toml.as_str()))
            }
            ManifestMatchContext::Direct { ws_dir, target_manifest, raw_toml } => {
                let Ok(canon_msg) =
                    validate_manifest_path_no_links(Path::new(raw_msg_manifest), ws_dir)
                else {
                    continue;
                };
                manifest_matches_target_with_toml(&canon_msg, target_manifest, raw_toml.as_deref())
            }
        };
        if !matched {
            continue;
        }
        if val.pointer("/target/name").and_then(|v| v.as_str()) != Some(bin_name) {
            continue;
        }
        if !val
            .pointer("/target/kind")
            .and_then(|v| v.as_array())
            .is_some_and(|ks| ks.iter().any(|k| k.as_str() == Some("bin")))
        {
            continue;
        }
        if val.pointer("/profile/test").and_then(|v| v.as_bool()) == Some(true) {
            continue;
        }
        if let Some(exe) = val.get("executable").and_then(|v| v.as_str()).filter(|s| !s.is_empty())
        {
            let cand = PathBuf::from(exe);
            if let Some(prev) = &found
                && prev != &cand
            {
                return Err(format!(
                    "conflicting compiler-artifact executables for {bin_name}: {} vs {}",
                    prev.display(),
                    cand.display()
                ));
            }
            found = Some(cand);
        }
    }
    found.ok_or_else(|| {
        format!("cargo build JSON output lacked compiler-artifact executable for {bin_name}")
    })
}

pub(crate) fn validate_dir_path_no_symlinks(
    dir_path: &Path,
    caller_cwd: &Path,
) -> Result<PathBuf, String> {
    use std::path::Component;

    let joined =
        if dir_path.is_absolute() { dir_path.to_path_buf() } else { caller_cwd.join(dir_path) };
    let mut cur = PathBuf::new();
    for comp in joined.components() {
        match comp {
            Component::Prefix(p) => cur.push(p.as_os_str()),
            Component::RootDir => cur.push(comp.as_os_str()),
            Component::CurDir => {
                let meta = fs::symlink_metadata(&cur)
                    .map_err(|e| format!("stat workspace dir {}: {e}", cur.display()))?;
                if meta.file_type().is_symlink() || !meta.is_dir() {
                    return Err(format!("workspace dir must not be a symlink: {}", cur.display()));
                }
            }
            Component::ParentDir => {
                return Err(format!(
                    "workspace dir must not contain parent-directory traversal (`..`): {}",
                    dir_path.display()
                ));
            }
            Component::Normal(seg) => {
                cur.push(seg);
                let meta = fs::symlink_metadata(&cur)
                    .map_err(|e| format!("stat workspace dir {}: {e}", dir_path.display()))?;
                if meta.file_type().is_symlink() {
                    return Err(format!(
                        "workspace dir must not traverse a symlink: {}",
                        cur.display()
                    ));
                }
            }
        }
    }
    let final_meta = fs::symlink_metadata(&cur)
        .map_err(|e| format!("stat workspace dir {}: {e}", cur.display()))?;
    if final_meta.file_type().is_symlink() || !final_meta.is_dir() {
        return Err(format!("workspace dir is not a real directory: {}", cur.display()));
    }
    fs::canonicalize(&cur).map_err(|e| format!("canonicalize workspace dir: {e}"))
}

/// Validate every path component of `file_path` against `caller_cwd`,
/// rejecting symlinks on both leaf and intermediate/ancestor components before
/// returning the canonical regular-file path.
pub(crate) fn validate_file_path_no_symlinks(
    file_path: &Path,
    caller_cwd: &Path,
    label: &str,
) -> Result<PathBuf, String> {
    validate_file_path_no_symlinks_impl(file_path, caller_cwd, label, false)
}

pub(crate) fn validate_executable_no_links(
    file_path: &Path,
    caller_cwd: &Path,
    label: &str,
) -> Result<PathBuf, String> {
    validate_file_path_no_symlinks_impl(file_path, caller_cwd, label, true)
}

/// Validate a directory path that may not yet have its trailing directory
/// components created on disk, rejecting symlinks and non-directory files on
/// every existing ancestor or leaf component before returning an absolute path.
pub(crate) fn validate_dir_or_uncreated_path_no_symlinks(
    dir_path: &Path,
    caller_cwd: &Path,
    label: &str,
) -> Result<PathBuf, String> {
    use std::path::Component;

    let joined =
        if dir_path.is_absolute() { dir_path.to_path_buf() } else { caller_cwd.join(dir_path) };
    let mut existing = PathBuf::new();
    let mut tail: Vec<std::ffi::OsString> = Vec::new();
    for comp in joined.components() {
        if !tail.is_empty() {
            match comp {
                Component::CurDir => {}
                Component::Normal(seg) => tail.push(seg.to_os_string()),
                Component::ParentDir => {
                    return Err(format!(
                        "{label} parent traversal cannot cross non-existent directory: {}",
                        dir_path.display()
                    ));
                }
                Component::Prefix(_) | Component::RootDir => {
                    return Err(format!(
                        "{label} has invalid path structure: {}",
                        dir_path.display()
                    ));
                }
            }
            continue;
        }
        match comp {
            Component::Prefix(p) => existing.push(p.as_os_str()),
            Component::RootDir => existing.push(comp.as_os_str()),
            Component::CurDir => {
                let meta = fs::symlink_metadata(&existing)
                    .map_err(|e| format!("stat {label} {}: {e}", existing.display()))?;
                if meta.file_type().is_symlink() || !meta.is_dir() {
                    return Err(format!(
                        "{label} ancestor must be a real directory: {}",
                        existing.display()
                    ));
                }
            }
            Component::ParentDir => {
                return Err(format!(
                    "{label} must not contain parent-directory traversal (`..`): {}",
                    dir_path.display()
                ));
            }
            Component::Normal(seg) => {
                existing.push(seg);
                match fs::symlink_metadata(&existing) {
                    Ok(meta) => {
                        if meta.file_type().is_symlink() {
                            return Err(format!(
                                "{label} must not be or traverse a symlink: {}",
                                existing.display()
                            ));
                        }
                        if !meta.is_dir() {
                            return Err(format!(
                                "{label} component is not a directory: {}",
                                existing.display()
                            ));
                        }
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                        existing.pop();
                        tail.push(seg.to_os_string());
                    }
                    Err(e) => {
                        return Err(format!("stat {label} {}: {e}", existing.display()));
                    }
                }
            }
        }
    }
    let mut resolved = fs::canonicalize(&existing)
        .map_err(|e| format!("canonicalize {label} {}: {e}", existing.display()))?;
    for seg in tail {
        resolved.push(seg);
    }
    Ok(resolved)
}

fn validate_file_path_no_symlinks_impl(
    file_path: &Path,
    caller_cwd: &Path,
    label: &str,
    reject_hardlinks: bool,
) -> Result<PathBuf, String> {
    use std::path::Component;

    let joined =
        if file_path.is_absolute() { file_path.to_path_buf() } else { caller_cwd.join(file_path) };
    let mut cur = PathBuf::new();
    for comp in joined.components() {
        match comp {
            Component::Prefix(p) => cur.push(p.as_os_str()),
            Component::RootDir => cur.push(comp.as_os_str()),
            Component::CurDir => {
                let meta = fs::symlink_metadata(&cur)
                    .map_err(|e| format!("stat {label} ancestor {}: {e}", cur.display()))?;
                if meta.file_type().is_symlink() || !meta.is_dir() {
                    return Err(format!(
                        "{label} ancestor must be a non-symlink directory: {}",
                        cur.display()
                    ));
                }
            }
            Component::ParentDir => {
                return Err(format!(
                    "{label} must not contain parent-directory traversal (`..`): {}",
                    file_path.display()
                ));
            }
            Component::Normal(seg) => {
                cur.push(seg);
                let meta = fs::symlink_metadata(&cur)
                    .map_err(|e| format!("stat {label} {}: {e}", file_path.display()))?;
                if meta.file_type().is_symlink() {
                    return Err(format!(
                        "{label} must not be or traverse a symlink: {}",
                        cur.display()
                    ));
                }
            }
        }
    }
    let final_meta =
        fs::symlink_metadata(&cur).map_err(|e| format!("stat {label} {}: {e}", cur.display()))?;
    if final_meta.file_type().is_symlink() {
        return Err(format!("{label} must not be a symlink: {}", cur.display()));
    }
    if !final_meta.is_file() {
        return Err(format!("{label} is not a regular file: {}", cur.display()));
    }
    if reject_hardlinks {
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;

            if final_meta.nlink() > 1 {
                return Err(format!(
                    "{label} must not be a hardlink (nlink={}): {}",
                    final_meta.nlink(),
                    cur.display()
                ));
            }
        }
    }
    fs::canonicalize(&cur).map_err(|e| format!("canonicalize {label}: {e}"))
}

fn validate_manifest_path_no_links(
    manifest_path: &Path,
    caller_cwd: &Path,
) -> Result<PathBuf, String> {
    validate_executable_no_links(manifest_path, caller_cwd, "--mir-eval-manifest")
}

/// Validate `--mir-eval-bin` against the caller's working directory, rejecting
/// symlinked leaves, symlinked ancestor components, and hardlinks (`nlink > 1`)
/// before canonicalization.
pub fn validate_mir_eval_bin_no_links(bin_path: &Path) -> Result<PathBuf, String> {
    let caller_cwd =
        env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
    validate_executable_no_links(bin_path, &caller_cwd, "--mir-eval-bin")
}

/// Validate `--mir-eval-bin` against symlinks and hardlinks (`nlink > 1`) and
/// copy the opened binary into a private `0o555` `ImmutableStagingDir` so
/// post-validation mutations to the caller's directory cannot swap the
/// executed Leg-3 binary.
pub fn stage_mir_eval_bin_no_links(bin_path: &Path) -> Result<PreparedMirEval, String> {
    let caller_cwd =
        env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
    let validated_tmpdir = validate_optional_existing_dir_env(
        env::var_os("TMPDIR").as_deref(),
        &caller_cwd,
        "TMPDIR",
    )?;
    let (path, _sha, staging) = stage_verified_single_link_executable_from_path(
        bin_path,
        &caller_cwd,
        "anneal-mir-eval",
        validated_tmpdir.as_deref(),
        false,
    )?;
    Ok(PreparedMirEval::from_staged(path, staging))
}

#[derive(Debug)]
struct ResolvedToolExecutable {
    path: PathBuf,
    is_rustup_proxy: bool,
    opened: Option<crate::rustc_runner::OpenedExecutable>,
}

fn open_non_store_tool_executable(
    cand: &Path,
    caller_cwd: &Path,
    env_label: &str,
) -> Result<ResolvedToolExecutable, String> {
    let opened =
        crate::rustc_runner::open_verified_executable_via_dirfd(cand, caller_cwd, true, env_label)?;
    Ok(ResolvedToolExecutable {
        path: opened.canon_path.clone(),
        is_rustup_proxy: false,
        opened: Some(opened),
    })
}

fn resolve_named_tool_executable_with_store(
    env_label: &str,
    default_cmd: &str,
    raw_override: Option<&std::ffi::OsStr>,
    path_env: Option<&std::ffi::OsStr>,
    caller_cwd: &Path,
    required: bool,
    store_prefix: &Path,
) -> Result<Option<ResolvedToolExecutable>, String> {
    let explicit = raw_override.filter(|v| !v.is_empty());
    let bin_path = explicit.map(PathBuf::from).unwrap_or_else(|| PathBuf::from(default_cmd));
    let has_sep = bin_path.to_string_lossy().chars().any(std::path::is_separator);
    if bin_path.is_absolute() || has_sep {
        let abs = if bin_path.is_absolute() { bin_path } else { caller_cwd.join(bin_path) };
        if let Some(res) = crate::rustc_runner::try_validate_store_contained_executable(
            &abs,
            store_prefix,
            caller_cwd,
            env_label,
        ) {
            return Ok(Some(ResolvedToolExecutable {
                path: res?,
                is_rustup_proxy: false,
                opened: None,
            }));
        }
        return Ok(Some(open_non_store_tool_executable(&abs, caller_cwd, env_label)?));
    }
    let Some(path_var) = path_env else {
        return if required {
            Err(format!("cannot resolve {default_cmd} binary {:?} because PATH is unset", bin_path))
        } else {
            Ok(None)
        };
    };
    for dir in env::split_paths(path_var) {
        let base_dir = if dir.is_absolute() { dir } else { caller_cwd.join(dir) };
        let cand = base_dir.join(&bin_path);
        match fs::symlink_metadata(&cand) {
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
            Err(e) => {
                return Err(format!("stat {env_label} PATH candidate {}: {e}", cand.display()));
            }
            Ok(leaf_meta) => {
                if let Some(store_res) =
                    crate::rustc_runner::try_validate_store_contained_executable(
                        &cand,
                        store_prefix,
                        caller_cwd,
                        env_label,
                    )
                {
                    return Ok(Some(ResolvedToolExecutable {
                        path: store_res?,
                        is_rustup_proxy: false,
                        opened: None,
                    }));
                }
                let clean_dir = validate_dir_path_no_symlinks(&base_dir, caller_cwd)
                    .map_err(|e| format!("{env_label} PATH entry invalid ({e})"))?;
                if !leaf_meta.file_type().is_symlink() {
                    return Ok(Some(open_non_store_tool_executable(&cand, caller_cwd, env_label)?));
                }
                // Standard `rustup` installs symlink `cargo`/`rustc` to
                // `rustup` and dispatch on `argv[0]`. Permit only when the
                // env var is unset and the sibling `rustup` binary is a
                // non-hardlinked regular file in the same non-symlink dir.
                if explicit.is_none()
                    && bin_path == Path::new(default_cmd)
                    && fs::read_link(&cand).ok().as_deref() == Some(Path::new("rustup"))
                {
                    let rustup_exe = clean_dir.join(format!("rustup{}", env::consts::EXE_SUFFIX));
                    let opened_rustup = crate::rustc_runner::open_verified_executable_via_dirfd(
                        &rustup_exe,
                        caller_cwd,
                        true,
                        &format!("{env_label} rustup proxy"),
                    )?;
                    return Ok(Some(ResolvedToolExecutable {
                        path: clean_dir.join(default_cmd),
                        is_rustup_proxy: true,
                        opened: Some(opened_rustup),
                    }));
                }
                return Err(format!("{env_label} must not be a symlink: {}", cand.display()));
            }
        }
    }
    if required || explicit.is_some() {
        return Err(format!(
            "cannot resolve {default_cmd} binary {:?} in PATH for --mir-eval-manifest",
            bin_path
        ));
    }
    Ok(None)
}

/// Validate `CARGO` (default `"cargo"`) against `caller_cwd` or `PATH`,
/// validating every directory and file component against symlinks and hardlinks
/// before constructing the build invocation (permitting only an unmodified
/// same-dir `rustup` sibling proxy when `CARGO` is unset on a `rustup`
/// toolchain).
fn resolve_cargo_executable_with_store(
    raw_cargo: Option<&std::ffi::OsStr>,
    path_env: Option<&std::ffi::OsStr>,
    caller_cwd: &Path,
    store_prefix: &Path,
) -> Result<ResolvedToolExecutable, String> {
    resolve_named_tool_executable_with_store(
        "CARGO",
        "cargo",
        raw_cargo,
        path_env,
        caller_cwd,
        true,
        store_prefix,
    )?
    .ok_or_else(|| "cannot resolve cargo binary".to_owned())
}

#[cfg_attr(not(test), allow(dead_code))]
fn resolve_cargo_executable(
    raw_cargo: Option<&std::ffi::OsStr>,
    path_env: Option<&std::ffi::OsStr>,
    caller_cwd: &Path,
) -> Result<PathBuf, String> {
    resolve_cargo_executable_with_store(
        raw_cargo,
        path_env,
        caller_cwd,
        Path::new(crate::rustc_runner::STORE_PREFIX),
    )
    .map(|r| r.path)
}

fn is_rustup_proxy_symlink(path: &Path) -> bool {
    fs::symlink_metadata(path).is_ok_and(|m| m.file_type().is_symlink())
        && fs::read_link(path).ok().as_deref() == Some(Path::new("rustup"))
}

pub(crate) fn build_temp_dir(
    prefix: &str,
    tmpdir: Option<&Path>,
) -> Result<tempfile::TempDir, String> {
    let mut builder = tempfile::Builder::new();
    builder.prefix(prefix);
    match tmpdir {
        Some(dir) => builder.tempdir_in(dir),
        None => builder.tempdir(),
    }
    .map_err(|e| format!("create temp dir ({prefix}): {e}"))
}

#[cfg(unix)]
fn read_rustup_settings_bytes_via_dirfd(
    rustup_dir: &Path,
    label: &str,
) -> Result<Option<Vec<u8>>, String> {
    use std::os::fd::{AsFd as _, AsRawFd as _};

    match fs::symlink_metadata(rustup_dir) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(format!("stat {label} {}: {e}", rustup_dir.display())),
        Ok(_) => {}
    }
    let dir_fd = crate::rustc_runner::open_dir_handle_no_symlinks(rustup_dir, None, label)?;
    let mut st = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: `dir_fd` is open and `c"settings.toml"` is NUL-terminated.
    if unsafe {
        libc::fstatat(
            dir_fd.as_raw_fd(),
            c"settings.toml".as_ptr(),
            st.as_mut_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    } != 0
    {
        let err = io::Error::last_os_error();
        if err.kind() == io::ErrorKind::NotFound {
            return Ok(None);
        }
        return Err(format!("stat {label}/settings.toml: {err}"));
    }
    let (mut file, _st) = crate::rustc_runner::open_regular_file_from_fd(
        dir_fd.as_fd(),
        c"settings.toml",
        None,
        false,
        &format!("{label}/settings.toml"),
    )?;
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes).map_err(|e| format!("read {label}/settings.toml: {e}"))?;
    Ok(Some(bytes))
}

#[cfg(not(unix))]
fn read_rustup_settings_bytes_via_dirfd(
    rustup_dir: &Path,
    label: &str,
) -> Result<Option<Vec<u8>>, String> {
    let settings = rustup_dir.join("settings.toml");
    match fs::symlink_metadata(&settings) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(format!("stat {label}/settings.toml {}: {e}", settings.display())),
        Ok(_) => {
            validate_executable_no_links(&settings, rustup_dir, &format!("{label}/settings.toml"))?;
            fs::read(&settings)
                .map(Some)
                .map_err(|e| format!("read {label}/settings.toml {}: {e}", settings.display()))
        }
    }
}

fn derive_toolchain_from_rustup_settings(
    bytes: &[u8],
    orig_work_dir: &Path,
    label: &str,
) -> Result<Option<String>, String> {
    let text = std::str::from_utf8(bytes)
        .map_err(|e| format!("{label}/settings.toml is not valid UTF-8: {e}"))?;
    let parsed: toml::Table =
        text.parse().map_err(|e| format!("parse {label}/settings.toml: {e}"))?;
    let mut derived: Option<String> = None;
    if let Some(overrides) = parsed.get("overrides").and_then(toml::Value::as_table) {
        for anc in orig_work_dir.ancestors() {
            if let Some(val) = overrides.iter().find_map(|(k, v)| {
                let kp = Path::new(k);
                let matched = kp == anc
                    || validate_dir_path_no_symlinks(kp, orig_work_dir).ok().as_deref()
                        == Some(anc);
                matched.then_some(v)
            }) {
                let tc_str = val.as_str().ok_or_else(|| {
                    format!("{label}/settings.toml [overrides] value must be a string")
                })?;
                derived = Some(tc_str.to_owned());
                break;
            }
        }
    }
    if derived.is_none()
        && let Some(def_val) = parsed.get("default_toolchain")
    {
        let tc_str = def_val
            .as_str()
            .ok_or_else(|| format!("{label}/settings.toml default_toolchain must be a string"))?;
        derived = Some(tc_str.to_owned());
    }
    if let Some(ref tc) = derived {
        let _ = validate_rustup_toolchain(Some(OsStr::new(tc)))?;
    }
    Ok(derived)
}

#[derive(Debug)]
struct PinnedRustupSettings {
    effective_rustup_home: Option<PathBuf>,
    effective_toolchain: Option<OsString>,
    _pin_staging: Option<Arc<crate::rustc_runner::ImmutableStagingDir>>,
}

fn pin_rustup_settings(
    validated_rustup_home: Option<&Path>,
    validated_home: Option<&Path>,
    rustup_toolchain_env: Option<&OsStr>,
    orig_work_dir: &Path,
    validated_tmpdir: Option<&Path>,
) -> Result<PinnedRustupSettings, String> {
    let explicit_tc = validate_rustup_toolchain(rustup_toolchain_env)?;
    let (settings_dir, label, explicit_rh) = if let Some(rh) = validated_rustup_home {
        (Some(rh.to_path_buf()), "RUSTUP_HOME", Some(rh.to_path_buf()))
    } else if let Some(h) = validated_home {
        let dot_rustup = h.join(".rustup");
        validate_dir_ancestors_no_symlinks(&dot_rustup, "HOME/.rustup")?;
        (Some(dot_rustup), "HOME/.rustup", None)
    } else {
        (None, "", None)
    };
    let settings_bytes = match settings_dir.as_deref() {
        Some(dir) => read_rustup_settings_bytes_via_dirfd(dir, label)?,
        None => None,
    };
    if let Some(rt) = explicit_tc {
        return Ok(PinnedRustupSettings {
            effective_rustup_home: explicit_rh,
            effective_toolchain: Some(rt.to_os_string()),
            _pin_staging: None,
        });
    }
    if let Some(bytes) = settings_bytes.as_deref()
        && let Some(derived_tc) =
            derive_toolchain_from_rustup_settings(bytes, orig_work_dir, label)?
    {
        return Ok(PinnedRustupSettings {
            effective_rustup_home: explicit_rh,
            effective_toolchain: Some(OsString::from(derived_tc)),
            _pin_staging: None,
        });
    }
    // No explicit or configured default/override toolchain: pin a private
    // immutable `settings.toml`-only `RUSTUP_HOME` so concurrent edits on disk
    // cannot hijack proxy selection between validation and `rustup which`.
    let temp_rh = build_temp_dir("anneal-rustup-home-", validated_tmpdir)?;
    let (_, staging) = crate::rustc_runner::ImmutableStagingDir::build_and_pin(
        temp_rh,
        "rustup settings",
        |_, pinned_root| {
            if let Some(bytes) = settings_bytes.as_deref() {
                let dst = pinned_root.join("settings.toml");
                let mut f =
                    fs::OpenOptions::new().write(true).create_new(true).open(&dst).map_err(
                        |e| format!("create pinned rustup settings {}: {e}", dst.display()),
                    )?;
                f.write_all(bytes)
                    .map_err(|e| format!("write pinned rustup settings {}: {e}", dst.display()))?;
                f.flush()
                    .map_err(|e| format!("flush pinned rustup settings {}: {e}", dst.display()))?;
                #[cfg(unix)]
                {
                    use std::os::unix::fs::PermissionsExt as _;
                    f.set_permissions(fs::Permissions::from_mode(0o444)).map_err(|e| {
                        format!("chmod pinned rustup settings {}: {e}", dst.display())
                    })?;
                }
            }
            Ok(())
        },
    )?;
    let pinned_rh = staging.pin_path(Path::new(""));
    Ok(PinnedRustupSettings {
        effective_rustup_home: Some(pinned_rh),
        effective_toolchain: None,
        _pin_staging: Some(staging),
    })
}

fn validate_rustup_toolchain(raw: Option<&OsStr>) -> Result<Option<&OsStr>, String> {
    let Some(val) = raw.filter(|v| !v.is_empty()) else {
        return Ok(None);
    };
    let s = val
        .to_str()
        .ok_or_else(|| "unsafe RUSTUP_TOOLCHAIN value: must be valid UTF-8".to_owned())?;
    if s.contains('\0') || s.contains('/') || s.contains('\\') || s.contains("..") {
        return Err(format!("unsafe RUSTUP_TOOLCHAIN value: {s:?}"));
    }
    Ok(Some(val))
}

#[allow(clippy::too_many_arguments)]
fn resolve_rustup_proxy_binary_opened_with_store(
    proxy_cmd: &Path,
    preopened_rustup: Option<&mut crate::rustc_runner::OpenedExecutable>,
    tool_name: &str,
    caller_cwd: &Path,
    probe_work_dir: &Path,
    validated_home: Option<&Path>,
    pinned_rustup: &PinnedRustupSettings,
    validated_tmpdir: Option<&Path>,
    store_prefix: &Path,
) -> Result<ResolvedToolExecutable, String> {
    let proxy_dir = proxy_cmd
        .parent()
        .ok_or_else(|| format!("rustup proxy has no parent dir: {}", proxy_cmd.display()))?;
    let rustup_dir = validate_dir_path_no_symlinks(proxy_dir, caller_cwd)
        .map_err(|e| format!("{tool_name} rustup proxy dir invalid: {e}"))?;
    let rustup_exe = rustup_dir.join(format!("rustup{}", env::consts::EXE_SUFFIX));
    let rustup_label = format!("{tool_name} rustup proxy");
    let (staged_rustup, rustup_staging) = if let Some(opened) = preopened_rustup {
        crate::rustc_runner::stage_immutable_opened_executable(
            opened,
            validated_tmpdir,
            &rustup_label,
        )?
    } else {
        crate::rustc_runner::stage_immutable_named_executable(
            &rustup_exe,
            store_prefix,
            caller_cwd,
            validated_tmpdir,
            &rustup_label,
        )?
    };
    let pinned_rustup_bin = crate::rustc_runner::ImmutableStagingDir::pin_path_with_guards(
        &[rustup_staging.as_ref()],
        &staged_rustup,
    );
    let staged_dir = pinned_rustup_bin.parent().unwrap_or(rustup_dir.as_path());
    let mut inv =
        Invocation::new(&pinned_rustup_bin, &["which", tool_name]).env("PATH", staged_dir);
    if let Some(h) = validated_home {
        inv = inv.env("HOME", h);
    }
    if let Some(rh) = &pinned_rustup.effective_rustup_home {
        inv = inv.env("RUSTUP_HOME", rh);
    }
    if let Some(rt) = &pinned_rustup.effective_toolchain {
        inv = inv.env("RUSTUP_TOOLCHAIN", rt);
    }
    if let Some(td) = validated_tmpdir {
        inv = inv.env("TMPDIR", td);
    }
    let tmp_dir = build_temp_dir("anneal-rustup-probe-", validated_tmpdir)?;
    let log_root = fs::canonicalize(tmp_dir.path())
        .map_err(|e| format!("canonicalize rustup probe dir: {e}"))?;
    let supervisor =
        ProcessSupervisor::new(Duration::from_secs(crate::rustc_runner::RUSTC_PROBE_TIMEOUT_SECS))?;
    let out = supervisor.run(&inv, probe_work_dir, &log_root.join("log"), &log_root)?;
    let raw_resolved = match out.termination {
        Termination::Exited(s) if s.success() => String::from_utf8(out.stdout)
            .map_err(|e| format!("invalid UTF-8 from `rustup which {tool_name}`: {e}"))?,
        other => {
            return Err(format!(
                "rustup proxy resolution failed for `{tool_name}` ({}): {}",
                other.describe(),
                String::from_utf8_lossy(&out.stderr).trim()
            ));
        }
    };
    let line = raw_resolved.lines().map(str::trim).find(|l| !l.is_empty()).ok_or_else(|| {
        format!("`{} which {tool_name}` returned empty output", rustup_exe.display())
    })?;
    let cand_path = Path::new(line);
    if !cand_path.is_absolute()
        || cand_path.components().any(|c| matches!(c, std::path::Component::ParentDir))
    {
        return Err(format!("rustup proxy returned unsafe `{tool_name}` path: {line}"));
    }
    if is_rustup_proxy_symlink(cand_path) {
        return Err(format!(
            "resolved rustup `{tool_name}` must not chain back to proxy: {}",
            cand_path.display()
        ));
    }
    if let Some(res) = crate::rustc_runner::try_validate_store_contained_executable(
        cand_path,
        store_prefix,
        probe_work_dir,
        &format!("resolved rustup {tool_name}"),
    ) {
        let resolved = res?;
        if is_rustup_proxy_symlink(&resolved) {
            return Err(format!(
                "resolved rustup `{tool_name}` must not chain back to proxy: {}",
                resolved.display()
            ));
        }
        return Ok(ResolvedToolExecutable { path: resolved, is_rustup_proxy: false, opened: None });
    }
    let opened = crate::rustc_runner::open_verified_executable_via_dirfd(
        cand_path,
        probe_work_dir,
        true,
        &format!("resolved rustup {tool_name}"),
    )?;
    if is_rustup_proxy_symlink(&opened.canon_path) {
        return Err(format!(
            "resolved rustup `{tool_name}` must not chain back to proxy: {}",
            opened.canon_path.display()
        ));
    }
    Ok(ResolvedToolExecutable {
        path: opened.canon_path.clone(),
        is_rustup_proxy: false,
        opened: Some(opened),
    })
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
fn resolve_rustup_proxy_binary_with_store(
    proxy_cmd: &Path,
    tool_name: &str,
    caller_cwd: &Path,
    work_dir: &Path,
    validated_home: Option<&Path>,
    validated_rustup_home: Option<&Path>,
    rustup_toolchain: Option<&OsStr>,
    validated_tmpdir: Option<&Path>,
    store_prefix: &Path,
) -> Result<PathBuf, String> {
    let pinned_settings = pin_rustup_settings(
        validated_rustup_home,
        validated_home,
        rustup_toolchain,
        work_dir,
        validated_tmpdir,
    )?;
    resolve_rustup_proxy_binary_opened_with_store(
        proxy_cmd,
        None,
        tool_name,
        caller_cwd,
        work_dir,
        validated_home,
        &pinned_settings,
        validated_tmpdir,
        store_prefix,
    )
    .map(|r| r.path)
}

fn resolve_rustc_executable_with_store(
    raw_rustc: Option<&std::ffi::OsStr>,
    path_env: Option<&std::ffi::OsStr>,
    caller_cwd: &Path,
    store_prefix: &Path,
) -> Result<ResolvedToolExecutable, String> {
    resolve_named_tool_executable_with_store(
        "RUSTC",
        "rustc",
        raw_rustc,
        path_env,
        caller_cwd,
        true,
        store_prefix,
    )?
    .ok_or_else(|| "cannot resolve rustc binary".to_owned())
}

#[derive(Clone, Debug)]
struct LockedRegistryCrate {
    name: String,
    version: String,
    checksum: Option<String>,
}

struct PinnedCargoHome {
    cargo_home: PathBuf,
    _staging: Arc<crate::rustc_runner::ImmutableStagingDir>,
}

enum CargoSourceDir {
    Store(PathBuf),
    Host(PathBuf),
}

fn validate_safe_toml_str(val: &str, label: &str) -> Result<(), String> {
    if val.is_empty() || val.contains('\0') || val.contains('\n') || val.contains('\r') {
        return Err(format!("{label} contains empty or unsafe control characters: {val:?}"));
    }
    Ok(())
}

fn resolve_cargo_source_directory(
    raw_dir: &str,
    cargo_home: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
    cfg_display: &Path,
    src_name: &str,
) -> Result<CargoSourceDir, String> {
    validate_safe_toml_str(
        raw_dir,
        &format!("CARGO_HOME config {} [source.{src_name}].directory", cfg_display.display()),
    )?;
    let dir_path = Path::new(raw_dir);
    let label = "CARGO_HOME [source] directory";
    // Cargo resolves relative `[source.<name>].directory` in
    // `$CARGO_HOME/config{,.toml}` against `CARGO_HOME`'s parent directory.
    let joined = if dir_path.is_absolute() {
        dir_path.to_path_buf()
    } else {
        if dir_path.components().any(|c| matches!(c, Component::ParentDir)) {
            return Err(format!(
                "CARGO_HOME config {} [source.{src_name}].directory invalid: \
                 must not contain `..`: {raw_dir}",
                cfg_display.display()
            ));
        }
        let rel_base =
            cargo_home.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(cargo_home);
        rel_base.join(dir_path)
    };
    if let Some(res) = crate::rustc_runner::try_validate_store_contained_path(
        &joined,
        store_prefix,
        caller_cwd,
        true,
        label,
    ) {
        let canon_store = res.map_err(|e| {
            format!(
                "CARGO_HOME config {} [source.{src_name}].directory invalid: {e}",
                cfg_display.display()
            )
        })?;
        let canon_root = validate_dir_path_no_symlinks(store_prefix, caller_cwd).map_err(|e| {
            format!(
                "CARGO_HOME config {} [source.{src_name}].directory invalid: {e}",
                cfg_display.display()
            )
        })?;
        crate::rustc_runner::validate_store_contained_dir_tree(
            &canon_store,
            store_prefix,
            &canon_root,
            label,
        )
        .map_err(|e| {
            format!(
                "CARGO_HOME config {} [source.{src_name}].directory invalid: {e}",
                cfg_display.display()
            )
        })?;
        return Ok(CargoSourceDir::Store(canon_store));
    }
    validate_dir_ancestors_no_symlinks(&joined, label).map_err(|e| {
        format!(
            "CARGO_HOME config {} [source.{src_name}].directory invalid: {e}",
            cfg_display.display()
        )
    })?;
    Ok(CargoSourceDir::Host(joined))
}

fn copy_host_cargo_source_dir_to_staging(host_dir: &Path, dst_dir: &Path) -> Result<(), String> {
    let label = "CARGO_HOME [source] directory";
    #[cfg(unix)]
    {
        use std::os::fd::AsFd as _;
        let src_fd = crate::rustc_runner::open_dir_handle_no_symlinks(host_dir, None, label)?;
        crate::rustc_runner::copy_validated_subtree_from_fd_with_filter(
            src_fd.as_fd(),
            host_dir,
            dst_dir,
            None,
            false,
            label,
            |_, _, _| false,
        )
    }
    #[cfg(not(unix))]
    {
        crate::rustc_runner::copy_validated_subtree(host_dir, dst_dir, None, false, label)
    }
}

fn read_cargo_home_config_bytes(
    cargo_home: &Path,
    cfg_name: &str,
) -> Result<Option<String>, String> {
    let cfg_path = cargo_home.join(cfg_name);
    #[cfg(unix)]
    {
        use std::os::fd::{AsFd as _, AsRawFd as _};
        let ch_fd =
            crate::rustc_runner::open_dir_handle_no_symlinks(cargo_home, None, "CARGO_HOME")?;
        let c_name =
            crate::rustc_runner::os_str_to_cstring(OsStr::new(cfg_name), "CARGO_HOME config name")?;
        let mut st = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: `ch_fd` is open and `c_name` is NUL-terminated.
        if unsafe {
            libc::fstatat(
                ch_fd.as_raw_fd(),
                c_name.as_ptr(),
                st.as_mut_ptr(),
                libc::AT_SYMLINK_NOFOLLOW,
            )
        } != 0
        {
            let err = io::Error::last_os_error();
            if err.kind() == io::ErrorKind::NotFound {
                return Ok(None);
            }
            return Err(format!("stat CARGO_HOME config {}: {err}", cfg_path.display()));
        }
        // SAFETY: `fstatat` succeeded and initialized `st`.
        let st_init = unsafe { st.assume_init() };
        if crate::rustc_runner::is_lnk_mode(&st_init) {
            return Err(format!(
                "ambient Cargo config symlink rejected before Cargo build: {}",
                cfg_path.display()
            ));
        }
        if !crate::rustc_runner::is_reg_mode(&st_init) {
            return Err(format!(
                "ambient Cargo config is not a regular file: {}",
                cfg_path.display()
            ));
        }
        let (mut file, _) = crate::rustc_runner::open_regular_file_from_fd(
            ch_fd.as_fd(),
            &c_name,
            Some(crate::rustc_runner::stat_dev_ino(&st_init)),
            false,
            "ambient Cargo config",
        )?;
        let mut raw = String::new();
        file.read_to_string(&mut raw)
            .map_err(|e| format!("read CARGO_HOME config {}: {e}", cfg_path.display()))?;
        Ok(Some(raw))
    }
    #[cfg(not(unix))]
    {
        let cfg_meta = match fs::symlink_metadata(&cfg_path) {
            Ok(meta) => meta,
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(format!("stat CARGO_HOME config {}: {e}", cfg_path.display())),
        };
        if cfg_meta.file_type().is_symlink() {
            return Err(format!(
                "ambient Cargo config symlink rejected before Cargo build: {}",
                cfg_path.display()
            ));
        }
        if !cfg_meta.is_file() {
            return Err(format!(
                "ambient Cargo config is not a regular file: {}",
                cfg_path.display()
            ));
        }
        fs::read_to_string(&cfg_path)
            .map(Some)
            .map_err(|e| format!("read CARGO_HOME config {}: {e}", cfg_path.display()))
    }
}

fn cargo_home_has_registry_dir(cargo_home: &Path) -> Result<bool, String> {
    #[cfg(unix)]
    {
        use std::os::fd::AsRawFd as _;
        let ch_fd =
            crate::rustc_runner::open_dir_handle_no_symlinks(cargo_home, None, "CARGO_HOME")?;
        let mut st = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: `ch_fd` is open and `c"registry"` is NUL-terminated.
        if unsafe {
            libc::fstatat(
                ch_fd.as_raw_fd(),
                c"registry".as_ptr(),
                st.as_mut_ptr(),
                libc::AT_SYMLINK_NOFOLLOW,
            )
        } != 0
        {
            let err = io::Error::last_os_error();
            if err.kind() == io::ErrorKind::NotFound {
                return Ok(false);
            }
            return Err(format!("stat CARGO_HOME registry: {err}"));
        }
        // SAFETY: `fstatat` succeeded.
        let st_init = unsafe { st.assume_init() };
        Ok(crate::rustc_runner::is_dir_mode(&st_init))
    }
    #[cfg(not(unix))]
    {
        Ok(fs::symlink_metadata(cargo_home.join("registry"))
            .is_ok_and(|m| !m.file_type().is_symlink() && m.is_dir()))
    }
}

fn copy_locked_cargo_registry_to_staging(
    cargo_home: &Path,
    stage_root: &Path,
    locked_crates: &[LockedRegistryCrate],
) -> Result<(), String> {
    #[cfg(unix)]
    {
        use std::os::fd::AsFd as _;
        let reg_dir = cargo_home.join("registry");
        let reg_fd = crate::rustc_runner::open_dir_handle_no_symlinks(
            &reg_dir,
            None,
            "CARGO_HOME registry",
        )?;
        if let Ok(idx_fd) = crate::rustc_runner::open_child_dir_nofollow(
            reg_fd.as_fd(),
            c"index",
            None,
            "CARGO_HOME registry index",
        ) {
            crate::rustc_runner::copy_validated_subtree_from_fd_with_filter(
                idx_fd.as_fd(),
                &reg_dir.join("index"),
                &stage_root.join("registry/index"),
                None,
                false,
                "CARGO_HOME registry index",
                |_, name, is_dir| is_dir && name == ".git",
            )?;
        }
        if let Ok(cache_fd) = crate::rustc_runner::open_child_dir_nofollow(
            reg_fd.as_fd(),
            c"cache",
            None,
            "CARGO_HOME registry cache",
        ) {
            for idx_entry in
                crate::rustc_runner::read_dir_entries_from_fd(cache_fd.as_fd(), "registry cache")?
            {
                if crate::rustc_runner::is_lnk_mode(&idx_entry.stat) {
                    return Err(format!(
                        "CARGO_HOME registry cache must not contain symlink: {}",
                        idx_entry.os_name.to_string_lossy()
                    ));
                }
                if !crate::rustc_runner::is_dir_mode(&idx_entry.stat) {
                    continue;
                }
                let sub_fd = crate::rustc_runner::open_child_dir_nofollow(
                    cache_fd.as_fd(),
                    &idx_entry.c_name,
                    Some(crate::rustc_runner::stat_dev_ino(&idx_entry.stat)),
                    "CARGO_HOME registry cache subdir",
                )?;
                let dst_sub = stage_root.join("registry/cache").join(&idx_entry.os_name);
                for krate in locked_crates {
                    if krate.name.contains('/')
                        || krate.name.contains('\\')
                        || krate.name.contains('\0')
                        || krate.version.contains('/')
                        || krate.version.contains('\\')
                        || krate.version.contains('\0')
                    {
                        return Err(format!(
                            "unsafe crate name/version in Cargo.lock: {} {}",
                            krate.name, krate.version
                        ));
                    }
                    let fname = format!("{}-{}.crate", krate.name, krate.version);
                    let c_fname =
                        crate::rustc_runner::os_str_to_cstring(OsStr::new(&fname), "crate file")?;
                    let (mut f, st) = match crate::rustc_runner::open_regular_file_from_fd(
                        sub_fd.as_fd(),
                        &c_fname,
                        None,
                        false,
                        "CARGO_HOME registry .crate",
                    ) {
                        Ok(res) => res,
                        Err(_) => continue,
                    };
                    if let Some(expected_sha) = &krate.checksum {
                        let got_sha = crate::rustc_runner::sha256_opened_file_hex(
                            &mut f,
                            "CARGO_HOME registry .crate",
                        )?;
                        if &got_sha != expected_sha {
                            return Err(format!(
                                "CARGO_HOME registry cache checksum mismatch for {fname}: \
                                 expected {expected_sha}, got {got_sha}"
                            ));
                        }
                        f.seek(SeekFrom::Start(0)).map_err(|e| format!("seek {fname}: {e}"))?;
                    }
                    fs::create_dir_all(&dst_sub).map_err(|e| {
                        format!("create staged registry cache dir {}: {e}", dst_sub.display())
                    })?;
                    let exec = (st.st_mode as libc::mode_t & 0o111) != 0;
                    let dst_file = dst_sub.join(&fname);
                    if !dst_file.exists() {
                        crate::rustc_runner::copy_opened_file_to_new_dst(
                            &mut f,
                            exec,
                            &dst_file,
                            false,
                            "CARGO_HOME registry .crate",
                        )?;
                    }
                }
            }
        }
        let reg_src = stage_root.join("registry/src");
        fs::create_dir_all(&reg_src)
            .map_err(|e| format!("create staged registry src {}: {e}", reg_src.display()))?;
        use std::os::unix::fs::PermissionsExt as _;
        fs::set_permissions(&reg_src, fs::Permissions::from_mode(0o700))
            .map_err(|e| format!("chmod staged registry src {}: {e}", reg_src.display()))?;
        Ok(())
    }
    #[cfg(not(unix))]
    {
        let _ = (cargo_home, stage_root, locked_crates);
        Ok(())
    }
}

fn inspect_and_stage_cargo_home(
    cargo_home: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
    stage_ctx: Option<(&Path, &Path)>,
    locked_crates: &[LockedRegistryCrate],
) -> Result<Option<PathBuf>, String> {
    let dir_meta = match fs::symlink_metadata(cargo_home) {
        Ok(m) => m,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(format!("stat CARGO_HOME {}: {e}", cargo_home.display())),
    };
    if dir_meta.file_type().is_symlink() {
        return Err(format!(
            "CARGO_HOME directory must not be a symlink before Cargo build: {}",
            cargo_home.display()
        ));
    }
    if !dir_meta.is_dir() {
        return Err(format!(
            "CARGO_HOME path is not a directory before Cargo build: {}",
            cargo_home.display()
        ));
    }

    let mut staged_cfg_count = 0usize;
    let mut staged_sources: BTreeMap<PathBuf, PathBuf> = BTreeMap::new();
    let mut next_src_idx = 0usize;

    for cfg_name in ["config", "config.toml"] {
        let cfg_path = cargo_home.join(cfg_name);
        let Some(raw_cfg) = read_cargo_home_config_bytes(cargo_home, cfg_name)? else {
            continue;
        };
        let mut parsed: toml::Table = raw_cfg
            .parse()
            .map_err(|e| format!("parse CARGO_HOME config {}: {e}", cfg_path.display()))?;
        let disallowed: Vec<&str> =
            parsed.keys().map(String::as_str).filter(|k| *k != "source").collect();
        if !disallowed.is_empty() {
            return Err(format!(
                "ambient Cargo config in CARGO_HOME ({}) defines disallowed section(s) \
                 {disallowed:?} (only `[source]` is permitted before Cargo build)",
                cfg_path.display()
            ));
        }
        if let Some(source_val) = parsed.get_mut("source") {
            let Some(source_tbl) = source_val.as_table_mut() else {
                return Err(format!(
                    "CARGO_HOME config {} `[source]` must be a TOML table",
                    cfg_path.display()
                ));
            };
            for (src_name, src_entry_val) in source_tbl.iter_mut() {
                let Some(src_tbl) = src_entry_val.as_table_mut() else {
                    return Err(format!(
                        "CARGO_HOME config {} [source.{src_name}] must be a TOML table",
                        cfg_path.display()
                    ));
                };
                for (k, v) in src_tbl.iter() {
                    if k != "replace-with" && k != "directory" {
                        return Err(format!(
                            "CARGO_HOME config {} [source.{src_name}] defines disallowed key \
                             {k:?} (only `replace-with` and `directory` are permitted)",
                            cfg_path.display()
                        ));
                    }
                    let Some(s) = v.as_str() else {
                        return Err(format!(
                            "CARGO_HOME config {} [source.{src_name}].{k} must be a string",
                            cfg_path.display()
                        ));
                    };
                    validate_safe_toml_str(
                        s,
                        &format!(
                            "CARGO_HOME config {} [source.{src_name}].{k}",
                            cfg_path.display()
                        ),
                    )?;
                }
                if let Some(raw_dir) =
                    src_tbl.get("directory").and_then(toml::Value::as_str).map(ToOwned::to_owned)
                {
                    let resolved = resolve_cargo_source_directory(
                        &raw_dir,
                        cargo_home,
                        store_prefix,
                        caller_cwd,
                        &cfg_path,
                        src_name,
                    )?;
                    let rewritten_dir = match resolved {
                        CargoSourceDir::Store(store_dir) => store_dir,
                        CargoSourceDir::Host(host_dir) => {
                            if let Some((_, pinned_root)) = stage_ctx {
                                let canon_host =
                                    validate_dir_path_no_symlinks(&host_dir, caller_cwd)?;
                                if let Some(existing) = staged_sources.get(&canon_host) {
                                    existing.clone()
                                } else {
                                    let slot = format!("src-{next_src_idx}");
                                    next_src_idx += 1;
                                    let dst_dir = pinned_root.join("sources").join(&slot);
                                    copy_host_cargo_source_dir_to_staging(&host_dir, &dst_dir)
                                        .map_err(|e| {
                                            format!(
                                                "CARGO_HOME config {} [source.{src_name}].directory invalid: {e}",
                                                cfg_path.display()
                                            )
                                        })?;
                                    staged_sources.insert(canon_host, dst_dir.clone());
                                    dst_dir
                                }
                            } else {
                                crate::rustc_runner::validate_dir_tree_no_links(
                                    &host_dir,
                                    "CARGO_HOME [source] directory",
                                )
                                .map_err(|e| {
                                    format!(
                                        "CARGO_HOME config {} [source.{src_name}].directory invalid: {e}",
                                        cfg_path.display()
                                    )
                                })?;
                                host_dir
                            }
                        }
                    };
                    src_tbl.insert(
                        "directory".to_owned(),
                        toml::Value::String(rewritten_dir.to_string_lossy().into_owned()),
                    );
                }
            }
        }
        if let Some((_, pinned_root)) = stage_ctx {
            let rendered = toml::to_string(&parsed).map_err(|e| {
                format!("serialize staged CARGO_HOME config {}: {e}", cfg_path.display())
            })?;
            let dst_cfg = pinned_root.join(cfg_name);
            let mut f =
                fs::OpenOptions::new().write(true).create_new(true).open(&dst_cfg).map_err(
                    |e| format!("create staged CARGO_HOME config {}: {e}", dst_cfg.display()),
                )?;
            f.write_all(rendered.as_bytes()).map_err(|e| {
                format!("write staged CARGO_HOME config {}: {e}", dst_cfg.display())
            })?;
            f.flush().map_err(|e| {
                format!("flush staged CARGO_HOME config {}: {e}", dst_cfg.display())
            })?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt as _;
                f.set_permissions(fs::Permissions::from_mode(0o444)).map_err(|e| {
                    format!("chmod staged CARGO_HOME config {}: {e}", dst_cfg.display())
                })?;
            }
            staged_cfg_count += 1;
        }
    }

    if let Some((_, pinned_root)) = stage_ctx
        && staged_cfg_count == 0
        && !locked_crates.is_empty()
        && cargo_home_has_registry_dir(cargo_home)?
    {
        copy_locked_cargo_registry_to_staging(cargo_home, pinned_root, locked_crates)?;
        return Ok(Some(PathBuf::from("registry/src")));
    }
    Ok(None)
}

#[cfg(test)]
fn validate_cargo_home_configs(
    cargo_home: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
) -> Result<(), String> {
    let _ = inspect_and_stage_cargo_home(cargo_home, store_prefix, caller_cwd, None, &[])?;
    Ok(())
}

fn validate_ambient_cargo_paths(
    work_dir: &Path,
    default_target_roots: &[PathBuf],
    cargo_home_override: Option<&Path>,
    home_override: Option<&Path>,
    caller_cwd: &Path,
) -> Result<(Option<PathBuf>, Option<PathBuf>, Option<PathBuf>), String> {
    let validated_home = if let Some(h_raw) = home_override {
        let anchored_home =
            if h_raw.is_absolute() { h_raw.to_path_buf() } else { caller_cwd.join(h_raw) };
        validate_dir_ancestors_no_symlinks(&anchored_home, "HOME")
            .map_err(|e| format!("HOME invalid before Cargo build ({}): {e}", h_raw.display()))?;
        Some(anchored_home)
    } else {
        None
    };

    let (explicit_cargo_home, default_cargo_home) = if let Some(ch_raw) = cargo_home_override {
        let anchored =
            if ch_raw.is_absolute() { ch_raw.to_path_buf() } else { caller_cwd.join(ch_raw) };
        validate_dir_ancestors_no_symlinks(&anchored, "CARGO_HOME").map_err(|e| {
            format!("CARGO_HOME invalid before Cargo build ({}): {e}", ch_raw.display())
        })?;
        (Some(anchored), None)
    } else if let Some(anchored_home) = &validated_home {
        let default_ch = anchored_home.join(".cargo");
        validate_dir_ancestors_no_symlinks(&default_ch, "HOME/.cargo").map_err(|e| {
            format!("HOME/.cargo invalid before Cargo build ({}): {e}", default_ch.display())
        })?;
        (None, Some(default_ch))
    } else {
        (None, None)
    };

    let effective_cargo_home = explicit_cargo_home.clone().or(default_cargo_home);
    let allowed_cargo_home = effective_cargo_home
        .as_ref()
        .and_then(|p| fs::canonicalize(p).ok().or_else(|| Some(p.clone())));

    for anc in work_dir.ancestors() {
        for tc_name in ["rust-toolchain", "rust-toolchain.toml"] {
            let tc_path = anc.join(tc_name);
            if fs::symlink_metadata(&tc_path).is_ok() {
                return Err(format!(
                    "ambient `{tc_name}` override rejected before Cargo build: {}",
                    tc_path.display()
                ));
            }
        }
        let dot_cargo = anc.join(".cargo");
        if let Ok(meta) = fs::symlink_metadata(&dot_cargo) {
            if meta.file_type().is_symlink() {
                return Err(format!(
                    "ambient `.cargo` symlink rejected before Cargo build: {}",
                    dot_cargo.display()
                ));
            }
            let in_repo_root = default_target_roots.iter().any(|r| r == anc);
            let is_cargo_home = !in_repo_root
                && allowed_cargo_home.as_ref().is_some_and(|ch| {
                    fs::canonicalize(&dot_cargo).ok().as_ref() == Some(ch) || &dot_cargo == ch
                });
            if !is_cargo_home {
                return Err(format!(
                    "ambient `.cargo` directory rejected before Cargo build: {}",
                    dot_cargo.display()
                ));
            }
        }
    }
    Ok((explicit_cargo_home, validated_home, effective_cargo_home))
}

#[cfg(test)]
fn reject_ambient_cargo_configs(
    work_dir: &Path,
    default_target_roots: &[PathBuf],
    cargo_home_override: Option<&Path>,
    home_override: Option<&Path>,
    caller_cwd: &Path,
) -> Result<(Option<PathBuf>, Option<PathBuf>), String> {
    let (explicit_cargo_home, validated_home, effective_cargo_home) = validate_ambient_cargo_paths(
        work_dir,
        default_target_roots,
        cargo_home_override,
        home_override,
        caller_cwd,
    )?;
    let store_prefix = Path::new(crate::rustc_runner::STORE_PREFIX);
    if let Some(ch_dir) = &effective_cargo_home {
        validate_cargo_home_configs(ch_dir, store_prefix, caller_cwd)?;
    }
    Ok((explicit_cargo_home, validated_home))
}

#[allow(clippy::too_many_arguments)]
fn reject_and_pin_ambient_cargo_configs(
    work_dir: &Path,
    default_target_roots: &[PathBuf],
    cargo_home_override: Option<&Path>,
    home_override: Option<&Path>,
    caller_cwd: &Path,
    validated_tmpdir: Option<&Path>,
    store_prefix: &Path,
    locked_crates: &[LockedRegistryCrate],
) -> Result<(PinnedCargoHome, Option<PathBuf>), String> {
    let (_explicit_cargo_home, validated_home, effective_cargo_home) =
        validate_ambient_cargo_paths(
            work_dir,
            default_target_roots,
            cargo_home_override,
            home_override,
            caller_cwd,
        )?;
    let temp_ch = build_temp_dir("anneal-cargo-home-", validated_tmpdir)?;
    let staging = crate::rustc_runner::ImmutableStagingDir::build_and_pin_with_writable(
        temp_ch,
        "CARGO_HOME",
        |priv_root, pinned_root| {
            if let Some(ch_dir) = &effective_cargo_home {
                inspect_and_stage_cargo_home(
                    ch_dir,
                    store_prefix,
                    caller_cwd,
                    Some((priv_root, pinned_root)),
                    locked_crates,
                )
            } else {
                Ok(None)
            }
        },
    )?;
    let cargo_home = staging.pin_path(Path::new(""));
    Ok((PinnedCargoHome { cargo_home, _staging: staging }, validated_home))
}

/// Validate existing ancestor/leaf components of a directory path before
/// invoking `cargo build`, rejecting `..`, symlinks, and non-dir parents.
fn validate_dir_ancestors_no_symlinks(dir_path: &Path, label: &str) -> Result<(), String> {
    use std::{io::ErrorKind, path::Component};

    let mut cur = PathBuf::new();
    for comp in dir_path.components() {
        match comp {
            Component::Prefix(p) => cur.push(p.as_os_str()),
            Component::RootDir => cur.push(comp.as_os_str()),
            Component::CurDir => {
                if let Ok(meta) = fs::symlink_metadata(&cur)
                    && (meta.file_type().is_symlink() || !meta.is_dir())
                {
                    return Err(format!(
                        "{label} ancestor must be a real directory: {}",
                        cur.display()
                    ));
                }
            }
            Component::ParentDir => {
                return Err(format!(
                    "{label} must not contain parent-directory traversal (`..`): {}",
                    dir_path.display()
                ));
            }
            Component::Normal(seg) => {
                cur.push(seg);
                match fs::symlink_metadata(&cur) {
                    Ok(meta) if meta.file_type().is_symlink() => {
                        return Err(format!(
                            "{label} must not be or traverse a symlink: {}",
                            cur.display()
                        ));
                    }
                    Ok(meta) if !meta.is_dir() => {
                        return Err(format!(
                            "{label} component is not a directory: {}",
                            cur.display()
                        ));
                    }
                    Ok(_) => {}
                    Err(e) if e.kind() == ErrorKind::NotFound => {}
                    Err(e) => {
                        return Err(format!("stat {label} {}: {e}", cur.display()));
                    }
                }
            }
        }
    }
    Ok(())
}

fn workspace_target_roots(work_dir: &Path) -> Result<Vec<PathBuf>, String> {
    let mut roots = vec![work_dir.to_path_buf()];
    for anc in work_dir.ancestors().skip(1) {
        let manifest = anc.join("Cargo.toml");
        match fs::symlink_metadata(&manifest) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
            Err(e) => {
                return Err(format!("stat ancestor Cargo.toml {}: {e}", manifest.display()));
            }
            Ok(_) => {
                #[cfg(unix)]
                {
                    use std::os::fd::AsFd as _;
                    let anc_fd = crate::rustc_runner::open_dir_handle_no_symlinks(
                        anc,
                        None,
                        "ancestor Cargo.toml dir",
                    )?;
                    let _ = crate::rustc_runner::open_regular_file_from_fd(
                        anc_fd.as_fd(),
                        c"Cargo.toml",
                        None,
                        false,
                        "ancestor Cargo.toml",
                    )?;
                }
                #[cfg(not(unix))]
                {
                    let _ = validate_executable_no_links(&manifest, anc, "ancestor Cargo.toml")?;
                }
                roots.push(anc.to_path_buf());
            }
        }
    }
    Ok(roots)
}

#[derive(Debug)]
struct PreparedMirEvalSources {
    canon_orig_manifest: PathBuf,
    canon_orig_work_dir: PathBuf,
    default_target_roots: Vec<PathBuf>,
    staged_manifest: PathBuf,
    staged_work_dir: PathBuf,
    staging: Option<Arc<crate::rustc_runner::ImmutableStagingDir>>,
    locked_registry_crates: Vec<LockedRegistryCrate>,
}

fn parse_locked_registry_crates(
    lock_text: &str,
    label: &str,
) -> Result<Vec<LockedRegistryCrate>, String> {
    let parsed: toml::Table =
        lock_text.parse().map_err(|e| format!("parse {label} Cargo.lock: {e}"))?;
    let Some(pkgs) = parsed.get("package").and_then(toml::Value::as_array) else {
        return Ok(Vec::new());
    };
    let mut out = Vec::new();
    for item in pkgs {
        let Some(tbl) = item.as_table() else {
            continue;
        };
        let Some(src) = tbl.get("source").and_then(toml::Value::as_str) else {
            continue;
        };
        if !src.starts_with("registry+") {
            continue;
        }
        let Some(name) = tbl.get("name").and_then(toml::Value::as_str) else {
            continue;
        };
        let Some(version) = tbl.get("version").and_then(toml::Value::as_str) else {
            continue;
        };
        let checksum = tbl.get("checksum").and_then(toml::Value::as_str).map(ToOwned::to_owned);
        out.push(LockedRegistryCrate {
            name: name.to_owned(),
            version: version.to_owned(),
            checksum,
        });
    }
    Ok(out)
}

#[cfg(unix)]
fn open_staged_dir_nofollow(dir: &Path, label: &str) -> Result<std::os::fd::OwnedFd, String> {
    #[cfg(target_os = "linux")]
    if dir.starts_with("/proc/self/fd/") {
        return crate::rustc_runner::open_pinned_proc_dir_fd(dir, label);
    }
    crate::rustc_runner::open_dir_handle_no_symlinks(dir, None, label)
}

fn read_locked_registry_crates_from_dir(
    dir: &Path,
    label: &str,
) -> Result<Option<Vec<LockedRegistryCrate>>, String> {
    #[cfg(unix)]
    {
        use std::os::fd::{AsFd as _, AsRawFd as _};
        let dir_fd = open_staged_dir_nofollow(dir, label)?;
        let mut st = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: `dir_fd` is open and `c"Cargo.lock"` is NUL-terminated.
        if unsafe {
            libc::fstatat(
                dir_fd.as_raw_fd(),
                c"Cargo.lock".as_ptr(),
                st.as_mut_ptr(),
                libc::AT_SYMLINK_NOFOLLOW,
            )
        } != 0
        {
            let err = io::Error::last_os_error();
            if err.kind() == io::ErrorKind::NotFound {
                return Ok(None);
            }
            return Err(format!("stat {label} Cargo.lock: {err}"));
        }
        let (mut f, _) = crate::rustc_runner::open_regular_file_from_fd(
            dir_fd.as_fd(),
            c"Cargo.lock",
            None,
            false,
            label,
        )?;
        let mut raw = String::new();
        f.read_to_string(&mut raw).map_err(|e| format!("read {label} Cargo.lock: {e}"))?;
        parse_locked_registry_crates(&raw, label).map(Some)
    }
    #[cfg(not(unix))]
    {
        let p = dir.join("Cargo.lock");
        match fs::symlink_metadata(&p) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(format!("stat {label} Cargo.lock {}: {e}", p.display())),
            Ok(_) => {
                let _ = validate_executable_no_links(&p, dir, label)?;
                let raw = fs::read_to_string(&p)
                    .map_err(|e| format!("read {label} Cargo.lock {}: {e}", p.display()))?;
                parse_locked_registry_crates(&raw, label).map(Some)
            }
        }
    }
}

fn normalize_manifest_rel_path(
    base_dir: &Path,
    raw_rel: &str,
    store_prefix: &Path,
    allow_store_abs: bool,
    label: &str,
) -> Result<(PathBuf, bool), String> {
    if raw_rel.is_empty() || raw_rel.contains('\0') {
        return Err(format!("empty or NUL {label} path in Cargo.toml: {raw_rel:?}"));
    }
    let p = Path::new(raw_rel);
    if p.is_absolute() {
        if allow_store_abs
            && let Some(res) = crate::rustc_runner::try_validate_store_contained_path(
                p,
                store_prefix,
                base_dir,
                true,
                label,
            )
        {
            return Ok((res?, true));
        }
        return Err(format!(
            "{label} must not use an absolute non-store path outside staged source tree: {raw_rel}"
        ));
    }
    let mut joined = base_dir.to_path_buf();
    for comp in p.components() {
        match comp {
            Component::CurDir => {}
            Component::Normal(seg) => joined.push(seg),
            Component::ParentDir => {
                if !joined.pop() || joined.as_os_str().is_empty() {
                    return Err(format!("{label} escaped filesystem root: {raw_rel}"));
                }
            }
            Component::Prefix(_) | Component::RootDir => {
                return Err(format!("unsupported {label} path component: {raw_rel}"));
            }
        }
    }
    Ok((joined, false))
}

fn check_manifest_dir_no_links_and_normalize(
    cand: &Path,
    label: &str,
) -> Result<Option<PathBuf>, String> {
    match fs::symlink_metadata(cand) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(format!("stat {label} {}: {e}", cand.display())),
        Ok(meta) => {
            if meta.file_type().is_symlink() {
                return Err(format!("{label} must not be a symlink: {}", cand.display()));
            }
            validate_dir_path_no_symlinks(cand, Path::new("/")).map(Some)
        }
    }
}

fn is_dir_excluded_by_patterns(ws_dir: &Path, excludes: &[String], cand_dir: &Path) -> bool {
    excludes.iter().any(|ex| {
        cand_dir
            .ancestors()
            .take_while(|a| a.starts_with(ws_dir) || !ex.contains(['*', '?', '[']))
            .any(|anc| workspace_pattern_matches_dir(ws_dir, ex, anc))
    })
}

fn parse_toml_string_array(
    tbl: &toml::Table,
    key: &str,
    label: &str,
) -> Result<Vec<String>, String> {
    let Some(val) = tbl.get(key) else {
        return Ok(Vec::new());
    };
    let arr = val
        .as_array()
        .ok_or_else(|| format!("Cargo.toml [workspace].{key} in {label} must be an array"))?;
    arr.iter()
        .map(|v| {
            v.as_str()
                .map(ToOwned::to_owned)
                .ok_or_else(|| format!("Cargo.toml [workspace].{key} item must be a string"))
        })
        .collect()
}

fn is_cargo_source_tree_skipped(rel_segs: &[OsString], name: &OsStr, is_dir: bool) -> bool {
    if !is_dir {
        return false;
    }
    let Some(s) = name.to_str() else {
        return false;
    };
    s == ".git" || (rel_segs.is_empty() && matches!(s, "target" | ".lake"))
}

fn is_forbidden_manifest_entry_name(name: &OsStr) -> bool {
    name.to_str().is_some_and(|s| matches!(s, ".cargo" | "rust-toolchain" | "rust-toolchain.toml"))
}

fn reject_ambient_configs_inside_staged_tree(root: &Path, label: &str) -> Result<(), String> {
    #[cfg(unix)]
    {
        use std::os::fd::AsFd as _;
        let root_fd = open_staged_dir_nofollow(root, label)?;
        let mut stack: Vec<(Option<std::os::fd::OwnedFd>, PathBuf)> =
            vec![(None, root.to_path_buf())];
        while let Some((dir_opt, cur_disp)) = stack.pop() {
            let cur_fd = dir_opt.as_ref().map(|d| d.as_fd()).unwrap_or_else(|| root_fd.as_fd());
            let entries = crate::rustc_runner::read_dir_entries_from_fd(cur_fd, label)?;
            for entry in entries {
                let p = cur_disp.join(&entry.os_name);
                if is_forbidden_manifest_entry_name(&entry.os_name) {
                    return Err(format!(
                        "ambient `{}` entry rejected inside staged {label}: {}",
                        entry.os_name.to_string_lossy(),
                        p.display()
                    ));
                }
                if crate::rustc_runner::is_dir_mode(&entry.stat) {
                    let child = crate::rustc_runner::open_child_dir_nofollow(
                        cur_fd,
                        &entry.c_name,
                        Some(crate::rustc_runner::stat_dev_ino(&entry.stat)),
                        label,
                    )?;
                    stack.push((Some(child), p));
                }
            }
        }
        Ok(())
    }
    #[cfg(not(unix))]
    {
        let mut stack = vec![root.to_path_buf()];
        while let Some(dir) = stack.pop() {
            let entries = fs::read_dir(&dir)
                .map_err(|e| format!("scan staged {label} {}: {e}", dir.display()))?;
            for entry in entries {
                let entry = entry.map_err(|e| format!("iter staged {label}: {e}"))?;
                let p = entry.path();
                if is_forbidden_manifest_entry_name(&entry.file_name()) {
                    return Err(format!(
                        "ambient `{}` entry rejected inside staged {label}: {}",
                        entry.file_name().to_string_lossy(),
                        p.display()
                    ));
                }
                if fs::symlink_metadata(&p).is_ok_and(|m| m.is_dir()) {
                    stack.push(p);
                }
            }
        }
        Ok(())
    }
}

fn expand_glob_workspace_member_dirs(
    ws_dir: &Path,
    pat_segs: &[&str],
    excludes: &[String],
) -> Result<Vec<PathBuf>, String> {
    let mut matched = Vec::new();
    #[cfg(unix)]
    {
        use std::os::fd::AsFd as _;
        let root_fd =
            crate::rustc_runner::open_dir_handle_no_symlinks(ws_dir, None, "workspace root")?;
        let mut stack: Vec<(Option<std::os::fd::OwnedFd>, PathBuf, Vec<String>)> =
            vec![(None, ws_dir.to_path_buf(), Vec::new())];
        while let Some((dir_opt, cur_disp, rel_segs)) = stack.pop() {
            if is_dir_excluded_by_patterns(ws_dir, excludes, &cur_disp) {
                continue;
            }
            let cur_fd = dir_opt.as_ref().map(|d| d.as_fd()).unwrap_or_else(|| root_fd.as_fd());
            if path_components_glob_match(pat_segs, &rel_segs) {
                let mut st = std::mem::MaybeUninit::<libc::stat>::uninit();
                use std::os::fd::AsRawFd as _;
                // SAFETY: `cur_fd` is open and `c"Cargo.toml"` is
                // NUL-terminated.
                if unsafe {
                    libc::fstatat(
                        cur_fd.as_raw_fd(),
                        c"Cargo.toml".as_ptr(),
                        st.as_mut_ptr(),
                        libc::AT_SYMLINK_NOFOLLOW,
                    )
                } == 0
                {
                    matched.push(cur_disp.clone());
                }
            }
            let entries =
                crate::rustc_runner::read_dir_entries_from_fd(cur_fd, "workspace members")?;
            for entry in entries {
                let name_str = entry.os_name.to_string_lossy();
                if matches!(name_str.as_ref(), "target" | ".git" | ".lake") {
                    continue;
                }
                if crate::rustc_runner::is_lnk_mode(&entry.stat) {
                    let sym_p = cur_disp.join(&entry.os_name);
                    if !is_dir_excluded_by_patterns(ws_dir, excludes, &sym_p) {
                        return Err(format!(
                            "workspace member path must not traverse a symlink: {}",
                            sym_p.display()
                        ));
                    }
                    continue;
                }
                if crate::rustc_runner::is_dir_mode(&entry.stat) {
                    let next_disp = cur_disp.join(&entry.os_name);
                    let mut next_rel = rel_segs.clone();
                    next_rel.push(name_str.into_owned());
                    let child = crate::rustc_runner::open_child_dir_nofollow(
                        cur_fd,
                        &entry.c_name,
                        Some(crate::rustc_runner::stat_dev_ino(&entry.stat)),
                        "workspace member dir",
                    )?;
                    stack.push((Some(child), next_disp, next_rel));
                }
            }
        }
    }
    #[cfg(not(unix))]
    {
        let mut stack = vec![(ws_dir.to_path_buf(), Vec::<String>::new())];
        while let Some((cur_dir, rel_segs)) = stack.pop() {
            if is_dir_excluded_by_patterns(ws_dir, excludes, &cur_dir) {
                continue;
            }
            if path_components_glob_match(pat_segs, &rel_segs)
                && fs::symlink_metadata(cur_dir.join("Cargo.toml")).is_ok()
            {
                matched.push(cur_dir.clone());
            }
            for entry in fs::read_dir(&cur_dir)
                .map_err(|e| format!("read workspace dir {}: {e}", cur_dir.display()))?
            {
                let entry = entry.map_err(|e| format!("iter workspace dir: {e}"))?;
                let p = entry.path();
                let name = entry.file_name();
                let name_str = name.to_string_lossy();
                if matches!(name_str.as_ref(), "target" | ".git" | ".lake") {
                    continue;
                }
                let meta = fs::symlink_metadata(&p)
                    .map_err(|e| format!("stat workspace entry {}: {e}", p.display()))?;
                if meta.file_type().is_symlink() {
                    if !is_dir_excluded_by_patterns(ws_dir, excludes, &p) {
                        return Err(format!(
                            "workspace member path must not traverse a symlink: {}",
                            p.display()
                        ));
                    }
                    continue;
                }
                if meta.is_dir() {
                    let mut next_rel = rel_segs.clone();
                    next_rel.push(name_str.into_owned());
                    stack.push((p, next_rel));
                }
            }
        }
    }
    matched.sort();
    Ok(matched)
}

fn collect_dep_table_paths(
    deps: &toml::Table,
    base_dir: &Path,
    store_prefix: &Path,
    out_dirs: &mut Vec<PathBuf>,
    out_store_dirs: &mut Vec<PathBuf>,
) -> Result<(), String> {
    for val in deps.values() {
        let Some(tbl) = val.as_table() else {
            continue;
        };
        if let Some(raw_path) = tbl.get("path").and_then(toml::Value::as_str) {
            let (cand, is_store) = normalize_manifest_rel_path(
                base_dir,
                raw_path,
                store_prefix,
                true,
                "Cargo dependency path",
            )?;
            if is_store {
                out_store_dirs.push(cand);
            } else if let Some(canon) =
                check_manifest_dir_no_links_and_normalize(&cand, "Cargo path dependency")?
            {
                out_dirs.push(canon);
            }
        }
    }
    Ok(())
}

fn collect_target_file_parent_dir(
    raw_path: &str,
    base_dir: &Path,
    store_prefix: &Path,
    out_dirs: &mut Vec<PathBuf>,
    label: &str,
) -> Result<(), String> {
    let (joined_file, _) =
        normalize_manifest_rel_path(base_dir, raw_path, store_prefix, false, label)?;
    let Some(parent) = joined_file.parent() else {
        return Err(format!("{label} has no parent directory: {raw_path}"));
    };
    if let Some(canon_parent) = check_manifest_dir_no_links_and_normalize(parent, label)? {
        out_dirs.push(canon_parent);
    }
    Ok(())
}

fn collect_manifest_referenced_dirs(
    parsed: &toml::Table,
    dir: &Path,
    include_workspace_members: bool,
    store_prefix: &Path,
) -> Result<(Vec<PathBuf>, Vec<PathBuf>), String> {
    let mut dirs = Vec::new();
    let mut store_dirs = Vec::new();

    for key in ["dependencies", "dev-dependencies", "build-dependencies"] {
        if let Some(tbl) = parsed.get(key).and_then(toml::Value::as_table) {
            collect_dep_table_paths(tbl, dir, store_prefix, &mut dirs, &mut store_dirs)?;
        }
    }
    if let Some(target_tbl) = parsed.get("target").and_then(toml::Value::as_table) {
        for cfg_val in target_tbl.values() {
            let Some(cfg_tbl) = cfg_val.as_table() else {
                continue;
            };
            for key in ["dependencies", "dev-dependencies", "build-dependencies"] {
                if let Some(tbl) = cfg_tbl.get(key).and_then(toml::Value::as_table) {
                    collect_dep_table_paths(tbl, dir, store_prefix, &mut dirs, &mut store_dirs)?;
                }
            }
        }
    }
    if let Some(patch_tbl) = parsed.get("patch").and_then(toml::Value::as_table) {
        for src_val in patch_tbl.values() {
            if let Some(tbl) = src_val.as_table() {
                collect_dep_table_paths(tbl, dir, store_prefix, &mut dirs, &mut store_dirs)?;
            }
        }
    }
    if let Some(replace_tbl) = parsed.get("replace").and_then(toml::Value::as_table) {
        collect_dep_table_paths(replace_tbl, dir, store_prefix, &mut dirs, &mut store_dirs)?;
    }
    if let Some(pkg_tbl) = parsed.get("package").and_then(toml::Value::as_table) {
        for key in ["build", "readme", "license-file"] {
            if let Some(s) = pkg_tbl.get(key).and_then(toml::Value::as_str) {
                collect_target_file_parent_dir(
                    s,
                    dir,
                    store_prefix,
                    &mut dirs,
                    &format!("package.{key}"),
                )?;
            }
        }
    }
    if let Some(lib_tbl) = parsed.get("lib").and_then(toml::Value::as_table)
        && let Some(s) = lib_tbl.get("path").and_then(toml::Value::as_str)
    {
        collect_target_file_parent_dir(s, dir, store_prefix, &mut dirs, "lib.path")?;
    }
    for arr_key in ["bin", "example", "test", "bench"] {
        if let Some(arr) = parsed.get(arr_key).and_then(toml::Value::as_array) {
            for item in arr {
                if let Some(s) =
                    item.as_table().and_then(|t| t.get("path")).and_then(toml::Value::as_str)
                {
                    collect_target_file_parent_dir(
                        s,
                        dir,
                        store_prefix,
                        &mut dirs,
                        &format!("{arr_key}.path"),
                    )?;
                }
            }
        }
    }
    if let Some(ws_tbl) = parsed.get("workspace").and_then(toml::Value::as_table) {
        if let Some(ws_deps) = ws_tbl.get("dependencies").and_then(toml::Value::as_table) {
            collect_dep_table_paths(ws_deps, dir, store_prefix, &mut dirs, &mut store_dirs)?;
        }
        if let Some(ws_pkg) = ws_tbl.get("package").and_then(toml::Value::as_table) {
            for key in ["readme", "license-file"] {
                if let Some(s) = ws_pkg.get(key).and_then(toml::Value::as_str) {
                    collect_target_file_parent_dir(
                        s,
                        dir,
                        store_prefix,
                        &mut dirs,
                        &format!("workspace.package.{key}"),
                    )?;
                }
            }
        }
        if include_workspace_members {
            let excludes = parse_toml_string_array(ws_tbl, "exclude", &dir.display().to_string())?;
            for m_key in ["members", "default-members"] {
                for pat in parse_toml_string_array(ws_tbl, m_key, &dir.display().to_string())? {
                    let trimmed = pat.trim();
                    if trimmed.is_empty() {
                        continue;
                    }
                    if trimmed.contains(['*', '?', '[']) {
                        let pat_segs: Vec<&str> =
                            trimmed.split('/').filter(|s| !s.is_empty() && *s != ".").collect();
                        dirs.extend(expand_glob_workspace_member_dirs(dir, &pat_segs, &excludes)?);
                    } else {
                        let (cand, _) = normalize_manifest_rel_path(
                            dir,
                            trimmed,
                            store_prefix,
                            false,
                            "workspace member",
                        )?;
                        if let Some(canon) =
                            check_manifest_dir_no_links_and_normalize(&cand, "workspace member")?
                            && !is_dir_excluded_by_patterns(dir, &excludes, &canon)
                        {
                            dirs.push(canon);
                        }
                    }
                }
            }
        }
    }
    Ok((dirs, store_dirs))
}

fn read_toml_from_dir_verified(
    dir: &Path,
    label: &str,
) -> Result<Option<(toml::Table, Vec<u8>)>, String> {
    #[cfg(unix)]
    {
        use std::os::fd::{AsFd as _, AsRawFd as _};
        let dir_fd = crate::rustc_runner::open_dir_handle_no_symlinks(dir, None, label)?;
        let mut st = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: `dir_fd` is open and `c"Cargo.toml"` is NUL-terminated.
        if unsafe {
            libc::fstatat(
                dir_fd.as_raw_fd(),
                c"Cargo.toml".as_ptr(),
                st.as_mut_ptr(),
                libc::AT_SYMLINK_NOFOLLOW,
            )
        } != 0
        {
            let err = io::Error::last_os_error();
            if err.kind() == io::ErrorKind::NotFound {
                return Ok(None);
            }
            return Err(format!("stat {label} Cargo.toml: {err}"));
        }
        let (mut file, _st) = crate::rustc_runner::open_regular_file_from_fd(
            dir_fd.as_fd(),
            c"Cargo.toml",
            None,
            false,
            label,
        )?;
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes).map_err(|e| format!("read {label} Cargo.toml: {e}"))?;
        let text = std::str::from_utf8(&bytes)
            .map_err(|e| format!("{label} Cargo.toml is not valid UTF-8: {e}"))?;
        let tbl: toml::Table =
            text.parse().map_err(|e| format!("parse {label} Cargo.toml: {e}"))?;
        Ok(Some((tbl, bytes)))
    }
    #[cfg(not(unix))]
    {
        let p = dir.join("Cargo.toml");
        match fs::symlink_metadata(&p) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(format!("stat {label} Cargo.toml {}: {e}", p.display())),
            Ok(_) => {
                let _ = validate_executable_no_links(&p, dir, label)?;
                let bytes = fs::read(&p)
                    .map_err(|e| format!("read {label} Cargo.toml {}: {e}", p.display()))?;
                let text = std::str::from_utf8(&bytes)
                    .map_err(|e| format!("{label} Cargo.toml is not valid UTF-8: {e}"))?;
                let tbl: toml::Table =
                    text.parse().map_err(|e| format!("parse {label} Cargo.toml: {e}"))?;
                Ok(Some((tbl, bytes)))
            }
        }
    }
}

fn compute_common_root(dirs: impl IntoIterator<Item = PathBuf>) -> Result<PathBuf, String> {
    let mut iter = dirs.into_iter();
    let Some(first) = iter.next() else {
        return Err("source staging graph is empty".to_owned());
    };
    let mut prefix: Vec<OsString> =
        first.components().map(|c| c.as_os_str().to_os_string()).collect();
    for dir in iter {
        let comps: Vec<OsString> = dir.components().map(|c| c.as_os_str().to_os_string()).collect();
        let common_len = prefix.iter().zip(comps.iter()).take_while(|(a, b)| a == b).count();
        prefix.truncate(common_len);
    }
    let mut root = PathBuf::new();
    for seg in prefix {
        root.push(seg);
    }
    if root.as_os_str().is_empty() || root.parent().is_none() {
        return Err(format!(
            "--mir-eval-manifest dependencies must share a non-root staging ancestor (got {})",
            root.display()
        ));
    }
    Ok(root)
}

#[cfg(unix)]
fn copy_workspace_root_files_from_fd(
    dir_fd: std::os::fd::BorrowedFd<'_>,
    src_disp: &Path,
    dst_dir: &Path,
) -> Result<(), String> {
    fs::create_dir_all(dst_dir)
        .map_err(|e| format!("create staged workspace root {}: {e}", dst_dir.display()))?;
    for entry in crate::rustc_runner::read_dir_entries_from_fd(dir_fd, "workspace root")? {
        let p = src_disp.join(&entry.os_name);
        if is_forbidden_manifest_entry_name(&entry.os_name) {
            return Err(format!(
                "ambient `{}` entry rejected in workspace root: {}",
                entry.os_name.to_string_lossy(),
                p.display()
            ));
        }
        if crate::rustc_runner::is_lnk_mode(&entry.stat) {
            let s = entry.os_name.to_string_lossy();
            if matches!(s.as_ref(), "Cargo.toml" | "Cargo.lock") {
                return Err(format!("workspace root file must not be a symlink: {}", p.display()));
            }
            continue;
        }
        if crate::rustc_runner::is_reg_mode(&entry.stat) {
            let (mut f, st) = crate::rustc_runner::open_regular_file_from_fd(
                dir_fd,
                &entry.c_name,
                Some(crate::rustc_runner::stat_dev_ino(&entry.stat)),
                false,
                "workspace root file",
            )?;
            let exec = (st.st_mode as libc::mode_t & 0o111) != 0;
            crate::rustc_runner::copy_opened_file_to_new_dst(
                &mut f,
                exec,
                &dst_dir.join(&entry.os_name),
                false,
                "workspace root file",
            )?;
        }
    }
    Ok(())
}

fn prepare_mir_eval_source_graph(
    manifest_path: &Path,
    caller_cwd: &Path,
    validated_tmpdir: Option<&Path>,
    store_prefix: &Path,
) -> Result<PreparedMirEvalSources, String> {
    if let Some(res) = crate::rustc_runner::try_validate_store_contained_path(
        manifest_path,
        store_prefix,
        caller_cwd,
        false,
        "--mir-eval-manifest",
    ) {
        let canon_manifest = res?;
        let work_dir = canon_manifest
            .parent()
            .ok_or_else(|| {
                format!("--mir-eval-manifest has no parent: {}", canon_manifest.display())
            })?
            .to_path_buf();
        let default_target_roots = workspace_target_roots(&work_dir)?;
        let canon_store = validate_dir_path_no_symlinks(store_prefix, caller_cwd)?;
        crate::rustc_runner::validate_store_contained_dir_tree(
            &work_dir,
            store_prefix,
            &canon_store,
            "--mir-eval-manifest store sources",
        )?;
        let locked_registry_crates =
            read_locked_registry_crates_from_dir(&work_dir, "store Cargo.lock")?
                .unwrap_or_default();
        return Ok(PreparedMirEvalSources {
            canon_orig_manifest: canon_manifest.clone(),
            canon_orig_work_dir: work_dir.clone(),
            default_target_roots,
            staged_manifest: canon_manifest,
            staged_work_dir: work_dir,
            staging: None,
            locked_registry_crates,
        });
    }

    let mut opened_manifest = crate::rustc_runner::open_verified_executable_via_dirfd(
        manifest_path,
        caller_cwd,
        true,
        "--mir-eval-manifest",
    )?;
    let canon_orig_manifest = opened_manifest.canon_path.clone();
    let canon_orig_work_dir = canon_orig_manifest
        .parent()
        .ok_or_else(|| {
            format!("--mir-eval-manifest has no parent: {}", canon_orig_manifest.display())
        })?
        .to_path_buf();
    let mut manifest_bytes = Vec::new();
    opened_manifest
        .file
        .read_to_end(&mut manifest_bytes)
        .map_err(|e| format!("read --mir-eval-manifest {}: {e}", canon_orig_manifest.display()))?;
    let manifest_text = std::str::from_utf8(&manifest_bytes).map_err(|e| {
        format!("--mir-eval-manifest {} is not valid UTF-8: {e}", canon_orig_manifest.display())
    })?;
    let root_toml: toml::Table = manifest_text
        .parse()
        .map_err(|e| format!("parse --mir-eval-manifest {}: {e}", canon_orig_manifest.display()))?;

    let default_target_roots = workspace_target_roots(&canon_orig_work_dir)?;
    let mut ws_root: Option<PathBuf> = None;
    if let Some(pkg_ws) = root_toml
        .get("package")
        .and_then(toml::Value::as_table)
        .and_then(|t| t.get("workspace"))
        .and_then(toml::Value::as_str)
    {
        let (cand, _) = normalize_manifest_rel_path(
            &canon_orig_work_dir,
            pkg_ws,
            store_prefix,
            false,
            "package.workspace",
        )?;
        if let Some(canon_ws) =
            check_manifest_dir_no_links_and_normalize(&cand, "package.workspace")?
        {
            ws_root = Some(canon_ws);
        }
    } else if !root_toml.contains_key("workspace") {
        for anc in default_target_roots.iter().skip(1) {
            if let Some((anc_toml, _)) = read_toml_from_dir_verified(anc, "ancestor Cargo.toml")?
                && let Some(ws_tbl) = anc_toml.get("workspace").and_then(toml::Value::as_table)
            {
                let excludes = parse_toml_string_array(ws_tbl, "exclude", "ancestor workspace")?;
                if !is_dir_excluded_by_patterns(anc, &excludes, &canon_orig_work_dir) {
                    ws_root = Some(anc.clone());
                }
                break;
            }
        }
    }

    // `copy_full = true` copies the directory's entire subtree (packages and
    // explicit target dirs); `false` copies only top-level regular files of a
    // pure `[workspace]` root alongside its resolved members and dependencies.
    let mut collected: BTreeMap<PathBuf, bool> = BTreeMap::new();
    let mut queue: VecDeque<(PathBuf, bool, Option<toml::Table>)> = VecDeque::new();
    collected.insert(canon_orig_work_dir.clone(), true);
    queue.push_back((
        canon_orig_work_dir.clone(),
        root_toml.contains_key("workspace"),
        Some(root_toml),
    ));
    if let Some(ref wr) = ws_root
        && wr != &canon_orig_work_dir
        && let Some((ws_toml, _)) = read_toml_from_dir_verified(wr, "workspace Cargo.toml")?
    {
        let ws_has_pkg = ws_toml.contains_key("package");
        collected.insert(wr.clone(), ws_has_pkg);
        queue.push_back((wr.clone(), true, Some(ws_toml)));
    }

    let canon_store_opt = validate_dir_path_no_symlinks(store_prefix, caller_cwd).ok();
    while let Some((dir, include_members, pre_toml)) = queue.pop_front() {
        let parsed = match pre_toml {
            Some(t) => Some(t),
            None => read_toml_from_dir_verified(&dir, "Cargo manifest")?.map(|(t, _)| t),
        };
        let Some(tbl) = parsed else {
            continue;
        };
        let (next_dirs, store_dirs) =
            collect_manifest_referenced_dirs(&tbl, &dir, include_members, store_prefix)?;
        for s_dir in store_dirs {
            let Some(ref cs) = canon_store_opt else {
                return Err(format!("store prefix missing for dependency: {}", s_dir.display()));
            };
            crate::rustc_runner::validate_store_contained_dir_tree(
                &s_dir,
                store_prefix,
                cs,
                "store dependency sources",
            )?;
        }
        for nd in next_dirs {
            if let Some(prev) = collected.get_mut(&nd) {
                if !*prev {
                    *prev = true;
                    queue.push_back((nd, false, None));
                }
            } else {
                collected.insert(nd.clone(), true);
                queue.push_back((nd, false, None));
            }
        }
    }

    let common_root = compute_common_root(collected.keys().cloned())?;
    let full_roots: BTreeSet<PathBuf> =
        collected.iter().filter(|&(_, full)| *full).map(|(d, _)| d.clone()).collect();
    let rel_manifest = canon_orig_manifest.strip_prefix(&common_root).map_err(|_| {
        format!(
            "--mir-eval-manifest {} outside common staging root {}",
            canon_orig_manifest.display(),
            common_root.display()
        )
    })?;
    let rel_work_dir = canon_orig_work_dir.strip_prefix(&common_root).map_err(|_| {
        format!(
            "--mir-eval-manifest work dir {} outside common staging root {}",
            canon_orig_work_dir.display(),
            common_root.display()
        )
    })?;
    let mut lock_rels = vec![rel_work_dir.to_path_buf()];
    if let Some(ref wr) = ws_root
        && let Ok(rel_ws) = wr.strip_prefix(&common_root)
        && rel_ws != rel_work_dir
    {
        lock_rels.insert(0, rel_ws.to_path_buf());
    }

    let temp_src = build_temp_dir("anneal-mir-eval-src-", validated_tmpdir)?;
    let (locked_registry_crates, staging) =
        crate::rustc_runner::ImmutableStagingDir::build_and_pin(
            temp_src,
            "Leg 3 manifest sources",
            |_, pinned_root| {
                for (dir, copy_full) in &collected {
                    let rel = dir.strip_prefix(&common_root).map_err(|_| {
                        format!(
                            "source dir {} outside common staging root {}",
                            dir.display(),
                            common_root.display()
                        )
                    })?;
                    let dst_dir = if rel.as_os_str().is_empty() {
                        pinned_root.to_path_buf()
                    } else {
                        pinned_root.join(rel)
                    };
                    let covered_by_parent =
                        dir.ancestors().skip(1).any(|anc| full_roots.contains(anc));
                    if covered_by_parent {
                        continue;
                    }
                    if *copy_full {
                        #[cfg(unix)]
                        {
                            use std::os::fd::AsFd as _;
                            let dir_fd = crate::rustc_runner::open_dir_handle_no_symlinks(
                                dir,
                                None,
                                "--mir-eval-manifest source dir",
                            )?;
                            crate::rustc_runner::copy_validated_subtree_from_fd_with_filter(
                                dir_fd.as_fd(),
                                dir,
                                &dst_dir,
                                None,
                                false,
                                "--mir-eval-manifest sources",
                                is_cargo_source_tree_skipped,
                            )?;
                        }
                        #[cfg(not(unix))]
                        {
                            crate::rustc_runner::copy_validated_subtree(
                                dir,
                                &dst_dir,
                                None,
                                false,
                                "--mir-eval-manifest sources",
                            )?;
                        }
                    } else {
                        #[cfg(unix)]
                        {
                            use std::os::fd::AsFd as _;
                            let dir_fd = crate::rustc_runner::open_dir_handle_no_symlinks(
                                dir,
                                None,
                                "workspace root dir",
                            )?;
                            copy_workspace_root_files_from_fd(dir_fd.as_fd(), dir, &dst_dir)?;
                        }
                        #[cfg(not(unix))]
                        {
                            fs::create_dir_all(&dst_dir).map_err(|e| {
                                format!("create staged workspace root {}: {e}", dst_dir.display())
                            })?;
                            if let Some((_, bytes)) =
                                read_toml_from_dir_verified(dir, "workspace root")?
                            {
                                fs::write(dst_dir.join("Cargo.toml"), bytes).map_err(|e| {
                                    format!("write staged workspace Cargo.toml: {e}")
                                })?;
                            }
                            let lock = dir.join("Cargo.lock");
                            if fs::symlink_metadata(&lock).is_ok() {
                                crate::rustc_runner::copy_verified_regular_file(
                                    &lock,
                                    &dst_dir.join("Cargo.lock"),
                                    false,
                                    "workspace Cargo.lock",
                                )?;
                            }
                        }
                    }
                }

                reject_ambient_configs_inside_staged_tree(
                    pinned_root,
                    "--mir-eval-manifest sources",
                )?;
                let mut found_registry_crates = Vec::new();
                for lock_rel in &lock_rels {
                    let lock_dir = if lock_rel.as_os_str().is_empty() {
                        pinned_root.to_path_buf()
                    } else {
                        pinned_root.join(lock_rel)
                    };
                    if let Some(crates) = read_locked_registry_crates_from_dir(
                        &lock_dir,
                        "staged workspace Cargo.lock",
                    )? {
                        found_registry_crates = crates;
                        break;
                    }
                }
                Ok(found_registry_crates)
            },
        )?;
    let staged_manifest = staging.pin_path(rel_manifest);
    let staged_work_dir = staging.pin_path(rel_work_dir);

    Ok(PreparedMirEvalSources {
        canon_orig_manifest,
        canon_orig_work_dir,
        default_target_roots,
        staged_manifest,
        staged_work_dir,
        staging: Some(staging),
        locked_registry_crates,
    })
}

/// Prepared immutable Leg-3 `anneal-mir-eval` executable built inside a private
/// target directory and isolated inside a read-only symlink-free staging root.
#[derive(Debug)]
pub struct PreparedMirEval {
    pub path: PathBuf,
    pub(crate) exec_path: PathBuf,
    pub(crate) _staging: Option<Arc<crate::rustc_runner::ImmutableStagingDir>>,
}

impl PreparedMirEval {
    fn from_staged(
        path: PathBuf,
        staging: Option<Arc<crate::rustc_runner::ImmutableStagingDir>>,
    ) -> Self {
        let exec_path = crate::rustc_runner::ImmutableStagingDir::pin_path_with_guards(
            &[staging.as_ref()],
            &path,
        );
        Self { path, exec_path, _staging: staging }
    }
}

/// Opt-in builder for an explicit `--mir-eval-manifest <Cargo.toml>` path.
///
/// Rejects symlinks fail-closed and never assumes any sibling `tools/`
/// directory exists unless explicitly supplied by the caller.
pub fn build_mir_eval_from_manifest(manifest_path: &Path) -> Result<PreparedMirEval, String> {
    let caller_cwd =
        env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
    build_mir_eval_from_manifest_with_env(
        manifest_path,
        &caller_cwd,
        env::var_os("CARGO").as_deref(),
        env::var_os("RUSTC").as_deref(),
        env::var_os("PATH").as_deref(),
        env::var_os("CARGO_TARGET_DIR").as_deref(),
    )
}

fn build_mir_eval_from_manifest_with_env(
    manifest_path: &Path,
    caller_cwd: &Path,
    cargo_env: Option<&std::ffi::OsStr>,
    rustc_env: Option<&std::ffi::OsStr>,
    path_env: Option<&std::ffi::OsStr>,
    target_dir_env: Option<&std::ffi::OsStr>,
) -> Result<PreparedMirEval, String> {
    build_mir_eval_from_manifest_with_env_and_cargo_home(
        manifest_path,
        caller_cwd,
        cargo_env,
        rustc_env,
        path_env,
        target_dir_env,
        env::var_os("CARGO_HOME").as_deref(),
    )
}

#[cfg(unix)]
fn is_cargo_hardlink_partner_in_dir(
    dir_fd: std::os::fd::BorrowedFd<'_>,
    name: &std::ffi::CStr,
    bin_dev_ino: (u64, u64),
    label: &str,
) -> bool {
    let Ok((_f, st)) =
        crate::rustc_runner::open_regular_file_from_fd(dir_fd, name, None, true, label)
    else {
        return false;
    };
    crate::rustc_runner::stat_nlink(&st) == 2
        && crate::rustc_runner::stat_dev_ino(&st) == bin_dev_ino
}

#[cfg(unix)]
fn has_verified_cargo_hardlink_partner_fd(
    profile_fd: std::os::fd::BorrowedFd<'_>,
    bin_name: &str,
    bin_dev_ino: (u64, u64),
) -> bool {
    use std::os::fd::AsFd as _;

    let stem = bin_name.replace('-', "_");
    if let Ok(deps_fd) =
        crate::rustc_runner::open_child_dir_nofollow(profile_fd, c"deps", None, "Cargo deps dir")
        && let Ok(entries) =
            crate::rustc_runner::read_dir_entries_from_fd(deps_fd.as_fd(), "Cargo deps dir")
    {
        let stem_prefix = format!("{stem}-");
        for entry in entries {
            if crate::rustc_runner::is_reg_mode(&entry.stat)
                && entry.os_name.to_str().is_some_and(|s| s.starts_with(&stem_prefix))
                && is_cargo_hardlink_partner_in_dir(
                    deps_fd.as_fd(),
                    &entry.c_name,
                    bin_dev_ino,
                    "Cargo deps binary",
                )
            {
                return true;
            }
        }
    }
    if let Ok(build_fd) =
        crate::rustc_runner::open_child_dir_nofollow(profile_fd, c"build", None, "Cargo build dir")
        && let Ok(pkg_entries) =
            crate::rustc_runner::read_dir_entries_from_fd(build_fd.as_fd(), "Cargo build dir")
    {
        let out_leaf = format!("{stem}{}", env::consts::EXE_SUFFIX);
        let Ok(c_out_leaf) = crate::rustc_runner::os_str_to_cstring(OsStr::new(&out_leaf), "out")
        else {
            return false;
        };
        for pkg_entry in pkg_entries {
            if !crate::rustc_runner::is_dir_mode(&pkg_entry.stat) {
                continue;
            }
            let Ok(pkg_fd) = crate::rustc_runner::open_child_dir_nofollow(
                build_fd.as_fd(),
                &pkg_entry.c_name,
                Some(crate::rustc_runner::stat_dev_ino(&pkg_entry.stat)),
                "Cargo build package dir",
            ) else {
                continue;
            };
            let Ok(hash_entries) =
                crate::rustc_runner::read_dir_entries_from_fd(pkg_fd.as_fd(), "Cargo hash dir")
            else {
                continue;
            };
            for hash_entry in hash_entries {
                if !crate::rustc_runner::is_dir_mode(&hash_entry.stat)
                    || !hash_entry.os_name.to_str().is_some_and(|s| {
                        !s.is_empty() && s.bytes().all(|b| b.is_ascii_alphanumeric())
                    })
                {
                    continue;
                }
                let Ok(hash_fd) = crate::rustc_runner::open_child_dir_nofollow(
                    pkg_fd.as_fd(),
                    &hash_entry.c_name,
                    Some(crate::rustc_runner::stat_dev_ino(&hash_entry.stat)),
                    "Cargo build hash dir",
                ) else {
                    continue;
                };
                if let Ok(out_fd) = crate::rustc_runner::open_child_dir_nofollow(
                    hash_fd.as_fd(),
                    c"out",
                    None,
                    "Cargo build out dir",
                ) && is_cargo_hardlink_partner_in_dir(
                    out_fd.as_fd(),
                    &c_out_leaf,
                    bin_dev_ino,
                    "Cargo out binary",
                ) {
                    return true;
                }
            }
        }
    }
    false
}

#[cfg(unix)]
pub(crate) fn stage_verified_single_link_executable(
    canon_bin: &Path,
    bin_name: &str,
    tmp_parent: Option<&Path>,
    allow_cargo_deps_hardlink: bool,
) -> Result<(PathBuf, String, Option<Arc<crate::rustc_runner::ImmutableStagingDir>>), String> {
    let parent = canon_bin.parent().unwrap_or(Path::new("/"));
    stage_verified_single_link_executable_from_path(
        canon_bin,
        parent,
        bin_name,
        tmp_parent,
        allow_cargo_deps_hardlink,
    )
}

pub(crate) fn stage_verified_single_link_executable_from_path(
    raw_bin: &Path,
    caller_cwd: &Path,
    bin_name: &str,
    tmp_parent: Option<&Path>,
    allow_cargo_deps_hardlink: bool,
) -> Result<(PathBuf, String, Option<Arc<crate::rustc_runner::ImmutableStagingDir>>), String> {
    let opened = crate::rustc_runner::open_verified_executable_via_dirfd(
        raw_bin,
        caller_cwd,
        !allow_cargo_deps_hardlink,
        bin_name,
    )?;
    stage_opened_single_link_executable_with_hook(
        opened,
        bin_name,
        tmp_parent,
        allow_cargo_deps_hardlink,
        || {},
    )
}

#[cfg(unix)]
pub(crate) fn stage_opened_single_link_executable_with_hook(
    mut opened: crate::rustc_runner::OpenedExecutable,
    bin_name: &str,
    tmp_parent: Option<&Path>,
    allow_cargo_deps_hardlink: bool,
    mut on_first_chunk: impl FnMut(),
) -> Result<(PathBuf, String, Option<Arc<crate::rustc_runner::ImmutableStagingDir>>), String> {
    use std::os::{
        fd::AsFd as _,
        unix::fs::{MetadataExt as _, PermissionsExt as _},
    };

    let expected_nlink = opened.nlink;
    if expected_nlink == 2 && allow_cargo_deps_hardlink {
        let profile_fd = opened.parent_fd.as_ref().ok_or_else(|| {
            format!("built {bin_name} has no profile parent: {}", opened.canon_path.display())
        })?;
        if !has_verified_cargo_hardlink_partner_fd(profile_fd.as_fd(), bin_name, opened.dev_ino) {
            return Err(format!(
                "built {bin_name} must not be hardlinked outside Cargo deps (nlink=2): {}",
                opened.canon_path.display()
            ));
        }
    } else if expected_nlink != 1 {
        return Err(format!(
            "{bin_name} must not have extra hardlinks (nlink={expected_nlink}): {}",
            opened.canon_path.display()
        ));
    }

    let opened_meta = opened
        .file
        .metadata()
        .map_err(|e| format!("fstat {bin_name} {}: {e}", opened.canon_path.display()))?;
    if !opened_meta.is_file()
        || opened_meta.nlink() != expected_nlink
        || (opened_meta.dev(), opened_meta.ino()) != opened.dev_ino
    {
        return Err(format!(
            "{bin_name} changed concurrently during isolation: {}",
            opened.canon_path.display()
        ));
    }
    opened
        .file
        .seek(SeekFrom::Start(0))
        .map_err(|e| format!("seek {bin_name} {}: {e}", opened.canon_path.display()))?;

    let stage_temp = build_temp_dir(&format!("anneal-stage-{bin_name}-"), tmp_parent)?;
    let ((dest_name, bin_sha), staging) = crate::rustc_runner::ImmutableStagingDir::build_and_pin(
        stage_temp,
        &format!("staged {bin_name}"),
        |_, pinned_root| {
            let mut tmp = tempfile::NamedTempFile::new_in(pinned_root).map_err(|e| {
                format!("create isolated temp bin in {}: {e}", pinned_root.display())
            })?;
            let mut hasher = Sha256::new();
            let mut buf = [0u8; 65536];
            let mut hooked = false;
            loop {
                let n = match opened.file.read(&mut buf) {
                    Ok(0) => break,
                    Ok(n) => n,
                    Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
                    Err(e) => {
                        return Err(format!(
                            "read {bin_name} {}: {e}",
                            opened.canon_path.display()
                        ));
                    }
                };
                hasher.update(&buf[..n]);
                tmp.as_file_mut()
                    .write_all(&buf[..n])
                    .map_err(|e| format!("copy {bin_name} to isolated single-link file: {e}"))?;
                if !hooked {
                    hooked = true;
                    on_first_chunk();
                }
            }
            tmp.as_file_mut().flush().map_err(|e| format!("flush isolated {bin_name}: {e}"))?;
            tmp.as_file()
                .set_permissions(fs::Permissions::from_mode(0o555))
                .map_err(|e| format!("chmod isolated {bin_name}: {e}"))?;
            let tmp_meta = tmp
                .as_file()
                .metadata()
                .map_err(|e| format!("fstat isolated temp {bin_name}: {e}"))?;
            if !tmp_meta.is_file() || tmp_meta.nlink() != 1 {
                return Err(format!(
                    "isolated {bin_name} temp file failed single-link check (nlink={})",
                    tmp_meta.nlink()
                ));
            }
            let bin_sha = format!("{:x}", hasher.finalize());
            let dest_name = format!("{bin_name}-{}", &bin_sha[..16]);
            let dest_path = pinned_root.join(&dest_name);
            let persisted = tmp.persist(&dest_path).map_err(|e| {
                format!("persist isolated {bin_name} {}: {}", dest_path.display(), e.error)
            })?;
            drop(persisted);

            let dest_meta = fs::symlink_metadata(&dest_path)
                .map_err(|e| format!("stat isolated {bin_name} {}: {e}", dest_path.display()))?;
            if dest_meta.file_type().is_symlink()
                || !dest_meta.is_file()
                || dest_meta.nlink() != 1
                || (dest_meta.dev(), dest_meta.ino()) != (tmp_meta.dev(), tmp_meta.ino())
            {
                return Err(format!(
                    "isolated {bin_name} failed single-link verification (nlink={}): {}",
                    dest_meta.nlink(),
                    dest_path.display()
                ));
            }
            Ok((dest_name, bin_sha))
        },
    )?;
    let _ = staging.open_verified_rel_file(Path::new(&dest_name), bin_name)?;
    let canon_dest = staging.root().join(&dest_name);
    Ok((canon_dest, bin_sha, Some(staging)))
}

#[cfg(not(unix))]
pub(crate) fn stage_opened_single_link_executable_with_hook(
    mut opened: crate::rustc_runner::OpenedExecutable,
    bin_name: &str,
    tmp_parent: Option<&Path>,
    _allow_cargo_deps_hardlink: bool,
    mut on_first_chunk: impl FnMut(),
) -> Result<(PathBuf, String, Option<Arc<crate::rustc_runner::ImmutableStagingDir>>), String> {
    let stage_temp = build_temp_dir(&format!("anneal-stage-{bin_name}-"), tmp_parent)?;
    let ((dest_name, bin_sha), staging) = crate::rustc_runner::ImmutableStagingDir::build_and_pin(
        stage_temp,
        &format!("staged {bin_name}"),
        |_, pinned_root| {
            let mut tmp = tempfile::NamedTempFile::new_in(pinned_root).map_err(|e| {
                format!("create isolated temp bin in {}: {e}", pinned_root.display())
            })?;
            let mut hasher = Sha256::new();
            let mut buf = [0u8; 65536];
            let mut hooked = false;
            loop {
                let n = match opened.file.read(&mut buf) {
                    Ok(0) => break,
                    Ok(n) => n,
                    Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
                    Err(e) => {
                        return Err(format!(
                            "read {bin_name} {}: {e}",
                            opened.canon_path.display()
                        ));
                    }
                };
                hasher.update(&buf[..n]);
                tmp.as_file_mut()
                    .write_all(&buf[..n])
                    .map_err(|e| format!("copy {bin_name} to staged file: {e}"))?;
                if !hooked {
                    hooked = true;
                    on_first_chunk();
                }
            }
            tmp.as_file_mut().flush().map_err(|e| format!("flush staged {bin_name}: {e}"))?;
            let bin_sha = format!("{:x}", hasher.finalize());
            let dest_name = format!("{bin_name}-{}{}", &bin_sha[..16], env::consts::EXE_SUFFIX);
            let dest_path = pinned_root.join(&dest_name);
            let persisted = tmp.persist(&dest_path).map_err(|e| {
                format!("persist staged {bin_name} {}: {}", dest_path.display(), e.error)
            })?;
            drop(persisted);
            Ok((dest_name, bin_sha))
        },
    )?;
    let canon_dest = staging.root().join(&dest_name);
    Ok((canon_dest, bin_sha, Some(staging)))
}

fn materialize_cargo_built_opened_executable(
    opened: crate::rustc_runner::OpenedExecutable,
    bin_name: &str,
    tmp_parent: Option<&Path>,
) -> Result<PreparedMirEval, String> {
    let (path, _sha, staging) =
        stage_opened_single_link_executable_with_hook(opened, bin_name, tmp_parent, true, || {})?;
    Ok(PreparedMirEval::from_staged(path, staging))
}

#[cfg(unix)]
#[cfg_attr(not(test), allow(dead_code))]
fn materialize_cargo_built_executable_with_hook(
    canon_bin: PathBuf,
    bin_name: &str,
    tmp_parent: Option<&Path>,
    on_first_chunk: impl FnMut(),
) -> Result<PreparedMirEval, String> {
    let parent = canon_bin.parent().unwrap_or(Path::new("/"));
    let opened = crate::rustc_runner::open_verified_executable_via_dirfd(
        &canon_bin, parent, false, bin_name,
    )?;
    let (path, _sha, staging) = stage_opened_single_link_executable_with_hook(
        opened,
        bin_name,
        tmp_parent,
        true,
        on_first_chunk,
    )?;
    Ok(PreparedMirEval::from_staged(path, staging))
}

struct PinnedLeg3Toolchain {
    pinned_cargo: PathBuf,
    pinned_rustc: PathBuf,
    host_triple: String,
    linker: PathBuf,
    ld_library_path: String,
    child_path: OsString,
    _sysroot_staging: Vec<Arc<crate::rustc_runner::ImmutableStagingDir>>,
}

fn validate_optional_dir_env(
    raw: Option<&OsStr>,
    caller_cwd: &Path,
    label: &str,
) -> Result<Option<PathBuf>, String> {
    let Some(val) = raw.filter(|v| !v.is_empty()) else {
        return Ok(None);
    };
    let p = PathBuf::from(val);
    let anchored = if p.is_absolute() { p } else { caller_cwd.join(p) };
    validate_dir_ancestors_no_symlinks(&anchored, label)?;
    Ok(Some(anchored))
}

pub(crate) fn validate_optional_existing_dir_env(
    raw: Option<&OsStr>,
    caller_cwd: &Path,
    label: &str,
) -> Result<Option<PathBuf>, String> {
    let Some(val) = raw.filter(|v| !v.is_empty()) else {
        return Ok(None);
    };
    validate_dir_path_no_symlinks(Path::new(val), caller_cwd)
        .map(Some)
        .map_err(|e| format!("{label} invalid: {e}"))
}

fn parse_rustc_host_triple(version_verbose_stdout: &str) -> Result<String, String> {
    let host = version_verbose_stdout
        .lines()
        .find_map(|line| line.trim().strip_prefix("host:"))
        .map(str::trim)
        .filter(|h| !h.is_empty())
        .ok_or_else(|| "`rustc -vV` output missing `host:` target triple".to_owned())?;
    if !host.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_') {
        return Err(format!("invalid characters in `rustc -vV` host triple: {host:?}"));
    }
    Ok(host.to_owned())
}

#[allow(clippy::too_many_arguments)]
fn run_rustc_leg3_probe(
    rustc_bin: &Path,
    args: &[&str],
    work_dir: &Path,
    probe_path: &OsStr,
    probe_ld: &str,
    validated_home: Option<&Path>,
    validated_cargo_home: Option<&Path>,
    validated_tmpdir: Option<&Path>,
) -> Result<String, String> {
    let mut inv = Invocation::new(rustc_bin, args).env("PATH", probe_path);
    if !probe_ld.is_empty() {
        inv = inv.env("LD_LIBRARY_PATH", probe_ld);
    }
    if let Some(h) = validated_home {
        inv = inv.env("HOME", h);
    }
    if let Some(ch) = validated_cargo_home {
        inv = inv.env("CARGO_HOME", ch);
    }
    if let Some(td) = validated_tmpdir {
        inv = inv.env("TMPDIR", td);
    }
    let tmp_dir = build_temp_dir("anneal-rustc-probe-", validated_tmpdir)?;
    let log_root = fs::canonicalize(tmp_dir.path())
        .map_err(|e| format!("canonicalize rustc probe dir: {e}"))?;
    let supervisor =
        ProcessSupervisor::new(Duration::from_secs(crate::rustc_runner::RUSTC_PROBE_TIMEOUT_SECS))?;
    let out = supervisor.run(&inv, work_dir, &log_root.join("log"), &log_root)?;
    match out.termination {
        Termination::Exited(s) if s.success() => String::from_utf8(out.stdout)
            .map_err(|e| format!("invalid UTF-8 from `{} {:?}`: {e}", rustc_bin.display(), args)),
        other => Err(format!(
            "`{} {:?}` failed ({}): {}",
            rustc_bin.display(),
            args,
            other.describe(),
            String::from_utf8_lossy(&out.stderr).trim()
        )),
    }
}

fn verify_staged_rustc_matches_opened(
    staged_bin: &Path,
    opened: Option<&mut crate::rustc_runner::OpenedExecutable>,
) -> Result<(), String> {
    let Some(opened) = opened else {
        return Ok(());
    };
    opened.file.seek(SeekFrom::Start(0)).map_err(|e| format!("seek opened rustc: {e}"))?;
    let want_sha = crate::rustc_runner::sha256_opened_file_hex(&mut opened.file, "opened rustc")?;
    let mut staged_f = File::open(staged_bin)
        .map_err(|e| format!("open staged rustc {}: {e}", staged_bin.display()))?;
    let got_sha = crate::rustc_runner::sha256_opened_file_hex(&mut staged_f, "staged rustc")?;
    if got_sha != want_sha {
        return Err(format!(
            "Leg 3 rustc binary changed concurrently during sysroot staging: {}",
            staged_bin.display()
        ));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn resolve_leg3_pinned_toolchain_opened_with_store(
    mut rustc_tool: ResolvedToolExecutable,
    mut cargo_tool: ResolvedToolExecutable,
    path_env: Option<&OsStr>,
    caller_cwd: &Path,
    work_dir: &Path,
    validated_home: Option<&Path>,
    validated_cargo_home: Option<&Path>,
    validated_tmpdir: Option<&Path>,
    store_prefix: &Path,
) -> Result<PinnedLeg3Toolchain, String> {
    let trusted_dirs: Vec<&Path> =
        crate::rustc_runner::TRUSTED_LINKER_DIRS.iter().map(Path::new).collect();
    let symlink_dirs: Vec<&Path> =
        crate::rustc_runner::TRUSTED_LINKER_SYMLINK_DIRS.iter().map(Path::new).collect();
    let trusted_child_dirs: Vec<&Path> =
        crate::rustc_runner::TRUSTED_CHILD_PATH_DIRS.iter().map(Path::new).collect();

    let abs_rustc = &rustc_tool.path;
    let abs_cargo = &cargo_tool.path;
    let raw_rustc_dir = abs_rustc
        .parent()
        .ok_or_else(|| format!("RUSTC binary has no parent dir: {}", abs_rustc.display()))?;
    let raw_cargo_dir = abs_cargo
        .parent()
        .ok_or_else(|| format!("CARGO binary has no parent dir: {}", abs_cargo.display()))?;
    let _ = crate::rustc_runner::validated_store_aware_dir(
        raw_rustc_dir,
        store_prefix,
        caller_cwd,
        "Leg 3 RUSTC bin dir",
    )?;
    let _ = crate::rustc_runner::validated_store_aware_dir(
        raw_cargo_dir,
        store_prefix,
        caller_cwd,
        "Leg 3 CARGO bin dir",
    )?;
    let rel_rustc = format!("bin/rustc{}", env::consts::EXE_SUFFIX);
    let mut staging_guards: Vec<Arc<crate::rustc_runner::ImmutableStagingDir>> = Vec::new();
    let (pinned_cargo, cargo_staging) = if let Some(ref mut opened_cargo) = cargo_tool.opened {
        crate::rustc_runner::stage_immutable_opened_executable(
            opened_cargo,
            validated_tmpdir,
            "Leg 3 cargo binary",
        )?
    } else {
        (abs_cargo.clone(), None)
    };
    if let Some(guard) = cargo_staging {
        staging_guards.push(guard);
    }
    let valid_cargo_dir = crate::rustc_runner::validated_store_aware_dir(
        pinned_cargo
            .parent()
            .ok_or_else(|| format!("pinned CARGO has no parent: {}", pinned_cargo.display()))?,
        store_prefix,
        caller_cwd,
        "Leg 3 pinned CARGO bin dir",
    )?;
    let mut prepared_probe_sysroot: Option<crate::rustc_runner::PreparedSysroot> = None;
    let mut probe_rustc_staging: Option<Arc<crate::rustc_runner::ImmutableStagingDir>> = None;
    let (staged_probe_rustc, initial_ld) = if let Some(prefix) = raw_rustc_dir.parent()
        && prefix.join("lib").join("rustlib").is_dir()
        && (prefix.join(&rel_rustc) == *abs_rustc
            || fs::canonicalize(prefix.join(&rel_rustc)).ok().as_ref()
                == fs::canonicalize(abs_rustc).ok().as_ref())
        && crate::rustc_runner::try_validate_store_contained_executable(
            abs_rustc,
            store_prefix,
            caller_cwd,
            "Leg 3 rustc binary",
        )
        .is_none()
    {
        let prepared = crate::rustc_runner::prepare_sysroot_binary_in(
            prefix,
            &rel_rustc,
            store_prefix,
            validated_tmpdir,
            "Leg 3 rustc binary",
        )?;
        verify_staged_rustc_matches_opened(&prepared.binary, rustc_tool.opened.as_mut())?;
        let bin = prepared.binary.clone();
        let ld = prepared.ld_library_path.clone();
        prepared_probe_sysroot = Some(prepared);
        (bin, ld)
    } else {
        let (bin, staging) = if let Some(ref mut opened_rustc) = rustc_tool.opened {
            crate::rustc_runner::stage_immutable_opened_executable(
                opened_rustc,
                validated_tmpdir,
                "Leg 3 probe rustc binary",
            )?
        } else {
            (abs_rustc.clone(), None)
        };
        probe_rustc_staging = staging;
        let ld = if let Some(prefix) = raw_rustc_dir.parent() {
            let prepared_init = crate::rustc_runner::prepare_toolchain_library_path_in(
                prefix,
                store_prefix,
                caller_cwd,
                true,
                validated_tmpdir,
            )?;
            if let Some(guard) = prepared_init._staging {
                staging_guards.push(guard);
            }
            prepared_init.ld_library_path
        } else {
            String::new()
        };
        (bin, ld)
    };
    let valid_probe_rustc_dir = crate::rustc_runner::validated_store_aware_dir(
        staged_probe_rustc.parent().ok_or_else(|| {
            format!("staged RUSTC has no parent: {}", staged_probe_rustc.display())
        })?,
        store_prefix,
        caller_cwd,
        "Leg 3 staged RUSTC bin dir",
    )?;
    let cargo_ld = if let Some(cargo_prefix) = raw_cargo_dir.parent()
        && raw_rustc_dir.parent() != Some(cargo_prefix)
    {
        let prepared_cargo_lib = crate::rustc_runner::prepare_toolchain_library_path_in(
            cargo_prefix,
            store_prefix,
            caller_cwd,
            true,
            validated_tmpdir,
        )?;
        if let Some(guard) = prepared_cargo_lib._staging {
            staging_guards.push(guard);
        }
        prepared_cargo_lib.ld_library_path
    } else {
        String::new()
    };
    let probe_path = crate::rustc_runner::build_child_path_with_bins(
        &[&valid_probe_rustc_dir, &valid_cargo_dir],
        None,
        store_prefix,
        &trusted_child_dirs,
        path_env,
        caller_cwd,
    )?;
    let mut probe_guards: Vec<Option<&Arc<crate::rustc_runner::ImmutableStagingDir>>> =
        staging_guards.iter().map(Some).collect();
    probe_guards.push(probe_rustc_staging.as_ref());
    probe_guards.push(prepared_probe_sysroot.as_ref().and_then(|ps| ps._staging.as_ref()));
    let pinned_probe_rustc = crate::rustc_runner::ImmutableStagingDir::pin_path_with_guards(
        &probe_guards,
        &staged_probe_rustc,
    );
    let pinned_initial_ld = if initial_ld.is_empty() {
        String::new()
    } else {
        crate::rustc_runner::ImmutableStagingDir::pin_env_paths_with_guards(
            &probe_guards,
            OsStr::new(&initial_ld),
        )?
        .to_string_lossy()
        .into_owned()
    };
    let pinned_probe_path = crate::rustc_runner::ImmutableStagingDir::pin_env_paths_with_guards(
        &probe_guards,
        &probe_path,
    )?;

    let sysroot_stdout = run_rustc_leg3_probe(
        &pinned_probe_rustc,
        &["--print", "sysroot"],
        work_dir,
        &pinned_probe_path,
        &pinned_initial_ld,
        validated_home,
        validated_cargo_home,
        validated_tmpdir,
    )?;
    let raw_sysroot_str = sysroot_stdout.trim();
    if raw_sysroot_str.is_empty() {
        return Err(format!("`{} --print sysroot` returned empty output", abs_rustc.display()));
    }
    let raw_sysroot = PathBuf::from(raw_sysroot_str);
    let mut canon_sysroot = crate::rustc_runner::validated_store_aware_dir(
        &raw_sysroot,
        store_prefix,
        caller_cwd,
        "Leg 3 rust_sysroot",
    )?;
    let (pinned_rustc, sysroot_ld) =
        if prepared_probe_sysroot.as_ref().is_some_and(|ps| canon_sysroot == ps.sysroot) {
            let prepared_sys = prepared_probe_sysroot.expect("checked Some above");
            if let Some(guard) = prepared_sys._staging {
                staging_guards.push(guard);
            }
            (prepared_sys.binary, prepared_sys.ld_library_path)
        } else if canon_sysroot.join(&rel_rustc) == *abs_rustc
            || fs::canonicalize(canon_sysroot.join(&rel_rustc)).ok().as_ref()
                == fs::canonicalize(abs_rustc).ok().as_ref()
        {
            let prepared_sys = crate::rustc_runner::prepare_sysroot_binary_in(
                &raw_sysroot,
                &rel_rustc,
                store_prefix,
                validated_tmpdir,
                "Leg 3 rustc binary",
            )?;
            verify_staged_rustc_matches_opened(&prepared_sys.binary, rustc_tool.opened.as_mut())?;
            canon_sysroot = prepared_sys.sysroot;
            if let Some(guard) = prepared_sys._staging {
                staging_guards.push(guard);
            }
            (prepared_sys.binary, prepared_sys.ld_library_path)
        } else {
            let prepared_lib = crate::rustc_runner::prepare_toolchain_library_path_in(
                &canon_sysroot,
                store_prefix,
                caller_cwd,
                true,
                validated_tmpdir,
            )?;
            if let Some(guard) = prepared_lib._staging {
                staging_guards.push(guard);
            }
            if let Some(guard) = probe_rustc_staging {
                staging_guards.push(guard);
            }
            if let Some(guard) = prepared_probe_sysroot.and_then(|ps| ps._staging) {
                staging_guards.push(guard);
            }
            (staged_probe_rustc, prepared_lib.ld_library_path)
        };
    let mut ld_entries = Vec::new();
    let mut seen_ld = BTreeSet::new();
    for entry in [sysroot_ld, initial_ld, cargo_ld] {
        if !entry.is_empty() && seen_ld.insert(entry.clone()) {
            ld_entries.push(PathBuf::from(entry));
        }
    }
    let raw_ld_library_path = if ld_entries.is_empty() {
        String::new()
    } else {
        env::join_paths(ld_entries)
            .map(|s| s.to_string_lossy().into_owned())
            .map_err(|e| format!("join Leg 3 LD_LIBRARY_PATH: {e}"))?
    };

    let valid_pinned_dir = crate::rustc_runner::validated_store_aware_dir(
        pinned_rustc
            .parent()
            .ok_or_else(|| format!("pinned RUSTC has no parent: {}", pinned_rustc.display()))?,
        store_prefix,
        caller_cwd,
        "Leg 3 pinned RUSTC bin dir",
    )?;
    let linker = crate::rustc_runner::resolve_and_validate_linker_with(
        &canon_sysroot,
        store_prefix,
        &trusted_dirs,
        &symlink_dirs,
        path_env,
        caller_cwd,
    )?;
    let raw_child_path = crate::rustc_runner::build_child_path_with_bins(
        &[&valid_pinned_dir, &valid_cargo_dir],
        Some(&linker),
        store_prefix,
        &trusted_child_dirs,
        path_env,
        caller_cwd,
    )?;
    let guard_refs: Vec<Option<&Arc<crate::rustc_runner::ImmutableStagingDir>>> =
        staging_guards.iter().map(Some).collect();
    let pinned_cargo =
        crate::rustc_runner::ImmutableStagingDir::pin_path_with_guards(&guard_refs, &pinned_cargo);
    let pinned_rustc =
        crate::rustc_runner::ImmutableStagingDir::pin_path_with_guards(&guard_refs, &pinned_rustc);
    let ld_library_path = if raw_ld_library_path.is_empty() {
        String::new()
    } else {
        crate::rustc_runner::ImmutableStagingDir::pin_env_paths_with_guards(
            &guard_refs,
            OsStr::new(&raw_ld_library_path),
        )?
        .to_string_lossy()
        .into_owned()
    };
    let child_path = crate::rustc_runner::ImmutableStagingDir::pin_env_paths_with_guards(
        &guard_refs,
        &raw_child_path,
    )?;

    let version_stdout = run_rustc_leg3_probe(
        &pinned_rustc,
        &["-vV"],
        work_dir,
        &child_path,
        &ld_library_path,
        validated_home,
        validated_cargo_home,
        validated_tmpdir,
    )?;
    let host_triple = parse_rustc_host_triple(&version_stdout)?;

    Ok(PinnedLeg3Toolchain {
        pinned_cargo,
        pinned_rustc,
        host_triple,
        linker,
        ld_library_path,
        child_path,
        _sysroot_staging: staging_guards,
    })
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
fn resolve_leg3_pinned_toolchain_with_store(
    abs_rustc: &Path,
    abs_cargo: &Path,
    path_env: Option<&OsStr>,
    caller_cwd: &Path,
    work_dir: &Path,
    validated_home: Option<&Path>,
    validated_cargo_home: Option<&Path>,
    validated_tmpdir: Option<&Path>,
    store_prefix: &Path,
) -> Result<PinnedLeg3Toolchain, String> {
    let rustc_tool = if let Some(res) = crate::rustc_runner::try_validate_store_contained_executable(
        abs_rustc,
        store_prefix,
        caller_cwd,
        "Leg 3 rustc binary",
    ) {
        ResolvedToolExecutable { path: res?, is_rustup_proxy: false, opened: None }
    } else {
        open_non_store_tool_executable(abs_rustc, caller_cwd, "Leg 3 rustc binary")?
    };
    let cargo_tool = if let Some(res) = crate::rustc_runner::try_validate_store_contained_executable(
        abs_cargo,
        store_prefix,
        caller_cwd,
        "Leg 3 cargo binary",
    ) {
        ResolvedToolExecutable { path: res?, is_rustup_proxy: false, opened: None }
    } else {
        open_non_store_tool_executable(abs_cargo, caller_cwd, "Leg 3 cargo binary")?
    };
    resolve_leg3_pinned_toolchain_opened_with_store(
        rustc_tool,
        cargo_tool,
        path_env,
        caller_cwd,
        work_dir,
        validated_home,
        validated_cargo_home,
        validated_tmpdir,
        store_prefix,
    )
}

#[allow(clippy::too_many_arguments)]
fn build_mir_eval_from_manifest_with_env_and_cargo_home(
    manifest_path: &Path,
    caller_cwd: &Path,
    cargo_env: Option<&std::ffi::OsStr>,
    rustc_env: Option<&std::ffi::OsStr>,
    path_env: Option<&std::ffi::OsStr>,
    target_dir_env: Option<&std::ffi::OsStr>,
    cargo_home_env: Option<&std::ffi::OsStr>,
) -> Result<PreparedMirEval, String> {
    build_mir_eval_from_manifest_with_env_and_homes(
        manifest_path,
        caller_cwd,
        cargo_env,
        rustc_env,
        path_env,
        target_dir_env,
        cargo_home_env,
        env::var_os("HOME").as_deref(),
    )
}

#[allow(clippy::too_many_arguments)]
fn build_mir_eval_from_manifest_with_env_and_homes(
    manifest_path: &Path,
    caller_cwd: &Path,
    cargo_env: Option<&std::ffi::OsStr>,
    rustc_env: Option<&std::ffi::OsStr>,
    path_env: Option<&std::ffi::OsStr>,
    target_dir_env: Option<&std::ffi::OsStr>,
    cargo_home_env: Option<&std::ffi::OsStr>,
    home_env: Option<&std::ffi::OsStr>,
) -> Result<PreparedMirEval, String> {
    build_mir_eval_from_manifest_full(
        manifest_path,
        caller_cwd,
        cargo_env,
        rustc_env,
        path_env,
        target_dir_env,
        cargo_home_env,
        home_env,
        env::var_os("RUSTUP_HOME").as_deref(),
        env::var_os("RUSTUP_TOOLCHAIN").as_deref(),
        env::var_os("CARGO_NET_OFFLINE").as_deref(),
        env::var_os("TMPDIR").as_deref(),
    )
}

#[allow(clippy::too_many_arguments)]
fn build_mir_eval_from_manifest_full(
    manifest_path: &Path,
    caller_cwd: &Path,
    cargo_env: Option<&OsStr>,
    rustc_env: Option<&OsStr>,
    path_env: Option<&OsStr>,
    target_dir_env: Option<&OsStr>,
    cargo_home_env: Option<&OsStr>,
    home_env: Option<&OsStr>,
    rustup_home_env: Option<&OsStr>,
    rustup_toolchain_env: Option<&OsStr>,
    cargo_net_offline_env: Option<&OsStr>,
    tmpdir_env: Option<&OsStr>,
) -> Result<PreparedMirEval, String> {
    build_mir_eval_from_manifest_full_with_store(
        manifest_path,
        caller_cwd,
        cargo_env,
        rustc_env,
        path_env,
        target_dir_env,
        cargo_home_env,
        home_env,
        rustup_home_env,
        rustup_toolchain_env,
        cargo_net_offline_env,
        tmpdir_env,
        Path::new(crate::rustc_runner::STORE_PREFIX),
    )
}

#[allow(clippy::too_many_arguments)]
fn build_mir_eval_from_manifest_full_with_store(
    manifest_path: &Path,
    caller_cwd: &Path,
    cargo_env: Option<&OsStr>,
    rustc_env: Option<&OsStr>,
    path_env: Option<&OsStr>,
    _target_dir_env: Option<&OsStr>,
    cargo_home_env: Option<&OsStr>,
    home_env: Option<&OsStr>,
    rustup_home_env: Option<&OsStr>,
    rustup_toolchain_env: Option<&OsStr>,
    cargo_net_offline_env: Option<&OsStr>,
    tmpdir_env: Option<&OsStr>,
    store_prefix: &Path,
) -> Result<PreparedMirEval, String> {
    let validated_tmpdir = validate_optional_existing_dir_env(tmpdir_env, caller_cwd, "TMPDIR")?;
    let prepared_src = prepare_mir_eval_source_graph(
        manifest_path,
        caller_cwd,
        validated_tmpdir.as_deref(),
        store_prefix,
    )?;
    let cargo_home_override = cargo_home_env.filter(|v| !v.is_empty()).map(PathBuf::from);
    let home_override = home_env.filter(|v| !v.is_empty()).map(PathBuf::from);
    let (pinned_cargo_home, validated_home) = reject_and_pin_ambient_cargo_configs(
        &prepared_src.canon_orig_work_dir,
        &prepared_src.default_target_roots,
        cargo_home_override.as_deref(),
        home_override.as_deref(),
        caller_cwd,
        validated_tmpdir.as_deref(),
        store_prefix,
        &prepared_src.locked_registry_crates,
    )?;
    let validated_rustup_home =
        validate_optional_dir_env(rustup_home_env, caller_cwd, "RUSTUP_HOME")?;
    let pinned_rustup = pin_rustup_settings(
        validated_rustup_home.as_deref(),
        validated_home.as_deref(),
        rustup_toolchain_env,
        &prepared_src.canon_orig_work_dir,
        validated_tmpdir.as_deref(),
    )?;

    let mut cand_cargo =
        resolve_cargo_executable_with_store(cargo_env, path_env, caller_cwd, store_prefix)?;
    let cargo_tool = if cand_cargo.is_rustup_proxy {
        resolve_rustup_proxy_binary_opened_with_store(
            &cand_cargo.path,
            cand_cargo.opened.as_mut(),
            "cargo",
            caller_cwd,
            &prepared_src.staged_work_dir,
            validated_home.as_deref(),
            &pinned_rustup,
            validated_tmpdir.as_deref(),
            store_prefix,
        )?
    } else {
        cand_cargo
    };

    let mut cand_rustc =
        resolve_rustc_executable_with_store(rustc_env, path_env, caller_cwd, store_prefix)?;
    let rustc_tool = if cand_rustc.is_rustup_proxy {
        resolve_rustup_proxy_binary_opened_with_store(
            &cand_rustc.path,
            cand_rustc.opened.as_mut(),
            "rustc",
            caller_cwd,
            &prepared_src.staged_work_dir,
            validated_home.as_deref(),
            &pinned_rustup,
            validated_tmpdir.as_deref(),
            store_prefix,
        )?
    } else {
        cand_rustc
    };

    let toolchain = resolve_leg3_pinned_toolchain_opened_with_store(
        rustc_tool,
        cargo_tool,
        path_env,
        caller_cwd,
        &prepared_src.staged_work_dir,
        validated_home.as_deref(),
        Some(&pinned_cargo_home.cargo_home),
        validated_tmpdir.as_deref(),
        store_prefix,
    )?;

    // Build inside an empty private `0o700` dir so stale `CARGO_TARGET_DIR`
    // or workspace `target/` fingerprints cannot bypass source compilation.
    let build_td_guard = build_temp_dir("anneal-mir-eval-target-", validated_tmpdir.as_deref())?;
    let canon_build_td =
        validate_dir_path_no_symlinks(build_td_guard.path(), &prepared_src.canon_orig_work_dir)?;

    let linker_cfg = format!(
        "target.{}.linker={}",
        toolchain.host_triple,
        toml::Value::String(toolchain.linker.to_string_lossy().into_owned())
    );
    let mut inv = Invocation::new(
        &toolchain.pinned_cargo,
        &[
            "build",
            "--locked",
            "--bin",
            "anneal-mir-eval",
            "--message-format=json",
            "--config",
            "build.rustc-wrapper=\"\"",
            "--config",
            "build.rustc-workspace-wrapper=\"\"",
        ],
    )
    .arg("--config")
    .arg(&linker_cfg)
    .arg("--manifest-path")
    .arg(&prepared_src.staged_manifest)
    .arg("--target-dir")
    .arg(&canon_build_td)
    .env("CARGO_TARGET_DIR", &canon_build_td)
    .env("PATH", &toolchain.child_path)
    .env("RUSTC", &toolchain.pinned_rustc)
    .env("CARGO_HOME", &pinned_cargo_home.cargo_home);
    if !toolchain.ld_library_path.is_empty() {
        inv = inv.env("LD_LIBRARY_PATH", &toolchain.ld_library_path);
    }
    if let Some(val) = cargo_net_offline_env.filter(|v| !v.is_empty()) {
        inv = inv.env("CARGO_NET_OFFLINE", val);
    }
    if let Some(td) = &validated_tmpdir {
        inv = inv.env("TMPDIR", td);
    }
    if let Some(h) = &validated_home {
        inv = inv.env("HOME", h);
    }

    let log_dir = build_temp_dir("anneal-mir-eval-log-", validated_tmpdir.as_deref())?;
    let log_root = fs::canonicalize(log_dir.path())
        .map_err(|e| format!("canonicalize mir-eval build log dir: {e}"))?;
    let timeout = effective_timeout_secs(MIR_EVAL_BUILD_TIMEOUT_SECS)?;
    let supervisor = ProcessSupervisor::new(Duration::from_secs(timeout))?;
    let out =
        supervisor.run(&inv, &prepared_src.staged_work_dir, &log_root.join("log"), &log_root)?;
    match out.termination {
        Termination::Exited(s) if s.success() => {}
        other => {
            return Err(format!(
                "building --mir-eval-manifest {} failed ({}): {}",
                prepared_src.canon_orig_manifest.display(),
                other.describe(),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
    }

    let stdout_text = String::from_utf8_lossy(&out.stdout);
    let extracted = extract_built_executable_with_staging(
        &stdout_text,
        "anneal-mir-eval",
        &prepared_src.staged_manifest,
        prepared_src.staging.as_deref(),
    )?;
    let opened_bin = crate::rustc_runner::open_verified_executable_via_dirfd(
        &extracted,
        &canon_build_td,
        false,
        "built anneal-mir-eval",
    )?;
    if !opened_bin.canon_path.starts_with(&canon_build_td) {
        return Err(format!(
            "built anneal-mir-eval escaped expected private Cargo target directory: {}",
            opened_bin.canon_path.display()
        ));
    }
    materialize_cargo_built_opened_executable(
        opened_bin,
        "anneal-mir-eval",
        validated_tmpdir.as_deref(),
    )
}

fn build_eval_args_raw(
    capture_json: &Path,
    body_id: usize,
    arg_vals: &[MirValue],
    fuel: usize,
) -> Result<Vec<OsString>, String> {
    let mut args = vec![
        OsString::from("eval"),
        capture_json.as_os_str().to_os_string(),
        OsString::from("--body"),
        OsString::from(body_id.to_string()),
        OsString::from("--fuel"),
        OsString::from(fuel.to_string()),
        OsString::from("--json"),
    ];
    for arg in arg_vals {
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
    run_mir_eval_raw(mir_eval_bin, capture_json, body_id, &case.args, case.fuel)
}

pub(crate) fn run_prepared_mir_eval_case(
    prepared: &PreparedMirEval,
    capture_json: &Path,
    body_id: usize,
    case: &LitmusCase,
) -> ObservedOutcome {
    run_mir_eval_raw_with_identity(
        &prepared.exec_path,
        false,
        capture_json,
        (body_id, None),
        &case.args,
        case.fuel,
        None,
    )
    .0
}

/// Execute `anneal-mir-eval eval` for an arbitrary captured body ID, argument
/// vector, and fuel budget (shared by Stage-1 and Stage-2 fuzzing).
pub fn run_mir_eval_raw(
    mir_eval_bin: &Path,
    capture_json: &Path,
    body_id: usize,
    args_vals: &[MirValue],
    fuel: usize,
) -> ObservedOutcome {
    run_mir_eval_raw_until(mir_eval_bin, capture_json, body_id, args_vals, fuel, None)
}

/// Deadline-clamped variant of [`run_mir_eval_raw`] used during shrinking.
pub fn run_mir_eval_raw_until(
    mir_eval_bin: &Path,
    capture_json: &Path,
    body_id: usize,
    args_vals: &[MirValue],
    fuel: usize,
    deadline: Option<Instant>,
) -> ObservedOutcome {
    run_mir_eval_raw_classified(mir_eval_bin, capture_json, body_id, args_vals, fuel, deadline).0
}

/// Execute `anneal-mir-eval eval` with optional deadline clamping, returning
/// `(outcome, is_global_infra_failure)` so batch callers can short-circuit on
/// binary-resolution failures, launch failures, timeouts, or deadline
/// exhaustion instead of serializing repeated per-case timeouts.
pub fn run_mir_eval_raw_classified(
    mir_eval_bin: &Path,
    capture_json: &Path,
    body_id: usize,
    args_vals: &[MirValue],
    fuel: usize,
    deadline: Option<Instant>,
) -> (ObservedOutcome, bool) {
    let (outcome, _ev, is_global) = run_mir_eval_raw_with_identity(
        mir_eval_bin,
        true,
        capture_json,
        (body_id, None),
        args_vals,
        fuel,
        deadline,
    );
    (outcome, is_global)
}

/// Execute `anneal-mir-eval eval` with optional deadline clamping, validating
/// that the emitted JSON `StepTrace` matches both elements of `expected_body`
/// and returning `(outcome, evidence, is_global_infra_failure)`.
pub fn run_mir_eval_raw_with_evidence(
    mir_eval_bin: &Path,
    capture_json: &Path,
    expected_body: (usize, &str),
    args_vals: &[MirValue],
    fuel: usize,
    deadline: Option<Instant>,
) -> (ObservedOutcome, Option<(usize, String)>, bool) {
    run_mir_eval_raw_with_identity(
        mir_eval_bin,
        true,
        capture_json,
        (expected_body.0, Some(expected_body.1)),
        args_vals,
        fuel,
        deadline,
    )
}

pub(crate) fn run_pinned_mir_eval_raw_with_evidence(
    pinned_exec_bin: &Path,
    capture_json: &Path,
    expected_body: (usize, &str),
    args_vals: &[MirValue],
    fuel: usize,
    deadline: Option<Instant>,
) -> (ObservedOutcome, Option<(usize, String)>, bool) {
    run_mir_eval_raw_with_identity(
        pinned_exec_bin,
        false,
        capture_json,
        (expected_body.0, Some(expected_body.1)),
        args_vals,
        fuel,
        deadline,
    )
}

fn run_mir_eval_raw_with_identity(
    mir_eval_bin: &Path,
    validate_unpinned: bool,
    capture_json: &Path,
    (body_id, expected_identity): (usize, Option<&str>),
    args_vals: &[MirValue],
    fuel: usize,
    deadline: Option<Instant>,
) -> (ObservedOutcome, Option<(usize, String)>, bool) {
    let canon_bin = if validate_unpinned {
        match validate_mir_eval_bin_no_links(mir_eval_bin) {
            Ok(path) => path,
            Err(detail) => return (ObservedOutcome::ToolError { detail }, None, true),
        }
    } else {
        mir_eval_bin.to_path_buf()
    };

    let args = match build_eval_args_raw(capture_json, body_id, args_vals, fuel) {
        Ok(args) => args,
        Err(detail) => return (ObservedOutcome::ToolError { detail }, None, false),
    };
    let mut inv = Invocation::new(canon_bin, &[]);
    for arg in args {
        inv = inv.arg(arg);
    }

    let child_path = match crate::lean_runner::validated_system_child_path() {
        Ok(p) => p,
        Err(detail) => return (ObservedOutcome::ToolError { detail }, None, true),
    };
    inv = inv.env("PATH", child_path);

    let caller_cwd = match env::current_dir() {
        Ok(d) => d,
        Err(e) => {
            return (
                ObservedOutcome::ToolError {
                    detail: format!("resolve current working directory: {e}"),
                },
                None,
                true,
            );
        }
    };
    let validated_tmpdir = match validate_optional_existing_dir_env(
        env::var_os("TMPDIR").as_deref(),
        &caller_cwd,
        "TMPDIR",
    ) {
        Ok(td) => td,
        Err(detail) => return (ObservedOutcome::ToolError { detail }, None, true),
    };

    let tmp_dir = match build_temp_dir("anneal-mir-eval-log-", validated_tmpdir.as_deref()) {
        Ok(d) => d,
        Err(e) => {
            return (
                ObservedOutcome::ToolError {
                    detail: format!("create anneal-mir-eval log dir: {e}"),
                },
                None,
                true,
            );
        }
    };
    let work_root = match fs::canonicalize(tmp_dir.path()) {
        Ok(p) => p,
        Err(e) => {
            return (
                ObservedOutcome::ToolError {
                    detail: format!("canonicalize anneal-mir-eval work dir: {e}"),
                },
                None,
                true,
            );
        }
    };

    let timeout = match effective_timeout_duration(MIR_EVAL_TIMEOUT_SECS, deadline) {
        Ok(dur) => dur,
        Err(detail) => return (ObservedOutcome::ToolError { detail }, None, true),
    };
    let supervisor = match ProcessSupervisor::new(timeout) {
        Ok(s) => s,
        Err(detail) => return (ObservedOutcome::ToolError { detail }, None, true),
    };
    let out = match supervisor.run(&inv, &work_root, &work_root.join("log"), &work_root) {
        Ok(o) => o,
        Err(detail) => return (ObservedOutcome::ToolError { detail }, None, true),
    };

    let code = match out.termination {
        Termination::Exited(status) => status.code(),
        Termination::TimedOut(status) => {
            return (
                ObservedOutcome::ToolError {
                    detail: format!(
                        "anneal-mir-eval timed out after {:.3}s ({status})",
                        timeout.as_secs_f64()
                    ),
                },
                None,
                true,
            );
        }
        Termination::LaunchFailed(err) => {
            return (
                ObservedOutcome::ToolError {
                    detail: format!("spawn {}: {err}", mir_eval_bin.display()),
                },
                None,
                true,
            );
        }
    };

    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    let expected = expected_identity.map(|ident| (body_id, ident));
    let (outcome, emitted_id) = parse_mir_eval_output_with_body(code, &stdout, &stderr, expected);
    let evidence = match (outcome.clone(), emitted_id) {
        (ObservedOutcome::ToolError { .. }, _) | (_, None) => None,
        (_, Some(bid)) => Some((bid, stdout.trim().to_owned())),
    };
    (outcome, evidence, false)
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
    #[serde(default)]
    body_id: Option<usize>,
    #[serde(default)]
    identity: Option<String>,
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
    parse_mir_eval_output_with_body(exit_code, stdout, stderr, None).0
}

/// Parse `anneal-mir-eval eval --json` output into `(outcome, body_id)`,
/// optionally validating that the trace's top-level `body_id` and `identity`
/// match `expected_body`.
pub fn parse_mir_eval_output_with_body(
    exit_code: Option<i32>,
    stdout: &str,
    stderr: &str,
    expected_body: Option<(usize, &str)>,
) -> (ObservedOutcome, Option<usize>) {
    if !matches!(exit_code, Some(0 | 2 | 3 | 4)) {
        return (
            ObservedOutcome::ToolError {
                detail: format!("anneal-mir-eval failed (exit {exit_code:?}): {}", stderr.trim()),
            },
            None,
        );
    }

    let trace: RawStepTrace = match serde_json::from_str(stdout) {
        Ok(parsed) => parsed,
        Err(e) => {
            return (
                ObservedOutcome::ToolError { detail: format!("parse anneal-mir-eval JSON: {e}") },
                None,
            );
        }
    };

    if let Some((exp_id, exp_ident)) = expected_body
        && (trace.body_id != Some(exp_id) || trace.identity.as_deref() != Some(exp_ident))
    {
        return (
            ObservedOutcome::ToolError {
                detail: format!(
                    "anneal-mir-eval body identity mismatch: expected ({exp_id}, {exp_ident:?}), got ({:?}, {:?})",
                    trace.body_id, trace.identity
                ),
            },
            None,
        );
    }

    let outcome = match trace.outcome {
        RawOutcome::Returned(RawTerminalOut::Returned { ret }) => {
            if exit_code != Some(0) {
                return (
                    ObservedOutcome::ToolError {
                        detail: format!(
                            "anneal-mir-eval protocol mismatch: Returned JSON with exit code {exit_code:?}"
                        ),
                    },
                    None,
                );
            }
            match convert_val(ret) {
                Ok(value) => ObservedOutcome::Returned { value },
                Err(detail) => ObservedOutcome::ToolError { detail },
            }
        }
        RawOutcome::Returned(RawTerminalOut::Unwound {}) => {
            if exit_code != Some(0) {
                return (
                    ObservedOutcome::ToolError {
                        detail: format!(
                            "anneal-mir-eval protocol mismatch: Unwound JSON with exit code {exit_code:?}"
                        ),
                    },
                    None,
                );
            }
            ObservedOutcome::Unwound { detail: "anneal-mir-eval unwound".to_owned() }
        }
        RawOutcome::Aborted {} => {
            if exit_code != Some(4) {
                return (
                    ObservedOutcome::ToolError {
                        detail: format!(
                            "anneal-mir-eval protocol mismatch: Aborted JSON with exit code {exit_code:?} (expected 4)"
                        ),
                    },
                    None,
                );
            }
            ObservedOutcome::AbnormalAbort {
                detail: "anneal-mir-eval aborted (UnwindAction::Terminate)".to_owned(),
            }
        }
        RawOutcome::Fault(f) => match f.kind.as_str() {
            "undefined" => {
                if exit_code != Some(2) {
                    return (
                        ObservedOutcome::ToolError {
                            detail: format!(
                                "anneal-mir-eval protocol mismatch: undefined JSON with exit code {exit_code:?} (expected 2)"
                            ),
                        },
                        None,
                    );
                }
                ObservedOutcome::UndefinedBehavior { detail: f.reason }
            }
            "unsupported" => {
                if exit_code != Some(3) {
                    return (
                        ObservedOutcome::ToolError {
                            detail: format!(
                                "anneal-mir-eval protocol mismatch: unsupported JSON with exit code {exit_code:?} (expected 3)"
                            ),
                        },
                        None,
                    );
                }
                ObservedOutcome::Unsupported { detail: f.reason }
            }
            other => ObservedOutcome::ToolError {
                detail: format!("unknown anneal-mir-eval fault kind {other:?}: {}", f.reason),
            },
        },
        RawOutcome::OutOfFuel => {
            if exit_code != Some(3) {
                return (
                    ObservedOutcome::ToolError {
                        detail: format!(
                            "anneal-mir-eval protocol mismatch: out_of_fuel JSON with exit code {exit_code:?} (expected 3)"
                        ),
                    },
                    None,
                );
            }
            ObservedOutcome::OutOfFuel { detail: "anneal-mir-eval hit fuel limit".to_owned() }
        }
    };
    let emitted_id =
        if matches!(outcome, ObservedOutcome::ToolError { .. }) { None } else { trace.body_id };
    (outcome, emitted_id)
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
        assert_eq!(
            parse_mir_eval_output_with_body(Some(0), ret_json, "", Some((0, "rust-path-v1::demo"))),
            (
                ObservedOutcome::Returned {
                    value: MirValue::Int { int_kind: IntKind::U32, bits: 42 }
                },
                Some(0),
            )
        );
        for wrong_expected in [(1, "rust-path-v1::demo"), (0, "rust-path-v1::other")] {
            let (out, bid) =
                parse_mir_eval_output_with_body(Some(0), ret_json, "", Some(wrong_expected));
            assert!(
                matches!(out, ObservedOutcome::ToolError { ref detail } if detail.contains("body identity mismatch")),
                "expected body identity mismatch for {wrong_expected:?}, got {out:?}"
            );
            assert_eq!(bid, None);
        }
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
        assert_eq!(
            parse_mir_eval_output_with_body(Some(0), ovf_json, "", Some((0, "rust-path-v1::demo")))
                .1,
            None,
            "trace missing body_id/identity must fail closed when identity is required"
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
        let args =
            build_eval_args_raw(Path::new("/tmp/cap.json"), 7, &case.args, case.fuel).unwrap();
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

    #[test]
    fn extract_built_executable_supports_virtual_workspace_and_fails_closed() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let vws_manifest = root.join("Cargo.toml");
        fs::write(
            &vws_manifest,
            "[workspace]\nresolver = \"2\"\nmembers = [\"tools/*\", \"tools/excluded_group/*\"]\nexclude = [\"tools/excluded\", \"tools/excluded_group\"]\n",
        )
        .unwrap();
        let member_dir = root.join("tools/anneal-mir-eval");
        fs::create_dir_all(&member_dir).unwrap();
        let member_manifest = member_dir.join("Cargo.toml");
        fs::write(&member_manifest, "[package]\nname = \"anneal-mir-eval\"\n").unwrap();

        let excl_dir = root.join("tools/excluded");
        fs::create_dir_all(&excl_dir).unwrap();
        let excl_manifest = excl_dir.join("Cargo.toml");
        fs::write(&excl_manifest, "[package]\nname = \"anneal-mir-eval\"\n").unwrap();

        let other_dir = root.join("tools/other");
        fs::create_dir_all(&other_dir).unwrap();
        let other_manifest = other_dir.join("Cargo.toml");
        fs::write(&other_manifest, "[package]\nname = \"other\"\n").unwrap();

        let exe_path = root.join("target/debug/anneal-mir-eval");
        let member_line = serde_json::json!({
            "reason": "compiler-artifact",
            "manifest_path": member_manifest,
            "target": { "kind": ["bin"], "name": "anneal-mir-eval" },
            "profile": { "test": false },
            "executable": exe_path,
        })
        .to_string();

        assert_eq!(
            extract_built_executable(&member_line, "anneal-mir-eval", &vws_manifest).unwrap(),
            exe_path
        );
        assert_eq!(
            extract_built_executable(&member_line, "anneal-mir-eval", &member_manifest).unwrap(),
            exe_path
        );
        assert!(extract_built_executable("", "anneal-mir-eval", &member_manifest).is_err());

        let excl_line = serde_json::json!({
            "reason": "compiler-artifact",
            "manifest_path": excl_manifest,
            "target": { "kind": ["bin"], "name": "anneal-mir-eval" },
            "profile": { "test": false },
            "executable": exe_path,
        })
        .to_string();
        assert!(extract_built_executable(&excl_line, "anneal-mir-eval", &vws_manifest).is_err());

        // Excluded parent directory without its own `Cargo.toml` must still
        // exclude descendant member crates (`tools/excluded_group/nested`).
        let nested_excl_dir = root.join("tools/excluded_group/nested");
        fs::create_dir_all(&nested_excl_dir).unwrap();
        let nested_excl_manifest = nested_excl_dir.join("Cargo.toml");
        fs::write(&nested_excl_manifest, "[package]\nname = \"anneal-mir-eval\"\n").unwrap();
        let nested_excl_line = serde_json::json!({
            "reason": "compiler-artifact",
            "manifest_path": nested_excl_manifest,
            "target": { "kind": ["bin"], "name": "anneal-mir-eval" },
            "profile": { "test": false },
            "executable": exe_path,
        })
        .to_string();
        assert!(
            extract_built_executable(&nested_excl_line, "anneal-mir-eval", &vws_manifest).is_err()
        );

        let conflict_stdout = format!(
            "{member_line}\n{}",
            serde_json::json!({
                "reason": "compiler-artifact",
                "manifest_path": other_manifest,
                "target": { "kind": ["bin"], "name": "anneal-mir-eval" },
                "profile": { "test": false },
                "executable": root.join("target/debug/other-bin"),
            })
        );
        assert!(
            extract_built_executable(&conflict_stdout, "anneal-mir-eval", &vws_manifest).is_err()
        );
    }

    #[test]
    fn extract_built_executable_supports_nonvirtual_default_members_and_fails_closed() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let root_manifest = root.join("Cargo.toml");
        let member_dir = root.join("tools/anneal-mir-eval");
        fs::create_dir_all(&member_dir).unwrap();
        let member_manifest = member_dir.join("Cargo.toml");
        fs::write(&member_manifest, "[package]\nname = \"anneal-mir-eval\"\n").unwrap();

        let other_dir = root.join("tools/other");
        fs::create_dir_all(&other_dir).unwrap();
        let other_manifest = other_dir.join("Cargo.toml");
        fs::write(&other_manifest, "[package]\nname = \"other\"\n").unwrap();

        let excl_dir = root.join("tools/excluded");
        fs::create_dir_all(&excl_dir).unwrap();
        let excl_manifest = excl_dir.join("Cargo.toml");
        fs::write(&excl_manifest, "[package]\nname = \"excluded\"\n").unwrap();

        let exe_path = root.join("target/debug/anneal-mir-eval");
        let make_line = |manifest: &Path| {
            serde_json::json!({
                "reason": "compiler-artifact",
                "manifest_path": manifest,
                "target": { "kind": ["bin"], "name": "anneal-mir-eval" },
                "profile": { "test": false },
                "executable": exe_path,
            })
            .to_string()
        };

        // Package + workspace with explicit `default-members` accepts selected
        // members while rejecting unselected, excluded, and omitted root `"."`.
        fs::write(
            &root_manifest,
            "[package]\nname = \"root\"\n\
             [workspace]\nmembers = [\"tools/*\"]\n\
             exclude = [\"tools/excluded\"]\n\
             default-members = [\"tools/anneal-mir-eval\"]\n",
        )
        .unwrap();
        assert_eq!(
            extract_built_executable(
                &make_line(&member_manifest),
                "anneal-mir-eval",
                &root_manifest
            )
            .unwrap(),
            exe_path
        );
        assert!(
            extract_built_executable(
                &make_line(&other_manifest),
                "anneal-mir-eval",
                &root_manifest
            )
            .is_err()
        );
        assert!(
            extract_built_executable(&make_line(&excl_manifest), "anneal-mir-eval", &root_manifest)
                .is_err()
        );
        assert!(
            extract_built_executable(&make_line(&root_manifest), "anneal-mir-eval", &root_manifest)
                .is_err()
        );

        // Listing `"."` alongside a member accepts both root and member crates.
        fs::write(
            &root_manifest,
            "[package]\nname = \"root\"\n\
             [workspace]\nmembers = [\"tools/*\"]\n\
             default-members = [\".\", \"tools/anneal-mir-eval\"]\n",
        )
        .unwrap();
        assert_eq!(
            extract_built_executable(&make_line(&root_manifest), "anneal-mir-eval", &root_manifest)
                .unwrap(),
            exe_path
        );
        assert_eq!(
            extract_built_executable(
                &make_line(&member_manifest),
                "anneal-mir-eval",
                &root_manifest
            )
            .unwrap(),
            exe_path
        );

        // Package + workspace without `default-members` targets root only.
        fs::write(
            &root_manifest,
            "[package]\nname = \"root\"\n[workspace]\nmembers = [\"tools/*\"]\n",
        )
        .unwrap();
        assert_eq!(
            extract_built_executable(&make_line(&root_manifest), "anneal-mir-eval", &root_manifest)
                .unwrap(),
            exe_path
        );
        assert!(
            extract_built_executable(
                &make_line(&member_manifest),
                "anneal-mir-eval",
                &root_manifest
            )
            .is_err()
        );

        // Empty `default-members` rejects both root and member artifacts.
        fs::write(
            &root_manifest,
            "[package]\nname = \"root\"\n[workspace]\nmembers = [\"tools/*\"]\ndefault-members = []\n",
        )
        .unwrap();
        assert!(
            extract_built_executable(&make_line(&root_manifest), "anneal-mir-eval", &root_manifest)
                .is_err()
        );
        assert!(
            extract_built_executable(
                &make_line(&member_manifest),
                "anneal-mir-eval",
                &root_manifest
            )
            .is_err()
        );
    }

    #[test]
    fn manifest_ancestor_symlinks_rejected_and_path_cargo_anchored_to_caller() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let anneal_cwd = root.join("anneal");
        let real_eval_dir = root.join("tools/anneal-mir-eval");
        fs::create_dir_all(&anneal_cwd).expect("mkdir anneal");
        fs::create_dir_all(&real_eval_dir).expect("mkdir eval");
        let real_manifest = real_eval_dir.join("Cargo.toml");
        fs::write(&real_manifest, "[package]\nname = \"anneal-mir-eval\"\n").unwrap();

        // Parent-directory traversal segments (`..`) must fail closed across
        // all file, dir, uncreated-dir, and CARGO_TARGET_DIR validators.
        let trav_err = validate_manifest_path_no_links(
            Path::new("../tools/anneal-mir-eval/Cargo.toml"),
            &anneal_cwd,
        )
        .unwrap_err();
        assert!(trav_err.contains(".."), "{trav_err}");
        let sub_trav = validate_file_path_no_symlinks(
            Path::new("sub/../tools/anneal-mir-eval/Cargo.toml"),
            &root,
            "capture artifact",
        )
        .unwrap_err();
        assert!(sub_trav.contains(".."), "{sub_trav}");
        assert!(validate_dir_path_no_symlinks(Path::new("../tools"), &anneal_cwd).is_err());
        assert!(
            validate_dir_or_uncreated_path_no_symlinks(
                Path::new("sub/../fresh"),
                &anneal_cwd,
                "--cache-root"
            )
            .is_err()
        );
        assert!(
            validate_dir_ancestors_no_symlinks(&anneal_cwd.join("../target"), "CARGO_TARGET_DIR")
                .is_err()
        );

        #[cfg(unix)]
        {
            use std::os::unix::fs::symlink;

            let sym_dir = anneal_cwd.join("link");
            symlink(&real_eval_dir, &sym_dir).unwrap();

            // `link/Cargo.toml` and `/abs/link/Cargo.toml` must fail closed.
            let rel_err =
                validate_manifest_path_no_links(Path::new("link/Cargo.toml"), &anneal_cwd)
                    .unwrap_err();
            assert!(rel_err.contains("symlink"), "{rel_err}");
            let abs_err =
                validate_manifest_path_no_links(&sym_dir.join("Cargo.toml"), &root).unwrap_err();
            assert!(abs_err.contains("symlink"), "{abs_err}");

            // `link/../anneal-mir-eval/Cargo.toml` must also fail closed.
            assert!(
                validate_manifest_path_no_links(
                    Path::new("link/../anneal-mir-eval/Cargo.toml"),
                    &anneal_cwd,
                )
                .is_err()
            );

            // Hardlinked `--mir-eval-manifest`, `compiler-artifact`
            // `manifest_path`, and `--mir-eval-bin` inputs must fail closed
            // (`nlink > 1`).
            let hard_manifest = root.join("hard-Cargo.toml");
            fs::hard_link(&real_manifest, &hard_manifest).unwrap();
            let err_hard_manifest =
                validate_manifest_path_no_links(&hard_manifest, &root).unwrap_err();
            assert!(err_hard_manifest.contains("hardlink"), "{err_hard_manifest}");
            fs::remove_file(&hard_manifest).unwrap();

            // `--mir-eval-bin` must likewise reject parent traversal (`..`),
            // binaries beneath symlinked dirs, and hardlinks (`nlink > 1`).
            let real_bin = real_eval_dir.join("anneal-mir-eval");
            fs::write(&real_bin, "#!/bin/sh\nexit 0\n").unwrap();
            assert!(
                validate_executable_no_links(
                    Path::new("../tools/anneal-mir-eval/anneal-mir-eval"),
                    &anneal_cwd,
                    "--mir-eval-bin",
                )
                .is_err()
            );
            assert!(
                validate_executable_no_links(
                    Path::new("link/../anneal-mir-eval/anneal-mir-eval"),
                    &anneal_cwd,
                    "--mir-eval-bin",
                )
                .is_err()
            );

            for bad_bin in [PathBuf::from("link/anneal-mir-eval"), sym_dir.join("anneal-mir-eval")]
            {
                let err = validate_executable_no_links(&bad_bin, &anneal_cwd, "--mir-eval-bin")
                    .unwrap_err();
                assert!(err.contains("symlink"), "{err}");
            }
            let hard_bin = root.join("hard-anneal-mir-eval");
            fs::hard_link(&real_bin, &hard_bin).unwrap();
            let hard_bin_err =
                validate_executable_no_links(&hard_bin, &root, "--mir-eval-bin").unwrap_err();
            assert!(hard_bin_err.contains("hardlink"), "{hard_bin_err}");
            let (hard_out, hard_global) =
                run_mir_eval_raw_classified(&hard_bin, &real_manifest, 0, &[], 64, None);
            assert!(hard_global);
            assert!(
                matches!(hard_out, ObservedOutcome::ToolError { detail } if detail.contains("hardlink"))
            );
            fs::remove_file(&hard_bin).unwrap();

            let (out, global_fail) = run_mir_eval_raw_classified(
                &sym_dir.join("anneal-mir-eval"),
                &real_manifest,
                0,
                &[],
                64,
                None,
            );
            assert!(global_fail);
            assert!(
                matches!(out, ObservedOutcome::ToolError { detail } if detail.contains("symlink"))
            );

            // Built artifact paths beneath a symlinked `CARGO_TARGET_DIR` (and
            // `CARGO_TARGET_DIR` itself) must also fail closed before
            // canonicalization.
            let real_target_debug = root.join("real-target/debug");
            fs::create_dir_all(&real_target_debug).unwrap();
            let built_leaf = real_target_debug.join("anneal-mir-eval");
            fs::write(&built_leaf, "#!/bin/sh\nexit 0\n").unwrap();
            let sym_target = anneal_cwd.join("sym-target");
            symlink(root.join("real-target"), &sym_target).unwrap();
            assert!(validate_dir_ancestors_no_symlinks(&sym_target, "CARGO_TARGET_DIR").is_err());
            assert!(
                validate_dir_ancestors_no_symlinks(
                    &anneal_cwd.join("fresh-target/nested"),
                    "CARGO_TARGET_DIR"
                )
                .is_ok()
            );
            let built_err = validate_file_path_no_symlinks(
                &sym_target.join("debug/anneal-mir-eval"),
                &real_eval_dir,
                "built anneal-mir-eval",
            )
            .unwrap_err();
            assert!(built_err.contains("symlink"), "{built_err}");
        }

        // Relative path-valued `CARGO` anchors against `caller_cwd`.
        let tc_bin = anneal_cwd.join("toolchain/bin");
        fs::create_dir_all(&tc_bin).unwrap();
        let fake_cargo = tc_bin.join("cargo");
        fs::write(&fake_cargo, "#!/bin/sh\n").unwrap();
        let resolved_rel = resolve_cargo_executable(
            Some(std::ffi::OsStr::new("./toolchain/bin/cargo")),
            None,
            &anneal_cwd,
        )
        .expect("resolve relative CARGO with separator");
        assert_eq!(resolved_rel, fake_cargo);

        let resolved_sub = resolve_cargo_executable(
            Some(std::ffi::OsStr::new("toolchain/bin/cargo")),
            None,
            &anneal_cwd,
        )
        .expect("resolve relative subdir CARGO");
        assert_eq!(resolved_sub, fake_cargo);

        assert!(
            resolve_cargo_executable(
                Some(std::ffi::OsStr::new("./toolchain/bin/missing")),
                Some(tc_bin.as_os_str()),
                &anneal_cwd,
            )
            .is_err()
        );

        let resolved_bare =
            resolve_cargo_executable(None, Some(tc_bin.as_os_str()), &anneal_cwd).unwrap();
        assert_eq!(resolved_bare, fake_cargo);

        #[cfg(unix)]
        {
            use std::os::unix::fs::symlink;

            let sym_cargo = anneal_cwd.join("sym-cargo");
            symlink(&fake_cargo, &sym_cargo).unwrap();
            let err_sym_file = resolve_cargo_executable(
                Some(std::ffi::OsStr::new("./sym-cargo")),
                None,
                &anneal_cwd,
            )
            .unwrap_err();
            assert!(err_sym_file.contains("symlink"), "{err_sym_file}");

            let sym_tc_dir = anneal_cwd.join("sym-tc-bin");
            symlink(&tc_bin, &sym_tc_dir).unwrap();
            let err_sym_dir = resolve_cargo_executable(
                Some(std::ffi::OsStr::new("sym-tc-bin/cargo")),
                None,
                &anneal_cwd,
            )
            .unwrap_err();
            assert!(err_sym_dir.contains("symlink"), "{err_sym_dir}");

            let err_path_dir =
                resolve_cargo_executable(None, Some(sym_tc_dir.as_os_str()), &anneal_cwd)
                    .unwrap_err();
            assert!(err_path_dir.contains("symlink"), "{err_path_dir}");

            let sym_leaf_dir = anneal_cwd.join("sym-leaf-bin");
            fs::create_dir_all(&sym_leaf_dir).unwrap();
            symlink(&fake_cargo, sym_leaf_dir.join("cargo")).unwrap();
            let err_path_leaf =
                resolve_cargo_executable(None, Some(sym_leaf_dir.as_os_str()), &anneal_cwd)
                    .unwrap_err();
            assert!(err_path_leaf.contains("symlink"), "{err_path_leaf}");

            // Unset `CARGO` supports standard `rustup` sibling proxy
            // `cargo -> rustup` in a real dir, while explicit `CARGO=cargo`
            // still rejects symlinks fail-closed.
            let rustup_dir = anneal_cwd.join("rustup-bin");
            fs::create_dir_all(&rustup_dir).unwrap();
            fs::write(rustup_dir.join("rustup"), "#!/bin/sh\n").unwrap();
            symlink("rustup", rustup_dir.join("cargo")).unwrap();
            let ok_rustup =
                resolve_cargo_executable(None, Some(rustup_dir.as_os_str()), &anneal_cwd)
                    .expect("unset CARGO permits verified sibling rustup proxy");
            assert_eq!(ok_rustup, rustup_dir.join("cargo"));
            let err_explicit_bare = resolve_cargo_executable(
                Some(std::ffi::OsStr::new("cargo")),
                Some(rustup_dir.as_os_str()),
                &anneal_cwd,
            )
            .unwrap_err();
            assert!(err_explicit_bare.contains("symlink"), "{err_explicit_bare}");
        }
    }

    #[cfg(unix)]
    #[test]
    fn build_mir_eval_from_manifest_rejects_poisoned_default_target_and_uncontained_exe() {
        use std::os::unix::fs::{MetadataExt, PermissionsExt, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let ws_root = root.join("ws");
        let eval_dir = ws_root.join("tools/anneal-mir-eval");
        let ext_dir = root.join("external/debug");
        fs::create_dir_all(&eval_dir).unwrap();
        fs::create_dir_all(&ext_dir).unwrap();
        fs::write(
            ws_root.join("Cargo.toml"),
            "[workspace]\nmembers = [\"tools/anneal-mir-eval\"]\n",
        )
        .unwrap();
        let manifest = eval_dir.join("Cargo.toml");
        fs::write(&manifest, "[package]\nname = \"anneal-mir-eval\"\n").unwrap();

        let ext_bin = ext_dir.join("anneal-mir-eval");
        fs::write(&ext_bin, "#!/bin/sh\nexit 0\n").unwrap();
        let sentinel = root.join("cargo-invoked");
        let args_log = root.join("cargo-args.txt");
        let env_log = root.join("cargo-env.txt");
        let fake_cargo = root.join("fake-cargo.sh");
        fs::write(
            &fake_cargo,
            format!(
                "#!/bin/sh\ntouch '{}'\nprintf '%s\\n' \"$*\" > '{}'\n\
                 mp=\"\"\nprev=\"\"\n\
                 for a in \"$@\"; do\n  if [ \"$prev\" = \"--manifest-path\" ]; then mp=\"$a\"; break; fi\n  prev=\"$a\"\ndone\n\
                 rustc_real=\"\"\n\
                 if [ -n \"${{RUSTC:-}}\" ]; then rustc_real=\"$(cd \"$(dirname \"$RUSTC\")\" && pwd -P)/$(basename \"$RUSTC\")\"; fi\n\
                 ld_real=\"\"\n\
                 if [ -n \"${{LD_LIBRARY_PATH:-}}\" ]; then ld_real=\"$(cd \"${{LD_LIBRARY_PATH%%:*}}\" && pwd -P)\"; fi\n\
                 printf 'RUSTC=%s\\nRUSTC_REAL=%s\\nPATH=%s\\nLD=%s\\nLD_REAL=%s\\nCARGO_TARGET_DIR=%s\\nTMPDIR=%s\\n' \
                 \"${{RUSTC:-}}\" \"$rustc_real\" \"${{PATH:-}}\" \"${{LD_LIBRARY_PATH:-}}\" \"$ld_real\" \
                 \"${{CARGO_TARGET_DIR:-}}\" \"${{TMPDIR:-}}\" > '{}'\n\
                 printf '{{\"reason\":\"compiler-artifact\",\"manifest_path\":\"%s\",\"target\":{{\"kind\":[\"bin\"],\"name\":\"anneal-mir-eval\"}},\"profile\":{{\"test\":false}},\"executable\":\"{}\"}}\\n' \"$mp\"\n",
                sentinel.display(),
                args_log.display(),
                env_log.display(),
                ext_bin.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_cargo, fs::Permissions::from_mode(0o755)).unwrap();

        // 0. Symlinked or hardlinked `CARGO`/`RUSTC` fails pre-Cargo.
        let sym_cargo = root.join("sym-cargo.sh");
        symlink(&fake_cargo, &sym_cargo).unwrap();
        let err_sym_cargo = build_mir_eval_from_manifest_with_env(
            &manifest,
            &ws_root,
            Some(sym_cargo.as_os_str()),
            None,
            None,
            None,
        )
        .unwrap_err();
        assert!(err_sym_cargo.contains("symlink"), "{err_sym_cargo}");
        assert!(!sentinel.exists(), "symlinked cargo must never be invoked");

        let hard_src_cargo = root.join("hard-src-cargo.sh");
        fs::write(&hard_src_cargo, "#!/bin/sh\nexit 0\n").unwrap();
        let hard_cargo = root.join("hard-cargo.sh");
        fs::hard_link(&hard_src_cargo, &hard_cargo).unwrap();
        let err_hard_cargo = build_mir_eval_from_manifest_with_env(
            &manifest,
            &ws_root,
            Some(hard_cargo.as_os_str()),
            None,
            None,
            None,
        )
        .unwrap_err();
        assert!(err_hard_cargo.contains("hardlink"), "{err_hard_cargo}");
        assert!(!sentinel.exists(), "hardlinked cargo must never be invoked");

        let hard_rustc_bin = root.join("hard-rustc");
        fs::hard_link(&hard_src_cargo, &hard_rustc_bin).unwrap();
        let err_hard_rustc = build_mir_eval_from_manifest_with_env(
            &manifest,
            &ws_root,
            Some(fake_cargo.as_os_str()),
            Some(hard_rustc_bin.as_os_str()),
            None,
            None,
        )
        .unwrap_err();
        assert!(err_hard_rustc.contains("hardlink"), "{err_hard_rustc}");
        assert!(!sentinel.exists(), "hardlinked rustc must never be invoked");

        // 1. Prepopulated `<ws_root>/target` and `CARGO_TARGET_DIR` are never
        // reused, and artifacts emitted outside the private build target dir
        // fail closed (`escaped expected private Cargo target directory`).
        let ws_target = ws_root.join("target");
        fs::create_dir_all(ws_target.join("debug")).unwrap();
        let planted_ws_bin = ws_target.join("debug/anneal-mir-eval");
        fs::write(&planted_ws_bin, "#!/bin/sh\nexit 99\n").unwrap();
        let ambient_td = root.join("ambient-target");
        fs::create_dir_all(ambient_td.join("debug")).unwrap();
        let planted_ambient_bin = ambient_td.join("debug/anneal-mir-eval");
        fs::write(&planted_ambient_bin, "#!/bin/sh\nexit 98\n").unwrap();

        // 2. Ambient `.cargo/config.toml` (in `work_dir` or an ancestor)
        // and `rust-toolchain.toml` fail closed before Cargo executes.
        fs::create_dir_all(eval_dir.join(".cargo")).unwrap();
        fs::write(
            eval_dir.join(".cargo/config.toml"),
            "[build]\nrustc-wrapper = \"/bin/false\"\nrustc-workspace-wrapper = \"/bin/false\"\n",
        )
        .unwrap();
        let err_dot_cargo = build_mir_eval_from_manifest_with_env(
            &manifest,
            &ws_root,
            Some(fake_cargo.as_os_str()),
            None,
            None,
            None,
        )
        .unwrap_err();
        assert!(err_dot_cargo.contains(".cargo"), "{err_dot_cargo}");
        assert!(!sentinel.exists(), "ambient .cargo config must fail before cargo runs");
        fs::remove_dir_all(eval_dir.join(".cargo")).unwrap();

        let tc_file = ws_root.join("rust-toolchain.toml");
        fs::write(&tc_file, "[toolchain]\nchannel = \"nightly\"\n").unwrap();
        let err_tc = build_mir_eval_from_manifest_with_env(
            &manifest,
            &ws_root,
            Some(fake_cargo.as_os_str()),
            None,
            None,
            None,
        )
        .unwrap_err();
        assert!(err_tc.contains("rust-toolchain.toml"), "{err_tc}");
        assert!(!sentinel.exists(), "ambient rust-toolchain.toml must fail before cargo runs");
        fs::remove_file(&tc_file).unwrap();

        let fake_sysroot = root.join("fake-rustc-sysroot");
        fs::create_dir_all(fake_sysroot.join("bin")).unwrap();
        fs::create_dir_all(fake_sysroot.join("lib")).unwrap();
        let sysroot_rustc_bin = fake_sysroot.join("bin/rustc");
        let probe_tmp_log = root.join("rustc-probe-tmp.txt");
        let rustc_stub_body = format!(
            "#!/bin/sh\nif [ \"${{1:-}}\" = \"--print\" ] && [ \"${{2:-}}\" = \"sysroot\" ]; then\n\
             printf '%s\\n' '{}'\nexit 0\nfi\n\
             if [ \"${{1:-}}\" = \"-vV\" ]; then\n\
             printf '%s\\n' \"${{TMPDIR:-}}\" >> '{}'\n\
             printf 'rustc 1.90.0\\nhost: x86_64-unknown-linux-gnu\\n'\nexit 0\nfi\nexit 0\n",
            fake_sysroot.display(),
            probe_tmp_log.display(),
        );
        fs::write(&sysroot_rustc_bin, &rustc_stub_body).unwrap();
        fs::set_permissions(&sysroot_rustc_bin, fs::Permissions::from_mode(0o755)).unwrap();

        let clean_rustc = root.join("clean-rustc");
        fs::write(&clean_rustc, &rustc_stub_body).unwrap();
        fs::set_permissions(&clean_rustc, fs::Permissions::from_mode(0o755)).unwrap();

        // 3b. Poisoned `CARGO_HOME` configs (`target.<triple>.runner`,
        // `target.'cfg(...)'.runner`, `[build]`, symlinks, hardlinks) fail
        // closed before Cargo runs, while offline-vendor `[source]`-only
        // `CARGO_HOME/config.toml` passes pre-Cargo validation.
        let sym_ch = root.join("sym-cargo-home");
        let real_ext_ch = root.join("real-ext-cargo-home");
        fs::create_dir_all(&real_ext_ch).unwrap();
        symlink(&real_ext_ch, &sym_ch).unwrap();
        let err_sym_ch = build_mir_eval_from_manifest_with_env_and_cargo_home(
            &manifest,
            &ws_root,
            Some(fake_cargo.as_os_str()),
            Some(clean_rustc.as_os_str()),
            None,
            None,
            Some(sym_ch.as_os_str()),
        )
        .unwrap_err();
        assert!(err_sym_ch.contains("symlink"), "{err_sym_ch}");
        assert!(!sentinel.exists(), "symlinked CARGO_HOME must fail before cargo runs");

        for poisoned_toml in [
            "[target.x86_64-unknown-linux-gnu]\nrunner = \"/bin/false\"\n",
            "[target.'cfg(all())']\nrunner = \"/bin/false\"\n",
            "[build]\nrustc-wrapper = \"/bin/false\"\n",
        ] {
            let cfg_file = real_ext_ch.join("config.toml");
            fs::write(&cfg_file, poisoned_toml).unwrap();
            let err_ch_cfg = build_mir_eval_from_manifest_with_env_and_cargo_home(
                &manifest,
                &ws_root,
                Some(fake_cargo.as_os_str()),
                Some(clean_rustc.as_os_str()),
                None,
                None,
                Some(real_ext_ch.as_os_str()),
            )
            .unwrap_err();
            assert!(err_ch_cfg.contains("disallowed section"), "{err_ch_cfg}");
            assert!(!sentinel.exists(), "CARGO_HOME runner config must fail pre-Cargo");
            fs::remove_file(&cfg_file).unwrap();
        }

        let hard_cfg_src = root.join("hard-cfg-src.toml");
        fs::write(&hard_cfg_src, "[source.crates-io]\nreplace-with = \"v\"\n").unwrap();
        fs::hard_link(&hard_cfg_src, real_ext_ch.join("config.toml")).unwrap();
        let err_hard_cfg = build_mir_eval_from_manifest_with_env_and_cargo_home(
            &manifest,
            &ws_root,
            Some(fake_cargo.as_os_str()),
            Some(clean_rustc.as_os_str()),
            None,
            None,
            Some(real_ext_ch.as_os_str()),
        )
        .unwrap_err();
        assert!(err_hard_cfg.contains("hardlink"), "{err_hard_cfg}");
        assert!(!sentinel.exists(), "hardlinked CARGO_HOME config must fail pre-Cargo");
        fs::remove_file(real_ext_ch.join("config.toml")).unwrap();

        let vendor_dir = root.join("vendor");
        fs::create_dir_all(&vendor_dir).unwrap();
        fs::write(
            real_ext_ch.join("config.toml"),
            format!(
                "[source.crates-io]\nreplace-with = \"anneal-vendor\"\n\n\
                 [source.anneal-vendor]\ndirectory = \"{}\"\n",
                vendor_dir.display()
            ),
        )
        .unwrap();

        // 4. Clean build ignores ambient `CARGO_TARGET_DIR` / `<ws>/target`
        // and passes a fresh private `--target-dir`, clears wrappers, pins
        // `RUSTC`, `LD_LIBRARY_PATH` (`<sysroot>/lib`), sanitized `PATH`, and
        // `target.<host>.linker`, while rejecting uncontained executables
        // (including artifacts pointing back to `<ws>/target` or
        // `CARGO_TARGET_DIR`).
        let err_esc = build_mir_eval_from_manifest_with_env_and_cargo_home(
            &manifest,
            &ws_root,
            Some(fake_cargo.as_os_str()),
            Some(clean_rustc.as_os_str()),
            env::var_os("PATH").as_deref(),
            Some(ambient_td.as_os_str()),
            Some(real_ext_ch.as_os_str()),
        )
        .unwrap_err();
        assert!(sentinel.exists());
        let recorded_args = fs::read_to_string(&args_log).unwrap();
        let recorded_env = fs::read_to_string(&env_log).unwrap();
        let build_td_line = recorded_env
            .lines()
            .find_map(|l| l.strip_prefix("CARGO_TARGET_DIR="))
            .expect("CARGO_TARGET_DIR in child env");
        let private_td = Path::new(build_td_line);
        assert_ne!(private_td, ws_target);
        assert_ne!(private_td, ambient_td);
        assert!(
            !private_td.exists(),
            "temporary build target dir must be cleaned up on return: {}",
            private_td.display()
        );
        assert!(
            recorded_args.contains(&format!("--target-dir {}", private_td.display())),
            "expected private --target-dir pinning, got: {recorded_args}"
        );
        assert!(
            recorded_args.contains("--config build.rustc-wrapper=\"\""),
            "expected build.rustc-wrapper CLI clear, got: {recorded_args}"
        );
        assert!(
            recorded_args.contains("--config build.rustc-workspace-wrapper=\"\""),
            "expected build.rustc-workspace-wrapper CLI clear, got: {recorded_args}"
        );
        assert!(
            recorded_args.contains("--config target.x86_64-unknown-linux-gnu.linker="),
            "expected target.<host>.linker CLI pin, got: {recorded_args}"
        );
        let rustc_line = recorded_env
            .lines()
            .find_map(|l| l.strip_prefix("RUSTC="))
            .expect("RUSTC in cargo env");
        let rustc_real_line = recorded_env
            .lines()
            .find_map(|l| l.strip_prefix("RUSTC_REAL="))
            .expect("RUSTC_REAL in cargo env");
        assert!(
            rustc_line != clean_rustc.display().to_string()
                && rustc_line.starts_with("/proc/self/fd/")
                && rustc_line.ends_with("/bin/clean-rustc"),
            "expected staged immutable RUSTC in cargo env, got: {recorded_env}"
        );
        assert!(
            !rustc_real_line.is_empty() && !Path::new(rustc_real_line).exists(),
            "temporary staged RUSTC must be cleaned up on return: {rustc_real_line}"
        );
        let ld_line =
            recorded_env.lines().find_map(|l| l.strip_prefix("LD=")).expect("LD in cargo env");
        let ld_real_line = recorded_env
            .lines()
            .find_map(|l| l.strip_prefix("LD_REAL="))
            .expect("LD_REAL in cargo env");
        assert!(
            !ld_line.is_empty()
                && Path::new(ld_line) != fake_sysroot.join("lib")
                && ld_line.starts_with("/proc/self/fd/")
                && ld_line.ends_with("/lib"),
            "expected staged immutable sysroot lib LD_LIBRARY_PATH in cargo env, got: {recorded_env}"
        );
        assert!(
            !ld_real_line.is_empty() && !Path::new(ld_real_line).exists(),
            "temporary staged sysroot lib must be cleaned up on return: {ld_real_line}"
        );
        assert!(err_esc.contains("escaped expected private Cargo target directory"), "{err_esc}");

        let planted_cargo = root.join("planted-cargo.sh");
        fs::write(
            &planted_cargo,
            format!(
                "#!/bin/sh\nmp=\"\"\nprev=\"\"\n\
                 for a in \"$@\"; do\n  if [ \"$prev\" = \"--manifest-path\" ]; then mp=\"$a\"; break; fi\n  prev=\"$a\"\ndone\n\
                 printf '{{\"reason\":\"compiler-artifact\",\"manifest_path\":\"%s\",\"target\":{{\"kind\":[\"bin\"],\"name\":\"anneal-mir-eval\"}},\"profile\":{{\"test\":false}},\"executable\":\"{}\"}}\\n' \"$mp\"\n",
                planted_ambient_bin.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&planted_cargo, fs::Permissions::from_mode(0o755)).unwrap();
        let err_planted = build_mir_eval_from_manifest_with_env_and_cargo_home(
            &manifest,
            &ws_root,
            Some(planted_cargo.as_os_str()),
            Some(clean_rustc.as_os_str()),
            env::var_os("PATH").as_deref(),
            Some(ambient_td.as_os_str()),
            Some(real_ext_ch.as_os_str()),
        )
        .unwrap_err();
        assert!(
            err_planted.contains("escaped expected private Cargo target directory"),
            "{err_planted}"
        );

        // 5. Cargo-built `nlink == 2` executables paired with `<profile>/deps`
        // or `build/<pkg>/<hash>/out/` inside the private target dir isolate
        // into an immutable `0o555` staging dir (`nlink == 1`) that cleans up
        // on Drop, while rogue `nlink == 2` hardlinks fail closed.
        let deps_cargo = root.join("deps-cargo.sh");
        let private_td_log = root.join("private-td-path.txt");
        fs::write(
            &deps_cargo,
            format!(
                "#!/bin/sh\nset -e\n\
                 mp=\"\"\nprev=\"\"\n\
                 for a in \"$@\"; do\n  if [ \"$prev\" = \"--manifest-path\" ]; then mp=\"$a\"; break; fi\n  prev=\"$a\"\ndone\n\
                 printf '%s\\n' \"$CARGO_TARGET_DIR\" > '{}'\n\
                 dbg=\"$CARGO_TARGET_DIR/debug\"\nmkdir -p \"$dbg/deps\"\n\
                 printf '#!/bin/sh\\nexit 0\\n' > \"$dbg/deps/anneal_mir_eval-deadbeef\"\n\
                 chmod 755 \"$dbg/deps/anneal_mir_eval-deadbeef\"\n\
                 ln \"$dbg/deps/anneal_mir_eval-deadbeef\" \"$dbg/anneal-mir-eval\"\n\
                 printf '{{\"reason\":\"compiler-artifact\",\"manifest_path\":\"%s\",\"target\":{{\"kind\":[\"bin\"],\"name\":\"anneal-mir-eval\"}},\"profile\":{{\"test\":false}},\"executable\":\"%s\"}}\\n' \"$mp\" \"$dbg/anneal-mir-eval\"\n",
                private_td_log.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&deps_cargo, fs::Permissions::from_mode(0o755)).unwrap();
        let isolated = build_mir_eval_from_manifest_with_env_and_cargo_home(
            &manifest,
            &ws_root,
            Some(deps_cargo.as_os_str()),
            Some(clean_rustc.as_os_str()),
            env::var_os("PATH").as_deref(),
            Some(ambient_td.as_os_str()),
            Some(real_ext_ch.as_os_str()),
        )
        .expect("verified Cargo deps hardlink should isolate into immutable staging dir");
        let deps_private_td = PathBuf::from(fs::read_to_string(&private_td_log).unwrap().trim());
        assert!(!deps_private_td.exists(), "build target dir should be deleted after staging");
        assert_eq!(fs::symlink_metadata(&isolated.path).unwrap().nlink(), 1);
        assert_eq!(
            fs::symlink_metadata(&isolated.path).unwrap().permissions().mode() & 0o777,
            0o555
        );
        assert_eq!(
            fs::symlink_metadata(isolated.path.parent().unwrap()).unwrap().permissions().mode()
                & 0o777,
            0o555
        );
        assert!(validate_executable_no_links(&isolated.path, &ws_root, "--mir-eval-bin").is_ok());
        let staged_path = isolated.path.clone();
        drop(isolated);
        assert!(!staged_path.exists(), "PreparedMirEval drop must clean up staged binary");

        // Verified Cargo `build/<pkg>/<hash>/out/<stem>` hardlink layout
        // (Cargo 1.100+) must also isolate cleanly.
        let build_layout_cargo = root.join("build-layout-cargo.sh");
        fs::write(
            &build_layout_cargo,
            "#!/bin/sh\nset -e\n\
             mp=\"\"\nprev=\"\"\n\
             for a in \"$@\"; do\n  if [ \"$prev\" = \"--manifest-path\" ]; then mp=\"$a\"; break; fi\n  prev=\"$a\"\ndone\n\
             dbg=\"$CARGO_TARGET_DIR/debug\"\nout=\"$dbg/build/anneal-mir-eval/deadbeef12345678/out\"\n\
             mkdir -p \"$out\"\n\
             printf '#!/bin/sh\\nexit 0\\n' > \"$out/anneal_mir_eval\"\n\
             chmod 755 \"$out/anneal_mir_eval\"\n\
             ln \"$out/anneal_mir_eval\" \"$dbg/anneal-mir-eval\"\n\
             printf '{\"reason\":\"compiler-artifact\",\"manifest_path\":\"%s\",\"target\":{\"kind\":[\"bin\"],\"name\":\"anneal-mir-eval\"},\"profile\":{\"test\":false},\"executable\":\"%s\"}\\n' \"$mp\" \"$dbg/anneal-mir-eval\"\n",
        )
        .unwrap();
        fs::set_permissions(&build_layout_cargo, fs::Permissions::from_mode(0o755)).unwrap();
        let isolated_new_layout = build_mir_eval_from_manifest_with_env_and_cargo_home(
            &manifest,
            &ws_root,
            Some(build_layout_cargo.as_os_str()),
            Some(clean_rustc.as_os_str()),
            env::var_os("PATH").as_deref(),
            None,
            Some(real_ext_ch.as_os_str()),
        )
        .expect("verified Cargo build/<pkg>/<hash>/out hardlink should isolate");
        assert_eq!(fs::symlink_metadata(&isolated_new_layout.path).unwrap().nlink(), 1);

        let rogue_src = root.join("rogue-outside-bin");
        fs::write(&rogue_src, "#!/bin/sh\nexit 0\n").unwrap();
        let rogue_cargo = root.join("rogue-cargo.sh");
        fs::write(
            &rogue_cargo,
            format!(
                "#!/bin/sh\nset -e\n\
                 mp=\"\"\nprev=\"\"\n\
                 for a in \"$@\"; do\n  if [ \"$prev\" = \"--manifest-path\" ]; then mp=\"$a\"; break; fi\n  prev=\"$a\"\ndone\n\
                 dbg=\"$CARGO_TARGET_DIR/debug\"\nmkdir -p \"$dbg\"\n\
                 ln '{}' \"$dbg/anneal-mir-eval\"\n\
                 printf '{{\"reason\":\"compiler-artifact\",\"manifest_path\":\"%s\",\"target\":{{\"kind\":[\"bin\"],\"name\":\"anneal-mir-eval\"}},\"profile\":{{\"test\":false}},\"executable\":\"%s\"}}\\n' \"$mp\" \"$dbg/anneal-mir-eval\"\n",
                rogue_src.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&rogue_cargo, fs::Permissions::from_mode(0o755)).unwrap();
        let err_rogue_hard = build_mir_eval_from_manifest_with_env_and_cargo_home(
            &manifest,
            &ws_root,
            Some(rogue_cargo.as_os_str()),
            Some(clean_rustc.as_os_str()),
            env::var_os("PATH").as_deref(),
            None,
            Some(real_ext_ch.as_os_str()),
        )
        .unwrap_err();
        assert!(err_rogue_hard.contains("hardlinked outside Cargo deps"), "{err_rogue_hard}");

        // 6. Hardlinked `compiler-artifact.manifest_path` entries are ignored/
        // rejected when locating the built `anneal-mir-eval` artifact.
        let hard_art_manifest = root.join("hard-artifact-Cargo.toml");
        fs::hard_link(&manifest, &hard_art_manifest).unwrap();
        let hard_art_json = serde_json::json!({
            "reason": "compiler-artifact",
            "manifest_path": hard_art_manifest,
            "target": { "kind": ["bin"], "name": "anneal-mir-eval" },
            "profile": { "test": false },
            "executable": isolated_new_layout.path,
        })
        .to_string();
        assert!(extract_built_executable(&hard_art_json, "anneal-mir-eval", &manifest).is_err());
        drop(isolated_new_layout);
        fs::remove_file(&hard_art_manifest).unwrap();

        // 7. When `CARGO_HOME` is unset, `$HOME/.cargo` fallback must still
        // reject symlinked ancestors (`HOME` symlink or traversal) pre-Cargo.
        let sym_home = root.join("sym-home");
        symlink(&real_ext_ch, &sym_home).unwrap();
        let err_sym_home = build_mir_eval_from_manifest_with_env_and_homes(
            &manifest,
            &ws_root,
            Some(fake_cargo.as_os_str()),
            Some(clean_rustc.as_os_str()),
            None,
            None,
            None,
            Some(sym_home.as_os_str()),
        )
        .unwrap_err();
        assert!(err_sym_home.contains("symlink"), "{err_sym_home}");

        let trav_home = real_ext_ch.join("sub/../real");
        let err_trav_home = build_mir_eval_from_manifest_with_env_and_homes(
            &manifest,
            &ws_root,
            Some(fake_cargo.as_os_str()),
            Some(clean_rustc.as_os_str()),
            None,
            None,
            None,
            Some(trav_home.as_os_str()),
        )
        .unwrap_err();
        assert!(err_trav_home.contains(".."), "{err_trav_home}");

        // 8. Unset `CARGO` and `RUSTC` with `rustup` proxies on `PATH`: must
        // validate `RUSTUP_HOME` / `settings.toml`, resolve both proxies via
        // `rustup which` BEFORE invoking `rustc` probes or `cargo build`,
        // anchor & validate relative `TMPDIR`, strip poisoned `PATH`, and fail
        // closed on unsafe `TMPDIR` or proxy-chaining resolution.
        let sentinel_unset = root.join("cargo-unset-invoked");
        let proxy_bypassed = root.join("rustup-proxy-bypassed");
        let unset_args_log = root.join("cargo-unset-args.txt");
        let unset_env_log = root.join("cargo-unset-env.txt");
        let sysroot_cargo_bin = fake_sysroot.join("bin/cargo");
        fs::write(
            &sysroot_cargo_bin,
            format!(
                "#!/bin/sh\nset -e\ntouch '{}'\nprintf '%s\\n' \"$*\" > '{}'\n\
                 mp=\"\"\nprev=\"\"\n\
                 for a in \"$@\"; do\n  if [ \"$prev\" = \"--manifest-path\" ]; then mp=\"$a\"; break; fi\n  prev=\"$a\"\ndone\n\
                 rustc_real=\"\"\n\
                 if [ -n \"${{RUSTC:-}}\" ]; then rustc_real=\"$(cd \"$(dirname \"$RUSTC\")\" && pwd -P)/$(basename \"$RUSTC\")\"; fi\n\
                 ld_real=\"\"\n\
                 if [ -n \"${{LD_LIBRARY_PATH:-}}\" ]; then ld_real=\"$(cd \"${{LD_LIBRARY_PATH%%:*}}\" && pwd -P)\"; fi\n\
                 printf 'RUSTC=%s\\nRUSTC_REAL=%s\\nPATH=%s\\nLD=%s\\nLD_REAL=%s\\nTMPDIR=%s\\n' \
                 \"${{RUSTC:-}}\" \"$rustc_real\" \"${{PATH:-}}\" \"${{LD_LIBRARY_PATH:-}}\" \"$ld_real\" \"${{TMPDIR:-}}\" > '{}'\n\
                 dbg=\"$CARGO_TARGET_DIR/debug\"\nmkdir -p \"$dbg\"\n\
                 printf '#!/bin/sh\\nexit 0\\n' > \"$dbg/anneal-mir-eval\"\n\
                 chmod 755 \"$dbg/anneal-mir-eval\"\n\
                 printf '{{\"reason\":\"compiler-artifact\",\"manifest_path\":\"%s\",\"target\":{{\"kind\":[\"bin\"],\"name\":\"anneal-mir-eval\"}},\"profile\":{{\"test\":false}},\"executable\":\"%s\"}}\\n' \"$mp\" \"$dbg/anneal-mir-eval\"\n",
                sentinel_unset.display(),
                unset_args_log.display(),
                unset_env_log.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&sysroot_cargo_bin, fs::Permissions::from_mode(0o755)).unwrap();

        let err_missing_rustc = build_mir_eval_from_manifest_with_env_and_cargo_home(
            &manifest,
            &ws_root,
            Some(sysroot_cargo_bin.as_os_str()),
            None,
            None,
            None,
            Some(real_ext_ch.as_os_str()),
        )
        .unwrap_err();
        assert!(err_missing_rustc.contains("rustc"), "{err_missing_rustc}");
        assert!(!sentinel_unset.exists(), "cargo must not run without resolved RUSTC");

        let clean_rustup_home = root.join("clean-rustup-home");
        fs::create_dir_all(&clean_rustup_home).unwrap();
        let sym_rustup_home = root.join("sym-rustup-home");
        symlink(&clean_rustup_home, &sym_rustup_home).unwrap();
        let err_sym_rh = build_mir_eval_from_manifest_full(
            &manifest,
            &ws_root,
            Some(sysroot_cargo_bin.as_os_str()),
            Some(clean_rustc.as_os_str()),
            None,
            None,
            Some(real_ext_ch.as_os_str()),
            Some(real_ext_ch.as_os_str()),
            Some(sym_rustup_home.as_os_str()),
            None,
            None,
            None,
        )
        .unwrap_err();
        assert!(err_sym_rh.contains("symlink"), "{err_sym_rh}");
        assert!(!sentinel_unset.exists());

        // Symlinked `RUSTUP_HOME/settings.toml` must fail before `rustup` runs.
        let evil_settings = root.join("evil-settings.toml");
        fs::write(&evil_settings, "default_toolchain = \"evil\"\n").unwrap();
        symlink(&evil_settings, clean_rustup_home.join("settings.toml")).unwrap();
        let err_sym_settings = build_mir_eval_from_manifest_full(
            &manifest,
            &ws_root,
            Some(sysroot_cargo_bin.as_os_str()),
            Some(clean_rustc.as_os_str()),
            None,
            None,
            Some(real_ext_ch.as_os_str()),
            Some(real_ext_ch.as_os_str()),
            Some(clean_rustup_home.as_os_str()),
            None,
            None,
            None,
        )
        .unwrap_err();
        assert!(err_sym_settings.contains("symlink"), "{err_sym_settings}");
        fs::remove_file(clean_rustup_home.join("settings.toml")).unwrap();

        // Hardlinked `RUSTUP_HOME/settings.toml` must fail before `rustup`.
        fs::hard_link(&evil_settings, clean_rustup_home.join("settings.toml")).unwrap();
        let err_hard_settings = build_mir_eval_from_manifest_full(
            &manifest,
            &ws_root,
            Some(sysroot_cargo_bin.as_os_str()),
            Some(clean_rustc.as_os_str()),
            None,
            None,
            Some(real_ext_ch.as_os_str()),
            Some(real_ext_ch.as_os_str()),
            Some(clean_rustup_home.as_os_str()),
            None,
            None,
            None,
        )
        .unwrap_err();
        assert!(err_hard_settings.contains("hardlink"), "{err_hard_settings}");
        fs::remove_file(clean_rustup_home.join("settings.toml")).unwrap();
        fs::write(clean_rustup_home.join("settings.toml"), "default_toolchain = \"pinned\"\n")
            .unwrap();

        let evil_path_dir = root.join("evil-ambient-path");
        let rustup_proxy_dir = root.join("proxy-cargo-bin");
        fs::create_dir_all(&evil_path_dir).unwrap();
        fs::create_dir_all(&rustup_proxy_dir).unwrap();
        let rustup_which_tmp_log = root.join("rustup-which-tmp.txt");
        let rustup_stub = format!(
            "#!/bin/sh\nbase=${{0##*/}}\n\
             if [ \"$base\" != \"rustup\" ] || [ \"${{1:-}}\" != \"which\" ]; then\n\
               printf 'bypassed\\n' > '{}'\nexit 1\nfi\n\
             printf '%s\\n' \"${{TMPDIR:-}}\" >> '{}'\n\
             if [ \"${{2:-}}\" = \"cargo\" ]; then printf '%s\\n' '{}'; exit 0; fi\n\
             if [ \"${{2:-}}\" = \"rustc\" ]; then printf '%s\\n' '{}'; exit 0; fi\n\
             exit 1\n",
            proxy_bypassed.display(),
            rustup_which_tmp_log.display(),
            sysroot_cargo_bin.display(),
            sysroot_rustc_bin.display(),
        );
        fs::write(rustup_proxy_dir.join("rustup"), &rustup_stub).unwrap();
        fs::set_permissions(rustup_proxy_dir.join("rustup"), fs::Permissions::from_mode(0o755))
            .unwrap();
        symlink("rustup", rustup_proxy_dir.join("cargo")).unwrap();
        symlink("rustup", rustup_proxy_dir.join("rustc")).unwrap();

        let rel_tmp = ws_root.join("rel-tmp");
        fs::create_dir_all(&rel_tmp).unwrap();
        let mut test_path_entries = vec![evil_path_dir.clone(), rustup_proxy_dir.clone()];
        if let Some(sys_path) = env::var_os("PATH") {
            test_path_entries.extend(
                env::split_paths(&sys_path)
                    .filter(|p| p.starts_with(crate::rustc_runner::STORE_PREFIX)),
            );
        }
        let poisoned_path = env::join_paths(&test_path_entries).unwrap();
        let _ = fs::remove_file(&probe_tmp_log);

        let built_via_proxies = build_mir_eval_from_manifest_full(
            &manifest,
            &ws_root,
            None,
            None,
            Some(poisoned_path.as_os_str()),
            None,
            Some(real_ext_ch.as_os_str()),
            Some(real_ext_ch.as_os_str()),
            Some(clean_rustup_home.as_os_str()),
            None,
            None,
            Some(OsStr::new("rel-tmp")),
        )
        .expect("unset CARGO and RUSTC with rustup proxies and relative TMPDIR must succeed");
        assert!(
            !proxy_bypassed.exists(),
            "rustup symlink proxies must be resolved via `rustup which` before any probe/build"
        );
        assert!(
            built_via_proxies.path.starts_with(&rel_tmp),
            "expected staged binary inside anchored TMPDIR {}, got {}",
            rel_tmp.display(),
            built_via_proxies.path.display()
        );
        assert_eq!(fs::symlink_metadata(&built_via_proxies.path).unwrap().nlink(), 1);
        let unset_args = fs::read_to_string(&unset_args_log).unwrap();
        assert!(
            unset_args.contains("--config target.x86_64-unknown-linux-gnu.linker="),
            "expected linker pin with unset RUSTC, got: {unset_args}"
        );
        let unset_env = fs::read_to_string(&unset_env_log).unwrap();
        let unset_rustc = unset_env
            .lines()
            .find_map(|l| l.strip_prefix("RUSTC="))
            .expect("RUSTC in unset cargo env");
        let unset_rustc_real = unset_env
            .lines()
            .find_map(|l| l.strip_prefix("RUSTC_REAL="))
            .expect("RUSTC_REAL in unset cargo env");
        let staged_root =
            Path::new(unset_rustc).parent().and_then(Path::parent).expect("staged rustc sysroot");
        assert!(
            Path::new(unset_rustc) != sysroot_rustc_bin
                && unset_rustc.starts_with("/proc/self/fd/")
                && Path::new(unset_rustc).ends_with("bin/rustc")
                && !unset_rustc_real.is_empty()
                && !Path::new(unset_rustc_real).exists(),
            "expected staged immutable rustc unwrapped from proxy, got: {unset_env}"
        );
        let unset_ld =
            unset_env.lines().find_map(|l| l.strip_prefix("LD=")).expect("LD in unset cargo env");
        let unset_ld_real = unset_env
            .lines()
            .find_map(|l| l.strip_prefix("LD_REAL="))
            .expect("LD_REAL in unset cargo env");
        let unset_ld_entries: Vec<PathBuf> = env::split_paths(unset_ld).collect();
        assert_eq!(
            unset_ld_entries.first(),
            Some(&staged_root.join("lib")),
            "expected staged sysroot LD_LIBRARY_PATH first, got: {unset_env}"
        );
        assert!(
            !unset_ld_entries.iter().any(|p| p == &fake_sysroot.join("lib"))
                && !unset_ld_real.is_empty()
                && !Path::new(unset_ld_real).exists(),
            "expected cleaned-up immutable LD_LIBRARY_PATH entries, got: {unset_env}"
        );
        assert!(
            unset_env.contains(&format!("TMPDIR={}\n", rel_tmp.display())),
            "expected anchored TMPDIR in cargo env, got: {unset_env}"
        );
        assert!(
            !unset_env.contains(&evil_path_dir.display().to_string()),
            "poisoned ambient PATH leaked into Cargo env: {unset_env}"
        );
        let probe_tmps = fs::read_to_string(&probe_tmp_log).unwrap();
        assert!(
            probe_tmps.lines().all(|l| l == rel_tmp.display().to_string()),
            "expected anchored TMPDIR in rustc probes, got: {probe_tmps}"
        );
        let which_tmps = fs::read_to_string(&rustup_which_tmp_log).unwrap();
        assert_eq!(
            which_tmps.lines().collect::<Vec<_>>(),
            vec![rel_tmp.display().to_string(), rel_tmp.display().to_string()],
            "expected anchored TMPDIR in both `rustup which` probes"
        );

        // Traversal, symlink, or missing `TMPDIR` fails before `rustup` or
        // `cargo` runs.
        let _ = fs::remove_file(&sentinel_unset);
        let sym_tmp = ws_root.join("sym-tmp");
        symlink(&rel_tmp, &sym_tmp).unwrap();
        for bad_tmp in
            [OsStr::new("../outside-tmp"), sym_tmp.as_os_str(), OsStr::new("does-not-exist-tmp")]
        {
            let err_tmp = build_mir_eval_from_manifest_full(
                &manifest,
                &ws_root,
                Some(sysroot_cargo_bin.as_os_str()),
                Some(sysroot_rustc_bin.as_os_str()),
                Some(poisoned_path.as_os_str()),
                None,
                Some(real_ext_ch.as_os_str()),
                Some(real_ext_ch.as_os_str()),
                Some(clean_rustup_home.as_os_str()),
                None,
                None,
                Some(bad_tmp),
            )
            .unwrap_err();
            assert!(err_tmp.contains("TMPDIR"), "bad TMPDIR {:?} -> {err_tmp}", bad_tmp);
            assert!(!sentinel_unset.exists(), "cargo must not run with bad TMPDIR");
        }
    }

    #[cfg(unix)]
    #[test]
    fn workspace_target_roots_and_manifest_build_reject_linked_ancestor_manifests() {
        use std::os::unix::fs::{PermissionsExt, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let ws_root = root.join("ws");
        let pkg_dir = ws_root.join("tools/anneal-mir-eval");
        let outside = root.join("outside");
        for d in [&ws_root, &pkg_dir, &outside] {
            fs::create_dir_all(d).unwrap();
        }
        let pkg_manifest = pkg_dir.join("Cargo.toml");
        fs::write(&pkg_manifest, "[package]\nname = \"anneal-mir-eval\"\nversion = \"0.1.0\"\n")
            .unwrap();
        let ext_ch = root.join("clean-cargo-home");
        fs::create_dir_all(&ext_ch).unwrap();
        let evil_ws_manifest = outside.join("Cargo.toml");
        fs::write(&evil_ws_manifest, "[workspace]\nmembers = [\"tools/anneal-mir-eval\"]\n")
            .unwrap();

        let marker = root.join("cargo_invoked.marker");
        let fake_cargo = root.join("fake-cargo");
        fs::write(&fake_cargo, format!("#!/bin/sh\ntouch '{}'\nexit 0\n", marker.display()))
            .unwrap();
        fs::set_permissions(&fake_cargo, fs::Permissions::from_mode(0o755)).unwrap();
        let fake_rustc = root.join("fake-rustc");
        fs::write(&fake_rustc, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&fake_rustc, fs::Permissions::from_mode(0o755)).unwrap();

        // 1. Symlinked ancestor `Cargo.toml` fails closed before Cargo runs.
        let anc_manifest = ws_root.join("Cargo.toml");
        symlink(&evil_ws_manifest, &anc_manifest).unwrap();
        let sym_err = workspace_target_roots(&pkg_dir).unwrap_err();
        assert!(sym_err.contains("symlink"), "{sym_err}");
        let build_sym_err = build_mir_eval_from_manifest_with_env_and_cargo_home(
            &pkg_manifest,
            &pkg_dir,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(ext_ch.as_os_str()),
        )
        .unwrap_err();
        assert!(build_sym_err.contains("symlink"), "{build_sym_err}");
        assert!(!marker.exists(), "cargo must not run when ancestor Cargo.toml is a symlink");
        fs::remove_file(&anc_manifest).unwrap();

        // 2. Hardlinked ancestor `Cargo.toml` (`nlink > 1`) fails closed before
        // Cargo runs.
        fs::hard_link(&evil_ws_manifest, &anc_manifest).unwrap();
        let hard_err = workspace_target_roots(&pkg_dir).unwrap_err();
        assert!(hard_err.contains("hardlink"), "{hard_err}");
        let build_hard_err = build_mir_eval_from_manifest_with_env_and_cargo_home(
            &pkg_manifest,
            &pkg_dir,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(ext_ch.as_os_str()),
        )
        .unwrap_err();
        assert!(build_hard_err.contains("hardlink"), "{build_hard_err}");
        assert!(!marker.exists(), "cargo must not run when ancestor Cargo.toml is a hardlink");
        fs::remove_file(&anc_manifest).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn run_mir_eval_raw_with_evidence_enforces_emitted_body_identity() {
        use std::os::unix::fs::PermissionsExt;

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let cap_json = root.join("capture.json");
        fs::write(&cap_json, "{}").unwrap();
        let fake_eval = root.join("fake-mir-eval.sh");
        let raw_json = r#"{"body_id":0,"identity":"crate::fuzz_case_0000","outcome":{"kind":"returned","value":{"kind":"returned","ret":{"kind":"scalar","value":{"width":"i32","signed":false,"bits":"7"}}}}}"#;
        fs::write(&fake_eval, format!("#!/bin/sh\nprintf '%s\\n' '{raw_json}'\n")).unwrap();
        fs::set_permissions(&fake_eval, fs::Permissions::from_mode(0o755)).unwrap();

        let (ok_out, ok_ev, ok_global) = run_mir_eval_raw_with_evidence(
            &fake_eval,
            &cap_json,
            (0, "crate::fuzz_case_0000"),
            &[],
            100,
            None,
        );
        assert!(!ok_global);
        assert_eq!(
            ok_out,
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );
        assert_eq!(ok_ev, Some((0, raw_json.to_owned())));

        for wrong in [(1, "crate::fuzz_case_0000"), (0, "crate::fuzz_case_0001")] {
            let (bad_out, bad_ev, bad_global) =
                run_mir_eval_raw_with_evidence(&fake_eval, &cap_json, wrong, &[], 100, None);
            assert!(!bad_global);
            assert!(
                matches!(bad_out, ObservedOutcome::ToolError { ref detail } if detail.contains("body identity mismatch")),
                "expected ToolError for {wrong:?}, got {bad_out:?}"
            );
            assert_eq!(bad_ev, None);
        }
    }

    #[cfg(unix)]
    #[test]
    fn build_from_manifest_allows_nix_store_wrapper_symlinks_and_rejects_escape() {
        use std::os::unix::fs::{MetadataExt, PermissionsExt, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let fake_store = root.join("nix/store");
        let pkg_rust = fake_store.join("1111-rust-toolchain");
        let opt_dir = root.join("opt/anneal-nix");
        let opt_tc = opt_dir.join("rust-toolchain");
        let outside = root.join("outside");
        let ws = root.join("ws");
        let eval_dir = ws.join("tools/anneal-mir-eval");
        for d in [
            pkg_rust.join("bin"),
            pkg_rust.join("lib"),
            opt_dir.clone(),
            outside.clone(),
            eval_dir.clone(),
        ] {
            fs::create_dir_all(d).unwrap();
        }
        let manifest = eval_dir.join("Cargo.toml");
        fs::write(&manifest, "[package]\nname = \"anneal-mir-eval\"\nversion = \"0.1.0\"\n")
            .unwrap();

        let store_rustc = pkg_rust.join("bin/rustc");
        fs::write(
            &store_rustc,
            format!(
                "#!/bin/sh\nif [ \"${{1:-}}\" = \"--print\" ] && [ \"${{2:-}}\" = \"sysroot\" ]; then\n\
                 printf '%s\\n' '{}'\nexit 0\nfi\n\
                 if [ \"${{1:-}}\" = \"-vV\" ]; then\n\
                 printf 'rustc 1.90.0\\nhost: x86_64-unknown-linux-gnu\\n'\nexit 0\nfi\nexit 0\n",
                opt_tc.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&store_rustc, fs::Permissions::from_mode(0o755)).unwrap();
        let store_cargo = pkg_rust.join("bin/cargo");
        let rustc_env_log = root.join("nix-cargo-rustc.log");
        fs::write(
            &store_cargo,
            format!(
                "#!/bin/sh\nset -e\n\
                 mp=\"\"\nprev=\"\"\n\
                 for a in \"$@\"; do\n  if [ \"$prev\" = \"--manifest-path\" ]; then mp=\"$a\"; break; fi\n  prev=\"$a\"\ndone\n\
                 rustc_real=\"$(cd \"$(dirname \"$RUSTC\")\" && pwd -P)/$(basename \"$RUSTC\")\"\n\
                 printf 'RUSTC=%s\\nRUSTC_REAL=%s\\nLD=%s\\n' \"${{RUSTC:-}}\" \"$rustc_real\" \"${{LD_LIBRARY_PATH:-}}\" > '{}'\n\
                 dbg=\"$CARGO_TARGET_DIR/debug\"\nmkdir -p \"$dbg\"\n\
                 printf '#!/bin/sh\\nexit 42\\n' > \"$dbg/anneal-mir-eval\"\n\
                 chmod 755 \"$dbg/anneal-mir-eval\"\n\
                 printf '{{\"reason\":\"compiler-artifact\",\"manifest_path\":\"%s\",\"target\":{{\"kind\":[\"bin\"],\"name\":\"anneal-mir-eval\"}},\"profile\":{{\"test\":false}},\"executable\":\"%s\"}}\\n' \"$mp\" \"$dbg/anneal-mir-eval\"\n",
                rustc_env_log.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&store_cargo, fs::Permissions::from_mode(0o755)).unwrap();

        // Mirror `ci/docker/anneal-tc.Dockerfile`: symlink
        // `/opt/anneal-nix/rust-toolchain` into `/nix/store`, and provide
        // regular script `/opt/anneal-nix/build-rustc`.
        symlink(&pkg_rust, &opt_tc).unwrap();
        let build_rustc = opt_dir.join("build-rustc");
        fs::write(
            &build_rustc,
            format!("#!/bin/sh\nexec '{}' \"$@\"\n", opt_tc.join("bin/rustc").display()),
        )
        .unwrap();
        fs::set_permissions(&build_rustc, fs::Permissions::from_mode(0o755)).unwrap();

        let clean_ch = root.join("clean-cargo-home");
        fs::create_dir_all(&clean_ch).unwrap();
        let path_with_sym = env::join_paths([opt_tc.join("bin")]).unwrap();
        let built = build_mir_eval_from_manifest_full_with_store(
            &manifest,
            &ws,
            None,
            Some(build_rustc.as_os_str()),
            Some(path_with_sym.as_os_str()),
            None,
            Some(clean_ch.as_os_str()),
            Some(clean_ch.as_os_str()),
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .expect("Nix-store wrapper symlink on PATH and --print sysroot must succeed");
        assert_eq!(fs::read(&built.path).unwrap(), b"#!/bin/sh\nexit 42\n");
        assert_eq!(fs::symlink_metadata(&built.path).unwrap().nlink(), 1);
        let env_out = fs::read_to_string(&rustc_env_log).unwrap();
        let rustc_line =
            env_out.lines().find_map(|l| l.strip_prefix("RUSTC=")).expect("RUSTC in wrapper env");
        let rustc_real = env_out
            .lines()
            .find_map(|l| l.strip_prefix("RUSTC_REAL="))
            .expect("RUSTC_REAL in wrapper env");
        assert!(
            rustc_line != build_rustc.display().to_string()
                && rustc_line.starts_with("/proc/self/fd/")
                && rustc_line.ends_with("/bin/build-rustc"),
            "{env_out}"
        );
        assert!(env_out.contains(&pkg_rust.join("lib").display().to_string()), "{env_out}");
        drop(built);
        assert!(
            !rustc_real.is_empty() && !Path::new(rustc_real).exists(),
            "staged wrapper RUSTC must be cleaned up: {rustc_real}"
        );

        // Wrapper symlink escaping outside store must fail closed.
        let evil_dir = outside.join("evil-bin");
        fs::create_dir_all(&evil_dir).unwrap();
        fs::write(evil_dir.join("cargo"), "#!/bin/sh\nexit 0\n").unwrap();
        let bad_wrap = root.join("opt/bad-toolchain");
        symlink(&evil_dir, &bad_wrap).unwrap();
        let bad_path = env::join_paths([bad_wrap]).unwrap();
        let err = build_mir_eval_from_manifest_full_with_store(
            &manifest,
            &ws,
            None,
            Some(build_rustc.as_os_str()),
            Some(bad_path.as_os_str()),
            None,
            Some(clean_ch.as_os_str()),
            Some(clean_ch.as_os_str()),
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .unwrap_err();
        assert!(err.contains("symlink"), "{err}");
    }

    #[cfg(unix)]
    #[test]
    fn materialize_cargo_built_executable_hashes_single_pass_under_concurrent_partner_write() {
        use std::os::unix::fs::PermissionsExt;

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let target_dir = root.join("target");
        let profile_dir = target_dir.join("debug");
        let deps_dir = profile_dir.join("deps");
        fs::create_dir_all(&deps_dir).unwrap();

        let dep_bin = deps_dir.join("anneal_mir_eval-abc");
        let out_bin = profile_dir.join("anneal-mir-eval");
        // Exceed 64 KiB read chunk so the partner hardlink mutates in-place
        // mid-copy after chunk 1.
        let mut initial = vec![b'A'; 80_000];
        initial[0..4].copy_from_slice(b"HEAD");
        fs::write(&dep_bin, &initial).unwrap();
        fs::set_permissions(&dep_bin, fs::Permissions::from_mode(0o755)).unwrap();
        fs::hard_link(&dep_bin, &out_bin).unwrap();

        let dep_partner = dep_bin.clone();
        let iso = materialize_cargo_built_executable_with_hook(
            out_bin,
            "anneal-mir-eval",
            None,
            move || {
                use std::io::{Seek as _, SeekFrom};
                let mut f = fs::OpenOptions::new().write(true).open(&dep_partner).unwrap();
                f.seek(SeekFrom::Start(70_000)).unwrap();
                f.write_all(b"MUTATED_TAIL").unwrap();
            },
        )
        .expect("single-pass isolation succeeds under partner write");

        let actual_sha = crate::lean_runner::sha256_file_hex(&iso.path).unwrap();
        let expected_name = format!("anneal-mir-eval-{}", &actual_sha[..16]);
        assert_eq!(iso.path.file_name().and_then(|n| n.to_str()), Some(expected_name.as_str()));
        assert_ne!(iso.path.file_name(), None);
        // Verify filename matches exact copied bytes (never pre-mutation hash).
        let mut mut_bytes = initial.clone();
        mut_bytes[70_000..70_012].copy_from_slice(b"MUTATED_TAIL");
        assert_eq!(fs::read(&iso.path).unwrap(), mut_bytes);
    }

    #[cfg(unix)]
    #[test]
    fn stage_mir_eval_bin_no_links_isolates_from_source_mutation() {
        use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let bin = root.join("anneal-mir-eval");
        fs::write(&bin, b"#!/bin/sh\necho ORIGINAL\n").unwrap();
        fs::set_permissions(&bin, fs::Permissions::from_mode(0o755)).unwrap();

        let prepared =
            stage_mir_eval_bin_no_links(&bin).expect("clean --mir-eval-bin must stage cleanly");
        assert_ne!(prepared.path, bin);
        assert_eq!(fs::symlink_metadata(&prepared.path).unwrap().nlink(), 1);
        assert_eq!(
            fs::symlink_metadata(&prepared.path).unwrap().permissions().mode() & 0o777,
            0o555
        );
        assert_eq!(
            fs::symlink_metadata(prepared.path.parent().unwrap()).unwrap().permissions().mode()
                & 0o777,
            0o555
        );

        // Overwrite and replace the original writable binary after staging;
        // the frozen copy must retain the original bytes.
        fs::write(&bin, b"#!/bin/sh\necho TAMPERED\n").unwrap();
        assert_eq!(fs::read(&prepared.path).unwrap(), b"#!/bin/sh\necho ORIGINAL\n");

        let hard = root.join("hard-mir-eval");
        fs::hard_link(&bin, &hard).unwrap();
        let err_hard = stage_mir_eval_bin_no_links(&hard).unwrap_err();
        assert!(err_hard.contains("hardlink"), "{err_hard}");

        let sym = root.join("sym-mir-eval");
        std::os::unix::fs::symlink(&bin, &sym).unwrap();
        let err_sym = stage_mir_eval_bin_no_links(&sym).unwrap_err();
        assert!(err_sym.contains("symlink"), "{err_sym}");

        let staged_path = prepared.path.clone();
        drop(prepared);
        assert!(!staged_path.exists(), "drop must clean up staged --mir-eval-bin");
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn stage_mir_eval_bin_no_links_accepts_frozen_proc_fd_and_rejects_writable() {
        use std::os::{fd::AsRawFd as _, unix::fs::PermissionsExt as _};

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");

        // 1. A frozen `0o555` `/proc/self/fd/<fd>/.anneal-isolated-bins/...`
        // tree stays stageable even after its backing directory is renamed.
        let stage_tmp = tempfile::Builder::new()
            .prefix("frozen-proc-fd-")
            .tempdir_in(&root)
            .expect("stage tempdir");
        let stage_disk = fs::canonicalize(stage_tmp.path()).expect("canon stage");
        let staging = crate::rustc_runner::ImmutableStagingDir::build_and_pin_with_writable(
            stage_tmp,
            "frozen-proc-fd",
            |priv_root, _pinned| {
                let iso_dir = priv_root.join(".anneal-isolated-bins");
                fs::create_dir_all(&iso_dir).unwrap();
                let bin = iso_dir.join("anneal-mir-eval-pinned");
                fs::write(&bin, b"#!/bin/sh\necho PINNED_EVAL\n").unwrap();
                fs::set_permissions(&bin, fs::Permissions::from_mode(0o555)).unwrap();
                Ok(None)
            },
        )
        .expect("build frozen staging dir");
        let pinned_bin =
            staging.pin_path(Path::new(".anneal-isolated-bins/anneal-mir-eval-pinned"));
        assert!(pinned_bin.starts_with("/proc/self/fd/"), "{}", pinned_bin.display());

        let renamed = root.join("renamed-stage");
        fs::rename(&stage_disk, &renamed).unwrap();
        let attacker_iso = stage_disk.join(".anneal-isolated-bins");
        fs::create_dir_all(&attacker_iso).unwrap();
        fs::write(attacker_iso.join("anneal-mir-eval-pinned"), b"#!/bin/sh\necho ATTACKER\n")
            .unwrap();

        let prepared = stage_mir_eval_bin_no_links(&pinned_bin)
            .expect("stage_mir_eval_bin_no_links must accept frozen /proc/self/fd binary");
        assert_eq!(fs::read(&prepared.path).unwrap(), b"#!/bin/sh\necho PINNED_EVAL\n");
        drop(prepared);
        drop(staging);
        crate::rustc_runner::restore_dir_write_perms_top_down(&renamed);
        fs::remove_dir_all(&renamed).unwrap();

        // 2. An unfrozen writable dir exposed via `/proc/self/fd/<fd>/...`
        // must fail closed before opening or staging the leaf.
        let writable_dir = root.join("writable-fd-dir");
        fs::create_dir_all(&writable_dir).unwrap();
        let writable_bin = writable_dir.join("anneal-mir-eval");
        fs::write(&writable_bin, b"#!/bin/sh\necho WRITABLE\n").unwrap();
        fs::set_permissions(&writable_bin, fs::Permissions::from_mode(0o555)).unwrap();
        let writable_fd =
            crate::rustc_runner::open_dir_handle_no_symlinks(&writable_dir, None, "writable dir")
                .unwrap();
        let raw_writable =
            PathBuf::from(format!("/proc/self/fd/{}/anneal-mir-eval", writable_fd.as_raw_fd()));
        let err = stage_mir_eval_bin_no_links(&raw_writable).unwrap_err();
        assert!(err.contains("frozen non-writable"), "{err}");
    }

    #[cfg(unix)]
    #[test]
    fn resolve_leg3_toolchain_and_build_stage_non_store_cargo_before_exec() {
        use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let fake_store = root.join("nix/store");
        let ws = root.join("ws");
        let eval_dir = ws.join("tools/anneal-mir-eval");
        let tc = root.join("writable-tc");
        let clean_ch = root.join("clean-cargo-home");
        for d in [&fake_store, &eval_dir, &tc.join("bin"), &tc.join("lib"), &clean_ch] {
            fs::create_dir_all(d).unwrap();
        }
        let manifest = eval_dir.join("Cargo.toml");
        fs::write(&manifest, "[package]\nname = \"anneal-mir-eval\"\nversion = \"0.1.0\"\n")
            .unwrap();

        let fake_cargo = tc.join("bin/cargo");
        let cargo_script = "#!/bin/sh\nset -e\n\
             mp=\"\"\nprev=\"\"\n\
             for a in \"$@\"; do\n  if [ \"$prev\" = \"--manifest-path\" ]; then mp=\"$a\"; break; fi\n  prev=\"$a\"\ndone\n\
             dbg=\"$CARGO_TARGET_DIR/debug\"\nmkdir -p \"$dbg\"\n\
             printf '#!/bin/sh\\nexit 43\\n' > \"$dbg/anneal-mir-eval\"\n\
             chmod 755 \"$dbg/anneal-mir-eval\"\n\
             printf '{\"reason\":\"compiler-artifact\",\"manifest_path\":\"%s\",\"target\":{\"kind\":[\"bin\"],\"name\":\"anneal-mir-eval\"},\"profile\":{\"test\":false},\"executable\":\"%s\"}\\n' \"$mp\" \"$dbg/anneal-mir-eval\"\n"
        .to_owned();
        fs::write(&fake_cargo, &cargo_script).unwrap();
        fs::set_permissions(&fake_cargo, fs::Permissions::from_mode(0o755)).unwrap();

        // Simulate an attacker overwriting `fake_cargo` during
        // `rustc --print sysroot` AFTER Leg-3 toolchain resolution.
        let fake_rustc = tc.join("bin/rustc");
        fs::write(
            &fake_rustc,
            format!(
                "#!/bin/sh\n\
                 if [ \"${{1:-}}\" = \"--print\" ] && [ \"${{2:-}}\" = \"sysroot\" ]; then\n\
                   printf '#!/bin/sh\\necho TAMPERED_CARGO >&2\\nexit 99\\n' > '{}'\n\
                   printf '%s\\n' '{}'\nexit 0\n\
                 fi\n\
                 if [ \"${{1:-}}\" = \"-vV\" ]; then\n\
                   printf 'rustc 1.90.0\\nhost: x86_64-unknown-linux-gnu\\n'\nexit 0\n\
                 fi\nexit 0\n",
                fake_cargo.display(),
                tc.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_rustc, fs::Permissions::from_mode(0o755)).unwrap();

        let pinned = resolve_leg3_pinned_toolchain_with_store(
            &fake_rustc,
            &fake_cargo,
            None,
            &ws,
            &ws,
            None,
            Some(&clean_ch),
            None,
            &fake_store,
        )
        .expect("Leg-3 toolchain resolution must stage writable cargo");
        assert_ne!(pinned.pinned_cargo, fake_cargo);
        assert_eq!(fs::symlink_metadata(&pinned.pinned_cargo).unwrap().nlink(), 1);
        assert_eq!(
            fs::symlink_metadata(&pinned.pinned_cargo).unwrap().permissions().mode() & 0o777,
            0o555
        );
        assert_eq!(
            fs::symlink_metadata(pinned.pinned_cargo.parent().unwrap())
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o555
        );
        let path_dirs: Vec<PathBuf> = env::split_paths(&pinned.child_path).collect();
        assert!(path_dirs.contains(&pinned.pinned_cargo.parent().unwrap().to_path_buf()));
        assert!(!path_dirs.contains(&tc.join("bin")));
        // `fake_rustc --print sysroot` overwrote `fake_cargo`, yet staged
        // `pinned_cargo` kept original bytes.
        assert_eq!(fs::read_to_string(&pinned.pinned_cargo).unwrap(), cargo_script);
        drop(pinned);

        // Restore original cargo and verify full build tolerates concurrent
        // tamper during sysroot probe.
        fs::write(&fake_cargo, &cargo_script).unwrap();
        fs::set_permissions(&fake_cargo, fs::Permissions::from_mode(0o755)).unwrap();
        let built = build_mir_eval_from_manifest_full_with_store(
            &manifest,
            &ws,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(clean_ch.as_os_str()),
            None,
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .expect("build must execute staged cargo even if writable source is tampered mid-probe");
        assert_eq!(fs::read(&built.path).unwrap(), b"#!/bin/sh\nexit 43\n");
    }

    #[cfg(unix)]
    #[test]
    fn reject_ambient_cargo_configs_and_build_anchor_and_validate_home_with_cargo_home() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let fake_store = root.join("nix/store");
        let caller_cwd = root.join("caller");
        let ws = root.join("ws");
        let eval_dir = ws.join("tools/anneal-mir-eval");
        let tc = root.join("writable-tc");
        let clean_ch = root.join("clean-cargo-home");
        let clean_rh = root.join("clean-rustup-home");
        let rel_home_caller = caller_cwd.join("rel-home");
        let poison_ws_rustup = ws.join("rel-home/.rustup");
        for d in [
            &fake_store,
            &eval_dir,
            &tc.join("bin"),
            &tc.join("lib"),
            &clean_ch,
            &clean_rh,
            &rel_home_caller,
            &poison_ws_rustup,
        ] {
            fs::create_dir_all(d).unwrap();
        }
        let manifest = eval_dir.join("Cargo.toml");
        fs::write(&manifest, "[package]\nname = \"anneal-mir-eval\"\nversion = \"0.1.0\"\n")
            .unwrap();
        fs::write(clean_rh.join("settings.toml"), "default_toolchain = \"nightly\"\n").unwrap();
        let poison_target = ws.join("poison-settings.toml");
        fs::write(&poison_target, "default_toolchain = \"evil\"\n").unwrap();
        symlink(&poison_target, poison_ws_rustup.join("settings.toml")).unwrap();

        let ran_marker = root.join("cargo-ran.txt");
        let home_log = root.join("cargo-home-env.txt");
        let fake_cargo = tc.join("bin/cargo");
        fs::write(
            &fake_cargo,
            format!(
                "#!/bin/sh\nset -eu\n\
                 mp=\"\"\nprev=\"\"\n\
                 for a in \"$@\"; do\n  if [ \"$prev\" = \"--manifest-path\" ]; then mp=\"$a\"; break; fi\n  prev=\"$a\"\ndone\n\
                 printf '%s\\n' \"${{HOME:-}}\" > '{}'\n\
                 : > '{}'\n\
                 dbg=\"$CARGO_TARGET_DIR/debug\"\nmkdir -p \"$dbg\"\n\
                 printf '#!/bin/sh\\nexit 0\\n' > \"$dbg/anneal-mir-eval\"\n\
                 chmod 755 \"$dbg/anneal-mir-eval\"\n\
                 printf '{{\"reason\":\"compiler-artifact\",\"manifest_path\":\"%s\",\"target\":{{\"kind\":[\"bin\"],\"name\":\"anneal-mir-eval\"}},\"profile\":{{\"test\":false}},\"executable\":\"%s\"}}\\n' \"$mp\" \"$dbg/anneal-mir-eval\"\n",
                home_log.display(),
                ran_marker.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_cargo, fs::Permissions::from_mode(0o755)).unwrap();

        let fake_rustc = tc.join("bin/rustc");
        fs::write(
            &fake_rustc,
            format!(
                "#!/bin/sh\n\
                 if [ \"${{1:-}}\" = \"--print\" ] && [ \"${{2:-}}\" = \"sysroot\" ]; then\n\
                   printf '%s\\n' '{}'\nexit 0\n\
                 fi\n\
                 if [ \"${{1:-}}\" = \"-vV\" ]; then\n\
                   printf 'rustc 1.90.0\\nhost: x86_64-unknown-linux-gnu\\n'\nexit 0\n\
                 fi\nexit 0\n",
                tc.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_rustc, fs::Permissions::from_mode(0o755)).unwrap();

        let sym_home = caller_cwd.join("sym-home");
        symlink(&rel_home_caller, &sym_home).unwrap();
        for bad_home in [sym_home.as_path(), Path::new("../outside-home")] {
            let rej_err = reject_ambient_cargo_configs(
                &ws,
                std::slice::from_ref(&ws),
                Some(&clean_ch),
                Some(bad_home),
                &caller_cwd,
            )
            .unwrap_err();
            assert!(rej_err.contains("HOME"), "{rej_err}");

            let build_err = build_mir_eval_from_manifest_full_with_store(
                &manifest,
                &caller_cwd,
                Some(fake_cargo.as_os_str()),
                Some(fake_rustc.as_os_str()),
                None,
                None,
                Some(clean_ch.as_os_str()),
                Some(bad_home.as_os_str()),
                Some(clean_rh.as_os_str()),
                None,
                None,
                None,
                &fake_store,
            )
            .unwrap_err();
            assert!(build_err.contains("HOME"), "{build_err}");
            assert!(!ran_marker.exists(), "cargo must never run for invalid HOME");
        }

        // Relative `HOME` anchors to `caller_cwd` even when `CARGO_HOME` is
        // set and `RUSTUP_HOME` is unset, bypassing `ws/rel-home/.rustup`.
        let (ret_ch, ret_home) = reject_ambient_cargo_configs(
            &ws,
            std::slice::from_ref(&ws),
            Some(&clean_ch),
            Some(Path::new("rel-home")),
            &caller_cwd,
        )
        .expect("clean relative HOME must anchor to caller_cwd");
        assert_eq!(ret_ch.as_deref(), Some(clean_ch.as_path()));
        assert_eq!(ret_home.as_deref(), Some(rel_home_caller.as_path()));

        let _built = build_mir_eval_from_manifest_full_with_store(
            &manifest,
            &caller_cwd,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(clean_ch.as_os_str()),
            Some(OsStr::new("rel-home")),
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .expect("anchored relative HOME must pass clean HOME/.rustup check");
        assert!(ran_marker.exists());
        assert_eq!(
            fs::read_to_string(&home_log).unwrap().trim(),
            rel_home_caller.display().to_string()
        );

        // Symlinked `caller_cwd/rel-home/.rustup` must now fail closed when
        // `CARGO_HOME` is set and `RUSTUP_HOME` is unset.
        fs::remove_file(&ran_marker).unwrap();
        symlink(&poison_ws_rustup, rel_home_caller.join(".rustup")).unwrap();
        let sym_rustup_err = build_mir_eval_from_manifest_full_with_store(
            &manifest,
            &caller_cwd,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(clean_ch.as_os_str()),
            Some(OsStr::new("rel-home")),
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .unwrap_err();
        assert!(sym_rustup_err.contains("HOME/.rustup"), "{sym_rustup_err}");
        // Check that `resolve_rustup_proxy_binary_with_store` stages non-store
        // `rustup` before running `rustup which` and never runs writable path.
        let stage_proxy_dir = root.join("staged-rustup-check");
        fs::create_dir_all(&stage_proxy_dir).unwrap();
        let rustup_exec_log = root.join("rustup-exec-path.txt");
        fs::write(
            stage_proxy_dir.join("rustup"),
            format!(
                "#!/bin/sh\nset -eu\n\
                 dir0=${{0%/*}}\nbase0=${{0##*/}}\n\
                 real0=\"$(cd \"$dir0\" && pwd -P)/$base0\"\n\
                 printf '%s\\n%s\\n' \"$0\" \"$real0\" >> '{}'\n\
                 if [ \"${{1:-}}\" = \"which\" ] && [ \"${{2:-}}\" = \"cargo\" ]; then\n\
                   printf '%s\\n' '{}'\nexit 0\nfi\n\
                 if [ \"${{1:-}}\" = \"which\" ] && [ \"${{2:-}}\" = \"rustc\" ]; then\n\
                   printf '%s\\n' '{}'\nexit 0\nfi\nexit 1\n",
                rustup_exec_log.display(),
                fake_cargo.display(),
                fake_rustc.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(stage_proxy_dir.join("rustup"), fs::Permissions::from_mode(0o755))
            .unwrap();
        symlink("rustup", stage_proxy_dir.join("cargo")).unwrap();
        let resolved_staged_cargo = resolve_rustup_proxy_binary_with_store(
            &stage_proxy_dir.join("cargo"),
            "cargo",
            &caller_cwd,
            &ws,
            None,
            Some(&clean_rh),
            None,
            None,
            &fake_store,
        )
        .expect("staged rustup proxy resolution must succeed");
        assert_eq!(resolved_staged_cargo, fake_cargo);
        let ran_lines: Vec<String> =
            fs::read_to_string(&rustup_exec_log).unwrap().lines().map(ToOwned::to_owned).collect();
        assert_eq!(ran_lines.len(), 2, "{ran_lines:?}");
        let ran_rustup_path = Path::new(&ran_lines[0]);
        assert_ne!(ran_rustup_path, stage_proxy_dir.join("rustup").as_path());
        assert!(ran_lines[0].starts_with("/proc/self/fd/"));
        assert!(ran_rustup_path.ends_with("bin/rustup"));
        assert!(
            !Path::new(&ran_lines[1]).exists(),
            "staged rustup probe dir must be cleaned up: {ran_lines:?}"
        );
        // Unsafe `RUSTUP_TOOLCHAIN` values (path separators, `..`, NUL) must
        // fail closed BEFORE invoking `rustup which` (neither proxy helper nor
        // full manifest build may spawn `rustup`).
        let before_bad_len = fs::read_to_string(&rustup_exec_log).unwrap().len();
        for bad_rt in ["../evil", "/tmp/evil", "dir/tc", "dir\\tc", "a\0b"] {
            let err_proxy = resolve_rustup_proxy_binary_with_store(
                &stage_proxy_dir.join("cargo"),
                "cargo",
                &caller_cwd,
                &ws,
                None,
                Some(&clean_rh),
                Some(OsStr::new(bad_rt)),
                None,
                &fake_store,
            )
            .unwrap_err();
            assert!(err_proxy.contains("RUSTUP_TOOLCHAIN"), "{bad_rt}: {err_proxy}");
            let err_build = build_mir_eval_from_manifest_full_with_store(
                &manifest,
                &caller_cwd,
                None,
                None,
                Some(stage_proxy_dir.as_os_str()),
                None,
                Some(clean_ch.as_os_str()),
                None,
                Some(clean_rh.as_os_str()),
                Some(OsStr::new(bad_rt)),
                None,
                None,
                &fake_store,
            )
            .unwrap_err();
            assert!(err_build.contains("RUSTUP_TOOLCHAIN"), "{bad_rt}: {err_build}");
        }
        assert_eq!(fs::read_to_string(&rustup_exec_log).unwrap().len(), before_bad_len);
        let ok_named = resolve_rustup_proxy_binary_with_store(
            &stage_proxy_dir.join("cargo"),
            "cargo",
            &caller_cwd,
            &ws,
            None,
            Some(&clean_rh),
            Some(OsStr::new("nightly-2026-05-31")),
            None,
            &fake_store,
        )
        .expect("named RUSTUP_TOOLCHAIN must succeed");
        assert_eq!(ok_named, fake_cargo);

        // Full non-store sysroot toolchain (`lib/rustlib/` present) must stage
        // `bin/` + `lib/` + `lib/rustlib/` into one immutable sysroot so Linux
        // `dladdr(librustc_driver)` `--print sysroot` preserves `lib/rustlib`.
        let full_tc = root.join("full-dladdr-tc");
        fs::create_dir_all(full_tc.join("bin")).unwrap();
        fs::create_dir_all(full_tc.join("lib/rustlib/host/lib")).unwrap();
        fs::write(full_tc.join("lib/libstd.so"), b"full-tc-so").unwrap();
        let orig_rlib = full_tc.join("lib/rustlib/host/lib/libstd.rlib");
        fs::write(&orig_rlib, b"full-tc-rlib").unwrap();
        let dladdr_rustc = full_tc.join("bin/rustc");
        fs::write(
            &dladdr_rustc,
            "#!/bin/sh\n\
             if [ \"${1:-}\" = \"--print\" ] && [ \"${2:-}\" = \"sysroot\" ]; then\n\
               real_ld=$(cd \"${LD_LIBRARY_PATH%%:*}\" && pwd -P)\n\
               dirname \"$real_ld\"\nexit 0\n\
             fi\n\
             if [ \"${1:-}\" = \"-vV\" ]; then\n\
               printf 'rustc 1.90.0\\nhost: x86_64-unknown-linux-gnu\\n'\nexit 0\n\
             fi\nexit 0\n",
        )
        .unwrap();
        fs::set_permissions(&dladdr_rustc, fs::Permissions::from_mode(0o755)).unwrap();
        let dladdr_cargo = full_tc.join("bin/cargo");
        fs::write(&dladdr_cargo, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&dladdr_cargo, fs::Permissions::from_mode(0o755)).unwrap();
        let pinned_full = resolve_leg3_pinned_toolchain_with_store(
            &dladdr_rustc,
            &dladdr_cargo,
            None,
            &ws,
            &ws,
            None,
            Some(&clean_ch),
            None,
            &fake_store,
        )
        .expect("full sysroot toolchain staging must preserve lib/rustlib");
        assert_ne!(pinned_full.pinned_rustc, dladdr_rustc);
        let staged_sys_root = Path::new(&pinned_full.ld_library_path).parent().unwrap();
        assert_eq!(pinned_full.pinned_rustc.parent().unwrap().parent().unwrap(), staged_sys_root);
        let staged_rlib = staged_sys_root.join("lib/rustlib/host/lib/libstd.rlib");
        fs::write(&orig_rlib, b"tampered-rlib").unwrap();
        assert_eq!(fs::read(&staged_rlib).unwrap(), b"full-tc-rlib");
    }

    #[cfg(unix)]
    #[test]
    fn dirfd_open_pins_executables_and_settings_toml_across_parent_renames_and_writes() {
        use std::os::unix::fs::PermissionsExt as _;

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let fake_store = root.join("nix/store");
        let orig_dir = root.join("orig-bin-dir");
        let moved_dir = root.join("moved-bin-dir");
        let rh = root.join("rustup-home");
        let work_dir = root.join("ws/pkg");
        for d in [&fake_store, &orig_dir, &rh, &work_dir] {
            fs::create_dir_all(d).unwrap();
        }

        // 1. Retained parent dirfd & open file survive renaming `orig_dir` and
        // planting a replacement directory with attacker bytes at `orig_dir`.
        let orig_bin = orig_dir.join("anneal-mir-eval");
        fs::write(&orig_bin, b"#!/bin/sh\necho FROM_PRE_RENAME_FD\n").unwrap();
        fs::set_permissions(&orig_bin, fs::Permissions::from_mode(0o755)).unwrap();
        let opened = crate::rustc_runner::open_verified_executable_via_dirfd(
            &orig_bin,
            &root,
            true,
            "--mir-eval-bin",
        )
        .expect("open via dirfd succeeds");
        fs::rename(&orig_dir, &moved_dir).unwrap();
        fs::create_dir_all(&orig_dir).unwrap();
        fs::write(&orig_bin, b"#!/bin/sh\necho ATTACKER_SWAPPED\n").unwrap();
        let (staged, _sha, staging) = stage_opened_single_link_executable_with_hook(
            opened,
            "anneal-mir-eval",
            None,
            false,
            || {},
        )
        .expect("staging from opened fd succeeds after parent rename");
        assert_eq!(fs::read(&staged).unwrap(), b"#!/bin/sh\necho FROM_PRE_RENAME_FD\n");
        drop(staging);

        // 2. When `RUSTUP_TOOLCHAIN` is unset, `pin_rustup_settings` derives it
        // from `[overrides]`/`default_toolchain` and ignores subsequent writes
        // to `settings.toml`, OR freezes a private immutable `RUSTUP_HOME`.
        let settings_path = rh.join("settings.toml");
        fs::write(
            &settings_path,
            format!(
                "default_toolchain = \"base-tc\"\n[overrides]\n\"{}\" = \"ovr-tc\"\n",
                work_dir.display()
            ),
        )
        .unwrap();
        let pinned_ovr =
            pin_rustup_settings(Some(&rh), None, None, &work_dir, None).expect("pin overrides");
        fs::write(&settings_path, "default_toolchain = \"tampered-tc\"\n").unwrap();
        assert_eq!(pinned_ovr.effective_toolchain.as_deref(), Some(OsStr::new("ovr-tc")));
        assert!(pinned_ovr._pin_staging.is_none());

        fs::write(&settings_path, "version = \"12\"\n").unwrap();
        let pinned_priv = pin_rustup_settings(Some(&rh), None, None, &work_dir, None)
            .expect("pin private settings");
        assert!(pinned_priv.effective_toolchain.is_none());
        let priv_rh = pinned_priv.effective_rustup_home.as_ref().expect("private RUSTUP_HOME");
        assert_ne!(priv_rh, &rh);
        fs::write(&settings_path, "default_toolchain = \"hijacked-tc\"\n").unwrap();
        assert_eq!(
            fs::read_to_string(priv_rh.join("settings.toml")).unwrap(),
            "version = \"12\"\n"
        );
    }

    #[cfg(unix)]
    #[test]
    fn leg3_manifest_build_materializes_immutable_source_graph_and_rejects_links() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let fake_store = root.join("nix/store");
        let ws = root.join("ws");
        let eval_dir = ws.join("tools/anneal-mir-eval");
        let dep_dir = ws.join("crates/helper-dep");
        let ch = root.join("cargo-home");
        for d in [
            &fake_store,
            &eval_dir.join("src"),
            &eval_dir.join("target/stale"),
            &dep_dir.join("src"),
            &ws.join(".git"),
            &ch,
        ] {
            fs::create_dir_all(d).unwrap();
        }
        fs::write(ws.join("Cargo.toml"), "[workspace]\nmembers = [\"tools/anneal-mir-eval\"]\n")
            .unwrap();
        fs::write(
            eval_dir.join("Cargo.toml"),
            "[package]\nname = \"anneal-mir-eval\"\nversion = \"0.1.0\"\n\
             [dependencies]\nhelper-dep = { path = \"../../crates/helper-dep\" }\n",
        )
        .unwrap();
        fs::write(eval_dir.join("build.rs"), "fn main() { /* SAFE_BUILD */ }\n").unwrap();
        fs::write(eval_dir.join("src/main.rs"), "fn main() {}\n").unwrap();
        fs::write(
            dep_dir.join("Cargo.toml"),
            "[package]\nname = \"helper-dep\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        fs::write(dep_dir.join("src/lib.rs"), "pub fn help() {}\n").unwrap();
        // Skipped build/VCS dirs outside source graph may hold stale/git data.
        fs::write(eval_dir.join("target/stale/junk"), b"skip").unwrap();
        fs::write(ws.join(".git/HEAD"), b"ref: refs/heads/main\n").unwrap();

        let ran_marker = root.join("cargo-ran.txt");
        let fake_rustc = root.join("fake-rustc.sh");
        fs::write(
            &fake_rustc,
            format!(
                "#!/bin/sh\nif [ \"${{1:-}}\" = \"--print\" ]; then printf '%s\\n' '{}'; exit 0; fi\n\
                 if [ \"${{1:-}}\" = \"-vV\" ]; then printf 'rustc 1.90.0\\nhost: x86_64-unknown-linux-gnu\\n'; exit 0; fi\n",
                root.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_rustc, fs::Permissions::from_mode(0o755)).unwrap();

        let observed_log = root.join("observed-sources.txt");
        let fake_cargo = root.join("fake-cargo.sh");
        fs::write(
            &fake_cargo,
            format!(
                "#!/bin/sh\nset -eu\n: > '{}'\n\
                 mp=\"\"\nprev=\"\"\n\
                 for a in \"$@\"; do\n  if [ \"$prev\" = \"--manifest-path\" ]; then mp=\"$a\"; break; fi\n  prev=\"$a\"\ndone\n\
                 pkg_dir=\"$(dirname \"$mp\")\"\n\
                 build_rs=\"$(cat \"$pkg_dir/build.rs\")\"\n\
                 dep_rs=\"$(cat \"$pkg_dir/../../crates/helper-dep/src/lib.rs\")\"\n\
                 printf 'CWD=%s\\nMP=%s\\nBUILD=%s\\nDEP=%s\\n' \"$PWD\" \"$mp\" \"$build_rs\" \"$dep_rs\" > '{}'\n\
                 if [ -e \"$pkg_dir/target\" ] || [ -e \"$pkg_dir/../../.git\" ]; then exit 91; fi\n\
                 if [ -w \"$pkg_dir/src/main.rs\" ] || [ -w \"$pkg_dir/../../crates/helper-dep/src/lib.rs\" ]; then exit 92; fi\n\
                 dbg=\"$CARGO_TARGET_DIR/debug\"\nmkdir -p \"$dbg\"\n\
                 printf '#!/bin/sh\\nexit 0\\n' > \"$dbg/anneal-mir-eval\"\n\
                 chmod 755 \"$dbg/anneal-mir-eval\"\n\
                 printf '{{\"reason\":\"compiler-artifact\",\"manifest_path\":\"%s\",\"target\":{{\"kind\":[\"bin\"],\"name\":\"anneal-mir-eval\"}},\"profile\":{{\"test\":false}},\"executable\":\"%s\"}}\\n' \"$mp\" \"$dbg/anneal-mir-eval\"\n",
                ran_marker.display(),
                observed_log.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_cargo, fs::Permissions::from_mode(0o755)).unwrap();

        let built = build_mir_eval_from_manifest_full_with_store(
            &eval_dir.join("Cargo.toml"),
            &ws,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(ch.as_os_str()),
            None,
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .expect("staged source graph build succeeds");
        drop(built);
        let obs = fs::read_to_string(&observed_log).unwrap();
        assert!(obs.contains("MP=/proc/self/fd/"), "{obs}");
        let obs_cwd = obs.lines().find_map(|l| l.strip_prefix("CWD=")).unwrap_or("");
        assert!(
            !Path::new(obs_cwd).starts_with(&ws)
                && obs_cwd.contains("anneal-mir-eval-src-")
                && obs_cwd.ends_with("/tools/anneal-mir-eval"),
            "{obs}"
        );
        assert!(obs.contains("SAFE_BUILD"), "{obs}");
        assert!(obs.contains("pub fn help()"), "{obs}");

        // Symlink inside `path` dependency must fail BEFORE Cargo runs.
        fs::remove_file(&ran_marker).unwrap();
        let outside_rs = root.join("outside.rs");
        fs::write(&outside_rs, "pub fn evil() {}\n").unwrap();
        symlink(&outside_rs, dep_dir.join("src/evil.rs")).unwrap();
        let sym_err = build_mir_eval_from_manifest_full_with_store(
            &eval_dir.join("Cargo.toml"),
            &ws,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(ch.as_os_str()),
            None,
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .unwrap_err();
        assert!(sym_err.contains("symlink"), "{sym_err}");
        assert!(!ran_marker.exists());
        fs::remove_file(dep_dir.join("src/evil.rs")).unwrap();

        // Hardlink inside `build.rs` must fail BEFORE Cargo runs.
        let hard_src = root.join("hard-build.rs");
        fs::write(&hard_src, "fn main() {}\n").unwrap();
        fs::remove_file(eval_dir.join("build.rs")).unwrap();
        fs::hard_link(&hard_src, eval_dir.join("build.rs")).unwrap();
        let hard_err = build_mir_eval_from_manifest_full_with_store(
            &eval_dir.join("Cargo.toml"),
            &ws,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(ch.as_os_str()),
            None,
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .unwrap_err();
        assert!(hard_err.contains("hardlink"), "{hard_err}");
        assert!(!ran_marker.exists());

        // Restore `build.rs` and verify `[replace]` table traversal rejects
        // absolute non-store paths and stages clean relative replacements.
        fs::remove_file(eval_dir.join("build.rs")).unwrap();
        fs::write(eval_dir.join("build.rs"), "fn main() { /* SAFE_BUILD */ }\n").unwrap();
        let rep_dir = ws.join("crates/rep-dep");
        fs::create_dir_all(rep_dir.join("src")).unwrap();
        fs::write(
            rep_dir.join("Cargo.toml"),
            "[package]\nname = \"rep-dep\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        fs::write(rep_dir.join("src/lib.rs"), "pub fn rep() {}\n").unwrap();
        fs::write(
            ws.join("Cargo.toml"),
            format!(
                "[workspace]\nmembers = [\"tools/anneal-mir-eval\"]\n\
                 [replace]\n\"rep-dep:0.1.0\" = {{ path = \"{}\" }}\n",
                root.join("outside-rep").display()
            ),
        )
        .unwrap();
        let abs_rep_err = build_mir_eval_from_manifest_full_with_store(
            &eval_dir.join("Cargo.toml"),
            &ws,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(ch.as_os_str()),
            None,
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .unwrap_err();
        assert!(abs_rep_err.contains("outside staged source tree"), "{abs_rep_err}");
        assert!(!ran_marker.exists());

        fs::write(
            ws.join("Cargo.toml"),
            "[workspace]\nmembers = [\"tools/anneal-mir-eval\"]\n\
             [replace]\n\"rep-dep:0.1.0\" = { path = \"crates/rep-dep\" }\n",
        )
        .unwrap();
        let rep_built = build_mir_eval_from_manifest_full_with_store(
            &eval_dir.join("Cargo.toml"),
            &ws,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(ch.as_os_str()),
            None,
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .expect("relative [replace] stages cleanly");
        drop(rep_built);
        let rep_obs = fs::read_to_string(&observed_log).unwrap();
        let rep_cwd = rep_obs.lines().find_map(|l| l.strip_prefix("CWD=")).unwrap();
        // The last invocation built from the staged workspace root; confirm
        // `crates/rep-dep/src/lib.rs` does not trigger a symlink rejection
        // when tainted with a symlink on retry.
        assert!(!rep_cwd.is_empty());
        fs::remove_file(&ran_marker).unwrap();
        symlink(&outside_rs, rep_dir.join("src/evil.rs")).unwrap();
        let rep_sym_err = build_mir_eval_from_manifest_full_with_store(
            &eval_dir.join("Cargo.toml"),
            &ws,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(ch.as_os_str()),
            None,
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .unwrap_err();
        assert!(rep_sym_err.contains("symlink"), "{rep_sym_err}");
        assert!(!ran_marker.exists());
    }

    #[cfg(unix)]
    #[test]
    fn leg3_manifest_build_pins_cargo_home_config_and_materializes_sources() {
        use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let fake_store = root.join("nix/store");
        let ws = root.join("ws");
        let eval_dir = ws.join("tools/anneal-mir-eval");
        let tc = root.join("tc");
        let ext_ch = root.join("ext-cargo-home");
        let empty_ch = root.join("empty-cargo-home");
        let vendor_dir = root.join("vendor");
        let vend_crate = vendor_dir.join("vendored_dep");
        let outside = root.join("outside");
        for d in [
            &fake_store,
            &eval_dir.join("src"),
            &tc.join("bin"),
            &tc.join("lib"),
            &ext_ch,
            &empty_ch,
            &vend_crate.join("src"),
            &outside,
        ] {
            fs::create_dir_all(d).unwrap();
        }

        fs::write(ws.join("Cargo.toml"), "[workspace]\nmembers = [\"tools/anneal-mir-eval\"]\n")
            .unwrap();
        fs::write(
            eval_dir.join("Cargo.toml"),
            "[package]\nname = \"anneal-mir-eval\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        fs::write(eval_dir.join("src/main.rs"), "fn main() {}\n").unwrap();
        fs::write(
            vend_crate.join("Cargo.toml"),
            "[package]\nname = \"vendored_dep\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        fs::write(vend_crate.join("build.rs"), "fn main() { /* GENUINE_VENDOR */ }\n").unwrap();
        fs::write(vend_crate.join("src/lib.rs"), "pub fn safe_v() -> u32 { 1 }\n").unwrap();
        fs::write(outside.join("secret.rs"), "pub fn evil() {}\n").unwrap();

        let ran_marker = root.join("cargo-ran");
        let obs_log = root.join("observed-cargo-home.txt");
        let fake_cargo = tc.join("bin/cargo");
        fs::write(
            &fake_cargo,
            format!(
                "#!/bin/sh\nset -eu\n: > '{}'\nmp=\"\"\nprev=\"\"\n\
                 for a in \"$@\"; do\n  if [ \"$prev\" = \"--manifest-path\" ]; then mp=\"$a\"; break; fi\n  prev=\"$a\"\ndone\n\
                 {{ printf 'CARGO_HOME=%s\\n' \"${{CARGO_HOME:-}}\";\n\
                    if [ -f \"$CARGO_HOME/config.toml\" ]; then\n\
                      printf 'CFG_START\\n'; cat \"$CARGO_HOME/config.toml\"; printf 'CFG_END\\n';\n\
                      vdir=$(sed -n 's/^directory = \"\\(.*\\)\"$/\\1/p' \"$CARGO_HOME/config.toml\" | head -n1);\n\
                      printf 'VDIR=%s\\n' \"$vdir\";\n\
                      if [ -f \"$vdir/vendored_dep/build.rs\" ]; then cat \"$vdir/vendored_dep/build.rs\"; fi;\n\
                      if [ -f \"$vdir/vendored_dep/src/lib.rs\" ]; then cat \"$vdir/vendored_dep/src/lib.rs\"; fi;\n\
                    else\n\
                      printf 'NO_CFG\\n';\n\
                    fi; }} > '{}'\n\
                 dbg=\"$CARGO_TARGET_DIR/debug\"\nmkdir -p \"$dbg\"\n\
                 printf '#!/bin/sh\\nexit 0\\n' > \"$dbg/anneal-mir-eval\"\nchmod 755 \"$dbg/anneal-mir-eval\"\n\
                 printf '{{\"reason\":\"compiler-artifact\",\"manifest_path\":\"%s\",\"target\":{{\"kind\":[\"bin\"],\"name\":\"anneal-mir-eval\"}},\"profile\":{{\"test\":false}},\"executable\":\"%s\"}}\\n' \"$mp\" \"$dbg/anneal-mir-eval\"\n",
                ran_marker.display(),
                obs_log.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_cargo, fs::Permissions::from_mode(0o755)).unwrap();

        // Race hook inside `-vV` rustc probe: mutates `ext_ch/config.toml`,
        // `vendor_dir/vendored_dep/build.rs`, and plants `empty_ch/config.toml`
        // before `cargo build` starts.
        let fake_rustc = tc.join("bin/rustc");
        fs::write(
            &fake_rustc,
            format!(
                "#!/bin/sh\nset -eu\n\
                 if [ \"${{1:-}}\" = \"--print\" ] && [ \"${{2:-}}\" = \"sysroot\" ]; then\n\
                   printf '%s\\n' '{}'\nexit 0\n\
                 fi\n\
                 if [ \"${{1:-}}\" = \"-vV\" ]; then\n\
                   if [ -f '{}/config.toml' ]; then\n\
                     printf '[build]\\nrustc-wrapper = \"/bin/false\"\\n' > '{}/config.toml'\n\
                   fi\n\
                   if [ -f '{}/vendored_dep/build.rs' ]; then\n\
                     printf 'fn main() {{ /* TAMPERED_VENDOR */ }}\\n' > '{}/vendored_dep/build.rs'\n\
                   fi\n\
                   printf '[build]\\nrustc-wrapper = \"/bin/false\"\\n' > '{}/config.toml'\n\
                   printf 'rustc 1.90.0\\nhost: x86_64-unknown-linux-gnu\\n'\nexit 0\n\
                 fi\nexit 0\n",
                tc.display(),
                ext_ch.display(),
                ext_ch.display(),
                vendor_dir.display(),
                vendor_dir.display(),
                empty_ch.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_rustc, fs::Permissions::from_mode(0o755)).unwrap();

        // 1. Disallowed `[source.<name>]` key (`local-registry`) fails closed.
        fs::write(
            ext_ch.join("config.toml"),
            format!("[source.evil]\nlocal-registry = \"{}\"\n", vendor_dir.display()),
        )
        .unwrap();
        let bad_key_err = build_mir_eval_from_manifest_full_with_store(
            &eval_dir.join("Cargo.toml"),
            &ws,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(ext_ch.as_os_str()),
            None,
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .unwrap_err();
        assert!(bad_key_err.contains("disallowed key"), "{bad_key_err}");
        assert!(!ran_marker.exists());

        // 2. Symlink and hardlink descendants inside `[source.*].directory`
        //    fail closed before Cargo runs.
        fs::write(
            ext_ch.join("config.toml"),
            format!(
                "[source.crates-io]\nreplace-with = \"anneal-vendor\"\n\
                 [source.anneal-vendor]\ndirectory = \"{}\"\n",
                vendor_dir.display()
            ),
        )
        .unwrap();
        symlink(outside.join("secret.rs"), vend_crate.join("src/evil.rs")).unwrap();
        let sym_vend_err = build_mir_eval_from_manifest_full_with_store(
            &eval_dir.join("Cargo.toml"),
            &ws,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(ext_ch.as_os_str()),
            None,
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .unwrap_err();
        assert!(sym_vend_err.contains("symlink"), "{sym_vend_err}");
        assert!(!ran_marker.exists());
        fs::remove_file(vend_crate.join("src/evil.rs")).unwrap();

        let hard_src = outside.join("hard-build.rs");
        fs::write(&hard_src, "fn main() {}\n").unwrap();
        fs::remove_file(vend_crate.join("build.rs")).unwrap();
        fs::hard_link(&hard_src, vend_crate.join("build.rs")).unwrap();
        let hard_vend_err = build_mir_eval_from_manifest_full_with_store(
            &eval_dir.join("Cargo.toml"),
            &ws,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(ext_ch.as_os_str()),
            None,
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .unwrap_err();
        assert!(hard_vend_err.contains("hardlink"), "{hard_vend_err}");
        assert!(!ran_marker.exists());
        fs::remove_file(vend_crate.join("build.rs")).unwrap();
        fs::write(vend_crate.join("build.rs"), "fn main() { /* GENUINE_VENDOR */ }\n").unwrap();

        // 3. Valid `[source]` config and vendor directory materialize into a
        //    pinned `0o555`/`0o444` private Cargo home immune to concurrent
        //    mutability in `ext_ch/config.toml` and `vendor_dir`.
        let staged_me = build_mir_eval_from_manifest_full_with_store(
            &eval_dir.join("Cargo.toml"),
            &ws,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(ext_ch.as_os_str()),
            None,
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .expect("materialized CARGO_HOME source build should succeed");
        drop(staged_me);
        let obs = fs::read_to_string(&obs_log).unwrap();
        let obs_ch = obs.lines().find_map(|l| l.strip_prefix("CARGO_HOME=")).unwrap();
        let obs_vdir = obs.lines().find_map(|l| l.strip_prefix("VDIR=")).unwrap();
        assert_ne!(Path::new(obs_ch), ext_ch);
        assert_ne!(Path::new(obs_vdir), vendor_dir);
        #[cfg(target_os = "linux")]
        {
            assert!(obs_ch.starts_with("/proc/self/fd/"), "{obs}");
            assert!(obs_vdir.starts_with("/proc/self/fd/"), "{obs}");
        }
        assert!(obs_vdir.contains("/sources/src-0"), "{obs}");
        assert!(obs.contains("GENUINE_VENDOR"), "{obs}");
        assert!(!obs.contains("TAMPERED_VENDOR"), "{obs}");
        assert!(!obs.contains("rustc-wrapper"), "{obs}");

        // 4. Empty `CARGO_HOME` also pins a private `0o555` home so concurrent
        //    creation of `empty_ch/config.toml` pre-build has zero effect.
        fs::remove_file(empty_ch.join("config.toml")).ok();
        let empty_me = build_mir_eval_from_manifest_full_with_store(
            &eval_dir.join("Cargo.toml"),
            &ws,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(empty_ch.as_os_str()),
            None,
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .expect("empty CARGO_HOME should pin empty private staging dir");
        assert_eq!(fs::symlink_metadata(&empty_me.path).unwrap().nlink(), 1);
        drop(empty_me);
        let obs2 = fs::read_to_string(&obs_log).unwrap();
        assert!(obs2.contains("NO_CFG"), "{obs2}");
        assert!(!obs2.contains("rustc-wrapper"), "{obs2}");
    }

    #[cfg(unix)]
    #[test]
    fn workspace_glob_matching_skips_literal_excluded_symlinks_and_rejects_unexcluded() {
        use std::os::unix::fs::symlink;

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let ws = root.join("ws");
        let outside = root.join("outside");
        fs::create_dir_all(ws.join("crates/ok/src")).unwrap();
        fs::create_dir_all(&outside).unwrap();
        fs::write(ws.join("crates/ok/Cargo.toml"), "[package]\nname=\"ok\"\nversion=\"0.1.0\"\n")
            .unwrap();
        fs::write(ws.join("crates/ok/src/lib.rs"), "pub fn ok() {}\n").unwrap();
        symlink(&outside, ws.join("excluded_sym")).unwrap();
        symlink(&outside, ws.join("crates/nested_sym")).unwrap();

        let excludes = vec!["excluded_sym".to_owned(), " crates/nested_sym/ ".to_owned()];
        assert!(workspace_pattern_matches_dir(&ws, "excluded_sym", &ws.join("excluded_sym")));
        assert!(workspace_pattern_matches_dir(
            &ws,
            " crates/nested_sym/ ",
            &ws.join("crates/nested_sym")
        ));
        assert!(!workspace_pattern_matches_dir(&ws, "/abs", Path::new("/abs")));

        let members = expand_glob_workspace_member_dirs(&ws, &["crates", "*"], &excludes)
            .expect("literal excluded symlinks must be skipped cleanly");
        assert_eq!(members, vec![ws.join("crates/ok")]);

        symlink(&outside, ws.join("crates/evil_sym")).unwrap();
        let err = expand_glob_workspace_member_dirs(&ws, &["crates", "*"], &excludes).unwrap_err();
        assert!(err.contains("symlink"), "{err}");
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn cargo_home_staging_writes_and_chmod_via_pinned_fd_resist_parent_rename() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let fake_store = root.join("nix/store");
        let vendor_dir = root.join("vendor");
        let vend_pkg = vendor_dir.join("vdep");
        let ch_src = root.join("ch-source");
        let ch_reg = root.join("ch-registry");
        let outside = root.join("outside");
        let stage_parent = root.join("stage-parent");
        let moved_parent = root.join("moved-parent");
        for d in [
            &fake_store,
            &vend_pkg.join("src"),
            &ch_src,
            &ch_reg.join("registry/index/idx-0"),
            &ch_reg.join("registry/cache/idx-0"),
            &outside,
            &stage_parent,
        ] {
            fs::create_dir_all(d).unwrap();
        }
        fs::write(vend_pkg.join("Cargo.toml"), "[package]\nname = \"vdep\"\nversion = \"0.1.0\"\n")
            .unwrap();
        fs::write(vend_pkg.join("src/lib.rs"), "pub fn safe_v() -> u32 { 7 }\n").unwrap();
        fs::write(
            ch_src.join("config.toml"),
            format!(
                "[source.crates-io]\nreplace-with = \"anneal-vendor\"\n\
                 [source.anneal-vendor]\ndirectory = \"{}\"\n",
                vendor_dir.display()
            ),
        )
        .unwrap();
        let crate_bytes = b"locked-crate-payload";
        let crate_path = ch_reg.join("registry/cache/idx-0/demo-1.0.0.crate");
        fs::write(&crate_path, crate_bytes).unwrap();
        let mut crate_file = fs::File::open(&crate_path).unwrap();
        let crate_sha =
            crate::rustc_runner::sha256_opened_file_hex(&mut crate_file, "test crate").unwrap();
        fs::write(ch_reg.join("registry/index/idx-0/config.json"), "{\"dl\":\"offline\"}\n")
            .unwrap();

        // 1. `[source.*]` writes and fchmod go strictly via `pinned_root`.
        let td_src = build_temp_dir("anneal-ch-race-src-", Some(&stage_parent)).unwrap();
        let mut decoy_src = None;
        let staging_src = crate::rustc_runner::ImmutableStagingDir::build_and_pin_with_writable(
            td_src,
            "raced CARGO_HOME [source]",
            |priv_root, pinned_root| {
                assert!(pinned_root.starts_with("/proc/self/fd/"));
                fs::rename(&stage_parent, &moved_parent).unwrap();
                fs::create_dir_all(priv_root).unwrap();
                symlink(&outside, priv_root.join("sources")).unwrap();
                decoy_src = Some(priv_root.to_path_buf());
                inspect_and_stage_cargo_home(
                    &ch_src,
                    &fake_store,
                    &root,
                    Some((priv_root, pinned_root)),
                    &[],
                )
            },
        )
        .expect("CARGO_HOME [source] staging must resist parent rename");
        let cfg_text = fs::read_to_string(staging_src.pin_path(Path::new("config.toml"))).unwrap();
        let parsed: toml::Table = cfg_text.parse().unwrap();
        let vdir = parsed["source"]["anneal-vendor"]["directory"].as_str().unwrap();
        assert!(vdir.starts_with("/proc/self/fd/"), "{cfg_text}");
        assert_eq!(
            fs::read_to_string(Path::new(vdir).join("vdep/src/lib.rs")).unwrap(),
            "pub fn safe_v() -> u32 { 7 }\n"
        );
        assert_eq!(
            fs::symlink_metadata(staging_src.pin_path(Path::new("config.toml")))
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o444
        );
        assert!(!decoy_src.as_ref().unwrap().join("config.toml").exists());
        drop(staging_src);
        if moved_parent.exists() {
            crate::rustc_runner::restore_dir_write_perms_top_down(&moved_parent);
            let _ = fs::remove_dir_all(&moved_parent);
        }

        // 2. Registry cache + writable `registry/src` stay FD-pinned too.
        let reg_parent = root.join("reg-stage-parent");
        let reg_moved = root.join("reg-moved-parent");
        fs::create_dir_all(&reg_parent).unwrap();
        let td_reg = build_temp_dir("anneal-ch-race-reg-", Some(&reg_parent)).unwrap();
        let locked = vec![LockedRegistryCrate {
            name: "demo".to_owned(),
            version: "1.0.0".to_owned(),
            checksum: Some(crate_sha),
        }];
        let mut decoy_reg = None;
        let staging_reg = crate::rustc_runner::ImmutableStagingDir::build_and_pin_with_writable(
            td_reg,
            "raced CARGO_HOME registry",
            |priv_root, pinned_root| {
                assert!(pinned_root.starts_with("/proc/self/fd/"));
                fs::rename(&reg_parent, &reg_moved).unwrap();
                fs::create_dir_all(priv_root).unwrap();
                symlink(&outside, priv_root.join("registry")).unwrap();
                decoy_reg = Some(priv_root.to_path_buf());
                inspect_and_stage_cargo_home(
                    &ch_reg,
                    &fake_store,
                    &root,
                    Some((priv_root, pinned_root)),
                    &locked,
                )
            },
        )
        .expect("CARGO_HOME registry staging must resist parent rename");
        let staged_crate = staging_reg.pin_path(Path::new("registry/cache/idx-0/demo-1.0.0.crate"));
        assert_eq!(fs::read(&staged_crate).unwrap(), crate_bytes);
        assert_eq!(
            fs::metadata(staging_reg.pin_path(Path::new(""))).unwrap().permissions().mode() & 0o777,
            0o555
        );
        assert_eq!(
            fs::metadata(staging_reg.pin_path(Path::new("registry/src")))
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o700
        );
        assert!(
            fs::symlink_metadata(decoy_reg.unwrap().join("registry"))
                .unwrap()
                .file_type()
                .is_symlink()
        );
        drop(staging_reg);
        if reg_moved.exists() {
            crate::rustc_runner::restore_dir_write_perms_top_down(&reg_moved);
            let _ = fs::remove_dir_all(&reg_moved);
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn mir_eval_workspace_extract_reads_manifest_via_pinned_fd_across_parent_rename() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fs::canonicalize(tmp.path()).expect("canon root");
        let fake_store = root.join("nix/store");
        let ws = root.join("ws");
        let eval_dir = ws.join("tools/anneal-mir-eval");
        let excl_dir = ws.join("tools/excluded");
        let tc = root.join("tc");
        let ch = root.join("empty-ch");
        let src_tmp = root.join("src-tmp");
        let moved_src_parent = root.join("moved-staged-parent");
        let decoy_dir = root.join("decoy");
        for d in [
            &fake_store,
            &eval_dir.join("src"),
            &excl_dir.join("src"),
            &tc.join("bin"),
            &tc.join("lib"),
            &ch,
            &src_tmp,
            &decoy_dir,
        ] {
            fs::create_dir_all(d).unwrap();
        }

        fs::write(
            ws.join("Cargo.toml"),
            "[workspace]\nresolver = \"2\"\nmembers = [\"tools/*\"]\nexclude = [\"tools/excluded\"]\n",
        )
        .unwrap();
        fs::write(
            eval_dir.join("Cargo.toml"),
            "[package]\nname = \"anneal-mir-eval\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        fs::write(eval_dir.join("src/main.rs"), "fn main() {}\n").unwrap();
        fs::write(
            excl_dir.join("Cargo.toml"),
            "[package]\nname = \"anneal-mir-eval\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        fs::write(excl_dir.join("src/main.rs"), "fn main() {}\n").unwrap();
        fs::write(decoy_dir.join("Cargo.toml"), "[package]\nname = \"evil\"\n").unwrap();

        // 1. Rename staging parent & plant a decoy symlink at `staging.root()`;
        //    `extract_built_executable_with_staging` verifies purely via fd.
        let prep =
            prepare_mir_eval_source_graph(&ws.join("Cargo.toml"), &ws, Some(&src_tmp), &fake_store)
                .unwrap();
        let staging = prep.staging.as_ref().expect("Linux staging guard");
        let pin_prefix = staging.pin_root_prefix().expect("Linux /proc/self/fd prefix");
        let orig_disk_root = staging.root().to_path_buf();
        fs::rename(&src_tmp, &moved_src_parent).unwrap();
        fs::create_dir_all(&orig_disk_root).unwrap();
        symlink(decoy_dir.join("Cargo.toml"), orig_disk_root.join("Cargo.toml")).unwrap();

        let exe_path = root.join("target/debug/anneal-mir-eval");
        let excl_json = serde_json::json!({
            "reason": "compiler-artifact",
            "manifest_path": format!("{pin_prefix}/tools/excluded/Cargo.toml"),
            "target": { "kind": ["bin"], "name": "anneal-mir-eval" },
            "profile": { "test": false },
            "executable": exe_path,
        })
        .to_string();
        assert!(
            extract_built_executable_with_staging(
                &excl_json,
                "anneal-mir-eval",
                &prep.staged_manifest,
                Some(staging),
            )
            .is_err()
        );
        let disk_json = serde_json::json!({
            "reason": "compiler-artifact",
            "manifest_path": orig_disk_root.join("tools/anneal-mir-eval/Cargo.toml"),
            "target": { "kind": ["bin"], "name": "anneal-mir-eval" },
            "profile": { "test": false },
            "executable": exe_path,
        })
        .to_string();
        assert!(
            extract_built_executable_with_staging(
                &disk_json,
                "anneal-mir-eval",
                &prep.staged_manifest,
                Some(staging),
            )
            .is_err()
        );
        let valid_json = format!(
            "{excl_json}\n{disk_json}\n{}",
            serde_json::json!({
                "reason": "compiler-artifact",
                "manifest_path": format!("{pin_prefix}/tools/anneal-mir-eval/Cargo.toml"),
                "target": { "kind": ["bin"], "name": "anneal-mir-eval" },
                "profile": { "test": false },
                "executable": exe_path,
            })
        );
        assert_eq!(
            extract_built_executable_with_staging(
                &valid_json,
                "anneal-mir-eval",
                &prep.staged_manifest,
                Some(staging),
            )
            .unwrap(),
            exe_path
        );
        drop(prep);
        if moved_src_parent.exists() {
            crate::rustc_runner::restore_dir_write_perms_top_down(&moved_src_parent);
            let _ = fs::remove_dir_all(&moved_src_parent);
        }

        // 2. End-to-end workspace build uses FD-pinned manifests exclusively.
        let fake_rustc = tc.join("bin/rustc");
        fs::write(
            &fake_rustc,
            format!(
                "#!/bin/sh\nset -eu\n\
                 if [ \"${{1:-}}\" = \"--print\" ] && [ \"${{2:-}}\" = \"sysroot\" ]; then\n\
                   printf '%s\\n' '{}'\nexit 0\n\
                 fi\n\
                 if [ \"${{1:-}}\" = \"-vV\" ]; then\n\
                   printf 'rustc 1.90.0\\nhost: x86_64-unknown-linux-gnu\\n'\nexit 0\n\
                 fi\nexit 0\n",
                tc.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_rustc, fs::Permissions::from_mode(0o755)).unwrap();

        let fake_cargo = tc.join("bin/cargo");
        fs::write(
            &fake_cargo,
            "#!/bin/sh\nset -eu\n\
             mp=\"\"\nprev=\"\"\n\
             for a in \"$@\"; do\n  if [ \"$prev\" = \"--manifest-path\" ]; then mp=\"$a\"; break; fi\n  prev=\"$a\"\ndone\n\
             fd_dir=\"${mp%/Cargo.toml}\"\n\
             dbg=\"$CARGO_TARGET_DIR/debug\"\nmkdir -p \"$dbg\"\n\
             printf '#!/bin/sh\\nexit 0\\n' > \"$dbg/anneal-mir-eval\"\nchmod 755 \"$dbg/anneal-mir-eval\"\n\
             printf '{\"reason\":\"compiler-artifact\",\"manifest_path\":\"%s\",\"target\":{\"kind\":[\"bin\"],\"name\":\"anneal-mir-eval\"},\"profile\":{\"test\":false},\"executable\":\"%s\"}\\n' \"${fd_dir}/tools/excluded/Cargo.toml\" \"$dbg/evil\"\n\
             printf '{\"reason\":\"compiler-artifact\",\"manifest_path\":\"%s\",\"target\":{\"kind\":[\"bin\"],\"name\":\"anneal-mir-eval\"},\"profile\":{\"test\":false},\"executable\":\"%s\"}\\n' \"${fd_dir}/tools/anneal-mir-eval/Cargo.toml\" \"$dbg/anneal-mir-eval\"\n",
        )
        .unwrap();
        fs::set_permissions(&fake_cargo, fs::Permissions::from_mode(0o755)).unwrap();

        let built = build_mir_eval_from_manifest_full_with_store(
            &ws.join("Cargo.toml"),
            &ws,
            Some(fake_cargo.as_os_str()),
            Some(fake_rustc.as_os_str()),
            None,
            None,
            Some(ch.as_os_str()),
            None,
            None,
            None,
            None,
            None,
            &fake_store,
        )
        .expect("workspace build extraction via pinned fd must succeed");
        assert!(built.exec_path.starts_with("/proc/self/fd/"), "{}", built.exec_path.display());
    }
}
