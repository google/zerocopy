// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Reading retained `--artifacts` files without following symlinks, and
//! verifying them against an inspected receipt.

#[cfg(unix)]
use std::io::{self, Read as _};
#[cfg(unix)]
use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd};
#[cfg(unix)]
use std::os::unix::ffi::OsStrExt as _;
use std::{
    collections::BTreeSet,
    fs,
    path::{Component, Path, PathBuf},
};

use super::MAX_ARTIFACT_FILE_BYTES;
use crate::{
    core::{
        digest::sha256_bytes,
        inspect::{
            render::ArtifactVerificationSummary,
            schema::{InspectParseError, ParsedReceipt},
            strict_json::StrictJsonDom,
        },
    },
    sys_util::SafeFs,
};

fn is_safe_artifact_rel_path(rel: &str) -> bool {
    !rel.is_empty()
        && !rel.contains('\\')
        && Path::new(rel).components().all(|c| matches!(c, Component::Normal(_)))
}

#[cfg(unix)]
fn c_path_component(os: &std::ffi::OsStr, label: &str) -> Result<std::ffi::CString, String> {
    std::ffi::CString::new(os.as_bytes())
        .map_err(|_| format!("artifact path `{label}` contains interior NUL byte"))
}

#[cfg(unix)]
fn normalize_artifact_root(path: &Path) -> Result<std::borrow::Cow<'_, Path>, String> {
    use std::os::unix::ffi::OsStrExt;
    let bytes = path.as_os_str().as_bytes();
    // Trailing `/`, `/.`, or `/..` makes `lstat` and `open(..., O_NOFOLLOW)`
    // resolve a final symlink component; trim separators while preserving `/`
    // root and reject trailing `.` / `..` segments.
    let trimmed_len = bytes
        .iter()
        .rposition(|&b| b != b'/')
        .map_or(usize::from(!bytes.is_empty()), |idx| idx + 1);
    let trimmed = &bytes[..trimmed_len];
    let last_segment = trimmed.rsplit(|&b| b == b'/').next().unwrap_or(trimmed);
    if last_segment == b".." || (last_segment == b"." && trimmed != b".") {
        return Err(format!(
            "artifacts root must be a concrete non-dot directory path: {}",
            path.display()
        ));
    }
    if trimmed_len == bytes.len() {
        Ok(std::borrow::Cow::Borrowed(path))
    } else {
        Ok(std::borrow::Cow::Borrowed(Path::new(std::ffi::OsStr::from_bytes(trimmed))))
    }
}

#[cfg(not(unix))]
fn normalize_artifact_root(path: &Path) -> Result<std::borrow::Cow<'_, Path>, String> {
    let Some(raw) = path.to_str() else {
        return Ok(std::borrow::Cow::Borrowed(path));
    };
    let prefix_len = match path.components().next() {
        Some(Component::Prefix(p)) => p.as_os_str().to_str().map_or(0, str::len),
        _ => 0,
    };
    let (prefix, rest) = raw.split_at(prefix_len);
    let trimmed = rest.trim_end_matches(['/', '\\']);
    let last_segment = trimmed.rsplit(['/', '\\']).next().unwrap_or(trimmed);
    if last_segment == ".." || (last_segment == "." && !(prefix.is_empty() && trimmed == ".")) {
        return Err(format!(
            "artifacts root must be a concrete non-dot directory path: {}",
            path.display()
        ));
    }
    if trimmed.is_empty() {
        if rest.is_empty() {
            Ok(std::borrow::Cow::Borrowed(path))
        } else {
            Ok(std::borrow::Cow::Owned(PathBuf::from(format!("{prefix}{}", &rest[..1]))))
        }
    } else if trimmed.len() == rest.len() {
        Ok(std::borrow::Cow::Borrowed(path))
    } else {
        Ok(std::borrow::Cow::Borrowed(Path::new(&raw[..prefix_len + trimmed.len()])))
    }
}

#[cfg(unix)]
fn read_artifact_under_dir(dir: &Path, rel: &str, max_bytes: u64) -> Result<Vec<u8>, String> {
    let dir = normalize_artifact_root(dir)?;
    let dir = dir.as_ref();
    if !is_safe_artifact_rel_path(rel) {
        return Err(format!("unsafe artifact relative path `{rel}`"));
    }
    let parts: Vec<&std::ffi::OsStr> = Path::new(rel)
        .components()
        .filter_map(|c| match c {
            Component::Normal(s) => Some(s),
            _ => None,
        })
        .collect();
    if parts.is_empty() {
        return Err(format!("empty artifact relative path `{rel}`"));
    }
    let c_root = c_path_component(dir.as_os_str(), &dir.display().to_string())?;
    // SAFETY: `c_root` is a valid NUL-terminated `CString` pointing to a live
    // buffer for the duration of the syscall.
    let root_fd = unsafe {
        libc::open(
            c_root.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        )
    };
    if root_fd < 0 {
        let err = io::Error::last_os_error();
        return Err(format!("cannot open artifacts root {}: {err}", dir.display()));
    }
    // SAFETY: `root_fd >= 0` was just returned as a newly owned fd by `open`.
    let mut dir_fd = unsafe { OwnedFd::from_raw_fd(root_fd) };
    for parent_part in &parts[..parts.len() - 1] {
        let c_part = c_path_component(parent_part, rel)?;
        // SAFETY: `dir_fd` is an open directory fd and `c_part` is a valid
        // NUL-terminated `CString` alive for the syscall.
        let next_fd = unsafe {
            libc::openat(
                dir_fd.as_raw_fd(),
                c_part.as_ptr(),
                libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            )
        };
        if next_fd < 0 {
            let err = io::Error::last_os_error();
            return Err(format!(
                "artifact intermediate dir `{}` check failed in `{rel}`: {err}",
                Path::new(parent_part).display()
            ));
        }
        // SAFETY: `next_fd >= 0` was just returned as a newly owned fd by
        // `openat`.
        dir_fd = unsafe { OwnedFd::from_raw_fd(next_fd) };
    }
    let c_leaf = c_path_component(parts[parts.len() - 1], rel)?;
    // SAFETY: `dir_fd` is an open directory fd and `c_leaf` is a valid
    // NUL-terminated `CString` alive for the syscall.
    let leaf_fd = unsafe {
        libc::openat(
            dir_fd.as_raw_fd(),
            c_leaf.as_ptr(),
            libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC,
        )
    };
    if leaf_fd < 0 {
        let err = io::Error::last_os_error();
        return Err(format!("artifact `{rel}` check failed: {err}"));
    }
    // SAFETY: `leaf_fd >= 0` was just returned as a newly owned fd by `openat`.
    let file = fs::File::from(unsafe { OwnedFd::from_raw_fd(leaf_fd) });
    let meta = file.metadata().map_err(|e| format!("artifact `{rel}` stat failed: {e}"))?;
    if !meta.is_file() {
        return Err(format!("artifact `{rel}` must be a regular file"));
    }
    if meta.len() > max_bytes {
        return Err(format!(
            "artifact `{rel}` exceeds {max_bytes}-byte cap ({} bytes)",
            meta.len()
        ));
    }
    let mut buf = Vec::with_capacity(meta.len().min(64 * 1024) as usize);
    let limit = max_bytes.saturating_add(1);
    file.take(limit)
        .read_to_end(&mut buf)
        .map_err(|e| format!("artifact `{rel}` read failed: {e}"))?;
    if (buf.len() as u64) > max_bytes {
        return Err(format!("artifact `{rel}` exceeded {max_bytes}-byte cap"));
    }
    Ok(buf)
}

/// Verify that `dir`, every intermediate component in `rel`, and the leaf file
/// are non-symlink filesystem entries of the expected kind.
#[cfg_attr(unix, allow(dead_code))]
pub(super) fn validate_artifact_dir_chain(dir: &Path, rel: &str) -> Result<PathBuf, String> {
    let root_meta = SafeFs::probe_symlink_metadata(dir, "inspect")
        .map_err(|e| format!("artifacts directory check failed: {}", e.message))?
        .ok_or_else(|| format!("artifacts directory `{}` does not exist", dir.display()))?;
    if root_meta.file_type().is_symlink() || !root_meta.is_dir() {
        return Err(format!(
            "artifacts root `{}` must be a real directory (not a symlink)",
            dir.display()
        ));
    }
    let mut cur = dir.to_path_buf();
    let comps: Vec<&std::ffi::OsStr> = Path::new(rel)
        .components()
        .map(|c| match c {
            std::path::Component::Normal(s) => Ok(s),
            _ => Err(format!("unsafe artifact relative path `{rel}`")),
        })
        .collect::<Result<_, _>>()?;
    if comps.is_empty() {
        return Err(format!("unsafe artifact relative path `{rel}`"));
    }
    for (idx, comp) in comps.iter().enumerate() {
        cur.push(comp);
        let is_leaf = idx + 1 == comps.len();
        let meta = SafeFs::probe_symlink_metadata(&cur, "inspect")
            .map_err(|e| format!("artifact `{rel}` check failed: {}", e.message))?
            .ok_or_else(|| format!("missing artifact `{rel}`"))?;
        if meta.file_type().is_symlink() {
            return Err(format!("artifact `{rel}` traverses a symlink"));
        }
        if is_leaf {
            if !meta.is_file() {
                return Err(format!("artifact `{rel}` is not a regular file"));
            }
        } else if !meta.is_dir() {
            return Err(format!("artifact `{rel}` intermediate component is not a directory"));
        }
    }
    Ok(cur)
}

#[cfg(not(unix))]
fn read_artifact_under_dir(dir: &Path, rel: &str, max_bytes: u64) -> Result<Vec<u8>, String> {
    let dir = normalize_artifact_root(dir)?;
    if !is_safe_artifact_rel_path(rel) {
        return Err(format!("unsafe artifact relative path `{rel}`"));
    }
    let target = validate_artifact_dir_chain(dir.as_ref(), rel)?;
    SafeFs::read_regular_nofollow_capped(&target, max_bytes, "inspect")
        .map_err(|e| format!("artifact `{rel}` check failed: {}", e.message))
}

fn check_retained_result_json(
    dir: &Path,
    receipt_bytes: &[u8],
    receipt_sha256: &str,
    artifacts_field: Option<&str>,
    max_receipt_bytes: usize,
    failures: &mut Vec<String>,
    checked_files: &mut usize,
) {
    let cap = MAX_ARTIFACT_FILE_BYTES.max(max_receipt_bytes as u64);
    let dom_cap = (MAX_ARTIFACT_FILE_BYTES as usize).max(max_receipt_bytes);
    let bytes = match read_artifact_under_dir(dir, "result.json", cap) {
        Ok(b) => {
            *checked_files += 1;
            b
        }
        Err(msg) => {
            failures.push(msg);
            return;
        }
    };
    let actual_sha = sha256_bytes(&bytes);
    if actual_sha.eq_ignore_ascii_case(receipt_sha256) {
        return;
    }
    // `cargo anneal verify --artifacts <dir>` writes `result.json` in the
    // stage directory before retention, then sets `artifacts` on stdout.
    // Accept exact strict-JSON object equality once `artifacts` is stripped
    // from the inspected stdout receipt, provided retained `result.json` has
    // no `artifacts` override.
    if let Some(expected_artifacts) = artifacts_field
        && let Ok(mut receipt_val) =
            StrictJsonDom::parse_with_max_bytes(receipt_bytes, max_receipt_bytes)
        && let Ok(retained_val) = StrictJsonDom::parse_with_max_bytes(&bytes, dom_cap)
        && let (Some(receipt_obj), Some(retained_obj)) =
            (receipt_val.as_object_mut(), retained_val.as_object())
        && !retained_obj.contains_key("artifacts")
        && receipt_obj.get("artifacts").and_then(|v| v.as_str()) == Some(expected_artifacts)
    {
        receipt_obj.remove("artifacts");
        if *receipt_obj == *retained_obj {
            return;
        }
    }
    failures.push(format!(
        "artifact `result.json` SHA-256 mismatch: expected {receipt_sha256}, got {actual_sha}"
    ));
}

pub(super) fn verify_retained_artifacts(
    dir: &Path,
    receipt: &ParsedReceipt,
    receipt_bytes: &[u8],
    receipt_sha256: &str,
    require_exact: bool,
    max_receipt_bytes: usize,
) -> Result<ArtifactVerificationSummary, InspectParseError> {
    let receipt_artifact_cap = MAX_ARTIFACT_FILE_BYTES.max(max_receipt_bytes as u64);
    let dir = normalize_artifact_root(dir).map_err(InspectParseError::Operational)?;
    let dir = dir.as_ref();
    let dir_meta = fs::symlink_metadata(dir).map_err(|e| {
        InspectParseError::Operational(format!(
            "cannot inspect artifacts dir {}: {e}",
            dir.display()
        ))
    })?;
    if dir_meta.file_type().is_symlink() || !dir_meta.file_type().is_dir() {
        return Err(InspectParseError::Operational(format!(
            "artifacts root must be a regular non-symlink directory: {}",
            dir.display()
        )));
    }
    let mut failures = Vec::new();
    let mut checked_files = 0usize;

    let check_hash_capped =
        |rel: &str, expected: &str, cap: u64, failures: &mut Vec<String>, count: &mut usize| {
            match read_artifact_under_dir(dir, rel, cap) {
                Ok(bytes) => {
                    *count += 1;
                    let actual = sha256_bytes(&bytes);
                    if !actual.eq_ignore_ascii_case(expected) {
                        failures.push(format!(
                            "artifact `{rel}` SHA-256 mismatch: expected {expected}, got {actual}"
                        ));
                    }
                }
                Err(msg) => failures.push(msg),
            }
        };
    let check_hash = |rel: &str, expected: &str, failures: &mut Vec<String>, count: &mut usize| {
        check_hash_capped(rel, expected, MAX_ARTIFACT_FILE_BYTES, failures, count);
    };

    match receipt {
        ParsedReceipt::Failure(_) => {
            let result_path = dir.join("result.json");
            match SafeFs::probe_symlink_metadata(&result_path, "inspect") {
                Ok(Some(_)) => {
                    check_hash_capped(
                        "result.json",
                        receipt_sha256,
                        receipt_artifact_cap,
                        &mut failures,
                        &mut checked_files,
                    );
                }
                Ok(None) => {
                    if require_exact {
                        failures.push(
                            "missing retained result.json required by --require-exact-artifacts"
                                .into(),
                        );
                    }
                }
                Err(e) => {
                    failures.push(format!("retained result.json check failed: {}", e.message))
                }
            }
        }
        ParsedReceipt::Success(s) => {
            check_hash("request.json", &s.request_sha256, &mut failures, &mut checked_files);
            check_hash(
                "capture/capture.json",
                &s.capture_sha256,
                &mut failures,
                &mut checked_files,
            );
            if let Some(ref shards_sha) = s.capture_shards_sha256 {
                match read_artifact_under_dir(
                    dir,
                    "capture/capture_shards.json",
                    receipt_artifact_cap,
                ) {
                    Ok(bytes) => {
                        checked_files += 1;
                        let actual = sha256_bytes(&bytes);
                        if !actual.eq_ignore_ascii_case(shards_sha) {
                            failures.push(format!(
                                "artifact `capture/capture_shards.json` SHA-256 mismatch: \
                                 expected {shards_sha}, got {actual}"
                            ));
                        }
                        if let Some(ref expected_shards) = s.shards {
                            match StrictJsonDom::parse_with_max_bytes(
                                &bytes,
                                (MAX_ARTIFACT_FILE_BYTES as usize).max(max_receipt_bytes),
                            ) {
                                Ok(disk_val) => match serde_json::to_value(expected_shards) {
                                    Ok(expected_val) => {
                                        if disk_val != expected_val {
                                            failures.push(
                                                "retained `capture/capture_shards.json` contents \
                                                 differ from receipt `shards` manifest"
                                                    .into(),
                                            );
                                        }
                                    }
                                    Err(err) => failures.push(format!(
                                        "failed to serialize receipt `shards` manifest for \
                                         artifact parity check: {err}"
                                    )),
                                },
                                Err(err) => failures.push(format!(
                                    "retained `capture/capture_shards.json` is not valid strict \
                                     JSON: {err}"
                                )),
                            }
                        }
                    }
                    Err(msg) => failures.push(msg),
                }
            } else if s.shards.is_some() {
                failures.push(
                    "receipt carries `shards` manifest without `capture_shards_sha256`".into(),
                );
            }
            for src in &s.sources {
                let rel = format!("rust/{}", src.relative_path);
                check_hash(&rel, &src.sha256, &mut failures, &mut checked_files);
            }
            if s.audit_sources.is_empty() {
                failures.push(
                    "receipt omits audit.sources required to verify retained Lean artifacts".into(),
                );
            } else {
                let mut has_model = false;
                let mut has_spec = false;
                let mut has_capture = false;
                let mut has_expected = false;
                let mut checked_id_tree = false;
                let mut seen_capture_modules = BTreeSet::new();
                let mut spec_count = 0usize;
                let mut on_disk_specs: Vec<(String, String)> = Vec::new();
                for entry in &s.audit_sources {
                    if entry.module.is_empty()
                        || !entry.module.split('.').all(|seg| {
                            !seg.is_empty()
                                && seg.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
                        })
                    {
                        failures.push(format!(
                            "audit.sources module `{}` is not a valid Lean module name",
                            entry.module
                        ));
                        continue;
                    }
                    let mod_path = entry.module.replace('.', "/");
                    let rel = match entry.role.as_str() {
                        "model" => {
                            has_model = true;
                            format!("anneal/trusted/lean/{mod_path}.lean")
                        }
                        "specification" => {
                            has_spec = true;
                            spec_count += 1;
                            format!("authored/{mod_path}.lean")
                        }
                        "capture" => {
                            has_capture = true;
                            seen_capture_modules.insert(entry.module.as_str());
                            format!("capture/{mod_path}.lean")
                        }
                        "expected" => {
                            has_expected = true;
                            format!("generated/{mod_path}.lean")
                        }
                        "proof" => {
                            if entry.module == "Anneal" || entry.module.starts_with("Anneal.") {
                                format!("anneal/theory/{mod_path}.lean")
                            } else if entry.module == "Proof.IdTree" && s.shards.is_some() {
                                checked_id_tree = true;
                                format!("generated/{mod_path}.lean")
                            } else {
                                format!("authored/{mod_path}.lean")
                            }
                        }
                        other => {
                            failures.push(format!(
                                "cannot map unknown audit.sources role `{other}` for `{}`",
                                entry.module
                            ));
                            continue;
                        }
                    };
                    match read_artifact_under_dir(dir, &rel, MAX_ARTIFACT_FILE_BYTES) {
                        Ok(bytes) => {
                            checked_files += 1;
                            let actual = sha256_bytes(&bytes);
                            if !actual.eq_ignore_ascii_case(&entry.source_sha256) {
                                failures.push(format!(
                                    "artifact `{rel}` SHA-256 mismatch: expected {}, got {actual}",
                                    entry.source_sha256
                                ));
                            }
                            if entry.role == "specification" {
                                on_disk_specs.push((entry.module.clone(), actual));
                            }
                        }
                        Err(msg) => failures.push(msg),
                    }
                }
                if !has_model || !has_spec || !has_capture || !has_expected {
                    failures.push(
                        "audit.sources is missing required model/specification/capture/expected \
                         entries for artifact verification"
                            .into(),
                    );
                } else if on_disk_specs.len() == spec_count
                    && let Ok(encoded_specs) = serde_json::to_vec_pretty(&on_disk_specs)
                {
                    let actual_spec_manifest = sha256_bytes(&encoded_specs);
                    if !actual_spec_manifest.eq_ignore_ascii_case(&s.specification_manifest_sha256)
                    {
                        failures.push(format!(
                            "retained specification manifest SHA-256 mismatch: expected {}, \
                             got {actual_spec_manifest}",
                            s.specification_manifest_sha256
                        ));
                    }
                }
                if let Some(ref sh) = s.shards {
                    if !checked_id_tree {
                        check_hash(
                            "generated/Proof/IdTree.lean",
                            &sh.id_tree_sha256,
                            &mut failures,
                            &mut checked_files,
                        );
                    }
                    for shard_entry in &sh.shards {
                        if !seen_capture_modules.contains(shard_entry.capture_module.as_str()) {
                            let valid_ident = !shard_entry.capture_module.is_empty()
                                && shard_entry.capture_module.split('.').all(|seg| {
                                    !seg.is_empty()
                                        && seg
                                            .bytes()
                                            .all(|b| b.is_ascii_alphanumeric() || b == b'_')
                                });
                            if !valid_ident {
                                failures.push(format!(
                                    "shards capture_module `{}` is not a valid Lean module name",
                                    shard_entry.capture_module
                                ));
                                continue;
                            }
                            let mod_path = shard_entry.capture_module.replace('.', "/");
                            let rel = format!("capture/{mod_path}.lean");
                            check_hash(
                                &rel,
                                &shard_entry.capture_sha256,
                                &mut failures,
                                &mut checked_files,
                            );
                        }
                    }
                }
            }
            if require_exact {
                check_retained_result_json(
                    dir,
                    receipt_bytes,
                    receipt_sha256,
                    s.artifacts.as_deref(),
                    max_receipt_bytes,
                    &mut failures,
                    &mut checked_files,
                );
            }
        }
    }

    Ok(ArtifactVerificationSummary {
        directory: dir.display().to_string(),
        exact_match: failures.is_empty(),
        checked_files,
        failures,
    })
}
