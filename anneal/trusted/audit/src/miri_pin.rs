// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Verifies `vendor/lean-miri/UPSTREAM_PIN.json`, authenticates sysroot
//! `{Init,Std,Lean}*` `.olean` manifests, and manages symlink-safe Miri
//! `.olean` caches for repository Pass 2.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    env,
    ffi::OsString,
    fs, io,
    path::{Component, Path, PathBuf},
};

use cargo_anneal::{
    Failure, ImportEdge, TOOLCHAIN, is_clean_relative_path, is_sha256_hex, regular, sha256_bytes,
    sha256_file,
};
pub use cargo_anneal::{LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256, verify_sysroot_foundation_dir};
use serde::Deserialize;
use walkdir::WalkDir;

/// Names the pinned upstream `proofs-rs/lean-miri` commit hash required by
/// `vendor/lean-miri/UPSTREAM_PIN.json`.
pub const LOCKED_MIRI_COMMIT: &str = "c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a";

/// Names the pinned SHA-256 digest of `vendor/lean-miri/UPSTREAM_PIN.json` so
/// any change to `UPSTREAM_PIN.json` requires a corresponding TCB diff inside
/// `trusted/audit/`.
pub const LOCKED_UPSTREAM_PIN_SHA256: &str =
    "b629a9b4c3fd184b20b791d34621a9f6aa1518ed9b164e42561b4eb688157271";

/// Lists the exact set of `vendor/lean-miri` files that must each carry one
/// consumer-side patch record in `UPSTREAM_PIN.json`.
pub const LOCKED_PATCHED_MIRI_FILES: &[&str] = &[
    "Miri/Interpreter/Call.lean",
    "Miri/Interpreter/Cast.lean",
    "Miri/Interpreter/ExecutionCalls.lean",
    "Miri/Interpreter/ExecutionCast.lean",
    "Miri/Interpreter/ExecutionMachine.lean",
    "Miri/Interpreter/LocalAccess.lean",
    "Miri/Interpreter/MachineHooks.lean",
    "Miri/Interpreter/OperandMachine.lean",
    "Miri/Interpreter/Place.lean",
    "Miri/Interpreter/PlaceMachine.lean",
];

/// Deserializes `vendor/lean-miri/UPSTREAM_PIN.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UpstreamPin {
    pub schema_version: i64,
    pub repository: String,
    pub commit: String,
    pub upstream_lean_toolchain: String,
    pub build_lean_toolchain: String,
    pub notes: Vec<String>,
    pub upstream_git_objects: BTreeMap<String, String>,
    pub upstream_pins: UpstreamSubPins,
    pub patched_files: Vec<PatchedMiriFile>,
    pub execution_machine_closure: Vec<MiriClosureEntry>,
    pub vendor_aux_files: Vec<VendorFileEntry>,
    pub vendor_tree: VendorTree,
}

impl UpstreamPin {
    /// Return the expected on-disk SHA-256 digest for each vendored `.lean`
    /// source file (`patched_sha256` when patched, otherwise `sha256`).
    pub fn expected_source_digests(&self) -> BTreeMap<String, String> {
        self.vendor_tree
            .files
            .iter()
            .map(|entry| {
                let sha = entry
                    .patched_sha256
                    .as_deref()
                    .unwrap_or(&entry.sha256)
                    .to_string();
                (entry.path.clone(), sha)
            })
            .collect()
    }
}

/// Stores the pinned upstream commit hashes inside `UPSTREAM_PIN.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UpstreamSubPins {
    pub aes_commit: String,
    pub miri_commit: String,
    pub rustc_apfloat_commit: String,
    pub rustc_commit: String,
    pub source_lock_sha256: String,
}

/// Describes one consumer-side patched file in `UPSTREAM_PIN.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PatchedMiriFile {
    pub path: String,
    pub upstream_sha256: String,
    pub patched_sha256: String,
    pub rationale: String,
}

/// Describes one compiled `Miri.*` module in `execution_machine_closure`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MiriClosureEntry {
    pub module: String,
    pub path: String,
    pub olean_sha256: String,
    #[serde(default)]
    pub olean_server_sha256: Option<String>,
    #[serde(default)]
    pub olean_private_sha256: Option<String>,
}

/// Describes one file path and SHA-256 entry in `vendor_tree` or
/// `vendor_aux_files`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VendorFileEntry {
    pub path: String,
    pub sha256: String,
    #[serde(default)]
    pub patched_sha256: Option<String>,
}

/// Holds the full `.lean` file manifest in `UPSTREAM_PIN.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VendorTree {
    pub file_count: usize,
    pub files: Vec<VendorFileEntry>,
    pub manifest_sha256: String,
}

/// Verify the SHA-256 digests of all `<prefix>/lib/lean/{Init,Std,Lean}*`
/// `.olean`, `.olean.server`, and `.olean.private` files against
/// [`LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`] and return the sorted list of
/// `.sysrootFoundation` module names (excluding `foundation_graph`).
pub(crate) fn verify_sysroot_foundation(
    prefix: &Path,
    foundation_graph: &BTreeMap<String, Vec<ImportEdge>>,
) -> Result<Vec<String>, Failure> {
    let foundation_modules: BTreeSet<String> = foundation_graph.keys().cloned().collect();
    verify_sysroot_foundation_dir(
        &prefix.join("lib/lean"),
        &foundation_modules,
        LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256,
    )
}

/// Normalize `.` and `..` path components purely lexically without consulting
/// the filesystem.
fn lexical_normalize(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();
    for comp in path.components() {
        match comp {
            Component::Prefix(prefix) => normalized.push(prefix.as_os_str()),
            Component::RootDir => normalized.push(comp.as_os_str()),
            Component::CurDir => {}
            Component::ParentDir => {
                if matches!(
                    normalized.components().next_back(),
                    Some(Component::Normal(_))
                ) {
                    normalized.pop();
                } else if !normalized.has_root() {
                    normalized.push(comp.as_os_str());
                }
            }
            Component::Normal(seg) => normalized.push(seg),
        }
    }
    normalized
}

/// Resolve an absolute path by following symlinks on every existing prefix
/// component (including dangling symlinks) while preserving non-existent
/// trailing components and normalizing `.`/`..`. Rejects any symlink located
/// inside `forbidden_root`.
fn resolve_path_for_containment(
    abs_path: &Path,
    forbidden_root: &Path,
    phase: &str,
) -> Result<PathBuf, Failure> {
    const MAX_SYMLINK_HOPS: usize = 40;
    let mut remaining_hops = MAX_SYMLINK_HOPS;
    let mut resolved = PathBuf::new();
    let mut queue: VecDeque<OsString> = VecDeque::new();
    let mut saw_root = false;

    for comp in abs_path.components() {
        match comp {
            Component::Prefix(prefix) => resolved.push(prefix.as_os_str()),
            Component::RootDir => {
                resolved.push(comp.as_os_str());
                saw_root = true;
            }
            Component::CurDir => {}
            Component::ParentDir => queue.push_back(OsString::from("..")),
            Component::Normal(seg) => queue.push_back(seg.to_os_string()),
        }
    }
    if !saw_root {
        return Err(Failure::operational(
            phase,
            format!("expected absolute path, got {}", abs_path.display()),
        ));
    }

    while let Some(seg) = queue.pop_front() {
        if seg == "." {
            continue;
        }
        if seg == ".." {
            if matches!(
                resolved.components().next_back(),
                Some(Component::Normal(_))
            ) {
                resolved.pop();
            }
            continue;
        }
        resolved.push(&seg);
        match fs::symlink_metadata(&resolved) {
            Ok(meta) if meta.file_type().is_symlink() => {
                if resolved.starts_with(forbidden_root) {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "Miri .olean cache directory must not traverse a symlink inside the repository checkout {}: {}",
                            forbidden_root.display(),
                            abs_path.display()
                        ),
                    ));
                }
                if remaining_hops == 0 {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "symlink loop while resolving Miri .olean cache directory: {}",
                            abs_path.display()
                        ),
                    ));
                }
                remaining_hops -= 1;
                let target = fs::read_link(&resolved).map_err(|e| {
                    Failure::operational(
                        phase,
                        format!("cannot read symlink {}: {e}", resolved.display()),
                    )
                })?;
                if target.is_absolute() {
                    resolved.clear();
                } else {
                    resolved.pop();
                }
                let mut target_segs = Vec::new();
                for comp in target.components() {
                    match comp {
                        Component::Prefix(prefix) => resolved.push(prefix.as_os_str()),
                        Component::RootDir => resolved.push(comp.as_os_str()),
                        Component::CurDir => {}
                        Component::ParentDir => target_segs.push(OsString::from("..")),
                        Component::Normal(s) => target_segs.push(s.to_os_string()),
                    }
                }
                for s in target_segs.into_iter().rev() {
                    queue.push_front(s);
                }
            }
            Ok(_) => {}
            Err(e)
                if matches!(
                    e.kind(),
                    io::ErrorKind::NotFound | io::ErrorKind::NotADirectory
                ) => {}
            Err(e) => {
                return Err(Failure::operational(
                    phase,
                    format!("cannot inspect {}: {e}", resolved.display()),
                ));
            }
        }
    }
    Ok(resolved)
}

/// Reject any `--miri-cache-dir` / `ANNEAL_MIRI_CACHE_DIR` path that resides
/// inside (or equals) the repository checkout `checkout`, checking both
/// lexical containment and symlink-resolved containment (including
/// non-existent leaf directories and dangling symlinks).
///
/// Keeping the Miri `.olean` cache outside the checkout prevents a PR from
/// committing pre-built `.olean` files inside the repository to satisfy cache
/// hits without compiling the pinned sources.
pub fn ensure_miri_cache_outside_checkout(
    checkout: &Path,
    cache_dir: &Path,
) -> Result<(), Failure> {
    let phase = "miri-pin";
    let canonical_checkout = fs::canonicalize(checkout).map_err(|e| {
        Failure::operational(
            phase,
            format!("cannot canonicalize checkout {}: {e}", checkout.display()),
        )
    })?;
    let abs_cache = if cache_dir.is_absolute() {
        cache_dir.to_path_buf()
    } else {
        env::current_dir()
            .map_err(|e| Failure::operational(phase, format!("cannot read cwd: {e}")))?
            .join(cache_dir)
    };
    let lexical_cache = lexical_normalize(&abs_cache);
    let resolved_cache = resolve_path_for_containment(&abs_cache, &canonical_checkout, phase)?;
    if lexical_cache.starts_with(&canonical_checkout)
        || resolved_cache.starts_with(&canonical_checkout)
    {
        return Err(Failure::policy(
            phase,
            format!(
                "Miri .olean cache directory must reside outside the repository checkout {}: {}",
                canonical_checkout.display(),
                cache_dir.display()
            ),
        ));
    }
    Ok(())
}

/// Validate that `cache_dir` and every path component of `rel_path` under
/// `cache_dir` is free of symlinks, returning the validated destination path
/// and creating missing intermediate directories without following links.
pub(crate) fn prepare_nosymlink_cache_path(
    cache_dir: &Path,
    rel_path: &str,
    create_dirs: bool,
    phase: &str,
) -> Result<PathBuf, Failure> {
    if !is_clean_relative_path(rel_path) {
        return Err(Failure::policy(
            phase,
            format!("invalid relative cache path: {rel_path}"),
        ));
    }
    // Strip any trailing slash so `symlink_metadata` inspects a symlinked
    // `cache_dir` entry itself rather than dereferencing it under POSIX.
    let cache_dir_buf: PathBuf = cache_dir.components().collect();
    let cache_dir = cache_dir_buf.as_path();
    match fs::symlink_metadata(cache_dir) {
        Ok(meta) => {
            if !meta.file_type().is_dir() {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "cache root must be a regular directory (not a symlink or file): {}",
                        cache_dir.display()
                    ),
                ));
            }
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            if create_dirs {
                fs::create_dir_all(cache_dir).map_err(|err| {
                    Failure::operational(
                        phase,
                        format!("cannot create cache root {}: {err}", cache_dir.display()),
                    )
                })?;
                let meta = fs::symlink_metadata(cache_dir).map_err(|err| {
                    Failure::operational(
                        phase,
                        format!("cannot stat cache root {}: {err}", cache_dir.display()),
                    )
                })?;
                if !meta.file_type().is_dir() {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "cache root is not a regular directory: {}",
                            cache_dir.display()
                        ),
                    ));
                }
            } else {
                return Ok(cache_dir.join(rel_path));
            }
        }
        Err(e) => {
            return Err(Failure::operational(
                phase,
                format!("cannot stat cache root {}: {e}", cache_dir.display()),
            ));
        }
    }
    let rel = Path::new(rel_path);
    let mut cur = cache_dir.to_path_buf();
    if let Some(parent) = rel.parent() {
        for comp in parent.components() {
            cur.push(comp);
            match fs::symlink_metadata(&cur) {
                Ok(meta) => {
                    if !meta.file_type().is_dir() {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "symlink or non-directory forbidden in cache path: {}",
                                cur.display()
                            ),
                        ));
                    }
                }
                Err(e) if e.kind() == io::ErrorKind::NotFound => {
                    if create_dirs {
                        fs::create_dir(&cur).map_err(|err| {
                            Failure::operational(
                                phase,
                                format!("cannot create cache directory {}: {err}", cur.display()),
                            )
                        })?;
                    } else {
                        return Ok(cache_dir.join(rel_path));
                    }
                }
                Err(e) => {
                    return Err(Failure::operational(
                        phase,
                        format!("cannot stat cache directory {}: {e}", cur.display()),
                    ));
                }
            }
        }
    }
    let dst = cache_dir.join(rel_path);
    match fs::symlink_metadata(&dst) {
        Ok(meta) => {
            if !meta.file_type().is_file() {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "symlink or non-regular file forbidden at cache entry: {}",
                        dst.display()
                    ),
                ));
            }
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) => {
            return Err(Failure::operational(
                phase,
                format!("cannot stat cache entry {}: {e}", dst.display()),
            ));
        }
    }
    Ok(dst)
}

/// Write a compiled artifact `src` into `cache_dir/rel_path` after rejecting
/// symlinks at every path component and creating a fresh regular file with
/// `create_new(true)`.
pub(crate) fn write_cache_file(
    src: &Path,
    cache_dir: &Path,
    rel_path: &str,
    phase: &str,
) -> Result<(), Failure> {
    regular(src, phase)?;
    let bytes = fs::read(src)
        .map_err(|e| Failure::operational(phase, format!("cannot read {}: {e}", src.display())))?;
    let dst = prepare_nosymlink_cache_path(cache_dir, rel_path, true, phase)?;
    if fs::symlink_metadata(&dst).is_ok() {
        fs::remove_file(&dst).map_err(|e| {
            Failure::operational(
                phase,
                format!("cannot replace cache entry {}: {e}", dst.display()),
            )
        })?;
    }
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&dst)
        .map_err(|e| {
            Failure::operational(
                phase,
                format!("cannot create cache entry {}: {e}", dst.display()),
            )
        })?;
    io::Write::write_all(&mut file, &bytes).map_err(|e| {
        Failure::operational(
            phase,
            format!("cannot write cache entry {}: {e}", dst.display()),
        )
    })?;
    Ok(())
}

/// Remove a stale companion artifact at `cache_dir/rel_path` after rejecting
/// symlinks along the path.
pub(crate) fn remove_cache_file(
    cache_dir: &Path,
    rel_path: &str,
    phase: &str,
) -> Result<(), Failure> {
    let dst = prepare_nosymlink_cache_path(cache_dir, rel_path, false, phase)?;
    if fs::symlink_metadata(&dst).is_ok() {
        fs::remove_file(&dst).map_err(|e| {
            Failure::operational(
                phase,
                format!("cannot remove stale cache entry {}: {e}", dst.display()),
            )
        })?;
    }
    Ok(())
}

/// Verify `vendor/lean-miri/UPSTREAM_PIN.json` and every file on disk under
/// `vendor_root`.
pub fn verify_upstream_pin(vendor_root: &Path) -> Result<UpstreamPin, Failure> {
    let phase = "miri-pin";
    if let Some(parent) = vendor_root.parent()
        && parent.file_name().and_then(|s| s.to_str()) == Some("vendor")
    {
        let parent_meta = fs::symlink_metadata(parent).map_err(|_| {
            Failure::policy(
                phase,
                format!("expected regular vendor directory: {}", parent.display()),
            )
        })?;
        if parent_meta.file_type().is_symlink() || !parent_meta.file_type().is_dir() {
            return Err(Failure::policy(
                phase,
                format!("expected regular vendor directory: {}", parent.display()),
            ));
        }
    }
    let root_meta = fs::symlink_metadata(vendor_root).map_err(|_| {
        Failure::policy(
            phase,
            format!(
                "expected regular vendor/lean-miri directory: {}",
                vendor_root.display()
            ),
        )
    })?;
    if root_meta.file_type().is_symlink() || !root_meta.file_type().is_dir() {
        return Err(Failure::policy(
            phase,
            format!(
                "expected regular vendor/lean-miri directory: {}",
                vendor_root.display()
            ),
        ));
    }
    let pin_path = vendor_root.join("UPSTREAM_PIN.json");
    let pin_meta = fs::symlink_metadata(&pin_path).map_err(|_| {
        Failure::policy(
            phase,
            format!("missing UPSTREAM_PIN.json: {}", pin_path.display()),
        )
    })?;
    if pin_meta.file_type().is_symlink() || !pin_meta.file_type().is_file() {
        return Err(Failure::policy(
            phase,
            format!(
                "expected regular file for UPSTREAM_PIN.json: {}",
                pin_path.display()
            ),
        ));
    }
    let pin_bytes = fs::read(&pin_path)
        .map_err(|e| Failure::operational(phase, format!("cannot read UPSTREAM_PIN.json: {e}")))?;
    let pin_sha = sha256_bytes(&pin_bytes);
    if !pin_sha.eq_ignore_ascii_case(LOCKED_UPSTREAM_PIN_SHA256) {
        return Err(Failure::policy(
            phase,
            format!(
                "UPSTREAM_PIN.json SHA-256 differs from locked digest: expected {LOCKED_UPSTREAM_PIN_SHA256}, got {pin_sha}"
            ),
        ));
    }
    verify_upstream_pin_bytes(vendor_root, &pin_bytes)
}

/// Parse `UPSTREAM_PIN.json` bytes that [`verify_upstream_pin`] has
/// authenticated against [`LOCKED_UPSTREAM_PIN_SHA256`] and verify every
/// internal invariant (commit, toolchain, `patched_files` allowlist,
/// `vendor_tree` and `vendor_aux_files` disk manifests,
/// `upstream/source-lock.json` closed schema and pin parity, and 160-module
/// `execution_machine_closure`) against the files under `vendor_root`.
fn verify_upstream_pin_bytes(vendor_root: &Path, pin_bytes: &[u8]) -> Result<UpstreamPin, Failure> {
    let phase = "miri-pin";
    let pin: UpstreamPin = serde_json::from_slice(pin_bytes)
        .map_err(|e| Failure::policy(phase, format!("malformed UPSTREAM_PIN.json: {e}")))?;

    if pin.schema_version != 2 {
        return Err(Failure::policy(
            phase,
            format!(
                "unsupported UPSTREAM_PIN.json schema_version: {}",
                pin.schema_version
            ),
        ));
    }
    if pin.commit != LOCKED_MIRI_COMMIT {
        return Err(Failure::policy(
            phase,
            format!(
                "UPSTREAM_PIN.json commit mismatch: expected {LOCKED_MIRI_COMMIT}, got {}",
                pin.commit
            ),
        ));
    }
    if pin.build_lean_toolchain != TOOLCHAIN {
        return Err(Failure::policy(
            phase,
            format!(
                "UPSTREAM_PIN.json build_lean_toolchain mismatch: expected {TOOLCHAIN}, got {}",
                pin.build_lean_toolchain
            ),
        ));
    }

    // Verify `patched_files` against the closed 10-file allowlist.
    let mut patched_map: BTreeMap<&str, &PatchedMiriFile> = BTreeMap::new();
    for pf in &pin.patched_files {
        if !LOCKED_PATCHED_MIRI_FILES.contains(&pf.path.as_str()) {
            return Err(Failure::policy(
                phase,
                format!(
                    "unauthorized patched file in UPSTREAM_PIN.json: {}",
                    pf.path
                ),
            ));
        }
        if !is_sha256_hex(&pf.upstream_sha256)
            || !is_sha256_hex(&pf.patched_sha256)
            || pf.upstream_sha256.eq_ignore_ascii_case(&pf.patched_sha256)
            || pf.rationale.trim().is_empty()
        {
            return Err(Failure::policy(
                phase,
                format!("invalid patched_files record for {}", pf.path),
            ));
        }
        if patched_map.insert(pf.path.as_str(), pf).is_some() {
            return Err(Failure::policy(
                phase,
                format!("duplicate patched_files record for {}", pf.path),
            ));
        }
    }
    if patched_map.len() != LOCKED_PATCHED_MIRI_FILES.len() {
        return Err(Failure::policy(
            phase,
            "patched_files list in UPSTREAM_PIN.json does not match locked 10-file set",
        ));
    }

    // Verify `vendor_tree` and `vendor_aux_files` against on-disk files.
    if pin.vendor_tree.files.is_empty()
        || pin.vendor_tree.files.len() != pin.vendor_tree.file_count
        || !is_sha256_hex(&pin.vendor_tree.manifest_sha256)
    {
        return Err(Failure::policy(
            phase,
            "invalid vendor_tree count or manifest_sha256 in UPSTREAM_PIN.json",
        ));
    }

    let mut expected_lean_files: BTreeMap<String, String> = BTreeMap::new();
    let mut manifest_buf = String::new();
    for entry in &pin.vendor_tree.files {
        if !is_clean_relative_path(&entry.path)
            || !entry.path.ends_with(".lean")
            || !is_sha256_hex(&entry.sha256)
        {
            return Err(Failure::policy(
                phase,
                format!("invalid vendor_tree entry: {}", entry.path),
            ));
        }
        let disk_sha = match (
            patched_map.get(entry.path.as_str()),
            entry.patched_sha256.as_deref(),
        ) {
            (Some(pf), Some(entry_patched)) => {
                if !pf.upstream_sha256.eq_ignore_ascii_case(&entry.sha256)
                    || !pf.patched_sha256.eq_ignore_ascii_case(entry_patched)
                {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "patched_sha256 mismatch between patched_files and vendor_tree for {}",
                            entry.path
                        ),
                    ));
                }
                entry_patched.to_string()
            }
            (None, None) => entry.sha256.clone(),
            _ => {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "inconsistent patched_sha256 annotation in vendor_tree for {}",
                        entry.path
                    ),
                ));
            }
        };
        if expected_lean_files
            .insert(entry.path.clone(), disk_sha)
            .is_some()
        {
            return Err(Failure::policy(
                phase,
                format!("duplicate vendor_tree entry: {}", entry.path),
            ));
        }
        manifest_buf.push_str(&format!("{}  {}\n", entry.sha256, entry.path));
    }
    let computed_manifest = sha256_bytes(manifest_buf.as_bytes());
    if !computed_manifest.eq_ignore_ascii_case(&pin.vendor_tree.manifest_sha256) {
        return Err(Failure::policy(
            phase,
            format!(
                "vendor_tree manifest_sha256 mismatch: expected {}, got {computed_manifest}",
                pin.vendor_tree.manifest_sha256
            ),
        ));
    }

    let mut expected_aux_files: BTreeMap<String, String> = BTreeMap::new();
    for entry in &pin.vendor_aux_files {
        if !is_clean_relative_path(&entry.path)
            || entry.path.ends_with(".lean")
            || entry.path == "UPSTREAM_PIN.json"
            || !is_sha256_hex(&entry.sha256)
        {
            return Err(Failure::policy(
                phase,
                format!("invalid vendor_aux_files entry: {}", entry.path),
            ));
        }
        if expected_aux_files
            .insert(entry.path.clone(), entry.sha256.clone())
            .is_some()
        {
            return Err(Failure::policy(
                phase,
                format!("duplicate vendor_aux_files entry: {}", entry.path),
            ));
        }
    }
    if !is_sha256_hex(&pin.upstream_pins.source_lock_sha256)
        || !expected_aux_files
            .get("upstream/source-lock.json")
            .is_some_and(|sha| sha.eq_ignore_ascii_case(&pin.upstream_pins.source_lock_sha256))
    {
        return Err(Failure::policy(
            phase,
            "upstream_pins.source_lock_sha256 mismatches vendor_aux_files for upstream/source-lock.json",
        ));
    }

    // Walk `vendor_root` without following symlinks and verify that on-disk
    // files match `expected_lean_files`, `expected_aux_files`, and
    // `UPSTREAM_PIN.json` with zero untracked files or compiled artifacts.
    let mut seen_lean = BTreeSet::new();
    let mut seen_aux = BTreeSet::new();
    for entry_res in WalkDir::new(vendor_root).follow_links(false) {
        let entry = entry_res.map_err(|e| Failure::operational(phase, e.to_string()))?;
        let path = entry.path();
        if path == vendor_root {
            continue;
        }
        let ft = entry.file_type();
        if ft.is_symlink() {
            return Err(Failure::policy(
                phase,
                format!("symlink forbidden in vendor/lean-miri: {}", path.display()),
            ));
        }
        if ft.is_dir() {
            continue;
        }
        if !ft.is_file() {
            return Err(Failure::policy(
                phase,
                format!("non-regular file in vendor/lean-miri: {}", path.display()),
            ));
        }
        let rel = path
            .strip_prefix(vendor_root)
            .map_err(|e| Failure::operational(phase, e.to_string()))?;
        let rel_str = rel
            .components()
            .map(|c| c.as_os_str().to_string_lossy())
            .collect::<Vec<_>>()
            .join("/");
        if rel_str == "UPSTREAM_PIN.json" {
            continue;
        }
        let actual_sha = sha256_file(path, phase)?;
        if rel_str.ends_with(".lean") {
            let Some(exp_sha) = expected_lean_files.get(&rel_str) else {
                return Err(Failure::policy(
                    phase,
                    format!("unlisted Lean file in vendor/lean-miri: {rel_str}"),
                ));
            };
            if !actual_sha.eq_ignore_ascii_case(exp_sha) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "vendor file SHA-256 mismatch for {rel_str}: expected {exp_sha}, got {actual_sha}"
                    ),
                ));
            }
            seen_lean.insert(rel_str);
        } else {
            let Some(exp_sha) = expected_aux_files.get(&rel_str) else {
                return Err(Failure::policy(
                    phase,
                    format!("unlisted file in vendor/lean-miri: {rel_str}"),
                ));
            };
            if !actual_sha.eq_ignore_ascii_case(exp_sha) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "vendor aux file SHA-256 mismatch for {rel_str}: expected {exp_sha}, got {actual_sha}"
                    ),
                ));
            }
            seen_aux.insert(rel_str);
        }
    }
    if seen_lean.len() != expected_lean_files.len() {
        return Err(Failure::policy(
            phase,
            "missing pinned .lean file in vendor/lean-miri",
        ));
    }
    if seen_aux.len() != expected_aux_files.len() {
        return Err(Failure::policy(
            phase,
            "missing pinned auxiliary file in vendor/lean-miri",
        ));
    }

    let source_lock_path = vendor_root.join("upstream/source-lock.json");
    let source_lock_bytes = fs::read(&source_lock_path).map_err(|e| {
        Failure::operational(phase, format!("cannot read upstream/source-lock.json: {e}"))
    })?;
    let source_lock_sha = sha256_bytes(&source_lock_bytes);
    if !source_lock_sha.eq_ignore_ascii_case(&pin.upstream_pins.source_lock_sha256) {
        return Err(Failure::policy(
            phase,
            format!(
                "upstream/source-lock.json SHA-256 differs from UPSTREAM_PIN.json: expected {}, got {source_lock_sha}",
                pin.upstream_pins.source_lock_sha256
            ),
        ));
    }
    verify_source_lock_bytes_against_pins(&source_lock_bytes, &pin.upstream_pins)?;

    // Verify `execution_machine_closure` and ensure
    // `Miri.Input.NativeMathHost` (which contains `@[extern]` host math
    // bindings) and umbrella `Miri` are excluded from the correspondence slice.
    let mut seen_closure_mods = BTreeSet::new();
    for entry in &pin.execution_machine_closure {
        let expected_rel = format!("{}.lean", entry.module.replace('.', "/"));
        if !entry.module.starts_with("Miri.")
            || entry.module == "Miri.Input.NativeMathHost"
            || entry.module == "Miri"
            || entry.path != expected_rel
            || !expected_lean_files.contains_key(&entry.path)
            || !is_sha256_hex(&entry.olean_sha256)
            || entry
                .olean_server_sha256
                .as_deref()
                .is_some_and(|h| !is_sha256_hex(h))
            || entry
                .olean_private_sha256
                .as_deref()
                .is_some_and(|h| !is_sha256_hex(h))
            || !seen_closure_mods.insert(entry.module.as_str())
        {
            return Err(Failure::policy(
                phase,
                format!(
                    "invalid execution_machine_closure entry for {}",
                    entry.module
                ),
            ));
        }
    }
    if pin.execution_machine_closure.len() != 160 {
        return Err(Failure::policy(
            phase,
            format!(
                "expected 160 execution_machine_closure entries in UPSTREAM_PIN.json, got {}",
                pin.execution_machine_closure.len()
            ),
        ));
    }
    if !seen_closure_mods.contains("Miri.Interpreter.ExecutionMachine") {
        return Err(Failure::policy(
            phase,
            "execution_machine_closure is missing Miri.Interpreter.ExecutionMachine",
        ));
    }

    Ok(pin)
}

/// The single upstream `c92d1d97` `supporting_files` record that retains a
/// stray `"**HASH**": null` key until upstream regenerates `source-lock.json`.
const LEGACY_STRAY_HASH_PATH: &str = "upstream/rustc-source/Cargo.lock";

#[derive(Debug, Clone, Default)]
enum LegacyStrayHash {
    #[default]
    Absent,
    Null,
    NonNull,
}

fn deserialize_legacy_stray_hash<'de, D>(deserializer: D) -> Result<LegacyStrayHash, D::Error>
where
    D: serde::Deserializer<'de>,
{
    match Option::<serde_json::Value>::deserialize(deserializer)? {
        None => Ok(LegacyStrayHash::Null),
        Some(_) => Ok(LegacyStrayHash::NonNull),
    }
}

/// Deserializes `vendor/lean-miri/upstream/source-lock.json` under a closed
/// schema so stray or unauthenticated keys fail closed.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceLock {
    pub schema_version: i64,
    pub acquisition: SourceLockAcquisition,
    pub coverage_expected_rust_modules: BTreeMap<String, usize>,
    pub coverage_roots: Vec<String>,
    pub external_dependencies: SourceLockExternalDependencies,
    pub features: BTreeMap<String, Vec<String>>,
    pub files: Vec<SupportingFileRecord>,
    pub pins: SourceLockPins,
    pub scope_notes: Vec<String>,
    pub supporting_files: Vec<SupportingFileRecord>,
}

/// Describes archive acquisition metadata in `upstream/source-lock.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceLockAcquisition {
    pub note: String,
    pub pin_markers: BTreeMap<String, String>,
    pub procedure: String,
    pub procedure_sha256: String,
    pub rustc_selected_archive_paths: SourceLockSelectedArchivePaths,
}

/// Describes the extracted rustc file list metadata in
/// `SourceLockAcquisition`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceLockSelectedArchivePaths {
    pub count: usize,
    pub path: String,
    pub sha256: String,
}

/// Describes non-vendored dependencies and lockfile provenance in
/// `upstream/source-lock.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceLockExternalDependencies {
    pub cargo_packages: Vec<SourceLockCargoPackage>,
    pub resolution_file: SourceLockResolutionFile,
    pub rustc_private_crates: Vec<SourceLockRustcPrivateCrate>,
    pub rustc_upstream_resolution_file: SourceLockResolutionFile,
    pub toolchain_and_native: Vec<String>,
}

/// Describes one Cargo dependency requirement recorded in `source-lock.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceLockCargoPackage {
    pub name: String,
    pub scope: String,
    #[serde(default)]
    pub version: Option<String>,
    #[serde(default)]
    pub requirement: Option<String>,
    #[serde(default)]
    pub path: Option<String>,
    #[serde(default)]
    pub default_features: Option<bool>,
    #[serde(default)]
    pub features: Option<Vec<String>>,
    #[serde(default)]
    pub optional: Option<bool>,
}

/// Describes a referenced `Cargo.lock` resolution file in `source-lock.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceLockResolutionFile {
    pub note: String,
    pub path: String,
    pub sha256: String,
}

/// Describes one `rustc_private` crate inventory entry in `source-lock.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceLockRustcPrivateCrate {
    pub name: String,
    pub status: String,
    pub coverage_roots: Vec<String>,
    pub evidence: String,
    #[serde(default)]
    pub version: Option<String>,
    #[serde(default)]
    pub checksum: Option<String>,
    #[serde(default)]
    pub git_commit: Option<String>,
}

/// Holds the four component pin records in `upstream/source-lock.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceLockPins {
    pub aes: SourceLockComponentPin,
    pub miri: SourceLockComponentPin,
    pub rustc: SourceLockComponentPin,
    pub rustc_apfloat: SourceLockComponentPin,
}

/// Describes one pinned upstream component in `upstream/source-lock.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceLockComponentPin {
    pub archive_path: String,
    pub archive_sha256: String,
    pub archive_url: String,
    pub commit: String,
    pub repository: String,
    #[serde(default)]
    pub checksum_source: Option<String>,
    #[serde(default)]
    pub commit_date_utc: Option<String>,
    #[serde(default)]
    pub commit_url: Option<String>,
    #[serde(default)]
    pub extracted_paths_manifest: Option<String>,
    #[serde(default)]
    pub extracted_paths_manifest_sha256: Option<String>,
    #[serde(default)]
    pub extracted_root: Option<String>,
    #[serde(default)]
    pub package_version: Option<String>,
    #[serde(default)]
    pub pinned_via: Option<String>,
    #[serde(default)]
    pub registry: Option<String>,
    #[serde(default)]
    pub tree: Option<String>,
}

/// Describes one file provenance record (`files` or `supporting_files`) in
/// `upstream/source-lock.json`.
///
/// Leaves upstream `c92d1d97`'s `upstream/source-lock.json` byte-identical
/// until upstream removes the legacy `"**HASH**": null` key on the next pin
/// regeneration; rejects `"**HASH**"` everywhere except that single `null`
/// entry.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SupportingFileRecord {
    pub component: String,
    pub git_blob: String,
    pub path: String,
    pub sha256: String,
    #[serde(default, rename = "**HASH**", deserialize_with = "deserialize_legacy_stray_hash")]
    legacy_stray_hash: LegacyStrayHash,
}

fn is_git_oid_hex(s: &str) -> bool {
    s.len() == 40 && s.bytes().all(|b| b.is_ascii_hexdigit())
}

fn is_canonical_relative_path(rel: &str) -> bool {
    !rel.is_empty()
        && rel == rel.trim()
        && !rel.contains('\\')
        && !rel.starts_with('/')
        && !rel.ends_with('/')
        && !rel.contains("//")
        && rel.split('/').all(|seg| !seg.is_empty() && seg != "." && seg != "..")
        && is_clean_relative_path(rel)
}

fn validate_component_pin(
    name: &str,
    pin: &SourceLockComponentPin,
    phase: &str,
) -> Result<(), Failure> {
    if !is_canonical_relative_path(&pin.archive_path)
        || !is_sha256_hex(&pin.archive_sha256)
        || pin.archive_url.trim().is_empty()
        || pin.repository.trim().is_empty()
        || !is_git_oid_hex(&pin.commit)
        || pin.tree.as_deref().is_some_and(|t| !is_git_oid_hex(t))
        || pin.extracted_paths_manifest_sha256.as_deref().is_some_and(|s| !is_sha256_hex(s))
    {
        return Err(Failure::policy(
            phase,
            format!("invalid `{name}` pin record in upstream/source-lock.json"),
        ));
    }
    Ok(())
}

fn validate_file_records<'a>(
    section: &str,
    records: &'a [SupportingFileRecord],
    seen_paths: &mut BTreeSet<&'a str>,
    phase: &str,
) -> Result<(), Failure> {
    if records.is_empty() {
        return Err(Failure::policy(
            phase,
            format!("upstream/source-lock.json `{section}` must not be empty"),
        ));
    }
    for record in records {
        match record.legacy_stray_hash {
            LegacyStrayHash::Absent => {}
            LegacyStrayHash::Null
                if section == "supporting_files" && record.path == LEGACY_STRAY_HASH_PATH => {}
            LegacyStrayHash::Null | LegacyStrayHash::NonNull => {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "unexpected `**HASH**` field in `{section}` record for {}",
                        record.path
                    ),
                ));
            }
        }
        if record.component.trim().is_empty() || record.component != record.component.trim() {
            return Err(Failure::policy(
                phase,
                format!(
                    "invalid `{section}` component name in upstream/source-lock.json: {:?}",
                    record.component
                ),
            ));
        }
        if !is_canonical_relative_path(&record.path) {
            return Err(Failure::policy(
                phase,
                format!("invalid `{section}` path in upstream/source-lock.json: {:?}", record.path),
            ));
        }
        if !is_git_oid_hex(&record.git_blob) {
            return Err(Failure::policy(
                phase,
                format!(
                    "invalid `{section}` git_blob for {} in upstream/source-lock.json: {:?}",
                    record.path, record.git_blob
                ),
            ));
        }
        if !is_sha256_hex(&record.sha256) {
            return Err(Failure::policy(
                phase,
                format!(
                    "invalid `{section}` sha256 for {} in upstream/source-lock.json: {:?}",
                    record.path, record.sha256
                ),
            ));
        }
        if !seen_paths.insert(record.path.as_str()) {
            return Err(Failure::policy(
                phase,
                format!("duplicate `{section}` path in upstream/source-lock.json: {}", record.path),
            ));
        }
    }
    Ok(())
}

/// Deserialize and validate `vendor/lean-miri/upstream/source-lock.json`
/// bytes against its closed schema and field invariants.
pub fn verify_source_lock_bytes(lock_bytes: &[u8]) -> Result<SourceLock, Failure> {
    let phase = "miri-pin";
    let lock: SourceLock = serde_json::from_slice(lock_bytes)
        .map_err(|e| Failure::policy(phase, format!("malformed upstream/source-lock.json: {e}")))?;
    if lock.schema_version != 1 {
        return Err(Failure::policy(
            phase,
            format!(
                "unsupported upstream/source-lock.json schema_version: {}",
                lock.schema_version
            ),
        ));
    }
    if !is_canonical_relative_path(&lock.acquisition.procedure)
        || !is_sha256_hex(&lock.acquisition.procedure_sha256)
        || !is_canonical_relative_path(&lock.acquisition.rustc_selected_archive_paths.path)
        || !is_sha256_hex(&lock.acquisition.rustc_selected_archive_paths.sha256)
        || lock.acquisition.rustc_selected_archive_paths.count == 0
    {
        return Err(Failure::policy(
            phase,
            "invalid `acquisition` metadata in upstream/source-lock.json",
        ));
    }
    for (label, res_file) in [
        ("resolution_file", &lock.external_dependencies.resolution_file),
        (
            "rustc_upstream_resolution_file",
            &lock.external_dependencies.rustc_upstream_resolution_file,
        ),
    ] {
        if !is_canonical_relative_path(&res_file.path) || !is_sha256_hex(&res_file.sha256) {
            return Err(Failure::policy(
                phase,
                format!("invalid `{label}` record in upstream/source-lock.json"),
            ));
        }
    }
    for (name, pin) in [
        ("aes", &lock.pins.aes),
        ("miri", &lock.pins.miri),
        ("rustc", &lock.pins.rustc),
        ("rustc_apfloat", &lock.pins.rustc_apfloat),
    ] {
        validate_component_pin(name, pin, phase)?;
    }
    let mut seen_paths = BTreeSet::new();
    validate_file_records("files", &lock.files, &mut seen_paths, phase)?;
    validate_file_records("supporting_files", &lock.supporting_files, &mut seen_paths, phase)?;
    Ok(lock)
}

fn verify_source_lock_bytes_against_pins(
    lock_bytes: &[u8],
    expected_pins: &UpstreamSubPins,
) -> Result<SourceLock, Failure> {
    let phase = "miri-pin";
    let lock = verify_source_lock_bytes(lock_bytes)?;
    for (component, actual, expected) in [
        ("aes", lock.pins.aes.commit.as_str(), expected_pins.aes_commit.as_str()),
        ("miri", lock.pins.miri.commit.as_str(), expected_pins.miri_commit.as_str()),
        ("rustc", lock.pins.rustc.commit.as_str(), expected_pins.rustc_commit.as_str()),
        (
            "rustc_apfloat",
            lock.pins.rustc_apfloat.commit.as_str(),
            expected_pins.rustc_apfloat_commit.as_str(),
        ),
    ] {
        if !actual.eq_ignore_ascii_case(expected) {
            return Err(Failure::policy(
                phase,
                format!(
                    "upstream/source-lock.json `{component}` commit mismatch: expected {expected}, got {actual}"
                ),
            ));
        }
    }
    Ok(lock)
}

#[cfg(test)]
mod tests {
    use super::*;
    use cargo_anneal::Json;
    use serde_json::json;

    #[test]
    fn rejects_unauthorized_patched_files_and_bad_closure_in_pin_bytes() {
        let vendor_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vendor/lean-miri");
        let orig_pin_bytes = fs::read(vendor_root.join("UPSTREAM_PIN.json")).unwrap();

        // Unauthorized `patched_files` entry is rejected even if the outer pin
        // digest check has already passed.
        let mut pin_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        pin_json["patched_files"]
            .as_array_mut()
            .unwrap()
            .push(json!({
                "path": "Miri.lean",
                "upstream_sha256": "0000000000000000000000000000000000000000000000000000000000000000",
                "patched_sha256": "1111111111111111111111111111111111111111111111111111111111111111",
                "rationale": "unauthorized patch"
            }));
        let err_unauth_patch =
            verify_upstream_pin_bytes(&vendor_root, &serde_json::to_vec(&pin_json).unwrap())
                .unwrap_err();
        assert_eq!(err_unauth_patch.code, 1);
        assert!(
            err_unauth_patch
                .message
                .contains("unauthorized patched file in UPSTREAM_PIN.json: Miri.lean"),
            "unexpected error: {err_unauth_patch}"
        );

        // Mismatched `patched_sha256` between `patched_files` and `vendor_tree`
        // is rejected.
        let mut pin_mismatch_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        pin_mismatch_json["patched_files"][0]["patched_sha256"] =
            json!("2222222222222222222222222222222222222222222222222222222222222222");
        let err_patch_mismatch = verify_upstream_pin_bytes(
            &vendor_root,
            &serde_json::to_vec(&pin_mismatch_json).unwrap(),
        )
        .unwrap_err();
        assert_eq!(err_patch_mismatch.code, 1);
        assert!(
            err_patch_mismatch
                .message
                .contains("patched_sha256 mismatch between patched_files and vendor_tree"),
            "unexpected error: {err_patch_mismatch}"
        );

        // Missing `patched_sha256` annotation in `vendor_tree` is rejected.
        let mut pin_missing_annot_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        for entry in pin_missing_annot_json["vendor_tree"]["files"]
            .as_array_mut()
            .unwrap()
        {
            if entry["path"].as_str() == Some("Miri/Interpreter/Call.lean") {
                entry.as_object_mut().unwrap().remove("patched_sha256");
            }
        }
        let err_missing_annot = verify_upstream_pin_bytes(
            &vendor_root,
            &serde_json::to_vec(&pin_missing_annot_json).unwrap(),
        )
        .unwrap_err();
        assert_eq!(err_missing_annot.code, 1);
        assert!(
            err_missing_annot.message.contains(
                "inconsistent patched_sha256 annotation in vendor_tree for Miri/Interpreter/Call.lean"
            ),
            "unexpected error: {err_missing_annot}"
        );

        // Forbidden `Miri.Input.NativeMathHost` closure entry is rejected.
        let mut pin_closure_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        pin_closure_json["execution_machine_closure"] = json!([{
            "module": "Miri.Input.NativeMathHost",
            "path": "Miri/Input/NativeMathHost.lean",
            "olean_sha256": "0000000000000000000000000000000000000000000000000000000000000000"
        }]);
        let err_bad_closure = verify_upstream_pin_bytes(
            &vendor_root,
            &serde_json::to_vec(&pin_closure_json).unwrap(),
        )
        .unwrap_err();
        assert_eq!(err_bad_closure.code, 1);
        assert!(
            err_bad_closure
                .message
                .contains("invalid execution_machine_closure entry for Miri.Input.NativeMathHost"),
            "unexpected error: {err_bad_closure}"
        );

        // Empty `execution_machine_closure` is rejected.
        pin_closure_json["execution_machine_closure"] = json!([]);
        let err_empty_closure = verify_upstream_pin_bytes(
            &vendor_root,
            &serde_json::to_vec(&pin_closure_json).unwrap(),
        )
        .unwrap_err();
        assert_eq!(err_empty_closure.code, 1);
        assert!(
            err_empty_closure.message.contains(
                "expected 160 execution_machine_closure entries in UPSTREAM_PIN.json, got 0"
            ),
            "unexpected error: {err_empty_closure}"
        );
    }

    #[test]
    fn rejects_malformed_patched_files_and_vendor_tree_annotations_in_pin_bytes() {
        let vendor_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vendor/lean-miri");
        let orig_pin_bytes = fs::read(vendor_root.join("UPSTREAM_PIN.json")).unwrap();

        // (a) A `patched_sha256` annotation on a non-allowlisted file in
        // `vendor_tree` is rejected.
        let mut pin_extra_annot: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        let mut found_miri = false;
        for entry in pin_extra_annot["vendor_tree"]["files"]
            .as_array_mut()
            .unwrap()
        {
            if entry["path"].as_str() == Some("Miri.lean") {
                entry.as_object_mut().unwrap().insert(
                    "patched_sha256".to_string(),
                    json!("3333333333333333333333333333333333333333333333333333333333333333"),
                );
                found_miri = true;
            }
        }
        assert!(found_miri, "Miri.lean must appear in vendor_tree.files");
        let err_extra_annot =
            verify_upstream_pin_bytes(&vendor_root, &serde_json::to_vec(&pin_extra_annot).unwrap())
                .unwrap_err();
        assert_eq!(err_extra_annot.code, 1);
        assert!(
            err_extra_annot
                .message
                .contains("inconsistent patched_sha256 annotation in vendor_tree for Miri.lean"),
            "unexpected error: {err_extra_annot}"
        );

        // (b) A dropped record / count mismatch in `patched_files` is
        // rejected.
        let mut pin_dropped: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        pin_dropped["patched_files"].as_array_mut().unwrap().pop();
        let err_dropped =
            verify_upstream_pin_bytes(&vendor_root, &serde_json::to_vec(&pin_dropped).unwrap())
                .unwrap_err();
        assert_eq!(err_dropped.code, 1);
        assert!(
            err_dropped.message.contains(
                "patched_files list in UPSTREAM_PIN.json does not match locked 10-file set"
            ),
            "unexpected error: {err_dropped}"
        );

        // (c) Duplicate records in `patched_files` are rejected.
        let mut pin_dup: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        let first_record = pin_dup["patched_files"][0].clone();
        let first_path = first_record["path"].as_str().unwrap().to_string();
        pin_dup["patched_files"]
            .as_array_mut()
            .unwrap()
            .push(first_record);
        let err_dup =
            verify_upstream_pin_bytes(&vendor_root, &serde_json::to_vec(&pin_dup).unwrap())
                .unwrap_err();
        assert_eq!(err_dup.code, 1);
        assert!(
            err_dup
                .message
                .contains(&format!("duplicate patched_files record for {first_path}")),
            "unexpected error: {err_dup}"
        );

        // (d1) An invalid `patched_files` record with
        // `upstream_sha256 == patched_sha256` is rejected.
        let mut pin_same_sha: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        let same_path = pin_same_sha["patched_files"][0]["path"]
            .as_str()
            .unwrap()
            .to_string();
        let upstream_sha = pin_same_sha["patched_files"][0]["upstream_sha256"].clone();
        pin_same_sha["patched_files"][0]["patched_sha256"] = upstream_sha;
        let err_same_sha =
            verify_upstream_pin_bytes(&vendor_root, &serde_json::to_vec(&pin_same_sha).unwrap())
                .unwrap_err();
        assert_eq!(err_same_sha.code, 1);
        assert!(
            err_same_sha
                .message
                .contains(&format!("invalid patched_files record for {same_path}")),
            "unexpected error: {err_same_sha}"
        );

        // (d2) An invalid `patched_files` record with empty/whitespace
        // `rationale` is rejected.
        let mut pin_blank_rationale: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        let blank_path = pin_blank_rationale["patched_files"][0]["path"]
            .as_str()
            .unwrap()
            .to_string();
        pin_blank_rationale["patched_files"][0]["rationale"] = json!("   \t\n ");
        let err_blank_rationale = verify_upstream_pin_bytes(
            &vendor_root,
            &serde_json::to_vec(&pin_blank_rationale).unwrap(),
        )
        .unwrap_err();
        assert_eq!(err_blank_rationale.code, 1);
        assert!(
            err_blank_rationale
                .message
                .contains(&format!("invalid patched_files record for {blank_path}")),
            "unexpected error: {err_blank_rationale}"
        );

        // (e) A mismatch between `patched_files.upstream_sha256` and
        // `vendor_tree.files[].sha256` is rejected.
        let mut pin_upstream_mismatch: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        let mismatch_path = pin_upstream_mismatch["patched_files"][0]["path"]
            .as_str()
            .unwrap()
            .to_string();
        pin_upstream_mismatch["patched_files"][0]["upstream_sha256"] =
            json!("4444444444444444444444444444444444444444444444444444444444444444");
        let err_upstream_mismatch = verify_upstream_pin_bytes(
            &vendor_root,
            &serde_json::to_vec(&pin_upstream_mismatch).unwrap(),
        )
        .unwrap_err();
        assert_eq!(err_upstream_mismatch.code, 1);
        assert!(
            err_upstream_mismatch.message.contains(&format!(
                "patched_sha256 mismatch between patched_files and vendor_tree for {mismatch_path}"
            )),
            "unexpected error: {err_upstream_mismatch}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn rejects_symlinks_in_miri_cache_dir() {
        use std::os::unix::fs::symlink;
        let tmp = tempfile::tempdir().unwrap();
        let src = tmp.path().join("staged.olean");
        fs::write(&src, b"compiled-olean").unwrap();
        let outside = tmp.path().join("outside");
        fs::create_dir_all(&outside).unwrap();
        let victim = outside.join("victim.olean");
        fs::write(&victim, b"keep-me").unwrap();

        // 1. Symlinked cache root (with and without trailing slash) is
        // rejected.
        let sym_root = tmp.path().join("sym-cache");
        symlink(&outside, &sym_root).unwrap();
        assert_eq!(
            write_cache_file(&src, &sym_root, "Miri/Hex.olean", "miri-pin")
                .unwrap_err()
                .code,
            1
        );
        let sym_root_slash = PathBuf::from(format!("{}/", sym_root.display()));
        assert_eq!(
            prepare_nosymlink_cache_path(&sym_root_slash, "Miri/Hex.olean", false, "miri-pin")
                .unwrap_err()
                .code,
            1
        );

        // 2. Symlinked intermediate subdirectory inside `cache_dir` is
        // rejected.
        let cache = tmp.path().join("real-cache");
        fs::create_dir_all(&cache).unwrap();
        symlink(&outside, cache.join("Miri")).unwrap();
        assert_eq!(
            write_cache_file(&src, &cache, "Miri/Hex.olean", "miri-pin")
                .unwrap_err()
                .code,
            1
        );
        assert!(!outside.join("Hex.olean").exists());
        fs::remove_file(cache.join("Miri")).unwrap();

        // 3. Symlinked (existing or dangling) leaf cache entry is rejected on
        // both write and stale-companion removal without touching the target.
        fs::create_dir_all(cache.join("Miri")).unwrap();
        symlink(&victim, cache.join("Miri/Hex.olean")).unwrap();
        assert_eq!(
            write_cache_file(&src, &cache, "Miri/Hex.olean", "miri-pin")
                .unwrap_err()
                .code,
            1
        );
        assert_eq!(
            remove_cache_file(&cache, "Miri/Hex.olean", "miri-pin")
                .unwrap_err()
                .code,
            1
        );
        assert_eq!(fs::read(&victim).unwrap(), b"keep-me");
    }

    #[test]
    fn verifies_source_lock_wiring_and_rejects_mismatched_pins_and_digests() {
        let vendor_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vendor/lean-miri");
        let orig_pin_bytes = fs::read(vendor_root.join("UPSTREAM_PIN.json")).unwrap();
        let mut pin_bad_sl_sha: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        pin_bad_sl_sha["upstream_pins"]["source_lock_sha256"] =
            json!("5555555555555555555555555555555555555555555555555555555555555555");
        let err_sl_sha =
            verify_upstream_pin_bytes(&vendor_root, &serde_json::to_vec(&pin_bad_sl_sha).unwrap())
                .unwrap_err();
        assert_eq!(err_sl_sha.code, 1);
        assert!(
            err_sl_sha
                .message
                .contains("upstream_pins.source_lock_sha256 mismatches vendor_aux_files"),
            "unexpected error: {err_sl_sha}"
        );

        let pin: UpstreamPin = serde_json::from_slice(&orig_pin_bytes).unwrap();
        let lock_bytes = fs::read(vendor_root.join("upstream/source-lock.json")).unwrap();
        let mut lock_json: Json = serde_json::from_slice(&lock_bytes).unwrap();
        lock_json["pins"]["rustc"]["commit"] = json!("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
        let err_commit = verify_source_lock_bytes_against_pins(
            &serde_json::to_vec(&lock_json).unwrap(),
            &pin.upstream_pins,
        )
        .unwrap_err();
        assert_eq!(err_commit.code, 1);
        assert!(
            err_commit.message.contains("upstream/source-lock.json `rustc` commit mismatch"),
            "unexpected error: {err_commit}"
        );

        // Audit-wiring check: `verify_upstream_pin_bytes` must validate the
        // parsed `source-lock.json` even when the caller supplies matching
        // `source_lock_sha256` and `vendor_aux_files` digests for a tampered
        // lockfile.
        let tmp = tempfile::tempdir().unwrap();
        let vendor_copy = tmp.path().join("vendor/lean-miri");
        for entry in WalkDir::new(&vendor_root).follow_links(false) {
            let entry = entry.unwrap();
            let rel = entry.path().strip_prefix(&vendor_root).unwrap();
            let dst = vendor_copy.join(rel);
            if entry.file_type().is_dir() {
                fs::create_dir_all(&dst).unwrap();
            } else {
                fs::copy(entry.path(), &dst).unwrap();
            }
        }
        let mut tampered_lock: Json = serde_json::from_slice(&lock_bytes).unwrap();
        tampered_lock["supporting_files"][0]
            .as_object_mut()
            .unwrap()
            .insert("**HASH**".to_string(), Json::Null);
        let tampered_bytes = serde_json::to_vec(&tampered_lock).unwrap();
        fs::write(vendor_copy.join("upstream/source-lock.json"), &tampered_bytes).unwrap();
        let tampered_sha = sha256_bytes(&tampered_bytes);
        let mut updated_pin: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        updated_pin["upstream_pins"]["source_lock_sha256"] = json!(tampered_sha);
        for aux in updated_pin["vendor_aux_files"].as_array_mut().unwrap() {
            if aux["path"].as_str() == Some("upstream/source-lock.json") {
                aux["sha256"] = json!(tampered_sha);
            }
        }
        let err_wired =
            verify_upstream_pin_bytes(&vendor_copy, &serde_json::to_vec(&updated_pin).unwrap())
                .unwrap_err();
        assert_eq!(err_wired.code, 1);
        assert!(
            err_wired.message.contains("unexpected `**HASH**` field in `supporting_files`"),
            "unexpected error: {err_wired}"
        );
    }
}
