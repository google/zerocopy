// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Content-addressed `.olean` reuse across prebuilt toolchain archives and a
//! user-local disk cache.
//!
//! Covers the static inspector (`TrustedBoundary.lean`), static bundled
//! `Trusted.*` / `Anneal.*` runtime libraries (prebuilt or disk), and
//! sandboxed target capture/proof shard artifacts (`Proof.IdTree`,
//! `Captured.Shard_*`, `Proof.Shard_*`; disabled whenever
//! `SandboxMode::Unsandboxed` / `ActiveSandbox::None` is active so unsandboxed
//! runs never share target-shard disk cache entries with sandboxed runs).
//! Every cached `.olean` must match the exact `lean` executable digest, sysroot
//! `.olean*` manifest digest, module source digest, compiler flags, and direct
//! and transitive import artifact digests, and is still copied into the
//! private stage, checked against `olean_ledger`, and replayed by
//! `target-audit` for the reachable theorem dependency cone.

#[cfg(unix)]
use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};
use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::OsStr,
    fs::{self, OpenOptions},
    io::{self, Write as _},
    path::{Component, Path, PathBuf},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::core::validate_olean_v2_header;
use crate::sandbox::{MAX_OLEAN_BYTES, copy_readonly_file, set_mode};
use crate::sys_util::{SafeFs, failure_from_io};
use crate::{
    Failure, ImportEdge, ModuleArtifacts, is_clean_relative_path, is_sha256_hex, sha256_bytes,
    toolchain::cache_dir_for_platform,
};

const CACHE_FORMAT_VERSION: u32 = 2;
const PREBUILT_MANIFEST_FILE: &str = "manifest.json";
const ENTRY_METADATA_FILE: &str = "metadata.json";

/// Discriminates cached `TrustedBoundary` inspector artifacts from regular
/// compiled Lean modules.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum CacheKind {
    Inspector,
    Module,
}

/// Binds a direct module `import` edge to both the exact SHA-256 digests of the
/// imported module's `.olean*` artifacts and its transitive import-DAG Merkle
/// digest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct CacheImportBinding {
    pub module: String,
    pub is_exported: bool,
    pub import_all: bool,
    pub is_meta: bool,
    pub part_sha256s: Vec<String>,
    pub transitive_sha256: String,
}

/// Complete deterministic cache-key input for an inspector, bundled library
/// module, or sandboxed target shard module.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct OleanCacheKeyInput {
    pub kind: CacheKind,
    pub module: String,
    pub lean_sha256: String,
    pub sysroot_manifest_sha256: String,
    pub source_sha256: String,
    pub is_module: bool,
    pub flags: Vec<String>,
    pub imports: Vec<CacheImportBinding>,
}

impl OleanCacheKeyInput {
    /// Compute the deterministic 64-hex-char SHA-256 digest naming this exact
    /// Merkle-DAG cache key (`v2`).
    pub(crate) fn cache_key(&self) -> String {
        let mut h = Sha256::new();
        h.update(b"anneal-olean-cache-v2\0");
        h.update(match self.kind {
            CacheKind::Inspector => b"inspector\0".as_slice(),
            CacheKind::Module => b"module\0".as_slice(),
        });
        feed_len_str(&mut h, &self.module);
        feed_len_str(&mut h, &self.lean_sha256.to_ascii_lowercase());
        feed_len_str(&mut h, &self.sysroot_manifest_sha256.to_ascii_lowercase());
        feed_len_str(&mut h, &self.source_sha256.to_ascii_lowercase());
        h.update([u8::from(self.is_module)]);
        h.update((self.flags.len() as u64).to_le_bytes());
        for flag in &self.flags {
            feed_len_str(&mut h, flag);
        }
        h.update((self.imports.len() as u64).to_le_bytes());
        for imp in &self.imports {
            feed_len_str(&mut h, &imp.module);
            h.update([
                u8::from(imp.is_exported),
                u8::from(imp.import_all),
                u8::from(imp.is_meta),
            ]);
            h.update((imp.part_sha256s.len() as u64).to_le_bytes());
            for sha in &imp.part_sha256s {
                feed_len_str(&mut h, &sha.to_ascii_lowercase());
            }
            feed_len_str(&mut h, &imp.transitive_sha256.to_ascii_lowercase());
        }
        format!("{:x}", h.finalize())
    }

    fn matches_entry(&self, other: &Self) -> bool {
        self.kind == other.kind
            && self.module == other.module
            && self.lean_sha256.eq_ignore_ascii_case(&other.lean_sha256)
            && self.sysroot_manifest_sha256.eq_ignore_ascii_case(&other.sysroot_manifest_sha256)
            && self.source_sha256.eq_ignore_ascii_case(&other.source_sha256)
            && self.is_module == other.is_module
            && self.flags == other.flags
            && self.imports.len() == other.imports.len()
            && self.imports.iter().zip(&other.imports).all(|(a, b)| {
                a.module == b.module
                    && a.is_exported == b.is_exported
                    && a.import_all == b.import_all
                    && a.is_meta == b.is_meta
                    && a.part_sha256s.len() == b.part_sha256s.len()
                    && a.part_sha256s
                        .iter()
                        .zip(&b.part_sha256s)
                        .all(|(x, y)| x.eq_ignore_ascii_case(y))
                    && a.transitive_sha256.eq_ignore_ascii_case(&b.transitive_sha256)
            })
    }
}

fn feed_len_str(h: &mut Sha256, s: &str) {
    h.update((s.len() as u64).to_le_bytes());
    h.update(s.as_bytes());
}

/// Recorded compiled output artifact inside a prebuilt or local cache entry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct CachePartRecord {
    /// Companion role (`"olean"`, `"olean.server"`, or `"olean.private"`).
    pub suffix: String,
    /// Relative file path beneath the entry root (or `prebuilt_dir`).
    pub path: String,
    pub sha256: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PrebuiltManifestEntry {
    #[serde(flatten)]
    input: OleanCacheKeyInput,
    parts: Vec<CachePartRecord>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PrebuiltManifestHeader {
    schema_version: u32,
    #[allow(dead_code)]
    entries: Vec<serde::de::IgnoredAny>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PrebuiltManifest {
    schema_version: u32,
    entries: Vec<PrebuiltManifestEntry>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct DiskCacheMetadata {
    schema_version: u32,
    cache_key: String,
    input: OleanCacheKeyInput,
    parts: Vec<CachePartRecord>,
}

/// Canonical compiler flags encoded in module cache keys (omitting `-M<MB>`,
/// `--json`, and file paths that do not alter compiled bytecode).
pub(crate) fn canonical_compile_flags(warn_as_err: bool) -> Vec<String> {
    let mut flags = vec![
        "-j1".to_owned(),
        "-t0".to_owned(),
        "-DElab.async=false".to_owned(),
        "-Ddebug.skipKernelTC=false".to_owned(),
    ];
    if warn_as_err {
        flags.push("-DwarningAsError=true".to_owned());
    }
    flags
}

/// Canonical compiler flags encoded in `TrustedBoundary.olean` cache keys.
pub(crate) fn canonical_inspector_flags() -> Vec<String> {
    canonical_compile_flags(false)
}

/// Return `true` iff `module` belongs to the bundled `Trusted.*` or `Anneal.*`
/// runtime libraries eligible for content-addressed `.olean` reuse.
pub(crate) fn is_cacheable_bundled_module(module: &str) -> bool {
    matches!(module, "Trusted" | "Anneal")
        || module.starts_with("Trusted.")
        || module.starts_with("Anneal.")
}

/// Return `true` iff `module` is a target capture/proof shard or `Proof.IdTree`
/// eligible for content-addressed disk `.olean` reuse across incremental
/// single-body verification runs.
pub(crate) fn is_cacheable_target_shard_module(module: &str) -> bool {
    module == "Proof.IdTree"
        || module.starts_with("Captured.Shard_")
        || module.starts_with("Proof.Shard_")
}

/// Derive a per-user disk cache directory (`<cache>/anneal/olean-cache`)
/// from explicit `HOME` and optional `XDG_CACHE_HOME` values without reading
/// ambient process environment variables.
pub(crate) fn cache_dir_from_env_vars(
    home: Option<&OsStr>,
    xdg_cache_home: Option<&OsStr>,
) -> Option<PathBuf> {
    let home = home.filter(|v| !v.is_empty()).map(PathBuf::from)?;
    let base = cache_dir_for_platform(cfg!(target_os = "macos"), xdg_cache_home, &home);
    Some(base.join("anneal/olean-cache"))
}

/// Derive the default per-user disk cache directory (`<cache>/anneal/olean-cache`)
/// matching `toolchain.rs` XDG precedence without creating any directories.
#[cfg(test)]
pub(crate) fn default_olean_cache_dir() -> Option<PathBuf> {
    let home = std::env::var_os("HOME");
    let xdg = std::env::var_os("XDG_CACHE_HOME");
    cache_dir_from_env_vars(home.as_deref(), xdg.as_deref())
}

type PrebuiltEntryMap = BTreeMap<(CacheKind, String), PrebuiltManifestEntry>;
type LoadedCacheParts = Vec<(String, Vec<u8>, String)>;

/// Materialized `.olean*` artifacts promoted from cache into a staging tree.
#[derive(Debug)]
pub(crate) struct CachedHitArtifact {
    /// `(suffix, materialized_path, sha256)` for every staged `.olean*` part.
    pub materialized_parts: Vec<(String, PathBuf, String)>,
}

/// Unified prebuilt + user-local `.olean` cache handle owned by `Checker`.
#[derive(Debug, Clone)]
pub(crate) struct OleanCache {
    enabled: bool,
    no_rebuild_bundled: bool,
    prebuilt_dir: Option<PathBuf>,
    disk_dir: Option<PathBuf>,
    prebuilt_entries: Option<PrebuiltEntryMap>,
    prebuilt_skipped_version: Option<u32>,
}

impl OleanCache {
    pub(crate) fn with_env_vars(home: Option<&OsStr>, xdg_cache_home: Option<&OsStr>) -> Self {
        Self {
            enabled: true,
            no_rebuild_bundled: false,
            prebuilt_dir: None,
            disk_dir: cache_dir_from_env_vars(home, xdg_cache_home),
            prebuilt_entries: None,
            prebuilt_skipped_version: None,
        }
    }

    #[cfg(test)]
    pub(crate) fn new_default() -> Self {
        Self {
            enabled: true,
            no_rebuild_bundled: false,
            prebuilt_dir: None,
            disk_dir: default_olean_cache_dir(),
            prebuilt_entries: None,
            prebuilt_skipped_version: None,
        }
    }

    pub(crate) fn preload_prebuilt(&mut self) -> Result<(), Failure> {
        let _ = self.load_prebuilt()?;
        Ok(())
    }

    pub(crate) fn is_enabled(&self) -> bool {
        self.enabled
    }

    pub(crate) fn set_enabled(&mut self, enabled: bool) {
        self.enabled = enabled;
    }

    pub(crate) fn set_no_rebuild_bundled(&mut self, no_rebuild: bool) {
        self.no_rebuild_bundled = no_rebuild;
    }

    pub(crate) fn set_prebuilt_dir(&mut self, dir: Option<PathBuf>) {
        if self.prebuilt_dir != dir {
            self.prebuilt_dir = dir;
            self.prebuilt_entries = None;
            self.prebuilt_skipped_version = None;
        }
    }

    #[cfg(test)]
    pub(crate) fn set_disk_dir(&mut self, dir: Option<PathBuf>) {
        self.disk_dir = dir;
    }

    fn load_prebuilt(&mut self) -> Result<Option<&PrebuiltEntryMap>, Failure> {
        if self.prebuilt_entries.is_some() {
            return Ok(self.prebuilt_entries.as_ref());
        }
        if self.prebuilt_skipped_version.is_some() {
            return Ok(None);
        }
        let Some(ref prebuilt_dir) = self.prebuilt_dir else {
            return Ok(None);
        };
        if !probe_existing_non_symlink_dir(prebuilt_dir, false)? {
            return Ok(None);
        }
        let manifest_path = prebuilt_dir.join(PREBUILT_MANIFEST_FILE);
        if !probe_existing_regular_file(&manifest_path, false)? {
            return Ok(None);
        }
        let bytes = read_regular_nofollow_capped(&manifest_path, MAX_OLEAN_BYTES, "olean-cache")?;
        let header: PrebuiltManifestHeader = serde_json::from_slice(&bytes).map_err(|e| {
            Failure::operational(
                "olean-cache",
                format!("invalid prebuilt olean manifest {}: {e}", manifest_path.display()),
            )
        })?;
        if header.schema_version != CACHE_FORMAT_VERSION {
            // Treat mismatched prebuilt manifest versions (e.g. a pinned v1
            // toolchain archive) as a cache miss rather than aborting,
            // matching v1/ disk-cache directory isolation while keeping
            // malformed manifests fail-closed above.
            self.prebuilt_skipped_version = Some(header.schema_version);
            return Ok(None);
        }
        let manifest: PrebuiltManifest = serde_json::from_slice(&bytes).map_err(|e| {
            Failure::operational(
                "olean-cache",
                format!("invalid prebuilt olean manifest {}: {e}", manifest_path.display()),
            )
        })?;
        let mut by_key = BTreeMap::new();
        for entry in manifest.entries {
            by_key.insert((entry.input.kind, entry.input.module.clone()), entry);
        }
        self.prebuilt_entries = Some(by_key);
        Ok(self.prebuilt_entries.as_ref())
    }

    /// Look up `input` in read-only `prebuilt_dir` first, then the user-local
    /// disk cache, validating every artifact byte-for-byte without writing
    /// staging files yet.
    pub(crate) fn lookup_bytes(
        &mut self,
        input: &OleanCacheKeyInput,
    ) -> Result<Option<LoadedCacheParts>, Failure> {
        if !self.enabled {
            return Ok(None);
        }
        if let Some(prebuilt_dir) = self.prebuilt_dir.clone()
            && let Some(entries) = self.load_prebuilt()?
            && let Some(entry) = entries.get(&(input.kind, input.module.clone()))
            && entry.input.matches_entry(input)
        {
            let parts = load_validated_parts(
                &prebuilt_dir,
                &entry.parts,
                /*require_owner_uid=*/ false,
            )?;
            return Ok(Some(parts));
        }

        if let Some(ref disk_dir) = self.disk_dir
            && let Some(parts) = lookup_disk_cache_bytes(disk_dir, input)?
        {
            return Ok(Some(parts));
        }

        if self.no_rebuild_bundled
            && (input.kind == CacheKind::Inspector || is_cacheable_bundled_module(&input.module))
        {
            let reason = if let Some(found_ver) = self.prebuilt_skipped_version {
                format!(
                    "missing prebuilt or cached .olean for {} (--no-rebuild-bundled; skipped prebuilt manifest schema_version {found_ver} != {CACHE_FORMAT_VERSION})",
                    input.module
                )
            } else {
                format!(
                    "missing prebuilt or cached .olean for {} (--no-rebuild-bundled)",
                    input.module
                )
            };
            return Err(Failure::operational("olean-cache", reason));
        }
        Ok(None)
    }

    /// Look up `input` and materialize validated parts into `dest_dir` with
    /// `0o444` permissions (`dest_leaf.<suffix>`).
    pub(crate) fn lookup_and_materialize(
        &mut self,
        input: &OleanCacheKeyInput,
        dest_dir: &Path,
        dest_leaf: &str,
    ) -> Result<Option<CachedHitArtifact>, Failure> {
        let Some(parts) = self.lookup_bytes(input)? else {
            return Ok(None);
        };
        materialize_loaded_parts(&parts, dest_dir, dest_leaf).map(Some)
    }

    /// Atomically persist compiled `.olean` artifacts into the user-local disk
    /// cache. Best-effort when the cache directory resides on a read-only
    /// filesystem or uncreatable home directory, while failing closed on
    /// symlink or ownership violations inside an existing cache tree.
    pub(crate) fn store_compiled(
        &self,
        input: &OleanCacheKeyInput,
        parts: &[(&str, &Path, &str)],
    ) -> Result<(), Failure> {
        if !self.enabled {
            return Ok(());
        }
        let Some(ref disk_dir) = self.disk_dir else {
            return Ok(());
        };
        if let Err(err) = ensure_private_cache_root(disk_dir) {
            if is_unwritable_cache_init_err(&err) {
                return Ok(());
            }
            return Err(err);
        }
        let v2_dir = disk_dir.join("v2");
        if !probe_existing_non_symlink_dir(&v2_dir, true)? {
            SafeFs::create_dir_mode(&v2_dir, 0o700, "olean-cache")?;
        }
        let key = input.cache_key();
        let entry_dir = v2_dir.join(&key);
        if probe_existing_non_symlink_dir(&entry_dir, true)? {
            return Ok(());
        }

        let tmp = tempfile::Builder::new()
            .prefix(".tmp-")
            .tempdir_in(&v2_dir)
            .map_err(|e| Failure::operational("olean-cache", format!("cannot stage cache temp dir: {e}")))?;
        #[cfg(unix)]
        set_mode(tmp.path(), 0o700)?;

        let mut part_records = Vec::with_capacity(parts.len());
        for &(suffix, src_path, expected_sha) in parts {
            let rel_name = format!("module.{suffix}");
            let staged = tmp.path().join(&rel_name);
            copy_readonly_file(src_path, &staged, "olean-cache")?;
            let actual_sha = sha256_bytes(
                &fs::read(&staged)
                    .map_err(|e| Failure::operational("olean-cache", e.to_string()))?,
            );
            if !actual_sha.eq_ignore_ascii_case(expected_sha) {
                return Err(Failure::operational(
                    "olean-cache",
                    format!("staged cache part {rel_name} digest mismatch during store"),
                ));
            }
            part_records.push(CachePartRecord {
                suffix: suffix.to_owned(),
                path: rel_name,
                sha256: expected_sha.to_ascii_lowercase(),
            });
        }
        let meta = DiskCacheMetadata {
            schema_version: CACHE_FORMAT_VERSION,
            cache_key: key.clone(),
            input: input.clone(),
            parts: part_records,
        };
        let meta_bytes = serde_json::to_vec(&meta)
            .map_err(|e| Failure::operational("olean-cache", e.to_string()))?;
        let meta_tmp = tmp.path().join(ENTRY_METADATA_FILE);
        fs::write(&meta_tmp, meta_bytes)
            .map_err(|e| Failure::operational("olean-cache", e.to_string()))?;
        set_mode(&meta_tmp, 0o444)?;

        let lock_path = v2_dir.join(format!("{key}.lock"));
        let _lock = acquire_exclusive_flock(&lock_path)?;
        if !probe_existing_non_symlink_dir(&entry_dir, true)? {
            let staged_path = tmp.keep();
            if let Err(err) = fs::rename(&staged_path, &entry_dir) {
                crate::sandbox::make_tree_writable(&staged_path);
                let _ = fs::remove_dir_all(&staged_path);
                if !probe_existing_non_symlink_dir(&entry_dir, true)? {
                    return Err(Failure::operational(
                        "olean-cache",
                        format!("cannot publish cache entry {}: {err}", entry_dir.display()),
                    ));
                }
            }
        }
        Ok(())
    }
}

fn is_unwritable_cache_init_err(err: &Failure) -> bool {
    err.is_unwritable_io_error()
}

fn lookup_disk_cache_bytes(
    disk_dir: &Path,
    input: &OleanCacheKeyInput,
) -> Result<Option<LoadedCacheParts>, Failure> {
    // Allow an absent or unsearchable ambient `$HOME`/`$XDG_CACHE_HOME` root
    // (`NotFound` or `PermissionDenied` on `lstat(disk_dir)`) to fall back to
    // a clean cache miss, while failing closed on any other root error or any
    // non-`NotFound` error inside an existing `disk_dir`.
    let disk_meta = match fs::symlink_metadata(disk_dir) {
        Ok(meta) => meta,
        Err(e) if matches!(e.kind(), io::ErrorKind::NotFound | io::ErrorKind::PermissionDenied) => {
            return Ok(None);
        }
        Err(e) => {
            return Err(failure_from_io(
                "olean-cache",
                format!("cannot inspect {}: {e}", disk_dir.display()),
                &e,
            ));
        }
    };
    verify_non_symlink_dir_meta(disk_dir, &disk_meta, "olean-cache", true)?;
    let v2_dir = disk_dir.join("v2");
    if !probe_existing_non_symlink_dir(&v2_dir, true)? {
        return Ok(None);
    }
    let key = input.cache_key();
    let entry_dir = v2_dir.join(&key);
    if !probe_existing_non_symlink_dir(&entry_dir, true)? {
        return Ok(None);
    }
    let meta_path = entry_dir.join(ENTRY_METADATA_FILE);
    if !probe_existing_regular_file(&meta_path, true)? {
        return Ok(None);
    }
    let meta_bytes = read_regular_nofollow_capped(&meta_path, MAX_OLEAN_BYTES, "olean-cache")?;
    let meta: DiskCacheMetadata = serde_json::from_slice(&meta_bytes).map_err(|e| {
        Failure::operational(
            "olean-cache",
            format!("corrupt cache metadata {}: {e}", meta_path.display()),
        )
    })?;
    if meta.schema_version != CACHE_FORMAT_VERSION
        || meta.cache_key != key
        || !meta.input.matches_entry(input)
    {
        return Err(Failure::operational(
            "olean-cache",
            format!("cache metadata mismatch in {}", meta_path.display()),
        ));
    }
    load_validated_parts(&entry_dir, &meta.parts, /*require_owner_uid=*/ true).map(Some)
}

fn load_validated_parts(
    base_dir: &Path,
    parts: &[CachePartRecord],
    require_owner_uid: bool,
) -> Result<LoadedCacheParts, Failure> {
    if !parts.iter().any(|p| p.suffix == "olean") {
        return Err(Failure::operational("olean-cache", "cached entry missing primary olean part"));
    }
    let mut loaded = Vec::with_capacity(parts.len());

    for part in parts {
        if !matches!(part.suffix.as_str(), "olean" | "olean.server" | "olean.private") {
            return Err(Failure::operational(
                "olean-cache",
                format!("unsupported cached olean suffix {}", part.suffix),
            ));
        }
        if !is_sha256_hex(&part.sha256) {
            return Err(Failure::operational(
                "olean-cache",
                format!("invalid cached SHA-256 digest for {}", part.path),
            ));
        }
        if !is_clean_relative_path(&part.path) {
            return Err(Failure::operational(
                "olean-cache",
                format!("invalid relative cache part path {}", part.path),
            ));
        }
        let src_path = join_checked_non_symlink(base_dir, Path::new(&part.path), require_owner_uid)?;
        let bytes = SafeFs::read_regular_nofollow_capped(&src_path, MAX_OLEAN_BYTES, "olean-cache")?;
        if require_owner_uid {
            verify_owner_uid(&src_path)?;
        }
        let actual_sha = sha256_bytes(&bytes);
        if !actual_sha.eq_ignore_ascii_case(&part.sha256) {
            return Err(Failure::operational(
                "olean-cache",
                format!(
                    "cached artifact SHA-256 mismatch for {} (expected {}, got {})",
                    src_path.display(),
                    part.sha256,
                    actual_sha
                ),
            ));
        }
        if part.suffix == "olean" {
            validate_olean_v2_header(&bytes, &src_path.display().to_string(), "olean-cache")?;
        }
        loaded.push((part.suffix.clone(), bytes, actual_sha));
    }

    Ok(loaded)
}

fn materialize_loaded_parts(
    parts: &[(String, Vec<u8>, String)],
    dest_dir: &Path,
    dest_leaf: &str,
) -> Result<CachedHitArtifact, Failure> {
    let mut materialized_parts = Vec::with_capacity(parts.len());

    for (suffix, bytes, actual_sha) in parts {
        let dest_path = dest_dir.join(format!("{dest_leaf}.{suffix}"));
        if let Some(parent) = dest_path.parent() {
            SafeFs::create_dir_mode(parent, 0o700, "olean-cache")?;
        }
        if probe_symlink_metadata(&dest_path)?.is_some() {
            fs::remove_file(&dest_path).map_err(|e| {
                Failure::operational(
                    "olean-cache",
                    format!("cannot replace staged {}: {e}", dest_path.display()),
                )
            })?;
        }
        let mut f = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&dest_path)
            .map_err(|e| {
                Failure::operational(
                    "olean-cache",
                    format!("cannot stage cached {}: {e}", dest_path.display()),
                )
            })?;
        f.write_all(bytes).map_err(|e| {
            Failure::operational(
                "olean-cache",
                format!("cannot write staged {}: {e}", dest_path.display()),
            )
        })?;
        drop(f);
        set_mode(&dest_path, 0o444)?;
        materialized_parts.push((suffix.clone(), dest_path, actual_sha.clone()));
    }

    Ok(CachedHitArtifact { materialized_parts })
}

fn ensure_private_cache_root(disk_dir: &Path) -> Result<(), Failure> {
    if !disk_dir.is_absolute() {
        return Err(Failure::operational(
            "olean-cache",
            format!("cache path must be absolute: {}", disk_dir.display()),
        ));
    }
    let mut cur = PathBuf::new();
    for comp in disk_dir.components() {
        match comp {
            Component::RootDir => cur.push(comp.as_os_str()),
            Component::Normal(seg) => {
                cur.push(seg);
                if let Some(meta) = probe_symlink_metadata(&cur)? {
                    if meta.file_type().is_symlink() || !meta.is_dir() {
                        return Err(Failure::operational(
                            "olean-cache",
                            format!(
                                "refusing symlink or non-directory cache ancestor {}",
                                cur.display()
                            ),
                        ));
                    }
                } else {
                    SafeFs::create_dir_mode(&cur, 0o700, "olean-cache")?;
                }
            }
            _ => {
                return Err(Failure::operational(
                    "olean-cache",
                    format!("invalid cache path component in {}", disk_dir.display()),
                ));
            }
        }
    }
    verify_non_symlink_dir(disk_dir, "olean-cache", true)
}

/// Inspect `path` without following symlinks, treating only
/// `io::ErrorKind::NotFound` as absent (`Ok(None)`) and failing closed on
/// other OS metadata errors (`PermissionDenied`, `NotADirectory`, `ELOOP`,
/// `EIO`).
fn probe_symlink_metadata(path: &Path) -> Result<Option<fs::Metadata>, Failure> {
    SafeFs::probe_symlink_metadata(path, "olean-cache")
}

/// Probe `dir` without following symlinks, returning `Ok(false)` only when
/// absent (`NotFound`) and rejecting symlinks, non-directories, owner UID
/// mismatches (when `require_owner_uid`), and other OS errors.
fn probe_existing_non_symlink_dir(dir: &Path, require_owner_uid: bool) -> Result<bool, Failure> {
    let Some(meta) = probe_symlink_metadata(dir)? else {
        return Ok(false);
    };
    verify_non_symlink_dir_meta(dir, &meta, "olean-cache", require_owner_uid)?;
    Ok(true)
}

/// Probe `path` without following symlinks, returning `Ok(false)` only when
/// absent (`NotFound`) and rejecting symlinks, non-regular files, owner UID
/// mismatches (when `require_owner_uid`), and other OS errors.
fn probe_existing_regular_file(path: &Path, require_owner_uid: bool) -> Result<bool, Failure> {
    let Some(meta) = probe_symlink_metadata(path)? else {
        return Ok(false);
    };
    if meta.file_type().is_symlink() || !meta.is_file() {
        return Err(Failure::operational(
            "olean-cache",
            format!("cache path {} must be a regular non-symlink file", path.display()),
        ));
    }
    if require_owner_uid {
        verify_meta_owner_uid(path, &meta)?;
    }
    Ok(true)
}

fn verify_non_symlink_dir(dir: &Path, phase: &str, require_owner_uid: bool) -> Result<(), Failure> {
    let meta = fs::symlink_metadata(dir)
        .map_err(|e| failure_from_io(phase, format!("cannot inspect {}: {e}", dir.display()), &e))?;
    verify_non_symlink_dir_meta(dir, &meta, phase, require_owner_uid)
}

fn verify_non_symlink_dir_meta(
    dir: &Path,
    meta: &fs::Metadata,
    phase: &str,
    require_owner_uid: bool,
) -> Result<(), Failure> {
    if meta.file_type().is_symlink() || !meta.is_dir() {
        return Err(Failure::operational(
            phase,
            format!("cache directory {} must be a regular non-symlink directory", dir.display()),
        ));
    }
    if require_owner_uid {
        verify_meta_owner_uid(dir, meta)?;
    }
    Ok(())
}

fn join_checked_non_symlink(
    base: &Path,
    rel: &Path,
    require_owner_uid: bool,
) -> Result<PathBuf, Failure> {
    let mut cur = base.to_path_buf();
    let comps: Vec<_> = rel.components().collect();
    for (idx, comp) in comps.iter().enumerate() {
        let Component::Normal(seg) = comp else {
            return Err(Failure::operational(
                "olean-cache",
                format!("invalid relative cache path {}", rel.display()),
            ));
        };
        cur.push(seg);
        let is_last = idx + 1 == comps.len();
        let meta = fs::symlink_metadata(&cur).map_err(|e| {
            Failure::operational("olean-cache", format!("missing cached file {}: {e}", cur.display()))
        })?;
        if meta.file_type().is_symlink() {
            return Err(Failure::operational(
                "olean-cache",
                format!("refusing symlink in cache path {}", cur.display()),
            ));
        }
        if is_last {
            if !meta.is_file() {
                return Err(Failure::operational(
                    "olean-cache",
                    format!("cached path {} is not a regular file", cur.display()),
                ));
            }
        } else if !meta.is_dir() {
            return Err(Failure::operational(
                "olean-cache",
                format!("cached ancestor {} is not a directory", cur.display()),
            ));
        }
        if require_owner_uid {
            verify_meta_owner_uid(&cur, &meta)?;
        }
    }
    Ok(cur)
}

fn verify_owner_uid(path: &Path) -> Result<(), Failure> {
    let meta = fs::symlink_metadata(path)
        .map_err(|e| Failure::operational("olean-cache", format!("cannot inspect {}: {e}", path.display())))?;
    verify_meta_owner_uid(path, &meta)
}

fn verify_meta_owner_uid(path: &Path, meta: &fs::Metadata) -> Result<(), Failure> {
    #[cfg(unix)]
    {
        // SAFETY: `geteuid` has no preconditions and always succeeds.
        let uid = unsafe { libc::geteuid() };
        if meta.uid() != uid {
            return Err(Failure::operational(
                "olean-cache",
                format!(
                    "cache path {} owner uid {} differs from current uid {uid}",
                    path.display(),
                    meta.uid()
                ),
            ));
        }
    }
    let _ = (path, meta);
    Ok(())
}

fn read_regular_nofollow_capped(path: &Path, max_bytes: u64, phase: &str) -> Result<Vec<u8>, Failure> {
    SafeFs::read_regular_nofollow_capped(path, max_bytes, phase)
}

struct FlockGuard {
    _file: fs::File,
}

impl Drop for FlockGuard {
    fn drop(&mut self) {
        #[cfg(unix)]
        {
            use std::os::unix::io::AsRawFd as _;
            // SAFETY: `_file` is an open file descriptor we locked exclusively.
            unsafe {
                libc::flock(self._file.as_raw_fd(), libc::LOCK_UN);
            }
        }
    }
}

fn acquire_exclusive_flock(lock_path: &Path) -> Result<FlockGuard, Failure> {
    let mut opts = OpenOptions::new();
    opts.create(true).read(true).write(true);
    #[cfg(unix)]
    {
        opts.mode(0o600);
        opts.custom_flags(libc::O_NOFOLLOW);
    }
    let file = opts.open(lock_path).map_err(|e| {
        Failure::operational("olean-cache", format!("cannot open lock {}: {e}", lock_path.display()))
    })?;
    #[cfg(unix)]
    {
        use std::os::unix::io::AsRawFd as _;
        let rc = loop {
            // SAFETY: `file` holds a valid fd opened above.
            let r = unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX) };
            if r == 0 {
                break 0;
            }
            if io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
                break -1;
            }
        };
        if rc != 0 {
            return Err(Failure::operational(
                "olean-cache",
                format!(
                    "cannot lock {}: {}",
                    lock_path.display(),
                    io::Error::last_os_error()
                ),
            ));
        }
    }
    Ok(FlockGuard { _file: file })
}

/// Resolve and memoize SHA-256 digests for each `.olean*` part of `module`.
fn resolve_module_part_sha256s(
    module: &str,
    artifacts: &BTreeMap<String, ModuleArtifacts>,
    path_sha_cache: &mut BTreeMap<String, String>,
) -> Result<Vec<String>, Failure> {
    let mod_arts = artifacts.get(module).ok_or_else(|| {
        Failure::operational("olean-cache", format!("missing artifact for import {module}"))
    })?;
    let mut shas = Vec::with_capacity(mod_arts.olean_parts.len());
    for p in &mod_arts.olean_parts {
        let sha = if let Some(cached) = path_sha_cache.get(p) {
            cached.clone()
        } else {
            let bytes = fs::read(p).map_err(|e| {
                Failure::operational("olean-cache", format!("cannot hash dependency {p}: {e}"))
            })?;
            let computed = sha256_bytes(&bytes);
            path_sha_cache.insert(p.clone(), computed.clone());
            computed
        };
        shas.push(sha);
    }
    Ok(shas)
}

/// Compute the canonical bottom-up Merkle digest for `module` over its own
/// `.olean*` part digests and canonically sorted outgoing import edges.
///
/// Direct `.olean*` digests alone miss upstream edits behind declaration-free
/// barrel modules whose serialized `.olean*` bytes remain identical. The hash
/// framing (`anneal-olean-transitive-v1\0`, `<Q` lengths, lowercase hex, sorted
/// edges) must stay byte-for-byte identical to `ci/prebuild_bundled_oleans.py`.
fn compute_transitive_module_sha256_inner(
    module: &str,
    artifacts: &BTreeMap<String, ModuleArtifacts>,
    graph: &BTreeMap<String, Vec<ImportEdge>>,
    path_sha_cache: &mut BTreeMap<String, String>,
    transitive_memo: &mut BTreeMap<String, String>,
    visiting: &mut BTreeSet<String>,
) -> Result<String, Failure> {
    if let Some(cached) = transitive_memo.get(module) {
        return Ok(cached.clone());
    }
    if !visiting.insert(module.to_owned()) {
        return Err(Failure::operational(
            "olean-cache",
            format!("import cycle detected at {module}"),
        ));
    }
    let result = (|| {
        let part_shas = resolve_module_part_sha256s(module, artifacts, path_sha_cache)?;
        let raw_edges = graph.get(module).ok_or_else(|| {
            Failure::operational("olean-cache", format!("missing import graph entry for {module}"))
        })?;
        let mut sorted_edges: Vec<&ImportEdge> = raw_edges.iter().collect();
        sorted_edges.sort_by(|a, b| {
            a.module
                .cmp(&b.module)
                .then(a.is_exported.cmp(&b.is_exported))
                .then(a.import_all.cmp(&b.import_all))
                .then(a.is_meta.cmp(&b.is_meta))
        });
        let mut dep_hashes = Vec::with_capacity(sorted_edges.len());
        for edge in &sorted_edges {
            dep_hashes.push(compute_transitive_module_sha256_inner(
                &edge.module,
                artifacts,
                graph,
                path_sha_cache,
                transitive_memo,
                visiting,
            )?);
        }

        let mut h = Sha256::new();
        h.update(b"anneal-olean-transitive-v1\0");
        h.update((part_shas.len() as u64).to_le_bytes());
        for sha in &part_shas {
            feed_len_str(&mut h, &sha.to_ascii_lowercase());
        }
        h.update((sorted_edges.len() as u64).to_le_bytes());
        for (edge, dep_transitive) in sorted_edges.iter().zip(&dep_hashes) {
            feed_len_str(&mut h, &edge.module);
            h.update([
                u8::from(edge.is_exported),
                u8::from(edge.import_all),
                u8::from(edge.is_meta),
            ]);
            feed_len_str(&mut h, &dep_transitive.to_ascii_lowercase());
        }
        Ok(format!("{:x}", h.finalize()))
    })();
    visiting.remove(module);
    if let Ok(ref digest) = result {
        transitive_memo.insert(module.to_owned(), digest.clone());
    }
    result
}

/// Compute a module's canonical bottom-up transitive import-DAG Merkle digest.
///
/// Fails closed on any missing artifact, missing graph node, or dependency
/// cycle.
pub(crate) fn compute_transitive_module_sha256(
    module: &str,
    artifacts: &BTreeMap<String, ModuleArtifacts>,
    graph: &BTreeMap<String, Vec<ImportEdge>>,
    path_sha_cache: &mut BTreeMap<String, String>,
    transitive_memo: &mut BTreeMap<String, String>,
) -> Result<String, Failure> {
    let mut visiting = BTreeSet::new();
    compute_transitive_module_sha256_inner(
        module,
        artifacts,
        graph,
        path_sha_cache,
        transitive_memo,
        &mut visiting,
    )
}

/// Build direct import bindings for `edge_list` paired with each imported
/// module's bottom-up transitive import-DAG Merkle digest.
pub(crate) fn build_import_bindings(
    edge_list: &[ImportEdge],
    artifacts: &BTreeMap<String, ModuleArtifacts>,
    graph: &BTreeMap<String, Vec<ImportEdge>>,
    path_sha_cache: &mut BTreeMap<String, String>,
    transitive_memo: &mut BTreeMap<String, String>,
) -> Result<Vec<CacheImportBinding>, Failure> {
    let mut bindings = Vec::with_capacity(edge_list.len());
    for edge in edge_list {
        let shas = resolve_module_part_sha256s(&edge.module, artifacts, path_sha_cache)?;
        let transitive_sha256 = compute_transitive_module_sha256(
            &edge.module,
            artifacts,
            graph,
            path_sha_cache,
            transitive_memo,
        )?;
        bindings.push(CacheImportBinding {
            module: edge.module.clone(),
            is_exported: edge.is_exported,
            import_all: edge.import_all,
            is_meta: edge.is_meta,
            part_sha256s: shas,
            transitive_sha256,
        });
    }
    Ok(bindings)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_input(source_sha: &str) -> OleanCacheKeyInput {
        OleanCacheKeyInput {
            kind: CacheKind::Module,
            module: "Trusted.MirAst".to_owned(),
            lean_sha256: "a".repeat(64),
            sysroot_manifest_sha256: "b".repeat(64),
            source_sha256: source_sha.to_owned(),
            is_module: false,
            flags: canonical_compile_flags(false),
            imports: vec![CacheImportBinding {
                module: "Init.Core".to_owned(),
                is_exported: true,
                import_all: false,
                is_meta: false,
                part_sha256s: vec!["c".repeat(64)],
                transitive_sha256: "e".repeat(64),
            }],
        }
    }

    fn fake_olean() -> Vec<u8> {
        let mut data = crate::core::OLEAN_V2_MAGIC.to_vec();
        data.extend_from_slice(b"\x014.34.1\0\0payload");
        data
    }

    #[test]
    fn cache_key_is_deterministic_and_sensitive_to_every_field() {
        let base = sample_input(&"1".repeat(64));
        assert_eq!(base.cache_key(), base.cache_key());

        let mut mod_src = sample_input(&"2".repeat(64));
        assert_ne!(base.cache_key(), mod_src.cache_key());

        mod_src = base.clone();
        mod_src.flags = canonical_compile_flags(true);
        assert_ne!(base.cache_key(), mod_src.cache_key());

        mod_src = base.clone();
        mod_src.imports[0].part_sha256s[0] = "d".repeat(64);
        assert_ne!(base.cache_key(), mod_src.cache_key());

        mod_src = base.clone();
        mod_src.imports[0].transitive_sha256 = "f".repeat(64);
        assert_ne!(base.cache_key(), mod_src.cache_key());

        // `cache_key` and `matches_entry` normalize hex case on digests while
        // still rejecting differing `transitive_sha256` values if stored.
        let mut upper = base.clone();
        upper.lean_sha256 = upper.lean_sha256.to_ascii_uppercase();
        upper.sysroot_manifest_sha256 = upper.sysroot_manifest_sha256.to_ascii_uppercase();
        upper.source_sha256 = upper.source_sha256.to_ascii_uppercase();
        upper.imports[0].part_sha256s[0] = upper.imports[0].part_sha256s[0].to_ascii_uppercase();
        upper.imports[0].transitive_sha256 =
            upper.imports[0].transitive_sha256.to_ascii_uppercase();
        assert_eq!(base.cache_key(), upper.cache_key());
        assert!(base.matches_entry(&upper));
        assert!(!base.matches_entry(&mod_src));
    }

    #[test]
    fn disk_cache_roundtrip_tamper_and_no_rebuild_guards() {
        let tmp = tempfile::tempdir().unwrap();
        let disk_dir = tmp.path().join("disk-cache");
        let src_dir = tmp.path().join("src");
        let stage_dir = tmp.path().join("stage");
        fs::create_dir_all(&src_dir).unwrap();
        fs::create_dir_all(&stage_dir).unwrap();

        let olean_bytes = fake_olean();
        let olean_sha = sha256_bytes(&olean_bytes);
        let src_olean = src_dir.join("MirAst.olean");
        fs::write(&src_olean, &olean_bytes).unwrap();

        let input = sample_input(&"1".repeat(64));
        let mut cache = OleanCache::new_default();
        cache.set_disk_dir(Some(disk_dir.clone()));

        cache.store_compiled(&input, &[("olean", &src_olean, &olean_sha)]).unwrap();
        let hit = cache
            .lookup_and_materialize(&input, &stage_dir, "Trusted/MirAst")
            .unwrap()
            .expect("disk cache hit expected");
        assert_eq!(hit.materialized_parts[0].0, "olean");
        assert_eq!(hit.materialized_parts[0].2, olean_sha);
        assert_eq!(fs::read(&hit.materialized_parts[0].1).unwrap(), olean_bytes);
        assert!(stage_dir.join("Trusted/MirAst.olean").is_file());

        // Different input misses cleanly by default, and fails closed under `--no-rebuild-bundled`.
        let missed_input = sample_input(&"9".repeat(64));
        assert!(cache.lookup_and_materialize(&missed_input, &stage_dir, "Trusted/MirAst").unwrap().is_none());
        cache.set_no_rebuild_bundled(true);
        let err = cache
            .lookup_and_materialize(&missed_input, &stage_dir, "Trusted/MirAst")
            .unwrap_err();
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("--no-rebuild-bundled"));

        // Corrupting the cached `.olean` fails closed on SHA-256 verification.
        let key_dir = disk_dir.join("v2").join(input.cache_key());
        let cached_file = key_dir.join("module.olean");
        set_mode(&cached_file, 0o600).unwrap();
        fs::write(&cached_file, b"tampered bytes").unwrap();
        cache.set_no_rebuild_bundled(false);
        let err_tamper = cache
            .lookup_and_materialize(&input, &stage_dir, "Trusted/MirAst")
            .unwrap_err();
        assert!(err_tamper.message.contains("SHA-256 mismatch"), "{err_tamper}");
    }

    #[test]
    fn prebuilt_manifest_precedes_disk_cache_and_rejects_symlinks() {
        let tmp = tempfile::tempdir().unwrap();
        let prebuilt = tmp.path().join("prebuilt");
        let stage = tmp.path().join("stage");
        fs::create_dir_all(prebuilt.join("lib/Trusted")).unwrap();
        fs::create_dir_all(&stage).unwrap();

        let bytes = fake_olean();
        let sha = sha256_bytes(&bytes);
        let rel = "lib/Trusted/MirAst.olean";
        fs::write(prebuilt.join(rel), &bytes).unwrap();

        let input = sample_input(&"3".repeat(64));
        let manifest = PrebuiltManifest {
            schema_version: CACHE_FORMAT_VERSION,
            entries: vec![PrebuiltManifestEntry {
                input: input.clone(),
                parts: vec![CachePartRecord {
                    suffix: "olean".to_owned(),
                    path: rel.to_owned(),
                    sha256: sha.clone(),
                }],
            }],
        };
        fs::write(prebuilt.join(PREBUILT_MANIFEST_FILE), serde_json::to_vec(&manifest).unwrap())
            .unwrap();

        let mut cache = OleanCache::new_default();
        cache.set_disk_dir(None);
        cache.set_prebuilt_dir(Some(prebuilt.clone()));
        cache.set_no_rebuild_bundled(true);

        let hit = cache
            .lookup_and_materialize(&input, &stage, "Trusted/MirAst")
            .unwrap()
            .expect("prebuilt cache hit expected");
        assert_eq!(hit.materialized_parts[0].2, sha);

        #[cfg(unix)]
        {
            fs::remove_file(prebuilt.join(rel)).unwrap();
            std::os::unix::fs::symlink(stage.join("Trusted/MirAst.olean"), prebuilt.join(rel))
                .unwrap();
            let err = cache
                .lookup_and_materialize(&input, &stage, "Trusted/MirAst")
                .unwrap_err();
            assert!(err.message.contains("symlink"), "{err}");
        }
    }

    #[cfg(unix)]
    struct RestoreDirModeGuard {
        path: PathBuf,
    }

    #[cfg(unix)]
    impl RestoreDirModeGuard {
        fn lock(path: &Path) -> Self {
            set_mode(path, 0o000).unwrap();
            Self { path: path.to_path_buf() }
        }
    }

    #[cfg(unix)]
    impl Drop for RestoreDirModeGuard {
        fn drop(&mut self) {
            let _ = set_mode(&self.path, 0o700);
        }
    }

    #[test]
    fn disk_cache_missing_components_return_none_while_not_a_dir_fails_closed() {
        let tmp = tempfile::tempdir().unwrap();
        let input = sample_input(&"4".repeat(64));
        let mut cache = OleanCache::new_default();

        // Missing root, missing `v2`, missing entry dir, and missing
        // `metadata.json` all treat `NotFound` as a clean cache miss.
        let disk_dir = tmp.path().join("disk-cache");
        cache.set_disk_dir(Some(disk_dir.clone()));
        assert!(cache.lookup_bytes(&input).unwrap().is_none());

        fs::create_dir_all(&disk_dir).unwrap();
        assert!(cache.lookup_bytes(&input).unwrap().is_none());

        let v2_dir = disk_dir.join("v2");
        fs::create_dir_all(&v2_dir).unwrap();
        assert!(cache.lookup_bytes(&input).unwrap().is_none());

        let entry_dir = v2_dir.join(input.cache_key());
        fs::create_dir_all(&entry_dir).unwrap();
        assert!(cache.lookup_bytes(&input).unwrap().is_none());

        // Directory in place of `metadata.json` fails closed.
        fs::create_dir_all(entry_dir.join(ENTRY_METADATA_FILE)).unwrap();
        let err = cache.lookup_bytes(&input).unwrap_err();
        assert_eq!(err.code, 2);
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("regular non-symlink file"), "{err}");

        // Regular file at `entry_dir` fails closed before inspecting
        // `metadata.json`.
        fs::remove_dir_all(&entry_dir).unwrap();
        fs::write(&entry_dir, b"not a dir").unwrap();
        let err = cache.lookup_bytes(&input).unwrap_err();
        assert_eq!(err.code, 2);
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("regular non-symlink directory"), "{err}");

        // Regular file at `v2` fails closed before probing `v2/<key>`.
        fs::remove_dir_all(&v2_dir).unwrap();
        fs::write(&v2_dir, b"not a dir").unwrap();
        let err = cache.lookup_bytes(&input).unwrap_err();
        assert_eq!(err.code, 2);
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("regular non-symlink directory"), "{err}");

        // Regular file ancestor of `disk_dir` (`ENOTDIR`) fails closed even as
        // root.
        let blocking_file = tmp.path().join("blocking-file");
        fs::write(&blocking_file, b"file").unwrap();
        cache.set_disk_dir(Some(blocking_file.join("olean-cache")));
        let err = cache.lookup_bytes(&input).unwrap_err();
        assert_eq!(err.code, 2);
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("cannot inspect"), "{err}");
    }

    #[test]
    fn prebuilt_missing_components_return_none_while_not_a_dir_fails_closed() {
        let tmp = tempfile::tempdir().unwrap();
        let input = sample_input(&"5".repeat(64));
        let mut cache = OleanCache::new_default();
        cache.set_disk_dir(None);

        // Missing `prebuilt_dir` and empty `prebuilt_dir` without
        // `manifest.json` both return `Ok(None)`.
        let prebuilt_dir = tmp.path().join("prebuilt");
        cache.set_prebuilt_dir(Some(prebuilt_dir.clone()));
        cache.preload_prebuilt().unwrap();
        assert!(cache.lookup_bytes(&input).unwrap().is_none());

        fs::create_dir_all(&prebuilt_dir).unwrap();
        cache.preload_prebuilt().unwrap();
        assert!(cache.lookup_bytes(&input).unwrap().is_none());

        // Directory in place of `manifest.json` fails closed.
        fs::create_dir_all(prebuilt_dir.join(PREBUILT_MANIFEST_FILE)).unwrap();
        let err = cache.preload_prebuilt().unwrap_err();
        assert_eq!(err.code, 2);
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("regular non-symlink file"), "{err}");
        let err = cache.lookup_bytes(&input).unwrap_err();
        assert_eq!(err.code, 2);
        assert_eq!(err.phase, "olean-cache");

        // Regular file at `prebuilt_dir` fails closed.
        fs::remove_dir_all(&prebuilt_dir).unwrap();
        fs::write(&prebuilt_dir, b"not a dir").unwrap();
        let err = cache.preload_prebuilt().unwrap_err();
        assert_eq!(err.code, 2);
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("regular non-symlink directory"), "{err}");

        // Regular file parent of `prebuilt_dir` (`ENOTDIR`) fails closed even
        // as root.
        let blocking_file = tmp.path().join("prebuilt-parent-file");
        fs::write(&blocking_file, b"file").unwrap();
        cache.set_prebuilt_dir(Some(blocking_file.join("prebuilt")));
        let err = cache.preload_prebuilt().unwrap_err();
        assert_eq!(err.code, 2);
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("cannot inspect"), "{err}");
        let err = cache.lookup_bytes(&input).unwrap_err();
        assert_eq!(err.code, 2);
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("cannot inspect"), "{err}");
    }

    #[cfg(unix)]
    #[test]
    fn unreadable_disk_and_prebuilt_cache_dirs_fail_closed() {
        // SAFETY: `geteuid` has no preconditions and always succeeds.
        if unsafe { libc::geteuid() } == 0 {
            return;
        }

        let tmp = tempfile::tempdir().unwrap();
        let disk_dir = tmp.path().join("disk-cache");
        let src_dir = tmp.path().join("src");
        fs::create_dir_all(&src_dir).unwrap();

        let olean_bytes = fake_olean();
        let olean_sha = sha256_bytes(&olean_bytes);
        let src_olean = src_dir.join("MirAst.olean");
        fs::write(&src_olean, &olean_bytes).unwrap();

        let input = sample_input(&"6".repeat(64));
        let other_input = sample_input(&"7".repeat(64));
        let mut cache = OleanCache::new_default();
        cache.set_disk_dir(Some(disk_dir.clone()));
        cache.store_compiled(&input, &[("olean", &src_olean, &olean_sha)]).unwrap();

        let v2_dir = disk_dir.join("v2");
        let entry_dir = v2_dir.join(input.cache_key());

        // Unreadable `entry_dir` causes `EACCES` on `metadata.json`.
        {
            let _guard = RestoreDirModeGuard::lock(&entry_dir);
            let err = cache.lookup_bytes(&input).unwrap_err();
            assert_eq!(err.code, 2);
            assert_eq!(err.phase, "olean-cache");
            assert!(err.message.contains("cannot inspect"), "{err}");
        }

        // Unreadable `v2_dir` causes `EACCES` on both lookup and store probes.
        {
            let _guard = RestoreDirModeGuard::lock(&v2_dir);
            let err = cache.lookup_bytes(&input).unwrap_err();
            assert_eq!(err.code, 2);
            assert_eq!(err.phase, "olean-cache");
            assert!(err.message.contains("cannot inspect"), "{err}");

            let err = cache
                .store_compiled(&other_input, &[("olean", &src_olean, &olean_sha)])
                .unwrap_err();
            assert_eq!(err.code, 2);
            assert_eq!(err.phase, "olean-cache");
            assert!(err.message.contains("cannot inspect"), "{err}");
        }

        // Unreadable existing `disk_dir` causes `EACCES` when probing `v2` on
        // both lookup and store.
        {
            let _guard = RestoreDirModeGuard::lock(&disk_dir);
            let err = cache.lookup_bytes(&input).unwrap_err();
            assert_eq!(err.code, 2);
            assert_eq!(err.phase, "olean-cache");
            assert!(err.message.contains("cannot inspect"), "{err}");

            let err = cache
                .store_compiled(&other_input, &[("olean", &src_olean, &olean_sha)])
                .unwrap_err();
            assert_eq!(err.code, 2);
            assert_eq!(err.phase, "olean-cache");
            assert!(err.message.contains("cannot inspect"), "{err}");
        }

        // Restored permissions return the cached entry cleanly.
        assert!(cache.lookup_bytes(&input).unwrap().is_some());

        // Unsearchable ambient parent of `disk_dir` falls back cleanly as a
        // best-effort unavailable cache on both lookup and store.
        let ambient_parent = tmp.path().join("ambient-parent");
        fs::create_dir_all(&ambient_parent).unwrap();
        {
            let _guard = RestoreDirModeGuard::lock(&ambient_parent);
            for candidate in [
                ambient_parent.join("olean-cache"),
                ambient_parent.join("anneal/olean-cache"),
            ] {
                cache.set_disk_dir(Some(candidate));
                assert!(cache.lookup_bytes(&input).unwrap().is_none());
                cache.store_compiled(&input, &[("olean", &src_olean, &olean_sha)]).unwrap();
            }
        }

        // Unreadable `prebuilt_dir` and unreadable parent of `prebuilt_dir`
        // fail closed.
        let prebuilt_parent = tmp.path().join("prebuilt-parent");
        let prebuilt_dir = prebuilt_parent.join("prebuilt");
        fs::create_dir_all(&prebuilt_dir).unwrap();
        cache.set_disk_dir(None);
        cache.set_prebuilt_dir(Some(prebuilt_dir.clone()));

        {
            let _guard = RestoreDirModeGuard::lock(&prebuilt_dir);
            let err = cache.preload_prebuilt().unwrap_err();
            assert_eq!(err.code, 2);
            assert_eq!(err.phase, "olean-cache");
            assert!(err.message.contains("cannot inspect"), "{err}");

            let err = cache.lookup_bytes(&input).unwrap_err();
            assert_eq!(err.code, 2);
            assert_eq!(err.phase, "olean-cache");
            assert!(err.message.contains("cannot inspect"), "{err}");
        }

        {
            let _guard = RestoreDirModeGuard::lock(&prebuilt_parent);
            let err = cache.preload_prebuilt().unwrap_err();
            assert_eq!(err.code, 2);
            assert_eq!(err.phase, "olean-cache");
            assert!(err.message.contains("cannot inspect"), "{err}");
        }
    }

    fn edge(module: &str, is_exported: bool, import_all: bool, is_meta: bool) -> ImportEdge {
        ImportEdge {
            module: module.to_owned(),
            is_exported,
            import_all,
            is_meta,
        }
    }

    fn arts(paths: &[PathBuf]) -> ModuleArtifacts {
        ModuleArtifacts {
            olean_parts: paths.iter().map(|p| p.to_string_lossy().into_owned()).collect(),
            ir_parts: Vec::new(),
        }
    }

    #[test]
    fn transitive_merkle_digest_detects_indirect_change_with_identical_barrel() {
        let tmp = tempfile::tempdir().unwrap();
        let dir = tmp.path();
        let disk_dir = dir.join("disk-cache");

        let init_path = dir.join("InitCore.olean");
        let leaf_path = dir.join("Leaf.olean");
        let barrel_path = dir.join("Barrel.olean");
        let downstream_path = dir.join("Downstream.olean");

        fs::write(&init_path, fake_olean()).unwrap();
        let mut leaf_v1 = fake_olean();
        leaf_v1.extend_from_slice(b"-leaf-rev-1");
        fs::write(&leaf_path, &leaf_v1).unwrap();
        fs::write(&barrel_path, fake_olean()).unwrap();
        let downstream_bytes = fake_olean();
        let downstream_sha = sha256_bytes(&downstream_bytes);
        fs::write(&downstream_path, &downstream_bytes).unwrap();

        let artifacts = BTreeMap::from([
            ("Init.Core".to_owned(), arts(std::slice::from_ref(&init_path))),
            ("Trusted.Leaf".to_owned(), arts(std::slice::from_ref(&leaf_path))),
            ("Trusted.Barrel".to_owned(), arts(std::slice::from_ref(&barrel_path))),
        ]);
        let graph = BTreeMap::from([
            ("Init.Core".to_owned(), Vec::new()),
            ("Trusted.Leaf".to_owned(), vec![edge("Init.Core", true, false, false)]),
            ("Trusted.Barrel".to_owned(), vec![edge("Trusted.Leaf", true, false, false)]),
        ]);
        let downstream_edges = [edge("Trusted.Barrel", true, false, false)];

        let bindings_v1 = build_import_bindings(
            &downstream_edges,
            &artifacts,
            &graph,
            &mut BTreeMap::new(),
            &mut BTreeMap::new(),
        )
        .unwrap();
        let key_v1 = OleanCacheKeyInput {
            kind: CacheKind::Module,
            module: "Anneal.Downstream".to_owned(),
            lean_sha256: "a".repeat(64),
            sysroot_manifest_sha256: "b".repeat(64),
            source_sha256: "1".repeat(64),
            is_module: false,
            flags: canonical_compile_flags(false),
            imports: bindings_v1.clone(),
        };

        let mut cache = OleanCache::new_default();
        cache.set_disk_dir(Some(disk_dir.clone()));
        cache.store_compiled(&key_v1, &[("olean", &downstream_path, &downstream_sha)]).unwrap();
        assert!(cache.lookup_bytes(&key_v1).unwrap().is_some());

        // Mutate `Trusted.Leaf` while leaving `Trusted.Barrel.olean` and
        // `Anneal.Downstream.lean` completely byte-for-byte identical.
        let mut leaf_v2 = fake_olean();
        leaf_v2.extend_from_slice(b"-leaf-rev-2");
        fs::write(&leaf_path, &leaf_v2).unwrap();

        let bindings_v2 = build_import_bindings(
            &downstream_edges,
            &artifacts,
            &graph,
            &mut BTreeMap::new(),
            &mut BTreeMap::new(),
        )
        .unwrap();
        assert_eq!(bindings_v1[0].part_sha256s, bindings_v2[0].part_sha256s);
        assert_ne!(bindings_v1[0].transitive_sha256, bindings_v2[0].transitive_sha256);

        let key_v2 = OleanCacheKeyInput { imports: bindings_v2, ..key_v1.clone() };
        assert_ne!(key_v1.cache_key(), key_v2.cache_key());
        assert!(cache.lookup_bytes(&key_v2).unwrap().is_none());

        // Pre-existing `v1` disk cache directories must never be reused under
        // `v2`.
        let legacy_v1_dir = disk_dir.join("v1").join(key_v2.cache_key());
        fs::create_dir_all(&legacy_v1_dir).unwrap();
        let src_v2_dir = disk_dir.join("v2").join(key_v1.cache_key());
        fs::copy(src_v2_dir.join("module.olean"), legacy_v1_dir.join("module.olean")).unwrap();
        fs::copy(src_v2_dir.join(ENTRY_METADATA_FILE), legacy_v1_dir.join(ENTRY_METADATA_FILE))
            .unwrap();
        assert!(cache.lookup_bytes(&key_v2).unwrap().is_none());
    }

    #[test]
    fn transitive_merkle_rejects_cycles_missing_graph_and_skips_v1_manifests() {
        let tmp = tempfile::tempdir().unwrap();
        let olean_a = tmp.path().join("A.olean");
        let olean_b = tmp.path().join("B.olean");
        fs::write(&olean_a, fake_olean()).unwrap();
        fs::write(&olean_b, fake_olean()).unwrap();

        let artifacts = BTreeMap::from([
            ("Mod.A".to_owned(), arts(std::slice::from_ref(&olean_a))),
            ("Mod.B".to_owned(), arts(std::slice::from_ref(&olean_b))),
        ]);
        let cyclic_graph = BTreeMap::from([
            ("Mod.A".to_owned(), vec![edge("Mod.B", true, false, false)]),
            ("Mod.B".to_owned(), vec![edge("Mod.A", true, false, false)]),
        ]);
        let err = compute_transitive_module_sha256(
            "Mod.A",
            &artifacts,
            &cyclic_graph,
            &mut BTreeMap::new(),
            &mut BTreeMap::new(),
        )
        .unwrap_err();
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("import cycle detected"), "{err}");

        let incomplete_graph = BTreeMap::from([
            ("Mod.A".to_owned(), vec![edge("Mod.B", true, false, false)]),
        ]);
        let err = compute_transitive_module_sha256(
            "Mod.A",
            &artifacts,
            &incomplete_graph,
            &mut BTreeMap::new(),
            &mut BTreeMap::new(),
        )
        .unwrap_err();
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("missing import graph entry for Mod.B"), "{err}");

        // Treat stale `schema_version: 1` prebuilt manifests (including entries
        // written without `transitive_sha256`) as a clean cache miss (`None`)
        // while keeping malformed JSON and unknown fields fail-closed.
        let prebuilt = tmp.path().join("prebuilt");
        fs::create_dir_all(&prebuilt).unwrap();
        let v1_input = sample_input(&"1".repeat(64));
        let v1_manifest = serde_json::json!({
            "schema_version": 1,
            "entries": [{
                "kind": "module",
                "module": v1_input.module,
                "lean_sha256": v1_input.lean_sha256,
                "sysroot_manifest_sha256": v1_input.sysroot_manifest_sha256,
                "source_sha256": v1_input.source_sha256,
                "is_module": v1_input.is_module,
                "flags": v1_input.flags,
                "imports": [{
                    "module": v1_input.imports[0].module,
                    "is_exported": v1_input.imports[0].is_exported,
                    "import_all": v1_input.imports[0].import_all,
                    "is_meta": v1_input.imports[0].is_meta,
                    "part_sha256s": v1_input.imports[0].part_sha256s,
                }],
                "parts": [{
                    "suffix": "olean",
                    "path": "lib/Trusted/MirAst.olean",
                    "sha256": "0".repeat(64),
                }],
            }],
        });
        fs::write(
            prebuilt.join(PREBUILT_MANIFEST_FILE),
            serde_json::to_vec(&v1_manifest).unwrap(),
        )
        .unwrap();
        let mut cache = OleanCache::new_default();
        cache.set_disk_dir(None);
        cache.set_prebuilt_dir(Some(prebuilt.clone()));
        assert!(cache.load_prebuilt().unwrap().is_none());
        cache.preload_prebuilt().unwrap();
        assert!(cache.lookup_bytes(&v1_input).unwrap().is_none());

        cache.set_no_rebuild_bundled(true);
        let err = cache.lookup_bytes(&v1_input).unwrap_err();
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("--no-rebuild-bundled"), "{err}");
        assert!(err.message.contains("schema_version 1 != 2"), "{err}");

        // Unknown top-level fields on `v1`, malformed JSON, and `v2` entries
        // omitting `transitive_sha256` must still fail closed.
        for bad_manifest in [
            br#"{"schema_version":1,"entries":[],"bogus":1}"#.as_slice(),
            br#"{not json"#.as_slice(),
            br#"{"schema_version":2,"entries":[{"kind":"module","module":"M","lean_sha256":"a","sysroot_manifest_sha256":"b","source_sha256":"c","is_module":false,"flags":[],"imports":[{"module":"I","is_exported":true,"import_all":false,"is_meta":false,"part_sha256s":[]}],"parts":[]}]}"#.as_slice(),
        ] {
            fs::write(prebuilt.join(PREBUILT_MANIFEST_FILE), bad_manifest).unwrap();
            cache.set_prebuilt_dir(None);
            cache.set_prebuilt_dir(Some(prebuilt.clone()));
            let err = cache.preload_prebuilt().unwrap_err();
            assert_eq!(err.phase, "olean-cache");
            assert!(err.message.contains("invalid prebuilt olean manifest"), "{err}");
        }
    }

    #[test]
    fn transitive_merkle_and_cache_key_match_python_golden_vectors() {
        // Cross-language parity fixture matched byte-for-byte in
        // `test_prebuild_bundled_oleans.py`.
        let artifacts = BTreeMap::from([
            ("Init.Core".to_owned(), arts(&[PathBuf::from("init-core.olean")])),
            (
                "Trusted.Leaf".to_owned(),
                arts(&[PathBuf::from("leaf.olean"), PathBuf::from("leaf.olean.server")]),
            ),
            ("Trusted.Barrel".to_owned(), arts(&[PathBuf::from("barrel.olean")])),
        ]);
        let mut path_sha_cache = BTreeMap::from([
            ("init-core.olean".to_owned(), "11".repeat(32)),
            ("leaf.olean".to_owned(), "22".repeat(32)),
            ("leaf.olean.server".to_owned(), "33".repeat(32)),
            ("barrel.olean".to_owned(), "44".repeat(32)),
        ]);
        let e_leaf = edge("Trusted.Leaf", true, false, false);
        let e_core = edge("Init.Core", false, false, true);
        let graph = BTreeMap::from([
            ("Init.Core".to_owned(), Vec::new()),
            ("Trusted.Leaf".to_owned(), vec![edge("Init.Core", true, false, false)]),
            ("Trusted.Barrel".to_owned(), vec![e_leaf.clone(), e_core.clone()]),
        ]);
        let bindings = build_import_bindings(
            &[edge("Trusted.Barrel", true, false, false)],
            &artifacts,
            &graph,
            &mut path_sha_cache,
            &mut BTreeMap::new(),
        )
        .unwrap();
        assert_eq!(
            bindings[0].transitive_sha256,
            "a242a0e936fc66db2f2520751fc3ad4e9b29e255d7ea9fbf3d73e49f72bec6bf"
        );

        let graph_reordered = BTreeMap::from([
            ("Init.Core".to_owned(), Vec::new()),
            ("Trusted.Leaf".to_owned(), vec![edge("Init.Core", true, false, false)]),
            ("Trusted.Barrel".to_owned(), vec![e_core, e_leaf]),
        ]);
        let reordered_digest = compute_transitive_module_sha256(
            "Trusted.Barrel",
            &artifacts,
            &graph_reordered,
            &mut path_sha_cache,
            &mut BTreeMap::new(),
        )
        .unwrap();
        assert_eq!(reordered_digest, bindings[0].transitive_sha256);

        let key_input = OleanCacheKeyInput {
            kind: CacheKind::Module,
            module: "Anneal.Downstream".to_owned(),
            lean_sha256: "AA".repeat(32),
            sysroot_manifest_sha256: "BB".repeat(32),
            source_sha256: "CC".repeat(32),
            is_module: false,
            flags: canonical_compile_flags(false),
            imports: bindings,
        };
        assert_eq!(
            key_input.cache_key(),
            "c3a4decebcd8ececefe5514fad6d3b409e7f8da2da1496de5310d612a7b89e09"
        );
    }

    #[test]
    fn target_shard_cache_policy_allows_shards_while_no_rebuild_bundled_stays_strict() {
        assert!(is_cacheable_bundled_module("Trusted"));
        assert!(is_cacheable_bundled_module("Anneal.SccSharding"));
        assert!(!is_cacheable_bundled_module("Proof.IdTree"));
        assert!(!is_cacheable_bundled_module("Captured.Shard_000"));
        assert!(!is_cacheable_bundled_module("Proof.Shard_000"));

        assert!(is_cacheable_target_shard_module("Proof.IdTree"));
        assert!(is_cacheable_target_shard_module("Captured.Shard_000"));
        assert!(is_cacheable_target_shard_module("Proof.Shard_000"));
        assert!(!is_cacheable_target_shard_module("Proof"));
        assert!(!is_cacheable_target_shard_module("Captured"));
        assert!(!is_cacheable_target_shard_module("Spec"));
        assert!(!is_cacheable_target_shard_module("Trusted.MirAst"));

        let tmp = tempfile::tempdir().unwrap();
        let disk_dir = tmp.path().join("disk-cache");
        let stage_dir = tmp.path().join("stage");
        let src_dir = tmp.path().join("src");
        fs::create_dir_all(&stage_dir).unwrap();
        fs::create_dir_all(&src_dir).unwrap();

        let mut cache = OleanCache::new_default();
        cache.set_disk_dir(Some(disk_dir));
        cache.set_no_rebuild_bundled(true);

        // Target shards and `Proof.IdTree` miss cleanly under
        // `--no-rebuild-bundled` so they can compile on demand, whereas
        // uncached bundled modules continue to fail closed.
        for module in ["Proof.IdTree", "Captured.Shard_000", "Proof.Shard_000"] {
            let mut input = sample_input(&"a".repeat(64));
            input.kind = CacheKind::Module;
            input.module = module.to_owned();
            assert!(cache.lookup_and_materialize(&input, &stage_dir, "Shard").unwrap().is_none());
        }
        let mut bundled = sample_input(&"b".repeat(64));
        bundled.module = "Anneal.SccSharding".to_owned();
        let err = cache.lookup_and_materialize(&bundled, &stage_dir, "Anneal/SccSharding").unwrap_err();
        assert_eq!(err.code, 2);
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("--no-rebuild-bundled"), "{err}");

        // `--no-rebuild-bundled` must also fail closed on inspector misses.
        let mut inspector = sample_input(&"d".repeat(64));
        inspector.kind = CacheKind::Inspector;
        inspector.module = "TrustedBoundary".to_owned();
        let err = cache.lookup_bytes(&inspector).unwrap_err();
        assert_eq!(err.code, 2);
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("--no-rebuild-bundled"), "{err}");

        // Round-tripping a target shard hits cleanly on repeat lookup.
        let olean_bytes = fake_olean();
        let olean_sha = sha256_bytes(&olean_bytes);
        let src_olean = src_dir.join("Shard_000.olean");
        fs::write(&src_olean, &olean_bytes).unwrap();
        let mut shard_input = sample_input(&"c".repeat(64));
        shard_input.kind = CacheKind::Module;
        shard_input.module = "Proof.Shard_000".to_owned();
        cache.store_compiled(&shard_input, &[("olean", &src_olean, &olean_sha)]).unwrap();
        let hit = cache
            .lookup_and_materialize(&shard_input, &stage_dir, "Proof/Shard_000")
            .unwrap()
            .expect("target shard cache hit expected");
        assert_eq!(fs::read(&hit.materialized_parts[0].1).unwrap(), olean_bytes);
    }
}
