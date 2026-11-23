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
//! Only the static inspector (`TrustedBoundary.lean`) and static bundled
//! `Trusted.*` / `Anneal.*` runtime modules are cached. Every cached `.olean`
//! must match the exact `lean` executable digest, sysroot `.olean*` manifest
//! digest, module source digest, compiler flags, and direct import artifact
//! digests, and is still copied into the private stage, checked against
//! `olean_ledger`, and replayed by `target-audit` (`0` new TCB assumptions).

#[cfg(unix)]
use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};
use std::{
    collections::BTreeMap,
    ffi::OsStr,
    fs::{self, OpenOptions},
    io::{self, Write as _},
    path::{Component, Path, PathBuf},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    Failure, ImportEdge, ModuleArtifacts, is_clean_relative_path, is_sha256_hex, sha256_bytes,
    toolchain::cache_dir_for_platform,
};
use crate::sandbox::{MAX_OLEAN_BYTES, OLEAN_V2_MAGIC, copy_readonly_file, create_dir_mode, set_mode};

const CACHE_FORMAT_VERSION: u32 = 1;
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

/// Binds a direct module `import` edge to the exact SHA-256 digests of the
/// imported module's `.olean*` artifacts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct CacheImportBinding {
    pub module: String,
    pub is_exported: bool,
    pub import_all: bool,
    pub is_meta: bool,
    pub part_sha256s: Vec<String>,
}

/// Complete deterministic cache-key input for an inspector or bundled module.
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
    /// Merkle-DAG cache key (`v1`).
    pub(crate) fn cache_key(&self) -> String {
        let mut h = Sha256::new();
        h.update(b"anneal-olean-cache-v1\0");
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
}

impl OleanCache {
    pub(crate) fn with_env_vars(home: Option<&OsStr>, xdg_cache_home: Option<&OsStr>) -> Self {
        Self {
            enabled: true,
            no_rebuild_bundled: false,
            prebuilt_dir: None,
            disk_dir: cache_dir_from_env_vars(home, xdg_cache_home),
            prebuilt_entries: None,
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
        let manifest: PrebuiltManifest = serde_json::from_slice(&bytes).map_err(|e| {
            Failure::operational(
                "olean-cache",
                format!("invalid prebuilt olean manifest {}: {e}", manifest_path.display()),
            )
        })?;
        if manifest.schema_version != CACHE_FORMAT_VERSION {
            return Err(Failure::operational(
                "olean-cache",
                format!("unsupported prebuilt manifest schema_version {}", manifest.schema_version),
            ));
        }
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

        if self.no_rebuild_bundled {
            return Err(Failure::operational(
                "olean-cache",
                format!(
                    "missing prebuilt or cached .olean for {} (--no-rebuild-bundled)",
                    input.module
                ),
            ));
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
        let v1_dir = disk_dir.join("v1");
        if !probe_existing_non_symlink_dir(&v1_dir, true)? {
            create_dir_mode(&v1_dir, 0o700)?;
        }
        let key = input.cache_key();
        let entry_dir = v1_dir.join(&key);
        if probe_existing_non_symlink_dir(&entry_dir, true)? {
            return Ok(());
        }

        let tmp = tempfile::Builder::new()
            .prefix(".tmp-")
            .tempdir_in(&v1_dir)
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

        let lock_path = v1_dir.join(format!("{key}.lock"));
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
    let lower = err.message.to_ascii_lowercase();
    lower.contains("permission denied")
        || lower.contains("read-only file system")
        || lower.contains("operation not permitted")
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
            return Err(Failure::operational(
                "olean-cache",
                format!("cannot inspect {}: {e}", disk_dir.display()),
            ));
        }
    };
    verify_non_symlink_dir_meta(disk_dir, &disk_meta, "olean-cache", true)?;
    let v1_dir = disk_dir.join("v1");
    if !probe_existing_non_symlink_dir(&v1_dir, true)? {
        return Ok(None);
    }
    let key = input.cache_key();
    let entry_dir = v1_dir.join(&key);
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
        let bytes = read_regular_nofollow_capped(&src_path, MAX_OLEAN_BYTES, "olean-cache")?;
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
        if part.suffix == "olean"
            && (bytes.len() < OLEAN_V2_MAGIC.len() || !bytes.starts_with(OLEAN_V2_MAGIC))
        {
            return Err(Failure::operational(
                "olean-cache",
                format!("cached artifact {} has invalid v2 .olean header", src_path.display()),
            ));
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
            create_dir_mode(parent, 0o700)?;
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
                    create_dir_mode(&cur, 0o700)?;
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
    match fs::symlink_metadata(path) {
        Ok(meta) => Ok(Some(meta)),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(Failure::operational(
            "olean-cache",
            format!("cannot inspect {}: {e}", path.display()),
        )),
    }
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
        .map_err(|e| Failure::operational(phase, format!("cannot inspect {}: {e}", dir.display())))?;
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
    let mut opts = OpenOptions::new();
    opts.read(true);
    #[cfg(unix)]
    opts.custom_flags(libc::O_NOFOLLOW);
    let mut file = opts
        .open(path)
        .map_err(|e| Failure::operational(phase, format!("cannot open {}: {e}", path.display())))?;
    let meta = file
        .metadata()
        .map_err(|e| Failure::operational(phase, format!("cannot stat {}: {e}", path.display())))?;
    if !meta.is_file() || meta.len() > max_bytes {
        return Err(Failure::operational(
            phase,
            format!("invalid regular cache file or size limit exceeded: {}", path.display()),
        ));
    }
    let mut buf = Vec::with_capacity(meta.len() as usize);
    io::Read::read_to_end(&mut file, &mut buf)
        .map_err(|e| Failure::operational(phase, format!("cannot read {}: {e}", path.display())))?;
    Ok(buf)
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

/// Build canonical sorted direct import bindings for `edge_list` using the
/// already-admitted `ModuleArtifacts` and any memoized path SHA-256 digests.
pub(crate) fn build_import_bindings(
    edge_list: &[ImportEdge],
    artifacts: &BTreeMap<String, ModuleArtifacts>,
    path_sha_cache: &mut BTreeMap<String, String>,
) -> Result<Vec<CacheImportBinding>, Failure> {
    let mut bindings = Vec::with_capacity(edge_list.len());
    for edge in edge_list {
        let mod_arts = artifacts.get(&edge.module).ok_or_else(|| {
            Failure::operational("olean-cache", format!("missing artifact for import {}", edge.module))
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
        bindings.push(CacheImportBinding {
            module: edge.module.clone(),
            is_exported: edge.is_exported,
            import_all: edge.import_all,
            is_meta: edge.is_meta,
            part_sha256s: shas,
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
            }],
        }
    }

    fn fake_olean() -> Vec<u8> {
        let mut data = OLEAN_V2_MAGIC.to_vec();
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
        let key_dir = disk_dir.join("v1").join(input.cache_key());
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

        // Missing root, missing `v1`, missing entry dir, and missing
        // `metadata.json` all treat `NotFound` as a clean cache miss.
        let disk_dir = tmp.path().join("disk-cache");
        cache.set_disk_dir(Some(disk_dir.clone()));
        assert!(cache.lookup_bytes(&input).unwrap().is_none());

        fs::create_dir_all(&disk_dir).unwrap();
        assert!(cache.lookup_bytes(&input).unwrap().is_none());

        let v1_dir = disk_dir.join("v1");
        fs::create_dir_all(&v1_dir).unwrap();
        assert!(cache.lookup_bytes(&input).unwrap().is_none());

        let entry_dir = v1_dir.join(input.cache_key());
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

        // Regular file at `v1` fails closed before probing `v1/<key>`.
        fs::remove_dir_all(&v1_dir).unwrap();
        fs::write(&v1_dir, b"not a dir").unwrap();
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

        let v1_dir = disk_dir.join("v1");
        let entry_dir = v1_dir.join(input.cache_key());

        // Unreadable `entry_dir` causes `EACCES` on `metadata.json`.
        {
            let _guard = RestoreDirModeGuard::lock(&entry_dir);
            let err = cache.lookup_bytes(&input).unwrap_err();
            assert_eq!(err.code, 2);
            assert_eq!(err.phase, "olean-cache");
            assert!(err.message.contains("cannot inspect"), "{err}");
        }

        // Unreadable `v1_dir` causes `EACCES` on both lookup and store probes.
        {
            let _guard = RestoreDirModeGuard::lock(&v1_dir);
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

        // Unreadable existing `disk_dir` causes `EACCES` when probing `v1` on
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
}
