// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Content-addressed incremental claim cache (`anneal-claim-cache-v1`).
//!
//! Stores independently re-validatable `"target-audit"` evidence payloads
//! keyed by a domain-separated SHA-256 digest of every normalized semantic,
//! proof, model, toolchain, sysroot, and host-policy input. Any tamper,
//! symlink, owner mismatch, digest drift, or schema mismatch fails closed.

use std::{
    ffi::OsStr,
    fs,
    path::{Component, Path, PathBuf},
    time::SystemTime,
};

use serde::{Deserialize, Serialize};
use serde_json::{self, Value as Json};
use sha2::{Digest, Sha256};

use crate::{
    Failure,
    olean_cache::{
        acquire_exclusive_flock_with_phase, cache_dir_with_leaf_from_env_vars,
        ensure_private_cache_root_with_phase, feed_len_str, is_unwritable_cache_init_err,
        probe_existing_non_symlink_dir_with_phase, probe_existing_regular_file_with_phase,
        publish_staged_cache_entry_dir_with_ready, read_regular_nofollow_capped,
        validate_existing_cache_ancestors,
    },
    sandbox::{create_dir_mode, set_mode},
};

const CLAIM_CACHE_FORMAT_VERSION: u32 = 1;
const CLAIM_CACHE_KEY_DOMAIN: &[u8] = b"anneal-claim-cache-v1\0";
const CLAIM_CACHE_PHASE: &str = "claim-cache";
const EVIDENCE_FILE_NAME: &str = "evidence.json";
const MAX_CLAIM_EVIDENCE_BYTES: u64 = crate::sandbox::MAX_INSPECTOR_RESULT_BYTES + 4 * 1024 * 1024;
const MAX_CLAIM_CACHE_TOTAL_BYTES: u64 = 512 * 1024 * 1024;

/// Version tag binding the verification replay/policy posture in
/// [`ClaimEvidenceKeyInput`].
pub(crate) const REPLAY_POSTURE_TAG: &str = "trusted_boundary_replay_exact_type_v1";

/// Canonical target module record committed into [`ClaimEvidenceKeyInput`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ClaimModuleDigest {
    pub module: String,
    pub role: String,
    pub sha256: String,
}

/// Domain-separated key input governing when cached `"target-audit"` evidence
/// applies to a live verification request.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ClaimEvidenceKeyInput {
    pub canonical_scope: String,
    pub modules: Vec<ClaimModuleDigest>,
    pub theorem_module: String,
    pub theorem_name: String,
    pub expected_module: String,
    pub expected_declaration: String,
    pub canonical_root: String,
    pub subject_declaration: String,
    pub specification_declaration: String,
    pub model_manifest_sha256: String,
    pub specification_manifest_sha256: String,
    pub correspondence_provenance_sha256: String,
    pub foundation_lock_sha256: String,
    pub library_lock_sha256: String,
    pub inspector_source_sha256: String,
    pub lean_binary_sha256: String,
    pub lean_version: String,
    pub sysroot_manifest_sha256: String,
    pub runtime_libs_verified: bool,
    pub active_sandbox: String,
    pub allow_unpinned_lean: bool,
    pub allow_sorry_in_proof: bool,
    pub replay_posture: String,
}

impl ClaimEvidenceKeyInput {
    /// Compute the deterministic lowercase hex SHA-256 key with
    /// length-prefixed framing over every input field.
    pub(crate) fn cache_key(&self) -> String {
        let mut h = Sha256::new();
        h.update(CLAIM_CACHE_KEY_DOMAIN);
        feed_len_str(&mut h, &self.canonical_scope);
        h.update((self.modules.len() as u64).to_le_bytes());
        for m in &self.modules {
            feed_len_str(&mut h, &m.module);
            feed_len_str(&mut h, &m.role);
            feed_len_str(&mut h, &m.sha256);
        }
        feed_len_str(&mut h, &self.theorem_module);
        feed_len_str(&mut h, &self.theorem_name);
        feed_len_str(&mut h, &self.expected_module);
        feed_len_str(&mut h, &self.expected_declaration);
        feed_len_str(&mut h, &self.canonical_root);
        feed_len_str(&mut h, &self.subject_declaration);
        feed_len_str(&mut h, &self.specification_declaration);
        feed_len_str(&mut h, &self.model_manifest_sha256);
        feed_len_str(&mut h, &self.specification_manifest_sha256);
        feed_len_str(&mut h, &self.correspondence_provenance_sha256);
        feed_len_str(&mut h, &self.foundation_lock_sha256);
        feed_len_str(&mut h, &self.library_lock_sha256);
        feed_len_str(&mut h, &self.inspector_source_sha256);
        feed_len_str(&mut h, &self.lean_binary_sha256);
        feed_len_str(&mut h, &self.lean_version);
        feed_len_str(&mut h, &self.sysroot_manifest_sha256);
        h.update([u8::from(self.runtime_libs_verified)]);
        feed_len_str(&mut h, &self.active_sandbox);
        h.update([u8::from(self.allow_unpinned_lean)]);
        h.update([u8::from(self.allow_sorry_in_proof)]);
        feed_len_str(&mut h, &self.replay_posture);
        format!("{:x}", h.finalize())
    }
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct CachedClaimEvidence {
    schema_version: u32,
    cache_key: String,
    input: ClaimEvidenceKeyInput,
    audit: Json,
}

/// Derive a disk claim cache directory (`<cache>/anneal/claim-cache`) from
/// explicit `HOME` and optional `XDG_CACHE_HOME` values.
///
/// On non-macOS platforms, an explicit absolute `XDG_CACHE_HOME` is honored
/// even when `HOME` is unset (such as inside `env_clear()` sandboxes).
pub(crate) fn claim_cache_dir_from_env_vars(
    home: Option<&OsStr>,
    xdg_cache_home: Option<&OsStr>,
) -> Option<PathBuf> {
    if !cfg!(target_os = "macos")
        && let Some(xdg) = xdg_cache_home.filter(|v| !v.is_empty()).map(PathBuf::from)
        && xdg.is_absolute()
    {
        return Some(strip_cur_dir_components(&xdg.join("anneal").join("claim-cache")));
    }
    cache_dir_with_leaf_from_env_vars(home, xdg_cache_home, "claim-cache")
        .map(|p| strip_cur_dir_components(&p))
}

/// Strip harmless `CurDir` (`.`) segments while preserving `ParentDir` (`..`)
/// so `validate_existing_cache_ancestors` still rejects `..` traversal.
pub(crate) fn strip_cur_dir_components(path: &Path) -> PathBuf {
    let mut cleaned = PathBuf::new();
    for comp in path.components() {
        if comp != Component::CurDir {
            cleaned.push(comp.as_os_str());
        }
    }
    cleaned
}

/// Persistent disk cache storing key-bound `"target-audit"` receipts under
/// `$XDG_CACHE_HOME/anneal/claim-cache/v1/<key>/evidence.json` or a supplied
/// `--claim-cache-dir`.
#[derive(Clone, Debug)]
pub(crate) struct ClaimCache {
    disk_dir: Option<PathBuf>,
    explicit_dir: bool,
}

impl ClaimCache {
    /// Construct a [`ClaimCache`] from host policy flags.
    pub(crate) fn from_policy(
        explicit_dir: Option<PathBuf>,
        disabled: bool,
    ) -> Result<Self, Failure> {
        if disabled {
            return Ok(Self { disk_dir: None, explicit_dir: false });
        }
        if let Some(dir) = explicit_dir {
            return Ok(Self { disk_dir: Some(dir), explicit_dir: true });
        }
        let home = std::env::var_os("HOME");
        let xdg = std::env::var_os("XDG_CACHE_HOME");
        let disk_dir = claim_cache_dir_from_env_vars(home.as_deref(), xdg.as_deref());
        Ok(Self { disk_dir, explicit_dir: false })
    }

    /// Look up cached `"target-audit"` JSON for `key_input`, returning
    /// `Ok(None)` on a clean miss and failing closed on symlinks, foreign
    /// UIDs, corrupt JSON, size overruns, or key/input mismatches.
    pub(crate) fn lookup(
        &self,
        key_input: &ClaimEvidenceKeyInput,
    ) -> Result<Option<Json>, Failure> {
        self.lookup_with_cap(key_input, MAX_CLAIM_EVIDENCE_BYTES)
    }

    fn lookup_with_cap(
        &self,
        key_input: &ClaimEvidenceKeyInput,
        max_entry_bytes: u64,
    ) -> Result<Option<Json>, Failure> {
        let Some(ref disk_dir) = self.disk_dir else {
            return Ok(None);
        };
        match validate_existing_cache_ancestors(disk_dir, CLAIM_CACHE_PHASE) {
            Ok(true) => {}
            Ok(false) => return Ok(None),
            Err(err) if !self.explicit_dir && is_unwritable_cache_init_err(&err) => {
                return Ok(None);
            }
            Err(err) => return Err(err),
        }
        let v1_dir = disk_dir.join("v1");
        if !probe_existing_non_symlink_dir_with_phase(&v1_dir, CLAIM_CACHE_PHASE, true)? {
            return Ok(None);
        }
        let key = key_input.cache_key();
        let entry_dir = v1_dir.join(&key);
        if !probe_existing_non_symlink_dir_with_phase(&entry_dir, CLAIM_CACHE_PHASE, true)? {
            return Ok(None);
        }
        let lock_path = v1_dir.join(format!("{key}.lock"));
        let _lock = match acquire_exclusive_flock_with_phase(&lock_path, CLAIM_CACHE_PHASE) {
            Ok(guard) => guard,
            Err(err) if !self.explicit_dir && is_unwritable_cache_init_err(&err) => {
                return Ok(None);
            }
            Err(err) => return Err(err),
        };
        if !probe_existing_non_symlink_dir_with_phase(&entry_dir, CLAIM_CACHE_PHASE, true)? {
            return Ok(None);
        }
        let evidence_path = entry_dir.join(EVIDENCE_FILE_NAME);
        if !probe_existing_regular_file_with_phase(&evidence_path, CLAIM_CACHE_PHASE, true)? {
            return Ok(None);
        }
        let bytes =
            read_regular_nofollow_capped(&evidence_path, max_entry_bytes, CLAIM_CACHE_PHASE)?;
        let record: CachedClaimEvidence = serde_json::from_slice(&bytes).map_err(|e| {
            Failure::operational(
                CLAIM_CACHE_PHASE,
                format!("corrupt claim cache entry {}: {e}", evidence_path.display()),
            )
        })?;
        if record.schema_version != CLAIM_CACHE_FORMAT_VERSION
            || record.cache_key != key
            || record.input != *key_input
        {
            return Err(Failure::operational(
                CLAIM_CACHE_PHASE,
                format!("claim cache key or input mismatch in {}", evidence_path.display()),
            ));
        }
        Ok(Some(record.audit))
    }

    /// Atomically persist verified `"target-audit"` JSON under
    /// `v1/<key>/evidence.json` (`0o444` file, `0o700` dirs, `flock` lock).
    pub(crate) fn store(
        &self,
        key_input: &ClaimEvidenceKeyInput,
        audit: &Json,
    ) -> Result<(), Failure> {
        self.store_with_caps(
            key_input,
            audit,
            MAX_CLAIM_EVIDENCE_BYTES,
            MAX_CLAIM_CACHE_TOTAL_BYTES,
        )
    }

    fn store_with_caps(
        &self,
        key_input: &ClaimEvidenceKeyInput,
        audit: &Json,
        max_entry_bytes: u64,
        max_total_bytes: u64,
    ) -> Result<(), Failure> {
        let Some(ref disk_dir) = self.disk_dir else {
            return Ok(());
        };
        if let Err(err) = ensure_private_cache_root_with_phase(disk_dir, CLAIM_CACHE_PHASE) {
            if !self.explicit_dir && is_unwritable_cache_init_err(&err) {
                return Ok(());
            }
            return Err(err);
        }
        let v1_dir = disk_dir.join("v1");
        if !probe_existing_non_symlink_dir_with_phase(&v1_dir, CLAIM_CACHE_PHASE, true)? {
            create_dir_mode(&v1_dir, 0o700)?;
        }
        let key = key_input.cache_key();
        let entry_dir = v1_dir.join(&key);
        if probe_existing_non_symlink_dir_with_phase(&entry_dir, CLAIM_CACHE_PHASE, true)?
            && probe_existing_regular_file_with_phase(
                &entry_dir.join(EVIDENCE_FILE_NAME),
                CLAIM_CACHE_PHASE,
                true,
            )?
        {
            return Ok(());
        }

        let record = CachedClaimEvidence {
            schema_version: CLAIM_CACHE_FORMAT_VERSION,
            cache_key: key.clone(),
            input: key_input.clone(),
            audit: audit.clone(),
        };
        let bytes = serde_json::to_vec(&record)
            .map_err(|e| Failure::operational(CLAIM_CACHE_PHASE, e.to_string()))?;
        let entry_len = bytes.len() as u64;
        if entry_len > max_entry_bytes || entry_len > max_total_bytes {
            // Skip persisting entries larger than the lookup or cache budget
            // so a passing proof never self-poisons later runs.
            return Ok(());
        }

        let tmp = tempfile::Builder::new().prefix(".tmp-").tempdir_in(&v1_dir).map_err(|e| {
            Failure::operational(
                CLAIM_CACHE_PHASE,
                format!("cannot stage claim cache temp dir: {e}"),
            )
        })?;
        #[cfg(unix)]
        set_mode(tmp.path(), 0o700)?;

        let evidence_tmp = tmp.path().join(EVIDENCE_FILE_NAME);
        fs::write(&evidence_tmp, bytes)
            .map_err(|e| Failure::operational(CLAIM_CACHE_PHASE, e.to_string()))?;
        set_mode(&evidence_tmp, 0o444)?;

        publish_staged_cache_entry_dir_with_ready(
            &v1_dir,
            &key,
            tmp,
            CLAIM_CACHE_PHASE,
            Some(EVIDENCE_FILE_NAME),
        )?;
        enforce_claim_cache_budget(&v1_dir, &key, max_total_bytes);
        Ok(())
    }
}

fn is_claim_cache_entry_name(name: &str) -> bool {
    name.len() == 64 && name.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
}

fn enforce_claim_cache_budget(v1_dir: &Path, preserve_key: &str, max_total_bytes: u64) {
    let Ok(read_dir) = fs::read_dir(v1_dir) else {
        return;
    };
    let mut entries: Vec<(SystemTime, String, u64, PathBuf)> = Vec::new();
    let mut total_bytes: u64 = 0;
    for entry in read_dir.flatten() {
        let name_os = entry.file_name();
        let Some(name) = name_os.to_str() else {
            continue;
        };
        if !is_claim_cache_entry_name(name) {
            continue;
        }
        let dir_path = entry.path();
        let Ok(dir_meta) = fs::symlink_metadata(&dir_path) else {
            continue;
        };
        if dir_meta.file_type().is_symlink() || !dir_meta.is_dir() {
            continue;
        }
        let evidence_path = dir_path.join(EVIDENCE_FILE_NAME);
        let (size, modified) = match fs::symlink_metadata(&evidence_path) {
            Ok(meta) if !meta.file_type().is_symlink() && meta.is_file() => {
                (meta.len(), meta.modified().unwrap_or(SystemTime::UNIX_EPOCH))
            }
            _ => (0, dir_meta.modified().unwrap_or(SystemTime::UNIX_EPOCH)),
        };
        total_bytes = total_bytes.saturating_add(size);
        if name != preserve_key {
            entries.push((modified, name.to_owned(), size, dir_path));
        }
    }
    if total_bytes <= max_total_bytes {
        return;
    }
    entries.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    for (_, key_name, size, dir_path) in entries {
        if total_bytes <= max_total_bytes {
            break;
        }
        let lock_path = v1_dir.join(format!("{key_name}.lock"));
        let Ok(_lock) = acquire_exclusive_flock_with_phase(&lock_path, CLAIM_CACHE_PHASE) else {
            continue;
        };
        let Ok(meta) = fs::symlink_metadata(&dir_path) else {
            continue;
        };
        if meta.file_type().is_symlink() || !meta.is_dir() {
            continue;
        }
        crate::sandbox::make_tree_writable(&dir_path);
        if fs::remove_dir_all(&dir_path).is_ok() {
            total_bytes = total_bytes.saturating_sub(size);
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    fn sample_key_input() -> ClaimEvidenceKeyInput {
        ClaimEvidenceKeyInput {
            canonical_scope: "{\"kind\":\"selected_unit\",\"roots\":[\"foo\"]}".into(),
            modules: vec![
                ClaimModuleDigest {
                    module: "Captured".into(),
                    role: "capture".into(),
                    sha256: "1".repeat(64),
                },
                ClaimModuleDigest {
                    module: "Spec".into(),
                    role: "specification".into(),
                    sha256: "2".repeat(64),
                },
                ClaimModuleDigest {
                    module: "Expected".into(),
                    role: "expected".into(),
                    sha256: "3".repeat(64),
                },
                ClaimModuleDigest {
                    module: "Proof".into(),
                    role: "proof".into(),
                    sha256: "4".repeat(64),
                },
            ],
            theorem_module: "Proof".into(),
            theorem_name: "Proof.verify".into(),
            expected_module: "Expected".into(),
            expected_declaration: "Expected.claim".into(),
            canonical_root: "Trusted.MirSemantics.UnitTheorem".into(),
            subject_declaration: "Captured.program".into(),
            specification_declaration: "Spec.specs".into(),
            model_manifest_sha256: "5".repeat(64),
            specification_manifest_sha256: "6".repeat(64),
            correspondence_provenance_sha256: "7".repeat(64),
            foundation_lock_sha256: "8".repeat(64),
            library_lock_sha256: "9".repeat(64),
            inspector_source_sha256: "a".repeat(64),
            lean_binary_sha256: "b".repeat(64),
            lean_version: "4.34.1".into(),
            sysroot_manifest_sha256: "c".repeat(64),
            runtime_libs_verified: true,
            active_sandbox: "linux_bwrap".into(),
            allow_unpinned_lean: false,
            allow_sorry_in_proof: false,
            replay_posture: REPLAY_POSTURE_TAG.into(),
        }
    }

    #[test]
    fn key_depends_on_every_semantic_proof_toolchain_and_policy_field() {
        let base = sample_key_input();
        let base_key = base.cache_key();
        assert_eq!(base_key.len(), 64);

        let mutations: Vec<ClaimEvidenceKeyInput> = vec![
            ClaimEvidenceKeyInput {
                canonical_scope: "{\"kind\":\"crate\"}".into(),
                ..base.clone()
            },
            {
                let mut m = base.clone();
                m.modules[0].sha256 = "f".repeat(64);
                m
            },
            {
                let mut m = base.clone();
                m.modules[1].sha256 = "f".repeat(64);
                m
            },
            {
                let mut m = base.clone();
                m.modules[3].sha256 = "f".repeat(64);
                m
            },
            {
                let mut m = base.clone();
                m.modules[1].role = "proof".into();
                m
            },
            ClaimEvidenceKeyInput { theorem_name: "Proof.alt".into(), ..base.clone() },
            ClaimEvidenceKeyInput { specification_declaration: "Spec.alt".into(), ..base.clone() },
            ClaimEvidenceKeyInput { model_manifest_sha256: "f".repeat(64), ..base.clone() },
            ClaimEvidenceKeyInput { specification_manifest_sha256: "f".repeat(64), ..base.clone() },
            ClaimEvidenceKeyInput {
                correspondence_provenance_sha256: "f".repeat(64),
                ..base.clone()
            },
            ClaimEvidenceKeyInput { foundation_lock_sha256: "f".repeat(64), ..base.clone() },
            ClaimEvidenceKeyInput { library_lock_sha256: "f".repeat(64), ..base.clone() },
            ClaimEvidenceKeyInput { inspector_source_sha256: "f".repeat(64), ..base.clone() },
            ClaimEvidenceKeyInput { lean_binary_sha256: "f".repeat(64), ..base.clone() },
            ClaimEvidenceKeyInput { lean_version: "4.35.0".into(), ..base.clone() },
            ClaimEvidenceKeyInput { sysroot_manifest_sha256: "f".repeat(64), ..base.clone() },
            ClaimEvidenceKeyInput { runtime_libs_verified: false, ..base.clone() },
            ClaimEvidenceKeyInput {
                active_sandbox: "linux_landlock_seccomp".into(),
                ..base.clone()
            },
            ClaimEvidenceKeyInput { allow_unpinned_lean: true, ..base.clone() },
            ClaimEvidenceKeyInput { allow_sorry_in_proof: true, ..base.clone() },
            ClaimEvidenceKeyInput { replay_posture: "alt".into(), ..base.clone() },
        ];
        for (idx, mutated) in mutations.iter().enumerate() {
            assert_ne!(
                mutated.cache_key(),
                base_key,
                "mutation {idx} failed to alter claim cache key"
            );
        }
    }

    #[test]
    fn roundtrip_and_fail_closed_corruption_and_symlink_rejection() {
        let tmp = tempfile::tempdir().unwrap();
        let cache_dir = tmp.path().join("claims");
        let cache = ClaimCache::from_policy(Some(cache_dir.clone()), false).unwrap();
        let key_input = sample_key_input();
        let key = key_input.cache_key();

        assert_eq!(cache.lookup(&key_input).unwrap(), None);

        let audit = json!({ "exactType": true, "replay": true });
        cache.store(&key_input, &audit).unwrap();
        assert_eq!(cache.lookup(&key_input).unwrap(), Some(audit));

        // Corrupt JSON payload -> fail closed (`tool_failed`).
        let evidence = cache_dir.join("v1").join(&key).join(EVIDENCE_FILE_NAME);
        #[cfg(unix)]
        set_mode(&evidence, 0o600).unwrap();
        fs::write(&evidence, b"{corrupt json").unwrap();
        let err = cache.lookup(&key_input).unwrap_err();
        assert_eq!(err.phase, CLAIM_CACHE_PHASE);
        assert!(err.message.contains("corrupt claim cache entry"), "{err}");

        // Swapped `input` inside valid JSON -> fail closed (`mismatch`).
        let mut wrong_input = sample_key_input();
        wrong_input.allow_sorry_in_proof = true;
        let forged = serde_json::to_vec(&CachedClaimEvidence {
            schema_version: CLAIM_CACHE_FORMAT_VERSION,
            cache_key: key.clone(),
            input: wrong_input,
            audit: json!({"exactType": true}),
        })
        .unwrap();
        fs::write(&evidence, forged).unwrap();
        let err = cache.lookup(&key_input).unwrap_err();
        assert_eq!(err.phase, CLAIM_CACHE_PHASE);
        assert!(err.message.contains("mismatch"), "{err}");

        // Unknown extra field -> fail closed (`deny_unknown_fields`).
        let extra = serde_json::to_vec(&json!({
            "schema_version": 1,
            "cache_key": key,
            "input": key_input,
            "audit": {},
            "smuggled": 1
        }))
        .unwrap();
        fs::write(&evidence, extra).unwrap();
        let err = cache.lookup(&key_input).unwrap_err();
        assert_eq!(err.phase, CLAIM_CACHE_PHASE);

        // Symlinked `evidence.json` -> fail closed.
        #[cfg(unix)]
        {
            let target = tmp.path().join("outside.json");
            fs::write(&target, b"{}").unwrap();
            fs::remove_file(&evidence).unwrap();
            std::os::unix::fs::symlink(&target, &evidence).unwrap();
            let err = cache.lookup(&key_input).unwrap_err();
            assert_eq!(err.phase, CLAIM_CACHE_PHASE);
            assert!(err.message.contains("regular non-symlink"), "{err}");

            // Symlinked cache root fails closed on lookup and store.
            let real_dir = tmp.path().join("real-dir");
            fs::create_dir_all(&real_dir).unwrap();
            let sym_dir = tmp.path().join("sym-dir");
            std::os::unix::fs::symlink(&real_dir, &sym_dir).unwrap();
            let sym_cache = ClaimCache::from_policy(Some(sym_dir), false).unwrap();
            let err_lookup = sym_cache.lookup(&key_input).unwrap_err();
            assert!(err_lookup.message.contains("symlink"), "{err_lookup}");
            let err_store = sym_cache.store(&key_input, &json!({})).unwrap_err();
            assert!(err_store.message.contains("symlink"), "{err_store}");
        }
    }

    #[test]
    fn env_var_resolution_honors_explicit_xdg_even_without_home() {
        let dir = claim_cache_dir_from_env_vars(None, Some(OsStr::new("/var/cache/./xdg-root")));
        if cfg!(target_os = "macos") {
            assert_eq!(dir, None);
        } else {
            assert_eq!(dir, Some(PathBuf::from("/var/cache/xdg-root/anneal/claim-cache")));
        }
        assert_eq!(claim_cache_dir_from_env_vars(None, Some(OsStr::new("relative/xdg"))), None);
        let fallback =
            claim_cache_dir_from_env_vars(Some(OsStr::new("/home/anneal-user")), None).unwrap();
        if cfg!(target_os = "macos") {
            assert_eq!(
                fallback,
                PathBuf::from("/home/anneal-user/Library/Caches/anneal/claim-cache")
            );
        } else {
            assert_eq!(fallback, PathBuf::from("/home/anneal-user/.cache/anneal/claim-cache"));
        }
    }

    #[test]
    fn oversize_entries_skip_store_and_fail_lookup_while_budget_evicts_oldest() {
        let tmp = tempfile::tempdir().unwrap();
        let cache_dir = tmp.path().join("claims");
        let cache = ClaimCache::from_policy(Some(cache_dir.clone()), false).unwrap();

        let mut k1 = sample_key_input();
        k1.canonical_scope = "k1".into();
        let mut k2 = sample_key_input();
        k2.canonical_scope = "k2".into();
        let mut k3 = sample_key_input();
        k3.canonical_scope = "k3".into();

        // Entry larger than `max_entry_bytes` is skipped cleanly on store.
        let big_audit = json!({ "payload": "x".repeat(2048) });
        cache.store_with_caps(&k1, &big_audit, 1500, 10_000).unwrap();
        assert_eq!(cache.lookup(&k1).unwrap(), None);

        // Planted oversized entry fails closed on capped lookup.
        cache.store(&k1, &big_audit).unwrap();
        let cap_err = cache.lookup_with_cap(&k1, 1500).unwrap_err();
        assert_eq!(cap_err.phase, CLAIM_CACHE_PHASE);
        assert!(cap_err.message.contains("exceeded"), "{cap_err}");

        // Evict oldest entries past budget, keeping newer and other files.
        let sentinel = cache_dir.join("v1").join("unrelated-note");
        fs::write(&sentinel, b"keep").unwrap();
        let small = json!({ "ok": true });
        let sample_len = serde_json::to_vec(&CachedClaimEvidence {
            schema_version: CLAIM_CACHE_FORMAT_VERSION,
            cache_key: k2.cache_key(),
            input: k2.clone(),
            audit: small.clone(),
        })
        .unwrap()
        .len() as u64;
        cache.store_with_caps(&k2, &small, sample_len + 128, sample_len + 128).unwrap();
        std::thread::sleep(std::time::Duration::from_millis(20));
        cache.store_with_caps(&k3, &small, sample_len + 128, sample_len + 128).unwrap();
        assert!(sentinel.is_file());
        assert_eq!(cache.lookup(&k3).unwrap(), Some(small));
        assert!(!cache_dir.join("v1").join(k1.cache_key()).exists());
    }

    #[test]
    fn filesystem_root_is_rejected_for_lookup_and_store() {
        let root_cache = ClaimCache::from_policy(Some(PathBuf::from("/")), false).unwrap();
        let key_input = sample_key_input();
        let err_lookup = root_cache.lookup(&key_input).unwrap_err();
        assert_eq!(err_lookup.phase, CLAIM_CACHE_PHASE);
        assert!(err_lookup.message.contains("root"), "{err_lookup}");
        let err_store = root_cache.store(&key_input, &json!({})).unwrap_err();
        assert_eq!(err_store.phase, CLAIM_CACHE_PHASE);
        assert!(err_store.message.contains("root"), "{err_store}");
    }

    #[test]
    fn incomplete_entry_dir_is_replaced_and_concurrent_eviction_is_race_free() {
        let tmp = tempfile::tempdir().unwrap();
        let cache_dir = tmp.path().join("claims");
        let cache = ClaimCache::from_policy(Some(cache_dir.clone()), false).unwrap();

        let key_input = sample_key_input();
        let orphan_dir = cache_dir.join("v1").join(key_input.cache_key());
        fs::create_dir_all(&orphan_dir).unwrap();
        let audit = json!({ "exactType": true });
        cache.store(&key_input, &audit).unwrap();
        assert_eq!(cache.lookup(&key_input).unwrap(), Some(audit.clone()));

        let small_len = serde_json::to_vec(&CachedClaimEvidence {
            schema_version: CLAIM_CACHE_FORMAT_VERSION,
            cache_key: key_input.cache_key(),
            input: key_input.clone(),
            audit: audit.clone(),
        })
        .unwrap()
        .len() as u64;

        std::thread::scope(|s| {
            for t in 0..4u32 {
                let cache_ref = &cache;
                let base_key = sample_key_input();
                let audit_ref = &audit;
                s.spawn(move || {
                    for iter in 0..25u32 {
                        let mut k = base_key.clone();
                        k.canonical_scope = format!("worker-{t}-{}", iter % 4);
                        cache_ref
                            .store_with_caps(&k, audit_ref, small_len + 128, (small_len + 128) * 3)
                            .unwrap();
                        if let Some(found) = cache_ref.lookup(&k).unwrap() {
                            assert_eq!(found, *audit_ref);
                        }
                    }
                });
            }
        });
    }
}
