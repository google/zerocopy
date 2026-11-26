// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Reference-oracle runner invoking Miri on staged differential fixtures.
//!
//! Uses a file-locked offline `cargo miri setup` cache configured with
//! `CARGO_NET_OFFLINE=true` and vendored crates from
//! `<rust_sysroot>/lib/rustlib/src/rust/library/vendor` inside an isolated
//! scratch `CARGO_HOME/config.toml` unless `ANNEAL_MIRI_SYSROOT` explicitly
//! provides a valid prepared non-symlink sysroot.

use std::{
    collections::{BTreeMap, BTreeSet, hash_map::RandomState},
    env,
    ffi::OsString,
    fmt::Write as _,
    fs::{self, File},
    hash::{BuildHasher as _, Hasher as _},
    io::Read as _,
    path::{Component, Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
    thread,
    time::{Duration, SystemTime, UNIX_EPOCH},
};

use anneal_testkit::{Invocation, ProcessOutcome, ProcessSupervisor, Termination};
use serde::Serialize;
use serde_json::Value;
use sha2::{Digest, Sha256};

use crate::{
    corpus::LitmusCase,
    lean_runner::{effective_timeout_secs, sha256_bytes_hex, sha256_file_hex},
    verdict::{Expectation, IntKind, MirValue, ObservedOutcome, OrderingKind},
};

const MIRI_RET_STEM: &str = "ANNEAL_MIRI_RET";
const MIRI_RET_PREFIX: &str = "ANNEAL_MIRI_RET=";
static MIRI_MARKER_SEQ: AtomicU64 = AtomicU64::new(0);
const PINNED_MIRI_TARGET: &str = "x86_64-unknown-linux-gnu";
const MIRI_SETUP_TIMEOUT_SECS: u64 = 300;
const MIRI_CASE_TIMEOUT_SECS: u64 = 120;
const RUSTC_PROBE_TIMEOUT_SECS: u64 = 30;

/// Prepared Miri binary and sysroot coordinates for executing reference checks.
#[derive(Clone, Debug)]
pub struct MiriSession {
    pub miri_bin: PathBuf,
    pub rust_sysroot: PathBuf,
    pub miri_sysroot: PathBuf,
}

impl MiriSession {
    /// Locate `miri` alongside `rust_sysroot` and resolve or offline-prepare
    /// a Miri target sysroot under `cache_root`.
    pub fn prepare(rust_sysroot: &Path, cache_root: &Path) -> Result<Self, String> {
        Self::prepare_with_env(rust_sysroot, cache_root, |k| env::var_os(k))
    }

    pub fn prepare_with_env(
        rust_sysroot: &Path,
        cache_root: &Path,
        get_env: impl Fn(&str) -> Option<OsString>,
    ) -> Result<Self, String> {
        let rust_sysroot = fs::canonicalize(rust_sysroot)
            .map_err(|e| format!("canonicalize rust_sysroot: {e}"))?;
        let miri_bin = rust_sysroot.join("bin/miri");
        if !miri_bin.is_file() {
            return Err(format!("pinned sysroot lacks `bin/miri`: {}", miri_bin.display()));
        }

        if let Some(explicit) =
            get_env("ANNEAL_MIRI_SYSROOT").filter(|v| !v.is_empty()).map(PathBuf::from)
        {
            if fs::symlink_metadata(&explicit)
                .map_err(|e| format!("stat ANNEAL_MIRI_SYSROOT={}: {e}", explicit.display()))?
                .file_type()
                .is_symlink()
            {
                return Err(format!(
                    "ANNEAL_MIRI_SYSROOT={} must not be a symlink",
                    explicit.display()
                ));
            }
            if !explicit.join("lib/rustlib").is_dir() {
                return Err(format!(
                    "ANNEAL_MIRI_SYSROOT={} does not contain `lib/rustlib`",
                    explicit.display()
                ));
            }
            let miri_sysroot = fs::canonicalize(&explicit)
                .map_err(|e| format!("canonicalize ANNEAL_MIRI_SYSROOT: {e}"))?;
            let ver_tag = rustc_version_tag(&rust_sysroot)?;
            let setup_sha = compute_miri_setup_input_sha256(&rust_sysroot, &ver_tag)?;
            verify_explicit_miri_sysroot_stamp(&miri_sysroot, &ver_tag, &setup_sha)?;
            return Ok(Self { miri_bin, rust_sysroot, miri_sysroot });
        }

        let ver_tag = rustc_version_tag(&rust_sysroot)?;
        let setup_sha = compute_miri_setup_input_sha256(&rust_sysroot, &ver_tag)?;
        let cache_id = format!("{ver_tag}-{}", &setup_sha[..16]);
        let expected_stamp = expected_miri_ready_stamp(&ver_tag, &setup_sha);
        fs::create_dir_all(cache_root)
            .map_err(|e| format!("create cache dir {}: {e}", cache_root.display()))?;
        let target_dir = cache_root.join(format!("miri-sysroot-{cache_id}"));
        let lock_path = cache_root.join(format!("miri-sysroot-{cache_id}.setup.lock"));
        let lock_file = File::options()
            .create(true)
            .read(true)
            .write(true)
            .truncate(false)
            .open(&lock_path)
            .map_err(|e| format!("open Miri lock {}: {e}", lock_path.display()))?;
        lock_file
            .lock()
            .map_err(|e| format!("acquire Miri setup lock {}: {e}", lock_path.display()))?;

        let ready_stamp = target_dir.join(".anneal-miri-ready");
        let stamp_matches = fs::symlink_metadata(&ready_stamp)
            .ok()
            .is_some_and(|m| !m.file_type().is_symlink() && m.is_file())
            && fs::read_to_string(&ready_stamp).ok().as_deref() == Some(expected_stamp.as_str());
        if !stamp_matches || !target_dir.join("lib/rustlib").is_dir() {
            build_offline_miri_sysroot(&rust_sysroot, &miri_bin, &target_dir)?;
            fs::write(&ready_stamp, &expected_stamp)
                .map_err(|e| format!("write Miri ready stamp: {e}"))?;
        }
        drop(lock_file);

        let miri_sysroot = fs::canonicalize(&target_dir)
            .map_err(|e| format!("canonicalize Miri sysroot {}: {e}", target_dir.display()))?;
        Ok(Self { miri_bin, rust_sysroot, miri_sysroot })
    }

    /// Execute all litmus cases under Miri, grouping harness generation by
    /// fixture source file and running cases across bounded worker threads.
    pub fn run_cases(
        &self,
        cases: &[LitmusCase],
    ) -> Result<BTreeMap<String, ObservedOutcome>, String> {
        let mut by_source: BTreeMap<PathBuf, Vec<&LitmusCase>> = BTreeMap::new();
        for case in cases {
            by_source.entry(case.source_abs.clone()).or_default().push(case);
        }

        let workers = thread::available_parallelism().map(|n| n.get().clamp(1, 4)).unwrap_or(1);
        let ld_path = join_library_path(&self.rust_sysroot.join("lib"));
        let path_env = build_child_path(&self.rust_sysroot.join("bin"))?;
        let rustc_bin = fs::canonicalize(self.rust_sysroot.join("bin/rustc"))
            .map_err(|e| format!("canonicalize rustc in {}: {e}", self.rust_sysroot.display()))?;
        let setup_timeout = effective_timeout_secs(MIRI_SETUP_TIMEOUT_SECS)?;

        let work_root = tempfile::tempdir()
            .map_err(|e| format!("create temporary Miri harness workspace: {e}"))?;
        let mut results = BTreeMap::new();
        struct MiriWorkItem {
            case_id: String,
            harness_path: PathBuf,
            bridge_rlib: PathBuf,
            corpus_dir: PathBuf,
            selector: String,
            token: String,
        }
        let mut work_items: Vec<MiriWorkItem> = Vec::with_capacity(cases.len());

        for (group_idx, (source_abs, group_cases)) in by_source.iter().enumerate() {
            let source_text = fs::read_to_string(source_abs)
                .map_err(|e| format!("read fixture {}: {e}", source_abs.display()))?;
            let bundle_res = build_isolated_miri_group(
                work_root.path(),
                group_idx,
                &source_text,
                group_cases,
                &rustc_bin,
                &self.miri_sysroot,
                &ld_path,
                &path_env,
                Duration::from_secs(setup_timeout),
            );
            match bundle_res {
                Ok(bundle) => {
                    for case in group_cases {
                        work_items.push(MiriWorkItem {
                            case_id: case.id.clone(),
                            harness_path: bundle.harness_path.clone(),
                            bridge_rlib: bundle.bridge_rlib.clone(),
                            corpus_dir: bundle.corpus_dir.clone(),
                            selector: case.id.clone(),
                            token: bundle.token.clone(),
                        });
                    }
                }
                Err(detail) => {
                    for case in group_cases {
                        results.insert(
                            case.id.clone(),
                            ObservedOutcome::ToolError { detail: detail.clone() },
                        );
                    }
                }
            }
        }

        for chunk in work_items.chunks(workers) {
            let outcomes = thread::scope(|scope| {
                let mut handles = Vec::with_capacity(chunk.len());
                for item in chunk {
                    let miri_bin = &self.miri_bin;
                    let miri_sysroot = &self.miri_sysroot;
                    let ld_path = &ld_path;
                    let path_env = &path_env;
                    handles.push(scope.spawn(move || {
                        let out = run_single_miri(
                            miri_bin,
                            miri_sysroot,
                            ld_path,
                            path_env,
                            &item.harness_path,
                            &item.bridge_rlib,
                            &item.corpus_dir,
                            &item.selector,
                            Some(item.token.as_str()),
                        );
                        (item.case_id.clone(), out)
                    }));
                }
                handles
                    .into_iter()
                    .map(|h| {
                        h.join().unwrap_or_else(|_| {
                            (
                                "<panicked>".to_owned(),
                                ObservedOutcome::ToolError {
                                    detail: "Miri worker thread panicked".to_owned(),
                                },
                            )
                        })
                    })
                    .collect::<Vec<_>>()
            });
            for (case_id, outcome) in outcomes {
                results.insert(case_id, outcome);
            }
        }

        Ok(results)
    }
}

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

fn render_vendored_cargo_config(vendor_dir: &Path) -> Result<String, String> {
    let cfg = ScratchCargoConfig {
        source: ScratchCargoSources {
            crates_io: ScratchCratesIoReplace { replace_with: "vendored-sources" },
            vendored_sources: ScratchVendorDir {
                directory: vendor_dir.to_string_lossy().into_owned(),
            },
        },
    };
    toml::to_string(&cfg).map_err(|e| format!("serialize offline Miri Cargo config: {e}"))
}

fn run_supervised(
    inv: &Invocation,
    work_dir: &Path,
    timeout_secs: u64,
    context: &str,
) -> Result<ProcessOutcome, String> {
    let tmp =
        tempfile::tempdir().map_err(|e| format!("create supervisor temp dir ({context}): {e}"))?;
    let canon_root = fs::canonicalize(tmp.path())
        .map_err(|e| format!("canonicalize supervisor temp dir ({context}): {e}"))?;
    let canon_work = fs::canonicalize(work_dir)
        .map_err(|e| format!("canonicalize work dir ({context}): {e}"))?;
    let supervisor = ProcessSupervisor::new(Duration::from_secs(timeout_secs))?;
    supervisor.run(inv, &canon_work, &canon_root.join("log"), &canon_root)
}

fn build_child_path(primary_bin: &Path) -> Result<OsString, String> {
    let mut path_entries = vec![primary_bin.to_path_buf()];
    if let Some(existing) = env::var_os("PATH") {
        path_entries.extend(env::split_paths(&existing));
    }
    env::join_paths(path_entries).map_err(|e| format!("join PATH entries: {e}"))
}

fn parse_rustc_version_tag(rustc: &Path, text: &str) -> Result<String, String> {
    let commit = text
        .lines()
        .find_map(|line| line.strip_prefix("commit-hash: "))
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .ok_or_else(|| format!("`{} -vV` output missing `commit-hash:` line", rustc.display()))?;
    let short: String = commit.chars().take(12).collect();
    let host = text
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .ok_or_else(|| format!("`{} -vV` output missing `host:` line", rustc.display()))?;
    let rustc_sha = sha256_file_hex(rustc)?;
    Ok(format!("{short}-{host}-{}", &rustc_sha[..12]))
}

fn expected_miri_ready_stamp(ver_tag: &str, setup_sha: &str) -> String {
    format!("anneal-miri-setup-v2:{ver_tag}:{setup_sha}\n")
}

fn verify_explicit_miri_sysroot_stamp(
    miri_sysroot: &Path,
    ver_tag: &str,
    setup_sha: &str,
) -> Result<(), String> {
    let ready_stamp = miri_sysroot.join(".anneal-miri-ready");
    let meta = fs::symlink_metadata(&ready_stamp).map_err(|e| {
        format!(
            "ANNEAL_MIRI_SYSROOT={} lacks verifiable `.anneal-miri-ready` setup stamp ({e})",
            miri_sysroot.display()
        )
    })?;
    if meta.file_type().is_symlink() || !meta.is_file() {
        return Err(format!(
            "ANNEAL_MIRI_SYSROOT={} `.anneal-miri-ready` must be a regular non-symlink file",
            miri_sysroot.display()
        ));
    }
    let expected = expected_miri_ready_stamp(ver_tag, setup_sha);
    let actual = fs::read_to_string(&ready_stamp)
        .map_err(|e| format!("read ANNEAL_MIRI_SYSROOT stamp {}: {e}", ready_stamp.display()))?;
    if actual != expected {
        return Err(format!(
            "ANNEAL_MIRI_SYSROOT={} setup stamp does not match current Miri/rust-src inputs",
            miri_sysroot.display()
        ));
    }
    Ok(())
}

/// Compute a full SHA-256 digest over all inputs participating in
/// `cargo miri setup` (`rustc`, `cargo`, `miri`, `cargo-miri`,
/// `PINNED_MIRI_TARGET`, and the entire `lib/rustlib/src/rust/library` tree
/// including `vendor/`) so cached Miri sysroots are invalidated whenever any
/// setup input changes.
fn compute_miri_setup_input_sha256(rust_sysroot: &Path, ver_tag: &str) -> Result<String, String> {
    let mut bin_shas = Vec::with_capacity(4);
    for rel_bin in ["bin/rustc", "bin/cargo", "bin/miri", "bin/cargo-miri"] {
        let bin_path = rust_sysroot.join(rel_bin);
        if !bin_path.is_file() {
            return Err(format!("pinned sysroot lacks `{rel_bin}`: {}", bin_path.display()));
        }
        let canon = fs::canonicalize(&bin_path)
            .map_err(|e| format!("canonicalize {rel_bin} ({}): {e}", bin_path.display()))?;
        bin_shas.push((rel_bin, sha256_file_hex(&canon)?));
    }

    let library_dir = rust_sysroot.join("lib/rustlib/src/rust/library");
    let vendor_dir = library_dir.join("vendor");
    if !vendor_dir.is_dir() {
        return Err(format!(
            "pinned rust_sysroot lacks vendored `rust-src` crates at {}",
            vendor_dir.display()
        ));
    }
    let canon_library = fs::canonicalize(&library_dir)
        .map_err(|e| format!("canonicalize rust-src library {}: {e}", library_dir.display()))?;
    let library_sha = hash_directory_tree_contents(&canon_library)?;

    let mut h = Sha256::new();
    h.update(b"anneal-miri-setup-inputs-v2\0");
    h.update(PINNED_MIRI_TARGET.as_bytes());
    h.update(b"\0");
    h.update(ver_tag.as_bytes());
    h.update(b"\0");
    for (name, sha) in &bin_shas {
        h.update(name.as_bytes());
        h.update(b":");
        h.update(sha.as_bytes());
        h.update(b"\n");
    }
    h.update(b"rust-src-library:");
    h.update(library_sha.as_bytes());
    h.update(b"\n");
    let digest = h.finalize();
    let mut hex = String::with_capacity(64);
    for b in digest {
        use std::fmt::Write as _;
        let _ = write!(hex, "{b:02x}");
    }
    Ok(hex)
}

fn hash_directory_tree_contents(root_dir: &Path) -> Result<String, String> {
    fn collect_files(
        cur_dir: &Path,
        rel_prefix: &Path,
        active_ancestors: &mut BTreeSet<PathBuf>,
        out: &mut Vec<(String, PathBuf)>,
    ) -> Result<(), String> {
        let canon_cur = fs::canonicalize(cur_dir)
            .map_err(|e| format!("canonicalize rust-src dir {}: {e}", cur_dir.display()))?;
        if !active_ancestors.insert(canon_cur.clone()) {
            return Err(format!("symlink cycle detected in rust-src tree: {}", cur_dir.display()));
        }
        let mut dir_entries: Vec<_> = fs::read_dir(cur_dir)
            .map_err(|e| format!("read rust-src dir {}: {e}", cur_dir.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| format!("iterate rust-src dir {}: {e}", cur_dir.display()))?;
        dir_entries.sort_by_key(|e| e.file_name());
        for entry in dir_entries {
            let path = entry.path();
            let meta = fs::metadata(&path)
                .map_err(|e| format!("stat rust-src entry {}: {e}", path.display()))?;
            let next_rel = rel_prefix.join(entry.file_name());
            if meta.is_dir() {
                collect_files(&path, &next_rel, active_ancestors, out)?;
            } else if meta.is_file() {
                let mut segs = Vec::new();
                for comp in next_rel.components() {
                    let Component::Normal(os) = comp else {
                        return Err(format!(
                            "invalid relative component in rust-src: {}",
                            path.display()
                        ));
                    };
                    let s = os
                        .to_str()
                        .ok_or_else(|| format!("non-UTF-8 path in rust-src: {}", path.display()))?;
                    segs.push(s);
                }
                out.push((segs.join("/"), path));
            } else {
                return Err(format!(
                    "unexpected non-regular entry in rust-src: {}",
                    path.display()
                ));
            }
        }
        active_ancestors.remove(&canon_cur);
        Ok(())
    }

    let mut files = Vec::new();
    let mut ancestors = BTreeSet::new();
    collect_files(root_dir, Path::new(""), &mut ancestors, &mut files)?;

    let workers = thread::available_parallelism()
        .map(|n| n.get().clamp(1, 4))
        .unwrap_or(1)
        .min(files.len().max(1));
    let mut entries: BTreeMap<String, String> = BTreeMap::new();
    if files.len() <= 1 || workers <= 1 {
        for (rel, path) in files {
            entries.insert(rel, sha256_file_hex(&path)?);
        }
    } else {
        let chunk_size = files.len().div_ceil(workers);
        let chunk_results: Vec<Result<Vec<(String, String)>, String>> = thread::scope(|scope| {
            let handles: Vec<_> = files
                .chunks(chunk_size)
                .map(|chunk| {
                    scope.spawn(move || {
                        let mut local = Vec::with_capacity(chunk.len());
                        for (rel, path) in chunk {
                            local.push((rel.clone(), sha256_file_hex(path)?));
                        }
                        Ok(local)
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| {
                    h.join().unwrap_or_else(|_| Err("rust-src hash worker panicked".to_owned()))
                })
                .collect()
        });
        for res in chunk_results {
            for (rel, sha) in res? {
                entries.insert(rel, sha);
            }
        }
    }

    let mut manifest = String::new();
    for (rel, sha) in &entries {
        manifest.push_str(rel);
        manifest.push(':');
        manifest.push_str(sha);
        manifest.push('\n');
    }
    Ok(sha256_bytes_hex(manifest.as_bytes()))
}

fn rustc_version_tag(rust_sysroot: &Path) -> Result<String, String> {
    let rustc = fs::canonicalize(rust_sysroot.join("bin/rustc"))
        .map_err(|e| format!("canonicalize rustc in {}: {e}", rust_sysroot.display()))?;
    let mut inv = Invocation::new(&rustc, &["-vV"])
        .env("LD_LIBRARY_PATH", join_library_path(&rust_sysroot.join("lib")));
    if let Some(path) = env::var_os("PATH") {
        inv = inv.env("PATH", path);
    }
    let probe_timeout = effective_timeout_secs(RUSTC_PROBE_TIMEOUT_SECS)?;
    let out = run_supervised(&inv, rust_sysroot, probe_timeout, "rustc -vV")?;
    match out.termination {
        Termination::Exited(status) if status.success() => {}
        other => {
            return Err(format!(
                "`{} -vV` failed ({}): {}",
                rustc.display(),
                other.describe(),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
    }
    let text = String::from_utf8_lossy(&out.stdout);
    parse_rustc_version_tag(&rustc, &text)
}

fn build_offline_miri_sysroot(
    rust_sysroot: &Path,
    miri_bin: &Path,
    target_dir: &Path,
) -> Result<(), String> {
    let rustc = fs::canonicalize(rust_sysroot.join("bin/rustc"))
        .map_err(|e| format!("canonicalize rustc: {e}"))?;
    let cargo_bin = rust_sysroot.join("bin/cargo");
    if !cargo_bin.is_file() {
        return Err(format!("pinned sysroot lacks `bin/cargo`: {}", cargo_bin.display()));
    }
    let cargo_bin =
        fs::canonicalize(&cargo_bin).map_err(|e| format!("canonicalize cargo bin: {e}"))?;

    let vendor_dir = rust_sysroot.join("lib/rustlib/src/rust/library/vendor");
    if !vendor_dir.is_dir() {
        return Err(format!(
            "pinned rust_sysroot lacks vendored `rust-src` crates at {}",
            vendor_dir.display()
        ));
    }
    let canon_vendor = fs::canonicalize(&vendor_dir)
        .map_err(|e| format!("canonicalize vendored rust-src deps: {e}"))?;

    let parent = target_dir
        .parent()
        .ok_or_else(|| format!("target dir has no parent: {}", target_dir.display()))?;
    let staging = tempfile::Builder::new()
        .prefix("miri-staging-")
        .tempdir_in(parent)
        .map_err(|e| format!("create Miri staging dir: {e}"))?;
    // Keep `CARGO_HOME`, `HOME`, and `TMPDIR` in system temp rather than
    // `parent`: when `parent` is `anneal/target/anneal-diff-cache`,
    // `cargo miri setup`'s temporary crate under `$TMPDIR` would otherwise
    // inherit `anneal/Cargo.toml` as an enclosing `[workspace]`. Keep
    // `staging` in `parent` so promoting to `target_dir` remains a same-FS
    // rename.
    let scratch_cargo_home = tempfile::Builder::new()
        .prefix("miri-cargo-home-")
        .tempdir()
        .map_err(|e| format!("create offline Miri CARGO_HOME: {e}"))?;
    let scratch_home = tempfile::Builder::new()
        .prefix("miri-home-")
        .tempdir()
        .map_err(|e| format!("create offline Miri HOME: {e}"))?;
    let cargo_config = render_vendored_cargo_config(&canon_vendor)?;
    fs::write(scratch_cargo_home.path().join("config.toml"), cargo_config)
        .map_err(|e| format!("write offline Miri Cargo config.toml: {e}"))?;

    let joined_path = build_child_path(&rust_sysroot.join("bin"))?;
    let scratch_tmp = scratch_home.path().join("tmp");
    fs::create_dir_all(&scratch_tmp).map_err(|e| format!("create Miri scratch tmp: {e}"))?;

    // `ProcessSupervisor` executes with `env_clear()`, ensuring ambient
    // `RUSTFLAGS`, `CARGO_ENCODED_RUSTFLAGS`, `RUSTC_WRAPPER`,
    // `RUSTC_WORKSPACE_WRAPPER`, `CARGO_TARGET_DIR`, `RUSTUP_TOOLCHAIN`,
    // `ANNEAL_CAPTURE_DIR`, and `ANNEAL_CAPTURE_FILTER` cannot pollute setup.
    // Offline resolution is enforced via `CARGO_NET_OFFLINE=true` paired with
    // the vendored `CARGO_HOME/config.toml` generated above (`cargo miri setup`
    // does not accept a `--offline` CLI flag).
    let inv = Invocation::new(&cargo_bin, &["miri", "setup", "--target", PINNED_MIRI_TARGET])
        .env("PATH", joined_path)
        .env("HOME", scratch_home.path())
        .env("CARGO_HOME", scratch_cargo_home.path())
        .env("TMPDIR", &scratch_tmp)
        .env("RUSTC", &rustc)
        .env("MIRI", miri_bin)
        .env("MIRI_SYSROOT", staging.path())
        .env("CARGO_NET_OFFLINE", "true")
        .env("LD_LIBRARY_PATH", join_library_path(&rust_sysroot.join("lib")));

    let setup_timeout = effective_timeout_secs(MIRI_SETUP_TIMEOUT_SECS)?;
    let out = run_supervised(&inv, scratch_home.path(), setup_timeout, "miri setup")?;
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
    let staged_path = staging.keep();
    fs::rename(&staged_path, target_dir).map_err(|e| {
        let _ = fs::remove_dir_all(&staged_path);
        format!("promote Miri sysroot {} -> {}: {e}", staged_path.display(), target_dir.display())
    })?;
    Ok(())
}

fn join_library_path(primary: &Path) -> String {
    match env::var("LD_LIBRARY_PATH") {
        Ok(existing) if !existing.is_empty() => format!("{}:{existing}", primary.display()),
        _ => primary.display().to_string(),
    }
}

fn fresh_miri_marker_token(disallowed_haystack: &str) -> String {
    loop {
        let nanos = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
        let seq = MIRI_MARKER_SEQ.fetch_add(1, Ordering::Relaxed);
        let mut h = Sha256::new();
        h.update(b"anneal-miri-marker-v2\0");
        h.update(nanos.to_le_bytes());
        h.update(std::process::id().to_le_bytes());
        h.update(seq.to_le_bytes());
        h.update((disallowed_haystack.len() as u64).to_le_bytes());
        let mut rs = RandomState::new().build_hasher();
        rs.write_u64(seq);
        h.update(rs.finish().to_le_bytes());
        if let Ok(mut urand) = File::open("/dev/urandom") {
            let mut buf = [0u8; 16];
            if urand.read_exact(&mut buf).is_ok() {
                h.update(buf);
            }
        }
        let digest = h.finalize();
        let mut tok = String::with_capacity(32);
        for b in &digest[..16] {
            let _ = write!(tok, "{b:02x}");
        }
        if !disallowed_haystack.contains(&tok) {
            return tok;
        }
    }
}

fn validate_rust_ident(ident: &str, label: &str) -> Result<(), String> {
    let mut bytes = ident.bytes();
    let Some(first) = bytes.next() else {
        return Err(format!("empty {label}"));
    };
    if !(first.is_ascii_alphabetic() || first == b'_')
        || !bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
    {
        return Err(format!("invalid {label} `{ident}`"));
    }
    Ok(())
}

fn validate_rust_fn_path(path: &str) -> Result<(), String> {
    if path.is_empty()
        || path.split("::").any(|seg| validate_rust_ident(seg, "fixture function segment").is_err())
    {
        return Err(format!("invalid fixture function path `{path}`"));
    }
    Ok(())
}

struct IsolatedMiriBundle {
    token: String,
    harness_path: PathBuf,
    bridge_rlib: PathBuf,
    corpus_dir: PathBuf,
}

#[allow(clippy::too_many_arguments)]
fn compile_miri_rlib(
    rustc_bin: &Path,
    miri_sysroot: &Path,
    ld_path: &str,
    path_env: &OsString,
    crate_name: &str,
    src_path: &Path,
    out_rlib: &Path,
    extra_extern: Option<(&str, &Path)>,
    extra_lib_dir: Option<&Path>,
    timeout_secs: u64,
) -> Result<(), String> {
    let mut inv = Invocation::new(rustc_bin, &["--edition=2024", "--target", PINNED_MIRI_TARGET])
        .arg("--sysroot")
        .arg(miri_sysroot)
        .arg("--cfg")
        .arg("miri")
        .arg("-Zalways-encode-mir")
        .arg("-C")
        .arg("opt-level=0")
        .arg("-C")
        .arg("debug-assertions=no")
        .arg("-C")
        .arg("overflow-checks=no")
        .arg("-A")
        .arg("dead_code")
        .arg("--crate-type=lib")
        .arg("--crate-name")
        .arg(crate_name);
    if let Some((dep_name, dep_rlib)) = extra_extern {
        inv = inv.arg("--extern").arg(format!("{dep_name}={}", dep_rlib.display()));
    }
    if let Some(lib_dir) = extra_lib_dir {
        inv = inv.arg("-L").arg(lib_dir);
    }
    inv = inv
        .arg("-o")
        .arg(out_rlib)
        .arg(src_path)
        .env("LD_LIBRARY_PATH", ld_path)
        .env("PATH", path_env);
    if let Some(tmp) = env::var_os("TMPDIR").filter(|v| !v.is_empty()) {
        inv = inv.env("TMPDIR", tmp);
    }

    let work_dir = src_path.parent().unwrap_or_else(|| Path::new("/"));
    let out = run_supervised(&inv, work_dir, timeout_secs, crate_name)?;
    match out.termination {
        Termination::Exited(status) if status.success() => Ok(()),
        other => Err(format!(
            "compile Miri `{crate_name}` crate failed ({}): {}",
            other.describe(),
            String::from_utf8_lossy(&out.stderr).lines().take(6).collect::<Vec<_>>().join(" | ")
        )),
    }
}

#[allow(clippy::too_many_arguments)]
fn build_isolated_miri_group(
    work_root: &Path,
    group_idx: usize,
    source_text: &str,
    group_cases: &[&LitmusCase],
    rustc_bin: &Path,
    miri_sysroot: &Path,
    ld_path: &str,
    path_env: &OsString,
    setup_timeout: Duration,
) -> Result<IsolatedMiriBundle, String> {
    let group_dir = work_root.join(format!("group_{group_idx}"));
    let corpus_dir = group_dir.join("c");
    let bridge_dir = group_dir.join("b");
    fs::create_dir_all(&corpus_dir)
        .map_err(|e| format!("create Miri corpus dir {}: {e}", corpus_dir.display()))?;
    fs::create_dir_all(&bridge_dir)
        .map_err(|e| format!("create Miri bridge dir {}: {e}", bridge_dir.display()))?;

    // Compile `corpus` and `bridge` into separate `.rlib` crates BEFORE
    // generating the secret token or writing `h/harness.rs`, keeping the
    // token strictly inside `h/harness.rs` source literals (never in paths,
    // symbols, args, or stack frame metadata).
    let corpus_src = corpus_dir.join("corpus.rs");
    fs::write(&corpus_src, source_text)
        .map_err(|e| format!("write Miri corpus {}: {e}", corpus_src.display()))?;
    let corpus_rlib = corpus_dir.join("libcorpus.rlib");
    let timeout_secs = setup_timeout.as_secs().max(1);
    compile_miri_rlib(
        rustc_bin,
        miri_sysroot,
        ld_path,
        path_env,
        "corpus",
        &corpus_src,
        &corpus_rlib,
        None,
        None,
        timeout_secs,
    )?;

    let bridge_code = generate_miri_bridge(group_cases)?;
    let bridge_src = bridge_dir.join("bridge.rs");
    fs::write(&bridge_src, &bridge_code)
        .map_err(|e| format!("write Miri bridge {}: {e}", bridge_src.display()))?;
    let bridge_rlib = bridge_dir.join("libbridge.rlib");
    compile_miri_rlib(
        rustc_bin,
        miri_sysroot,
        ld_path,
        path_env,
        "bridge",
        &bridge_src,
        &bridge_rlib,
        Some(("corpus", &corpus_rlib)),
        Some(&corpus_dir),
        timeout_secs,
    )?;

    let mut disallowed = String::with_capacity(source_text.len() + bridge_code.len() + 1);
    disallowed.push_str(source_text);
    disallowed.push('\n');
    disallowed.push_str(&bridge_code);
    let token = fresh_miri_marker_token(&disallowed);

    let harness_code = generate_miri_harness_with_token(group_cases, Some(&token))?;
    let harness_dir = group_dir.join("h");
    fs::create_dir_all(&harness_dir)
        .map_err(|e| format!("create Miri harness dir {}: {e}", harness_dir.display()))?;
    let harness_path = harness_dir.join("harness.rs");
    fs::write(&harness_path, harness_code)
        .map_err(|e| format!("write Miri harness {}: {e}", harness_path.display()))?;

    Ok(IsolatedMiriBundle { token, harness_path, bridge_rlib, corpus_dir })
}

fn miri_ret_prefix_for_token(token: Option<&str>) -> String {
    match token {
        Some(tok) => format!("{MIRI_RET_STEM}:{tok}="),
        None => MIRI_RET_PREFIX.to_owned(),
    }
}

fn generate_miri_bridge(cases: &[&LitmusCase]) -> Result<String, String> {
    let mut out = String::from("#![allow(unused_unsafe)]\nextern crate corpus;\n\n");
    for (idx, case) in cases.iter().enumerate() {
        validate_rust_fn_path(&case.function)?;
        let arg_exprs =
            case.args.iter().map(rust_arg_expr).collect::<Result<Vec<_>, _>>()?.join(", ");
        let call = format!("unsafe {{ corpus::{}({arg_exprs}) }}", case.function);
        match (&case.expected, &case.expected_return) {
            (Expectation::Pass, Some(exp)) => {
                let ret_ty = rust_ret_type(exp)?;
                let _ = writeln!(
                    out,
                    "#[inline(never)]\npub fn call_case_{idx}() -> {ret_ty} {{\n    {call}\n}}\n"
                );
            }
            _ => {
                let _ = writeln!(
                    out,
                    "#[inline(never)]\npub fn call_case_{idx}() {{\n    let _ret = {call};\n}}\n"
                );
            }
        }
    }
    Ok(out)
}

#[cfg_attr(not(test), allow(dead_code))]
fn generate_miri_harness(cases: &[&LitmusCase]) -> Result<String, String> {
    generate_miri_harness_with_token(cases, None)
}

fn generate_miri_harness_with_token(
    cases: &[&LitmusCase],
    token: Option<&str>,
) -> Result<String, String> {
    let ret_prefix = miri_ret_prefix_for_token(token);
    let mut out = String::from("extern crate bridge;\n\nfn main() {\n");
    out.push_str("    let selector = std::env::args().nth(1).expect(\"missing case selector\");\n");
    out.push_str("    match selector.as_str() {\n");

    for (idx, case) in cases.iter().enumerate() {
        out.push_str(&format!("        {:?} => {{\n", case.id));
        match (&case.expected, &case.expected_return) {
            (Expectation::Pass, Some(exp)) => {
                let ret_ty = rust_ret_type(exp)?;
                out.push_str(&format!(
                    "            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(bridge::call_case_{idx})) {{\n\
                     \x20               Ok(ret) => {{ let ret: {ret_ty} = ret; {}; }}\n\
                     \x20               Err(_) => println!(\"{ret_prefix}PANICKED\"),\n\
                     \x20           }}\n",
                    rust_print_ret_stmt(exp, "ret", &ret_prefix)?
                ));
            }
            _ => {
                out.push_str(&format!(
                    "            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(bridge::call_case_{idx})) {{\n\
                     \x20               Ok(()) => println!(\"{ret_prefix}UNEXPECTED_RETURN\"),\n\
                     \x20               Err(_) => println!(\"{ret_prefix}PANICKED\"),\n\
                     \x20           }}\n"
                ));
            }
        }
        out.push_str("        }\n");
    }

    out.push_str("        other => panic!(\"unknown differential case selector: {other}\"),\n");
    out.push_str("    }\n}\n");
    Ok(out)
}

fn rust_arg_expr(val: &MirValue) -> Result<String, String> {
    match val {
        MirValue::Int { int_kind, bits } => Ok(int_kind.format_rust_literal(*bits)),
        MirValue::Bool { value } => Ok(value.to_string()),
        MirValue::Char { scalar } => {
            char::from_u32(*scalar).ok_or_else(|| format!("invalid Unicode scalar {scalar}"))?;
            Ok(format!("char::from_u32({scalar}u32).unwrap()"))
        }
        MirValue::Ordering { value } => Ok(value.to_rust_expr().to_owned()),
        MirValue::Unit => Ok("()".to_owned()),
        MirValue::Enum { enum_type, variant, .. } => {
            validate_rust_ident(enum_type, "enum name")?;
            validate_rust_ident(variant, "enum variant")?;
            Ok(format!("corpus::{enum_type}::{variant}"))
        }
        MirValue::OverflowPair { .. } => {
            Err("OverflowPair is not a supported Miri harness input type in Stage 1".to_owned())
        }
    }
}

fn rust_ret_type(shape: &MirValue) -> Result<String, String> {
    match shape {
        MirValue::Int { int_kind, .. } => Ok(int_kind.rust_name().to_owned()),
        MirValue::Bool { .. } => Ok("bool".to_owned()),
        MirValue::Char { .. } => Ok("char".to_owned()),
        MirValue::Ordering { .. } => Ok("core::cmp::Ordering".to_owned()),
        MirValue::Unit => Ok("()".to_owned()),
        MirValue::OverflowPair { int_kind, .. } => Ok(format!("({}, bool)", int_kind.rust_name())),
        MirValue::Enum { .. } => Err("Enum expected_return is not supported in Stage 1".to_owned()),
    }
}

fn rust_print_ret_stmt(shape: &MirValue, var: &str, ret_prefix: &str) -> Result<String, String> {
    match shape {
        MirValue::Int { int_kind, .. } => {
            Ok(format!("println!(\"{ret_prefix}INT:{}:{{}}\", {var})", int_kind.rust_name()))
        }
        MirValue::Bool { .. } => Ok(format!("println!(\"{ret_prefix}BOOL:{{}}\", {var})")),
        MirValue::Char { .. } => Ok(format!("println!(\"{ret_prefix}CHAR:{{}}\", {var} as u32)")),
        MirValue::Ordering { .. } => Ok(format!(
            "println!(\"{ret_prefix}ORDERING:{{}}\", match {var} {{ \
             core::cmp::Ordering::Less => \"less\", \
             core::cmp::Ordering::Equal => \"equal\", \
             core::cmp::Ordering::Greater => \"greater\" }})"
        )),
        MirValue::Unit => Ok(format!("let () = {var}; println!(\"{ret_prefix}UNIT\")")),
        MirValue::OverflowPair { int_kind, .. } => Ok(format!(
            "println!(\"{ret_prefix}OVF:{}:{{}}:{{}}\", {var}.0, {var}.1)",
            int_kind.rust_name()
        )),
        MirValue::Enum { .. } => Err("Enum expected_return is not supported in Stage 1".to_owned()),
    }
}

#[allow(clippy::too_many_arguments)]
fn invoke_single_miri(
    miri_bin: &Path,
    miri_sysroot: &Path,
    ld_path: &str,
    path_env: &OsString,
    harness_path: &Path,
    bridge_rlib: &Path,
    corpus_dir: &Path,
    selector: &str,
    mute_target_io: bool,
) -> Result<(Option<i32>, String, String), ObservedOutcome> {
    let bridge_dir = bridge_rlib.parent().unwrap_or_else(|| Path::new("/"));
    let mut inv = Invocation::new(
        miri_bin,
        &["--edition=2024", "--target", PINNED_MIRI_TARGET, "--error-format=json"],
    )
    .arg("--sysroot")
    .arg(miri_sysroot)
    .arg("-C")
    .arg("opt-level=0")
    .arg("-C")
    .arg("debug-assertions=no")
    .arg("-C")
    .arg("overflow-checks=no")
    .arg("-Zmiri-tree-borrows")
    .arg("-Zmiri-seed=0");
    if mute_target_io {
        inv = inv.arg("-Zmiri-mute-stdout-stderr");
    }
    inv = inv
        .arg("--crate-name")
        .arg("harness")
        .arg("--extern")
        .arg(format!("bridge={}", bridge_rlib.display()))
        .arg("-L")
        .arg(bridge_dir)
        .arg("-L")
        .arg(corpus_dir)
        .arg(harness_path)
        .arg("--")
        .arg(selector)
        .env("LD_LIBRARY_PATH", ld_path)
        .env("PATH", path_env);
    if let Some(tmp) = env::var_os("TMPDIR").filter(|v| !v.is_empty()) {
        inv = inv.env("TMPDIR", tmp);
    }

    let case_timeout = effective_timeout_secs(MIRI_CASE_TIMEOUT_SECS)
        .map_err(|detail| ObservedOutcome::ToolError { detail })?;
    let work_dir = harness_path.parent().unwrap_or_else(|| Path::new("/"));
    let out = run_supervised(&inv, work_dir, case_timeout, selector)
        .map_err(|detail| ObservedOutcome::ToolError { detail })?;
    let exit_code = match out.termination {
        Termination::Exited(status) => status.code(),
        Termination::TimedOut(status) => {
            return Err(ObservedOutcome::ToolError {
                detail: format!("miri timed out after {case_timeout}s for {selector} ({status})"),
            });
        }
        Termination::LaunchFailed(err) => {
            return Err(ObservedOutcome::ToolError {
                detail: format!("spawn miri for {selector}: {err}"),
            });
        }
    };
    Ok((
        exit_code,
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    ))
}

#[allow(clippy::too_many_arguments)]
fn run_single_miri(
    miri_bin: &Path,
    miri_sysroot: &Path,
    ld_path: &str,
    path_env: &OsString,
    harness_path: &Path,
    bridge_rlib: &Path,
    corpus_dir: &Path,
    selector: &str,
    expected_token: Option<&str>,
) -> ObservedOutcome {
    let (exit_code, stdout, stderr) = match invoke_single_miri(
        miri_bin,
        miri_sysroot,
        ld_path,
        path_env,
        harness_path,
        bridge_rlib,
        corpus_dir,
        selector,
        false,
    ) {
        Ok(res) => res,
        Err(err) => return err,
    };
    if exit_code == Some(0) {
        return parse_miri_output_with_token(exit_code, &stdout, &stderr, expected_token);
    }
    // Non-zero exits re-run with `-Zmiri-mute-stdout-stderr` so Miri's host
    // diagnostics arrive over a channel fixture code cannot write.
    let (muted_exit, _muted_stdout, muted_stderr) = match invoke_single_miri(
        miri_bin,
        miri_sysroot,
        ld_path,
        path_env,
        harness_path,
        bridge_rlib,
        corpus_dir,
        selector,
        true,
    ) {
        Ok(res) => res,
        Err(err) => return err,
    };
    if muted_exit == Some(0) {
        return ObservedOutcome::ToolError {
            detail: format!(
                "Miri non-zero exit ({exit_code:?}) for {selector} did not reproduce under -Zmiri-mute-stdout-stderr"
            ),
        };
    }
    parse_miri_output_with_token(muted_exit, "", &muted_stderr, expected_token)
}

/// Parse Miri stdout, stderr, and exit status into an [`ObservedOutcome`].
pub fn parse_miri_output(exit_code: Option<i32>, stdout: &str, stderr: &str) -> ObservedOutcome {
    parse_miri_output_with_token(exit_code, stdout, stderr, None)
}

fn parse_miri_output_with_token(
    exit_code: Option<i32>,
    stdout: &str,
    stderr: &str,
    expected_token: Option<&str>,
) -> ObservedOutcome {
    if exit_code == Some(0) {
        let prefix = miri_ret_prefix_for_token(expected_token);
        let mut matched: Option<&str> = None;
        for raw_line in stdout.lines() {
            if let Some(payload) = raw_line.strip_prefix(&prefix) {
                if matched.is_some() {
                    return ObservedOutcome::ToolError {
                        detail: format!(
                            "Miri stdout contained duplicate `{prefix}` markers; stdout={stdout:?}"
                        ),
                    };
                }
                matched = Some(payload);
            } else if expected_token.is_some()
                && (raw_line.starts_with(MIRI_RET_PREFIX)
                    || raw_line.starts_with(&format!("{MIRI_RET_STEM}:")))
            {
                return ObservedOutcome::ToolError {
                    detail: format!(
                        "Miri stdout contained unauthenticated `{MIRI_RET_STEM}` marker; stdout={stdout:?}"
                    ),
                };
            }
        }
        let Some(line) = matched else {
            return ObservedOutcome::ToolError {
                detail: format!("Miri exited 0 without `{prefix}` line; stdout={stdout:?}"),
            };
        };
        if line == "PANICKED" {
            return ObservedOutcome::Panic {
                detail: "panicked during Miri execution (caught by harness)".to_owned(),
            };
        }
        if line == "UNEXPECTED_RETURN" {
            // Represent a clean return cleanly so evaluate_case distinguishes
            // normal return from expected UB or panic.
            return ObservedOutcome::Returned { value: MirValue::Unit };
        }
        return match parse_miri_ret_line(line) {
            Ok(value) => ObservedOutcome::Returned { value },
            Err(e) => {
                ObservedOutcome::ToolError { detail: format!("parse Miri return {line:?}: {e}") }
            }
        };
    }

    if expected_token.is_some() {
        return parse_miri_json_stderr(exit_code, stderr);
    }

    if stderr.contains("error: internal compiler error:")
        || stderr.contains("thread 'rustc' panicked at ")
    {
        return ObservedOutcome::ToolError {
            detail: format!(
                "Miri compiler ICE ({:?}): {}",
                exit_code,
                stderr.lines().take(6).collect::<Vec<_>>().join(" | ")
            ),
        };
    }
    if stderr.contains("error: Undefined Behavior:") {
        let headline = stderr
            .lines()
            .find(|l| l.contains("error: Undefined Behavior:"))
            .unwrap_or("Undefined Behavior")
            .trim()
            .to_owned();
        return ObservedOutcome::UndefinedBehavior { detail: headline };
    }
    if stderr.contains("error: abnormal termination:") {
        let headline = stderr
            .lines()
            .find(|l| l.contains("error: abnormal termination:"))
            .unwrap_or("abnormal termination")
            .trim()
            .to_owned();
        return ObservedOutcome::AbnormalAbort { detail: headline };
    }
    if stderr.contains("error: unsupported operation:") {
        let headline = stderr
            .lines()
            .find(|l| l.contains("error: unsupported operation:"))
            .unwrap_or("unsupported operation")
            .trim()
            .to_owned();
        return ObservedOutcome::Unsupported { detail: headline };
    }
    if stderr.contains("panicked at ") {
        let headline = stderr
            .lines()
            .find(|l| l.contains("panicked at "))
            .unwrap_or("panicked")
            .trim()
            .to_owned();
        return ObservedOutcome::Panic { detail: headline };
    }

    ObservedOutcome::ToolError {
        detail: format!(
            "Miri exited {:?}: {}",
            exit_code,
            stderr.lines().take(6).collect::<Vec<_>>().join(" | ")
        ),
    }
}

fn is_forged_plain_diagnostic_line(line: &str) -> bool {
    let trimmed = line.trim();
    trimmed.contains("error: Undefined Behavior:")
        || trimmed.contains("error: abnormal termination:")
        || trimmed.contains("error: unsupported operation:")
        || trimmed.contains("error: internal compiler error:")
}

fn is_abort_summary_message(msg: &str) -> bool {
    msg.starts_with("aborting due to ") && msg.contains("previous error")
}

fn normalize_diag_path(path: &str) -> String {
    path.replace('\\', "/")
}

fn path_matches_isolated_harness(path: &str) -> bool {
    let norm = normalize_diag_path(path);
    norm == "h/harness.rs" || norm.ends_with("/h/harness.rs")
}

fn is_harness_like_diag_path(path: &str) -> bool {
    let norm = normalize_diag_path(path);
    let base = norm.rsplit('/').next().unwrap_or("");
    base == "harness.rs"
        || base.starts_with("harness_")
        || base.starts_with("fuzz_miri_harness_")
        || norm.starts_with("sec_")
        || norm.contains("/sec_")
}

fn backtrace_note_references_active_harness(msg: &str) -> bool {
    if !msg.starts_with("stack backtrace:") {
        return false;
    }
    msg.lines().any(|line| {
        let Some(rest) = line.trim().strip_prefix("at ") else {
            return false;
        };
        let mut path_part = rest.split_once(": ").map_or(rest, |(head, _)| head);
        for _ in 0..2 {
            if let Some((head, tail)) = path_part.rsplit_once(':')
                && !tail.is_empty()
                && tail.bytes().all(|b| b.is_ascii_digit())
            {
                path_part = head;
            } else {
                break;
            }
        }
        path_matches_isolated_harness(path_part.trim())
    })
}

fn validate_diagnostic_origin(obj: &Value, msg: &str) -> Result<(), String> {
    let Some(spans) = obj.get("spans").and_then(Value::as_array) else {
        return Err("missing diagnostic spans array".to_owned());
    };
    let Some(children) = obj.get("children").and_then(Value::as_array) else {
        return Err("missing diagnostic children array".to_owned());
    };
    if !obj.get("rendered").is_some_and(Value::is_string) {
        return Err("missing diagnostic rendered text".to_owned());
    }
    let mut saw_active_harness = false;
    for span in spans {
        let Some(fname) = span.get("file_name").and_then(Value::as_str) else {
            return Err("diagnostic span missing file_name".to_owned());
        };
        if path_matches_isolated_harness(fname) {
            saw_active_harness = true;
        } else if is_harness_like_diag_path(fname) {
            return Err(format!("diagnostic span `{fname}` does not match isolated harness path"));
        }
    }
    for child in children {
        if child.get("level").and_then(Value::as_str) == Some("note")
            && let Some(cmsg) = child.get("message").and_then(Value::as_str)
            && backtrace_note_references_active_harness(cmsg)
        {
            saw_active_harness = true;
        }
    }
    if !msg.starts_with("internal compiler error:") && !saw_active_harness {
        return Err("diagnostic lacked stack frame or span from active isolated harness".to_owned());
    }
    Ok(())
}

fn parse_miri_json_stderr(exit_code: Option<i32>, stderr: &str) -> ObservedOutcome {
    if stderr.contains("thread 'rustc' panicked at ") {
        return ObservedOutcome::ToolError {
            detail: format!(
                "Miri compiler ICE ({:?}): {}",
                exit_code,
                stderr.lines().take(6).collect::<Vec<_>>().join(" | ")
            ),
        };
    }

    let mut fatal_errors: Vec<String> = Vec::new();
    let mut saw_abort_summary = false;
    let mut saw_plain_panic = false;

    for raw_line in stderr.lines() {
        let trimmed = raw_line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if let Ok(val) = serde_json::from_str::<Value>(trimmed)
            && val.get("$message_type").and_then(Value::as_str) == Some("diagnostic")
        {
            if val.get("level").and_then(Value::as_str) == Some("error") {
                let Some(msg) = val.get("message").and_then(Value::as_str) else {
                    return ObservedOutcome::ToolError {
                        detail: format!("Miri JSON error diagnostic missing message: {trimmed}"),
                    };
                };
                if is_abort_summary_message(msg) {
                    saw_abort_summary = true;
                } else {
                    if let Err(err) = validate_diagnostic_origin(&val, msg) {
                        return ObservedOutcome::ToolError {
                            detail: format!("Miri diagnostic failed schema/origin check: {err}"),
                        };
                    }
                    fatal_errors.push(msg.to_owned());
                }
            }
            continue;
        }
        if is_forged_plain_diagnostic_line(trimmed) {
            return ObservedOutcome::ToolError {
                detail: format!(
                    "Miri stderr contained unauthenticated plain-text diagnostic: {trimmed:?}"
                ),
            };
        }
        if trimmed.contains("panicked at ") {
            saw_plain_panic = true;
        }
    }

    if fatal_errors.len() > 1 {
        return ObservedOutcome::ToolError {
            detail: format!(
                "Miri stderr contained multiple fatal error diagnostics: {fatal_errors:?}"
            ),
        };
    }
    if let Some(msg) = fatal_errors.into_iter().next() {
        if saw_plain_panic || !saw_abort_summary {
            return ObservedOutcome::ToolError {
                detail: format!(
                    "Miri diagnostic `{msg}` lacked clean aborting summary or collided with target panic"
                ),
            };
        }
        if msg.starts_with("internal compiler error:") {
            return ObservedOutcome::ToolError {
                detail: format!("Miri compiler ICE ({exit_code:?}): error: {msg}"),
            };
        }
        if msg.starts_with("Undefined Behavior:") {
            return ObservedOutcome::UndefinedBehavior { detail: format!("error: {msg}") };
        }
        if msg.starts_with("abnormal termination:") {
            return ObservedOutcome::AbnormalAbort { detail: format!("error: {msg}") };
        }
        if msg.starts_with("unsupported operation:") {
            return ObservedOutcome::Unsupported { detail: format!("error: {msg}") };
        }
        return ObservedOutcome::ToolError {
            detail: format!("Miri exited {exit_code:?}: error: {msg}"),
        };
    }

    if exit_code == Some(101) && saw_plain_panic {
        let headline = stderr
            .lines()
            .find(|l| l.contains("panicked at "))
            .unwrap_or("panicked")
            .trim()
            .to_owned();
        return ObservedOutcome::Panic { detail: headline };
    }

    ObservedOutcome::ToolError {
        detail: format!(
            "Miri exited {:?}: {}",
            exit_code,
            stderr.lines().take(6).collect::<Vec<_>>().join(" | ")
        ),
    }
}

pub fn parse_miri_ret_line(line: &str) -> Result<MirValue, String> {
    if line == "UNIT" {
        return Ok(MirValue::Unit);
    }
    if let Some(rest) = line.strip_prefix("INT:") {
        let (kind_raw, dec_raw) =
            rest.split_once(':').ok_or_else(|| format!("malformed INT payload {rest:?}"))?;
        let int_kind = IntKind::parse_rust_name(kind_raw)?;
        let bits = int_kind.parse_decimal_bits(dec_raw)?;
        return Ok(MirValue::Int { int_kind, bits });
    }
    if let Some(rest) = line.strip_prefix("BOOL:") {
        return match rest.trim() {
            "true" => Ok(MirValue::Bool { value: true }),
            "false" => Ok(MirValue::Bool { value: false }),
            _ => Err(format!("invalid BOOL payload {rest:?}")),
        };
    }
    if let Some(rest) = line.strip_prefix("CHAR:") {
        let scalar: u32 =
            rest.trim().parse().map_err(|e| format!("invalid CHAR scalar {rest:?}: {e}"))?;
        char::from_u32(scalar).ok_or_else(|| format!("CHAR {scalar} is not a Unicode scalar"))?;
        return Ok(MirValue::Char { scalar });
    }
    if let Some(rest) = line.strip_prefix("ORDERING:") {
        return Ok(MirValue::Ordering { value: OrderingKind::parse(rest)? });
    }
    if let Some(rest) = line.strip_prefix("OVF:") {
        let mut parts = rest.splitn(3, ':');
        let kind_raw = parts.next().ok_or_else(|| format!("malformed OVF payload {rest:?}"))?;
        let dec_raw = parts.next().ok_or_else(|| format!("malformed OVF payload {rest:?}"))?;
        let ovf_raw = parts.next().ok_or_else(|| format!("malformed OVF payload {rest:?}"))?;
        let int_kind = IntKind::parse_rust_name(kind_raw)?;
        let bits = int_kind.parse_decimal_bits(dec_raw)?;
        let overflow = match ovf_raw.trim() {
            "true" => true,
            "false" => false,
            _ => return Err(format!("invalid OVF flag {ovf_raw:?}")),
        };
        return Ok(MirValue::OverflowPair { int_kind, bits, overflow });
    }
    Err(format!("unknown Miri return line {line:?}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_miri_return_lines() {
        assert_eq!(
            parse_miri_output(Some(0), "ANNEAL_MIRI_RET=INT:i32:-20\n", ""),
            ObservedOutcome::Returned {
                value: MirValue::Int { int_kind: IntKind::I32, bits: (-20i32 as u32) as u128 }
            }
        );
        assert_eq!(
            parse_miri_output(Some(0), "ANNEAL_MIRI_RET=OVF:u64:4:true\n", ""),
            ObservedOutcome::Returned {
                value: MirValue::OverflowPair { int_kind: IntKind::U64, bits: 4, overflow: true }
            }
        );
        assert_eq!(
            parse_miri_output(Some(0), "ANNEAL_MIRI_RET=ORDERING:less\n", ""),
            ObservedOutcome::Returned { value: MirValue::Ordering { value: OrderingKind::Less } }
        );
        let dup = parse_miri_output(
            Some(0),
            "ANNEAL_MIRI_RET=INT:u32:99\nANNEAL_MIRI_RET=INT:u32:7\n",
            "",
        );
        assert!(matches!(dup, ObservedOutcome::ToolError { .. }), "{dup:?}");
        let forged_bare = parse_miri_output_with_token(
            Some(0),
            "ANNEAL_MIRI_RET=INT:u32:99\nANNEAL_MIRI_RET:deadbeef=INT:u32:7\n",
            "",
            Some("deadbeef"),
        );
        assert!(matches!(forged_bare, ObservedOutcome::ToolError { .. }), "{forged_bare:?}");
        let forged_tok = parse_miri_output_with_token(
            Some(0),
            "ANNEAL_MIRI_RET:badtok=INT:u32:99\n",
            "",
            Some("deadbeef"),
        );
        assert!(matches!(forged_tok, ObservedOutcome::ToolError { .. }), "{forged_tok:?}");
        let valid_tok = parse_miri_output_with_token(
            Some(0),
            "ANNEAL_MIRI_RET:deadbeef=INT:u32:7\n",
            "",
            Some("deadbeef"),
        );
        assert_eq!(
            valid_tok,
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );
    }

    #[test]
    fn parses_miri_ub_abort_unsupported_and_panic() {
        let ub = parse_miri_output(
            Some(1),
            "",
            "error: Undefined Behavior: dividing by zero\n  --> src/ub.rs:5:1\n",
        );
        assert!(matches!(ub, ObservedOutcome::UndefinedBehavior { .. }));

        let abort = parse_miri_output(
            Some(1),
            "",
            "error: abnormal termination: the program aborted execution\n",
        );
        assert!(matches!(abort, ObservedOutcome::AbnormalAbort { .. }));

        let unsup = parse_miri_output(
            Some(1),
            "",
            "error: unsupported operation: calling foreign function\n",
        );
        assert!(matches!(unsup, ObservedOutcome::Unsupported { .. }));

        let panic = parse_miri_output(
            Some(101),
            "",
            "thread 'main' (1) panicked at src/main.rs:2:5:\nexplicit panic\n",
        );
        assert!(
            matches!(panic, ObservedOutcome::Panic { detail } if detail.contains("panicked at "))
        );

        // Genuine UB alongside panic text must not masquerade as benign Panic.
        let ub_with_panic = parse_miri_output(
            Some(101),
            "",
            "panicked at foo\nerror: Undefined Behavior: entering unreachable code\n",
        );
        assert!(matches!(ub_with_panic, ObservedOutcome::UndefinedBehavior { .. }));

        // Compiler/Miri ICEs must never masquerade as target-program panics.
        let ice = parse_miri_output(Some(101), "", "error: internal compiler error: broken MIR\n");
        assert!(matches!(ice, ObservedOutcome::ToolError { .. }));

        let rustc_panic = parse_miri_output(
            Some(101),
            "",
            "thread 'rustc' panicked at compiler/rustc_mir_transform/src/lib.rs:1:1:\nICE\n",
        );
        assert!(matches!(rustc_panic, ObservedOutcome::ToolError { .. }));

        // Authenticated JSON stderr checks: reject plain-text fixture
        // spoofing, mismatched harness spans, and duplicate diagnostics,
        // while classifying genuine `--error-format=json` Miri output and
        // `PANICKED` stdout tokens.
        let tok_panicked = parse_miri_output_with_token(
            Some(0),
            "ANNEAL_MIRI_RET:deadbeef=PANICKED\n",
            "error: Undefined Behavior: arithmetic overflow\n",
            Some("deadbeef"),
        );
        assert!(matches!(tok_panicked, ObservedOutcome::Panic { .. }), "{tok_panicked:?}");

        let forged_plain_ub = parse_miri_output_with_token(
            Some(101),
            "",
            "error: Undefined Behavior: arithmetic overflow\n\
             thread 'main' (1) panicked at src/main.rs:2:5:\nexplicit panic\n",
            Some("deadbeef"),
        );
        assert!(
            matches!(forged_plain_ub, ObservedOutcome::ToolError { .. }),
            "{forged_plain_ub:?}"
        );

        let forged_plain_abort = parse_miri_output_with_token(
            Some(1),
            "",
            "error: Undefined Behavior: forged\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"abnormal termination: the program aborted execution\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[{\"message\":\"stack backtrace:\\n0: main\\n    at /tmp/h/harness.rs:5:1: 5:10\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
            Some("deadbeef"),
        );
        assert!(
            matches!(forged_plain_abort, ObservedOutcome::ToolError { .. }),
            "{forged_plain_abort:?}"
        );

        let multi_json_err = parse_miri_output_with_token(
            Some(1),
            "",
            "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: forged\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/h/harness.rs\"}],\"children\":[],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"abnormal termination: the program aborted execution\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[{\"message\":\"stack backtrace:\\n0: main\\n    at /tmp/h/harness.rs:5:1: 5:10\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
            Some("deadbeef"),
        );
        assert!(matches!(multi_json_err, ObservedOutcome::ToolError { .. }), "{multi_json_err:?}");

        let wrong_harness_span = parse_miri_output_with_token(
            Some(1),
            "",
            "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: entering unreachable code\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/other/harness.rs\"}],\"children\":[],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
            Some("deadbeef"),
        );
        assert!(
            matches!(wrong_harness_span, ObservedOutcome::ToolError { .. }),
            "{wrong_harness_span:?}"
        );

        // Forged JSON diagnostics emitting empty `spans: []` or only corpus
        // spans without an authenticated harness stack frame must fail closed.
        let forged_empty_spans = parse_miri_output_with_token(
            Some(1),
            "",
            "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: forged\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
            Some("deadbeef"),
        );
        assert!(
            matches!(forged_empty_spans, ObservedOutcome::ToolError { .. }),
            "{forged_empty_spans:?}"
        );

        let forged_corpus_only = parse_miri_output_with_token(
            Some(1),
            "",
            "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: forged\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
            Some("deadbeef"),
        );
        assert!(
            matches!(forged_corpus_only, ObservedOutcome::ToolError { .. }),
            "{forged_corpus_only:?}"
        );

        let wrong_backtrace_tok = parse_miri_output_with_token(
            Some(1),
            "",
            "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: entering unreachable code\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[{\"message\":\"stack backtrace:\\n0: corpus::f\\n    at /tmp/c/corpus.rs:3:5: 3:20\\n1: main\\n    at /tmp/other/harness.rs:5:1: 5:10\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
            Some("deadbeef"),
        );
        assert!(
            matches!(wrong_backtrace_tok, ObservedOutcome::ToolError { .. }),
            "{wrong_backtrace_tok:?}"
        );

        let valid_json_ub = parse_miri_output_with_token(
            Some(1),
            "",
            "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: entering unreachable code\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[{\"message\":\"stack backtrace:\\n0: corpus::ub\\n    at /tmp/c/corpus.rs:3:5: 3:20\\n1: bridge::call_case_0\\n    at /tmp/b/bridge.rs:4:5: 4:20\\n2: main\\n    at /tmp/h/harness.rs:5:1: 5:10\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
            Some("deadbeef"),
        );
        assert!(
            matches!(
                valid_json_ub,
                ObservedOutcome::UndefinedBehavior { ref detail }
                    if detail == "error: Undefined Behavior: entering unreachable code"
            ),
            "{valid_json_ub:?}"
        );
    }

    #[test]
    fn offline_cargo_config_escapes_vendor_path() {
        let rendered = render_vendored_cargo_config(Path::new(
            "/tmp/rust/lib/rustlib/src/rust/library/vendor",
        ))
        .expect("render vendored Cargo config");
        assert!(rendered.contains("replace-with = \"vendored-sources\""), "{rendered}");
        assert!(
            rendered.contains("directory = \"/tmp/rust/lib/rustlib/src/rust/library/vendor\""),
            "{rendered}"
        );
    }

    #[test]
    fn missing_miri_or_vendor_sysroot_fails_closed() {
        let dir = tempfile::tempdir().unwrap();
        let err = MiriSession::prepare(dir.path(), dir.path()).unwrap_err();
        assert!(err.contains("lacks `bin/miri`"), "{err}");

        let fake_sysroot = dir.path().join("sys");
        fs::create_dir_all(fake_sysroot.join("bin")).unwrap();
        fs::write(fake_sysroot.join("bin/miri"), b"fake").unwrap();
        fs::write(fake_sysroot.join("bin/rustc"), b"fake").unwrap();
        fs::write(fake_sysroot.join("bin/cargo"), b"fake").unwrap();
        let cache = dir.path().join("cache");
        let err_vendor = build_offline_miri_sysroot(
            &fake_sysroot,
            &fake_sysroot.join("bin/miri"),
            &cache.join("miri-out"),
        )
        .unwrap_err();
        assert!(err_vendor.contains("vendored `rust-src` crates"), "{err_vendor}");

        let bogus = dir.path().join("bogus-miri");
        fs::create_dir_all(&bogus).unwrap();
        let err_explicit = MiriSession::prepare_with_env(&fake_sysroot, &cache, |k| {
            (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&bogus))
        })
        .unwrap_err();
        assert!(err_explicit.contains("does not contain `lib/rustlib`"), "{err_explicit}");

        // Ambient `MIRI_SYSROOT` is ignored rather than substituting a sysroot.
        let ambient_miri = dir.path().join("ambient-miri");
        fs::create_dir_all(ambient_miri.join("lib/rustlib")).unwrap();
        let err_ambient = MiriSession::prepare_with_env(&fake_sysroot, &cache, |k| {
            (k == "MIRI_SYSROOT").then(|| OsString::from(&ambient_miri))
        })
        .unwrap_err();
        assert!(!err_ambient.contains("MIRI_SYSROOT"), "{err_ambient}");

        #[cfg(unix)]
        {
            let sym = dir.path().join("sym-miri-sysroot");
            std::os::unix::fs::symlink(&ambient_miri, &sym).unwrap();
            let err_sym = MiriSession::prepare_with_env(&fake_sysroot, &cache, |k| {
                (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&sym))
            })
            .unwrap_err();
            assert!(err_sym.contains("must not be a symlink"), "{err_sym}");
        }
    }

    #[test]
    fn rustc_version_tag_requires_metadata_and_harness_emits_typed_ret() {
        let dir = tempfile::tempdir().unwrap();
        let fake_rustc = dir.path().join("rustc");
        fs::write(&fake_rustc, b"fake-rustc").unwrap();

        assert!(parse_rustc_version_tag(&fake_rustc, "rustc 1.98.0-nightly\nhost: x\n").is_err());
        assert!(parse_rustc_version_tag(&fake_rustc, "commit-hash: abcdef123456\n").is_err());
        let tag = parse_rustc_version_tag(
            &fake_rustc,
            "commit-hash: abcdef1234567890\nhost: x86_64-unknown-linux-gnu\n",
        )
        .unwrap();
        assert!(tag.starts_with("abcdef123456-x86_64-unknown-linux-gnu-"), "{tag}");

        let src_file = dir.path().join("f.rs");
        fs::write(&src_file, "#![no_std]\npub fn f() -> u32 { 7 }\n").unwrap();
        let case = LitmusCase {
            id: "c1".to_owned(),
            source_rel: PathBuf::from("f.rs"),
            source_abs: src_file,
            function: "f".to_owned(),
            category: "arith".to_owned(),
            expected: Expectation::Pass,
            miri_ub_contains: None,
            expected_miri: None,
            args: vec![],
            expected_return: Some(MirValue::Int { int_kind: IntKind::U32, bits: 7 }),
            fuel: 100,
        };
        let bridge = generate_miri_bridge(&[&case]).unwrap();
        assert!(bridge.contains("pub fn call_case_0() -> u32"), "{bridge}");
        assert!(bridge.contains("unsafe { corpus::f() }"), "{bridge}");
        let harness = generate_miri_harness(&[&case]).unwrap();
        assert!(harness.contains("bridge::call_case_0"), "{harness}");

        let bad_case = LitmusCase { function: "evil_macro!".to_owned(), ..case };
        assert!(generate_miri_bridge(&[&bad_case]).is_err());
    }

    #[test]
    fn miri_setup_fingerprint_tracks_binaries_and_rust_src_contents() {
        let dir = tempfile::tempdir().unwrap();
        let sys = dir.path().join("sysroot");
        let bin_dir = sys.join("bin");
        let vendor_dir = sys.join("lib/rustlib/src/rust/library/vendor/dep_a");
        let core_dir = sys.join("lib/rustlib/src/rust/library/core/src");
        fs::create_dir_all(&bin_dir).unwrap();
        fs::create_dir_all(&vendor_dir).unwrap();
        fs::create_dir_all(&core_dir).unwrap();

        fs::write(bin_dir.join("rustc"), b"rustc-v1").unwrap();
        fs::write(bin_dir.join("cargo"), b"cargo-v1").unwrap();
        fs::write(bin_dir.join("miri"), b"miri-v1").unwrap();
        fs::write(bin_dir.join("cargo-miri"), b"cargo-miri-v1").unwrap();
        fs::write(vendor_dir.join("lib.rs"), b"pub fn dep() {}\n").unwrap();
        fs::write(core_dir.join("lib.rs"), b"#![no_std]\n").unwrap();

        let ver_tag = "abcdef123456-x86_64-unknown-linux-gnu-001122334455";
        let base_fp = compute_miri_setup_input_sha256(&sys, ver_tag).unwrap();
        assert_eq!(base_fp.len(), 64);

        // Mutating `miri` without changing `rustc` must change the fingerprint.
        fs::write(bin_dir.join("miri"), b"miri-v2").unwrap();
        let miri_fp = compute_miri_setup_input_sha256(&sys, ver_tag).unwrap();
        assert_ne!(miri_fp, base_fp);

        // Mutating `cargo-miri` must change the fingerprint.
        fs::write(bin_dir.join("cargo-miri"), b"cargo-miri-v2").unwrap();
        let cmiri_fp = compute_miri_setup_input_sha256(&sys, ver_tag).unwrap();
        assert_ne!(cmiri_fp, miri_fp);

        // Mutating vendored `rust-src` must change the fingerprint.
        fs::write(vendor_dir.join("lib.rs"), b"pub fn dep() { let _ = 1; }\n").unwrap();
        let src_fp = compute_miri_setup_input_sha256(&sys, ver_tag).unwrap();
        assert_ne!(src_fp, cmiri_fp);

        // Explicit `ANNEAL_MIRI_SYSROOT` must carry a matching ready stamp.
        let explicit_sys = dir.path().join("explicit-miri-sysroot");
        fs::create_dir_all(explicit_sys.join("lib/rustlib")).unwrap();
        let unstamped = verify_explicit_miri_sysroot_stamp(&explicit_sys, ver_tag, &src_fp);
        assert!(unstamped.is_err());

        fs::write(
            explicit_sys.join(".anneal-miri-ready"),
            expected_miri_ready_stamp(ver_tag, &src_fp),
        )
        .unwrap();
        verify_explicit_miri_sysroot_stamp(&explicit_sys, ver_tag, &src_fp).unwrap();

        // Stale stamp after `miri` or `rust-src` mutation must fail closed.
        assert!(verify_explicit_miri_sysroot_stamp(&explicit_sys, ver_tag, &cmiri_fp).is_err());

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            let fake_rustc = bin_dir.join("rustc");
            fs::write(
                &fake_rustc,
                b"#!/bin/sh\nprintf 'commit-hash: abcdef1234567890\\nhost: x86_64-unknown-linux-gnu\\n'\n",
            )
            .unwrap();
            fs::set_permissions(&fake_rustc, fs::Permissions::from_mode(0o755)).unwrap();

            let real_tag = rustc_version_tag(&sys).unwrap();
            let real_sha = compute_miri_setup_input_sha256(&sys, &real_tag).unwrap();
            let cache = dir.path().join("cache");

            // Stale stamp from pre-executable `rustc` is rejected by
            // `prepare_with_env` before accepting `ANNEAL_MIRI_SYSROOT`.
            let Err(stale_err) = MiriSession::prepare_with_env(&sys, &cache, |k| {
                (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&explicit_sys))
            }) else {
                panic!("stale explicit stamp must fail");
            };
            assert!(stale_err.contains("setup stamp does not match"), "{stale_err}");

            // Refreshing the stamp to match current inputs succeeds.
            fs::write(
                explicit_sys.join(".anneal-miri-ready"),
                expected_miri_ready_stamp(&real_tag, &real_sha),
            )
            .unwrap();
            let session = MiriSession::prepare_with_env(&sys, &cache, |k| {
                (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&explicit_sys))
            })
            .expect("matching explicit stamp must succeed");
            assert_eq!(session.miri_sysroot, fs::canonicalize(&explicit_sys).unwrap());
        }

        // Missing `cargo-miri` fails closed.
        fs::remove_file(bin_dir.join("cargo-miri")).unwrap();
        assert!(compute_miri_setup_input_sha256(&sys, ver_tag).is_err());
    }
}
