// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Offline Miri sysroot preparation, its readiness stamp, and the
//! supervised child processes that build it.

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

pub(super) fn render_vendored_cargo_config(vendor_dir: &Path) -> Result<String, String> {
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

pub(super) fn run_supervised(
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

pub(super) fn build_child_path(primary_bin: &Path) -> Result<OsString, String> {
    let mut path_entries = vec![primary_bin.to_path_buf()];
    if let Some(existing) = env::var_os("PATH") {
        path_entries.extend(env::split_paths(&existing));
    }
    env::join_paths(path_entries).map_err(|e| format!("join PATH entries: {e}"))
}

pub(super) fn parse_rustc_version_tag(rustc: &Path, text: &str) -> Result<String, String> {
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

pub(super) fn expected_miri_ready_stamp(ver_tag: &str, setup_sha: &str) -> String {
    format!("anneal-miri-setup-v2:{ver_tag}:{setup_sha}\n")
}

pub(super) fn verify_explicit_miri_sysroot_stamp(
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
pub(super) fn compute_miri_setup_input_sha256(
    rust_sysroot: &Path,
    ver_tag: &str,
) -> Result<String, String> {
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

pub(super) fn rustc_version_tag(rust_sysroot: &Path) -> Result<String, String> {
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

pub(super) fn build_offline_miri_sysroot(
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

pub(super) fn join_library_path(primary: &Path) -> String {
    match env::var("LD_LIBRARY_PATH") {
        Ok(existing) if !existing.is_empty() => format!("{}:{existing}", primary.display()),
        _ => primary.display().to_string(),
    }
}
