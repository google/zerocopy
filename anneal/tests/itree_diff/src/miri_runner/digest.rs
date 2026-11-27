// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Streaming SHA-256 digests of toolchain binaries, host libraries, and
//! `rust-src` and built sysroot trees that bind cached Miri sysroots.

use super::*;

pub(super) fn sha256_file(path: &Path) -> Result<String, String> {
    let mut buf = vec![0u8; STREAM_HASH_BUF_BYTES];
    let (_, digest) = stream_sha256_file_with_buf(path, &mut buf)?;
    Ok(sha256_hex(&digest))
}

pub(super) fn sha256_file_pair(primary: &Path, secondary: &Path) -> Result<String, String> {
    let mut buf = vec![0u8; STREAM_HASH_BUF_BYTES];
    let (len_a, sha_a) = stream_sha256_file_with_buf(primary, &mut buf)?;
    let (len_b, sha_b) = stream_sha256_file_with_buf(secondary, &mut buf)?;
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-rustc-wrapper-pair-v1\0");
    hasher.update(len_a.to_le_bytes());
    hasher.update(sha_a);
    hasher.update(len_b.to_le_bytes());
    hasher.update(sha_b);
    Ok(sha256_hex(&hasher.finalize()))
}

fn stream_sha256_file_with_buf(path: &Path, buf: &mut [u8]) -> Result<(u64, [u8; 32]), String> {
    let mut file = File::open(path).map_err(|e| format!("open {}: {e}", path.display()))?;
    let mut hasher = Sha256::new();
    let mut total_bytes = 0u64;
    loop {
        match file.read(buf) {
            Ok(0) => break,
            Ok(n) => {
                hasher.update(&buf[..n]);
                total_bytes += n as u64;
            }
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(format!("read {}: {e}", path.display())),
        }
    }
    let digest = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    Ok((total_bytes, out))
}

type HashedTreeEntry = (String, u64, [u8; 32]);

fn stream_hash_sorted_entries(
    entries: &[(String, PathBuf)],
) -> Result<Vec<HashedTreeEntry>, String> {
    if entries.is_empty() {
        return Ok(Vec::new());
    }
    let workers = thread::available_parallelism()
        .map(|n| n.get().clamp(1, MAX_TREE_HASH_WORKERS))
        .unwrap_or(1)
        .min(entries.len());
    if workers <= 1 {
        let mut buf = vec![0u8; STREAM_HASH_BUF_BYTES];
        return entries
            .iter()
            .map(|(rel, path)| {
                let (len, sha) = stream_sha256_file_with_buf(path, &mut buf)?;
                Ok((rel.clone(), len, sha))
            })
            .collect();
    }

    let chunk_size = entries.len().div_ceil(workers);
    let chunk_results: Vec<Result<Vec<HashedTreeEntry>, String>> = thread::scope(|scope| {
        let mut handles = Vec::with_capacity(workers);
        for chunk in entries.chunks(chunk_size) {
            handles.push(scope.spawn(move || {
                let mut buf = vec![0u8; STREAM_HASH_BUF_BYTES];
                let mut local = Vec::with_capacity(chunk.len());
                for (rel, path) in chunk {
                    let (len, sha) = stream_sha256_file_with_buf(path, &mut buf)?;
                    local.push((rel.clone(), len, sha));
                }
                Ok(local)
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().unwrap_or_else(|_| Err("Miri tree hash worker panicked".to_string())))
            .collect()
    });

    let mut out = Vec::with_capacity(entries.len());
    for res in chunk_results {
        out.extend(res?);
    }
    Ok(out)
}

fn has_host_lib_extension(file_name: &str) -> bool {
    let ext = Path::new(file_name).extension().and_then(|s| s.to_str());
    matches!(ext, Some("so" | "dylib" | "dll" | "a")) || file_name.contains(".so.")
}

pub(super) fn compute_rustc_host_libs_digest(
    rust_sysroot: &Path,
    backing_sysroot: Option<&Path>,
) -> Result<String, String> {
    let canon_sysroot = fs::canonicalize(rust_sysroot)
        .map_err(|e| format!("canonicalize rust sysroot {}: {e}", rust_sysroot.display()))?;
    let lib_dir = canon_sysroot.join("lib");
    if !lib_dir.is_dir() {
        return Err(format!("missing sysroot `lib` directory at {}", lib_dir.display()));
    }

    let mut sorted: BTreeMap<String, PathBuf> = BTreeMap::new();
    for entry in
        fs::read_dir(&lib_dir).map_err(|e| format!("read_dir {}: {e}", lib_dir.display()))?
    {
        let entry = entry.map_err(|e| format!("iterate {}: {e}", lib_dir.display()))?;
        let raw_name = entry.file_name();
        let name = raw_name
            .to_str()
            .ok_or_else(|| {
                format!("non-UTF-8 library name in {}: {raw_name:?}", lib_dir.display())
            })?
            .to_string();
        if !has_host_lib_extension(&name) {
            continue;
        }
        let path = entry.path();
        let sym_meta = fs::symlink_metadata(&path)
            .map_err(|e| format!("inspect host lib {}: {e}", path.display()))?;
        let resolved = if sym_meta.file_type().is_symlink() {
            let target = fs::canonicalize(&path)
                .map_err(|e| format!("resolve host lib symlink {}: {e}", path.display()))?;
            let in_backing = backing_sysroot.is_some_and(|b| target.starts_with(b));
            if !target.starts_with(&canon_sysroot) && !in_backing {
                return Err(format!(
                    "host lib symlink {} escapes sysroot {} -> {}",
                    path.display(),
                    canon_sysroot.display(),
                    target.display()
                ));
            }
            target
        } else {
            path
        };
        let meta = fs::metadata(&resolved)
            .map_err(|e| format!("stat host lib {}: {e}", resolved.display()))?;
        if meta.is_file() {
            sorted.insert(name, resolved);
        }
    }

    let entries: Vec<(String, PathBuf)> = sorted.into_iter().collect();
    let hashed = stream_hash_sorted_entries(&entries)?;
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-miri-host-libs-v1\0");
    hasher.update((hashed.len() as u64).to_le_bytes());
    for (name, len, sha) in &hashed {
        update_len_prefixed(&mut hasher, name.as_bytes());
        hasher.update(len.to_le_bytes());
        hasher.update(sha);
    }
    Ok(sha256_hex(&hasher.finalize()))
}

/// Ordered search directories used both to locate and hash `cargo-miri` in
/// [`MiriSysrootIdentity`] and to construct the child `PATH` for offline Miri
/// sysroot preparation (`cargo_bin` sibling dir first, then `miri_bin` sibling
/// dir, `<rust_sysroot>/bin`, and ambient `PATH`).
pub fn miri_setup_search_dirs(
    rust_sysroot: &Path,
    miri_bin: &Path,
    cargo_bin: Option<&Path>,
    path_var: Option<&std::ffi::OsStr>,
) -> Vec<PathBuf> {
    let mut dirs = Vec::new();
    if let Some(dir) = cargo_bin.and_then(Path::parent).filter(|p| !p.as_os_str().is_empty()) {
        dirs.push(dir.to_path_buf());
    }
    if let Some(dir) = miri_bin.parent().filter(|p| !p.as_os_str().is_empty())
        && !dirs.iter().any(|d| d == dir)
    {
        dirs.push(dir.to_path_buf());
    }
    let sr_bin = rust_sysroot.join("bin");
    if !dirs.iter().any(|d| d == &sr_bin) {
        dirs.push(sr_bin);
    }
    if cargo_bin.is_some()
        && let Some(pv) = path_var
    {
        for dir in env::split_paths(pv) {
            if !dir.as_os_str().is_empty() && !dirs.iter().any(|d| d == &dir) {
                dirs.push(dir);
            }
        }
    }
    dirs
}

fn is_executable_file(path: &Path) -> bool {
    let Ok(meta) = fs::metadata(path) else {
        return false;
    };
    if !meta.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        meta.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        true
    }
}

/// Resolve the exact `cargo-miri` executable that offline Miri sysroot setup
/// invokes and [`MiriSysrootIdentity`] hashes.
pub fn resolve_cargo_miri_binary_with_suffix(
    rust_sysroot: &Path,
    miri_bin: &Path,
    cargo_bin: Option<&Path>,
    exe_suffix: &str,
) -> Option<PathBuf> {
    resolve_cargo_miri_binary_with_path_and_suffix(
        rust_sysroot,
        miri_bin,
        cargo_bin,
        env::var_os("PATH").as_deref(),
        exe_suffix,
    )
}

/// Environment-parameterized variant of
/// [`resolve_cargo_miri_binary_with_suffix`].
pub fn resolve_cargo_miri_binary_with_path_and_suffix(
    rust_sysroot: &Path,
    miri_bin: &Path,
    cargo_bin: Option<&Path>,
    path_var: Option<&std::ffi::OsStr>,
    exe_suffix: &str,
) -> Option<PathBuf> {
    let cm_exe = exe_name_for_suffix("cargo-miri", exe_suffix);
    for dir in miri_setup_search_dirs(rust_sysroot, miri_bin, cargo_bin, path_var) {
        let cand = dir.join(&cm_exe);
        if is_executable_file(&cand) {
            return canonicalize_preserving_rustup_proxy_with_suffix(
                &cand,
                Some(rust_sysroot),
                "cargo-miri",
                exe_suffix,
            )
            .ok()
            .or(Some(cand));
        }
    }
    None
}

fn walk_rust_src_tree(
    current_dir: &Path,
    rel_prefix: &str,
    canon_root: &Path,
    backing_src_root: Option<&Path>,
    active_dirs: &mut BTreeSet<PathBuf>,
    out: &mut Vec<(String, PathBuf)>,
) -> Result<(), String> {
    let mut dir_entries = Vec::new();
    for entry in
        fs::read_dir(current_dir).map_err(|e| format!("read_dir {}: {e}", current_dir.display()))?
    {
        let entry = entry.map_err(|e| format!("iterate {}: {e}", current_dir.display()))?;
        dir_entries.push(entry);
    }
    dir_entries.sort_by_key(|e| e.file_name());

    for entry in dir_entries {
        let raw_name = entry.file_name();
        let name = raw_name.to_str().ok_or_else(|| {
            format!("non-UTF-8 path entry in {}: {raw_name:?}", current_dir.display())
        })?;
        let path = entry.path();
        let sym_meta =
            fs::symlink_metadata(&path).map_err(|e| format!("inspect {}: {e}", path.display()))?;
        let ft = sym_meta.file_type();
        if name == ".git" && ft.is_dir() {
            continue;
        }
        let rel_path =
            if rel_prefix.is_empty() { name.to_string() } else { format!("{rel_prefix}/{name}") };

        if ft.is_symlink() {
            let target_canon = fs::canonicalize(&path)
                .map_err(|e| format!("resolve symlink {}: {e}", path.display()))?;
            let in_backing = backing_src_root.is_some_and(|b| target_canon.starts_with(b));
            if !target_canon.starts_with(canon_root) && !in_backing {
                return Err(format!(
                    "`rust-src` symlink {} escapes canonical `rust-src` root {} -> {}",
                    path.display(),
                    canon_root.display(),
                    target_canon.display()
                ));
            }
            let target_meta = fs::metadata(&target_canon)
                .map_err(|e| format!("stat symlink target {}: {e}", target_canon.display()))?;
            if target_meta.is_file() {
                out.push((rel_path, target_canon));
            } else if target_meta.is_dir() {
                if name == ".git" {
                    continue;
                }
                if !active_dirs.insert(target_canon.clone()) {
                    return Err(format!(
                        "`rust-src` symlink directory cycle at {}",
                        path.display()
                    ));
                }
                walk_rust_src_tree(
                    &target_canon,
                    &rel_path,
                    canon_root,
                    backing_src_root,
                    active_dirs,
                    out,
                )?;
                active_dirs.remove(&target_canon);
            } else {
                return Err(format!(
                    "unsupported special file symlink target {} in `rust-src` at {}",
                    target_canon.display(),
                    path.display()
                ));
            }
        } else if ft.is_dir() {
            let dir_canon = fs::canonicalize(&path)
                .map_err(|e| format!("canonicalize directory {}: {e}", path.display()))?;
            if !active_dirs.insert(dir_canon.clone()) {
                return Err(format!("`rust-src` directory cycle at {}", path.display()));
            }
            walk_rust_src_tree(&path, &rel_path, canon_root, backing_src_root, active_dirs, out)?;
            active_dirs.remove(&dir_canon);
        } else if ft.is_file() {
            out.push((rel_path, path));
        } else {
            return Err(format!("unsupported special file in `rust-src`: {}", path.display()));
        }
    }
    Ok(())
}

pub(super) fn compute_rust_src_digest(
    rust_sysroot: &Path,
    backing_sysroot: Option<&Path>,
) -> Result<String, String> {
    let rust_src = rust_sysroot.join("lib/rustlib/src/rust");
    if !rust_src.is_dir() {
        return Err(format!("missing `rust-src` directory at {}", rust_src.display()));
    }
    let core_toml = rust_src.join("library/core/Cargo.toml");
    let alloc_toml = rust_src.join("library/alloc/Cargo.toml");
    if !core_toml.is_file() || !alloc_toml.is_file() {
        return Err(format!(
            "`rust-src` at {} missing required `library/core/Cargo.toml` or `library/alloc/Cargo.toml`",
            rust_src.display()
        ));
    }
    let root_lock = rust_src.join("Cargo.lock");
    let lib_lock = rust_src.join("library/Cargo.lock");
    if !root_lock.is_file() && !lib_lock.is_file() {
        return Err(format!(
            "`rust-src` at {} missing `Cargo.lock` (checked `Cargo.lock` and `library/Cargo.lock`)",
            rust_src.display()
        ));
    }

    let canon_root = fs::canonicalize(&rust_src)
        .map_err(|e| format!("canonicalize `rust-src` {}: {e}", rust_src.display()))?;
    let backing_src_root = match backing_sysroot {
        Some(b) => fs::canonicalize(b.join("lib/rustlib/src/rust")).ok(),
        None => None,
    };
    let mut active_dirs = BTreeSet::from([canon_root.clone()]);
    let mut files = Vec::new();
    walk_rust_src_tree(
        &canon_root,
        "",
        &canon_root,
        backing_src_root.as_deref(),
        &mut active_dirs,
        &mut files,
    )?;
    files.sort_by(|a, b| a.0.cmp(&b.0));

    let hashed = stream_hash_sorted_entries(&files)?;
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-rust-src-v2\0");
    hasher.update((hashed.len() as u64).to_le_bytes());
    for (rel, byte_len, file_sha) in &hashed {
        update_len_prefixed(&mut hasher, rel.as_bytes());
        hasher.update(byte_len.to_le_bytes());
        hasher.update(file_sha);
    }
    Ok(sha256_hex(&hasher.finalize()))
}

fn update_len_prefixed(hasher: &mut Sha256, field: &[u8]) {
    hasher.update((field.len() as u64).to_le_bytes());
    hasher.update(field);
}

fn walk_regular_built_sysroot_tree(
    dir: &Path,
    prefix: &str,
    out: &mut Vec<(String, PathBuf)>,
) -> Result<(), String> {
    let mut entries = Vec::new();
    for entry in fs::read_dir(dir).map_err(|e| format!("read_dir {}: {e}", dir.display()))? {
        let entry = entry.map_err(|e| format!("iterate {}: {e}", dir.display()))?;
        let raw = entry.file_name();
        let name = raw
            .to_str()
            .ok_or_else(|| format!("non-UTF-8 entry in {}: {raw:?}", dir.display()))?
            .to_string();
        entries.push((name, entry.path()));
    }
    entries.sort_by(|a, b| a.0.cmp(&b.0));

    for (name, path) in entries {
        let sym = fs::symlink_metadata(&path)
            .map_err(|e| format!("inspect built sysroot entry {}: {e}", path.display()))?;
        let ft = sym.file_type();
        let rel = if prefix.is_empty() { name } else { format!("{prefix}/{name}") };
        if ft.is_symlink() {
            return Err(format!("unexpected symlink in built Miri sysroot: {}", path.display()));
        } else if ft.is_dir() {
            walk_regular_built_sysroot_tree(&path, &rel, out)?;
        } else if ft.is_file() {
            out.push((rel, path));
        } else {
            return Err(format!(
                "unsupported special file in built Miri sysroot: {}",
                path.display()
            ));
        }
    }
    Ok(())
}

pub(super) fn compute_built_miri_sysroot_digest(
    sysroot_dir: &Path,
    target: &str,
) -> Result<(usize, String), String> {
    let rustlib_dir = sysroot_dir.join("lib/rustlib");
    let rustlib_sym = fs::symlink_metadata(&rustlib_dir)
        .map_err(|e| format!("inspect Miri rustlib {}: {e}", rustlib_dir.display()))?;
    if !rustlib_sym.file_type().is_dir() {
        return Err(format!("Miri rustlib {} is not a real directory", rustlib_dir.display()));
    }
    let target_lib_prefix = format!("{target}/lib/");
    let mut files = Vec::new();
    walk_regular_built_sysroot_tree(&rustlib_dir, "", &mut files)?;
    files.sort_by(|a, b| a.0.cmp(&b.0));

    let hashed = stream_hash_sorted_entries(&files)?;
    let mut saw_target_crate = false;
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-miri-built-v1\0");
    hasher.update((hashed.len() as u64).to_le_bytes());
    for (rel, byte_len, file_sha) in &hashed {
        let is_compiled_lib =
            matches!(Path::new(rel).extension().and_then(|s| s.to_str()), Some("rlib" | "rmeta"));
        if is_compiled_lib && *byte_len == 0 {
            return Err(format!("empty compiled Miri sysroot artifact `{rel}`"));
        }
        if is_compiled_lib && rel.starts_with(&target_lib_prefix) {
            saw_target_crate = true;
        }
        update_len_prefixed(&mut hasher, rel.as_bytes());
        hasher.update(byte_len.to_le_bytes());
        hasher.update(file_sha);
    }
    if !saw_target_crate {
        return Err(format!(
            "built Miri sysroot at {} missing non-empty `{target_lib_prefix}*.rlib`/`.rmeta`",
            sysroot_dir.display()
        ));
    }
    Ok((hashed.len(), sha256_hex(&hasher.finalize())))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn compute_composite_miri_sha256(
    schema_version: u32,
    target: &str,
    rustc_vv: &str,
    rustc_bin_sha256: &str,
    rustc_host_libs_sha256: &str,
    miri_version_verbose: &str,
    miri_bin_sha256: &str,
    cargo_bin_sha256: Option<&str>,
    cargo_miri_bin_sha256: Option<&str>,
    rust_src_sha256: &str,
) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"anneal-itree-miri-sysroot-v4\0");
    hasher.update(schema_version.to_le_bytes());
    update_len_prefixed(&mut hasher, target.as_bytes());
    update_len_prefixed(&mut hasher, rustc_vv.as_bytes());
    update_len_prefixed(&mut hasher, rustc_bin_sha256.as_bytes());
    update_len_prefixed(&mut hasher, rustc_host_libs_sha256.as_bytes());
    update_len_prefixed(&mut hasher, miri_version_verbose.as_bytes());
    update_len_prefixed(&mut hasher, miri_bin_sha256.as_bytes());
    match cargo_bin_sha256 {
        Some(cb) => {
            hasher.update([1u8]);
            update_len_prefixed(&mut hasher, cb.as_bytes());
        }
        None => {
            hasher.update([0u8]);
        }
    }
    match cargo_miri_bin_sha256 {
        Some(cm) => {
            hasher.update([1u8]);
            update_len_prefixed(&mut hasher, cm.as_bytes());
        }
        None => {
            hasher.update([0u8]);
        }
    }
    update_len_prefixed(&mut hasher, rust_src_sha256.as_bytes());
    sha256_hex(&hasher.finalize())
}
