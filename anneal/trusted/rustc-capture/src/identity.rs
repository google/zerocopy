// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pre-capture compiler identity verification and Linux driver residency.
//!
//! All checks in this module use 100% safe Rust without FFI or extra crates.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

use sha2::{Digest, Sha256};

use crate::ir::{DriverIdentity, DriverLinkage};
use crate::{Failure, ir};

/// Dynamic-linker environment variables that inject foreign code or alter
/// symbol resolution regardless of `DT_RUNPATH` and must never be present in
/// the capture process environment.
const FORBIDDEN_LOADER_ENV_VARS: &[&str] = &[
    "LD_PRELOAD",
    "LD_AUDIT",
    "LD_DYNAMIC_WEAK",
    "LD_USE_LOAD_BIAS",
    "DYLD_INSERT_LIBRARIES",
    "DYLD_FORCE_FLAT_NAMESPACE",
];

/// Device and inode identity `(st_dev, st_ino)` for a regular file or
/// directory.
#[cfg(unix)]
pub(crate) type DevIno = (u64, u64);

/// Authenticated compiler identity and pinned sysroot directory inode returned
/// by [`verify_compiler`] for downstream TOCTOU checks and manifest emission.
pub(crate) struct VerifiedCompiler {
    #[cfg(unix)]
    pub(crate) sysroot_id: DevIno,
    pub(crate) rustc_sha256: String,
    pub(crate) driver: DriverIdentity,
}

/// Format a SHA-256 digest as lowercase hex using a byte loop compatible with
/// both `sha2` 0.10 and 0.11.
fn digest_to_hex(bytes: &[u8]) -> String {
    let mut hex = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        let _ = write!(hex, "{byte:02x}");
    }
    hex
}

pub(crate) fn sha256_bytes(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    digest_to_hex(digest.as_ref())
}

fn sha256_reader<R: io::Read>(mut reader: R) -> io::Result<String> {
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let read = reader.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    let digest = hasher.finalize();
    Ok(digest_to_hex(digest.as_ref()))
}

#[cfg(unix)]
pub(crate) fn regular_file_dev_ino(path: &Path) -> io::Result<DevIno> {
    use std::os::unix::fs::MetadataExt;

    let meta = fs::metadata(path)?;
    if !meta.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "path is not a regular file",
        ));
    }
    Ok((meta.dev(), meta.ino()))
}

#[cfg(unix)]
pub(crate) fn dir_dev_ino(path: &Path) -> io::Result<DevIno> {
    use std::os::unix::fs::MetadataExt;

    let meta = fs::metadata(path)?;
    if !meta.is_dir() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "path is not a directory",
        ));
    }
    Ok((meta.dev(), meta.ino()))
}

/// Normalize a sysroot path lexically to an absolute logical path without
/// dereferencing symlinks, preserving virtual symlink-forest topologies such
/// as `<sysroot>/bin/rustc` beside `<sysroot>/lib/rustlib`, while still
/// verifying that the resolved target exists and is a directory.
pub(crate) fn normalize_logical_sysroot(raw: &Path) -> Result<PathBuf, Failure> {
    let absolute = std::path::absolute(raw).map_err(Failure::io)?;
    let logical = absolute
        .normalize_lexically()
        .map_err(|_| Failure::tool(format!("cannot normalize sysroot path: {}", raw.display())))?;
    let meta = fs::metadata(&logical).map_err(Failure::io)?;
    if !meta.is_dir() {
        return Err(Failure::tool(format!(
            "sysroot path is not a directory: {}",
            logical.display()
        )));
    }
    Ok(logical)
}

/// Reject ambient dynamic-linker injection variables from an environment pair
/// iterator.
///
/// Rejection triggers on key presence regardless of value because loaders treat
/// empty values as active for presence-triggered flags such as glibc
/// `LD_DYNAMIC_WEAK` and macOS `DYLD_FORCE_FLAT_NAMESPACE`.
fn reject_loader_env_in<I, K, V>(vars: I) -> Result<(), Failure>
where
    I: IntoIterator<Item = (K, V)>,
    K: AsRef<OsStr>,
    V: AsRef<OsStr>,
{
    for (key, _value) in vars {
        let Some(key_str) = key.as_ref().to_str() else {
            continue;
        };
        if FORBIDDEN_LOADER_ENV_VARS.contains(&key_str) {
            return Err(Failure::tool(format!(
                "forbidden dynamic linker environment variable is set: {key_str}"
            )));
        }
    }
    Ok(())
}

fn reject_ambient_loader_env() -> Result<(), Failure> {
    reject_loader_env_in(std::env::vars_os())
}

/// Open a regular file once, verify regular-file metadata on the open handle,
/// and return its SHA-256 digest together with `(st_dev, st_ino)` on Unix.
#[cfg(unix)]
fn open_regular_and_hash(path: &Path) -> io::Result<(String, DevIno)> {
    use std::os::unix::fs::MetadataExt;

    let mut file = fs::File::open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "path is not a regular file",
        ));
    }
    let dev_ino = (meta.dev(), meta.ino());
    let digest = sha256_reader(&mut file)?;
    Ok((digest, dev_ino))
}

#[cfg(not(unix))]
fn open_regular_and_hash(path: &Path) -> io::Result<(String, ())> {
    let mut file = fs::File::open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "path is not a regular file",
        ));
    }
    let digest = sha256_reader(&mut file)?;
    Ok((digest, ()))
}

struct RustcVerboseVersion {
    version: String,
    commit: String,
    host: String,
}

fn parse_rustc_version_verbose(text: &str) -> Result<RustcVerboseVersion, Failure> {
    let mut version = None;
    let mut commit = None;
    let mut host = None;
    for line in text.lines() {
        if version.is_none()
            && let Some(rest) = line.strip_prefix("rustc ")
            && !rest.is_empty()
        {
            version = Some(rest.to_owned());
        } else if let Some(rest) = line.strip_prefix("commit-hash: ")
            && !rest.is_empty()
        {
            commit = Some(rest.to_owned());
        } else if let Some(rest) = line.strip_prefix("host: ")
            && !rest.is_empty()
        {
            host = Some(rest.to_owned());
        }
    }
    Ok(RustcVerboseVersion {
        version: version.ok_or_else(|| {
            Failure::tool("sysroot rustc --version --verbose omitted version header")
        })?,
        commit: commit.ok_or_else(|| {
            Failure::tool("sysroot rustc --version --verbose omitted commit-hash")
        })?,
        host: host
            .ok_or_else(|| Failure::tool("sysroot rustc --version --verbose omitted host"))?,
    })
}

/// Restrict host triples to single path-safe component characters so `host`
/// cannot traverse outside `<sysroot>/lib/rustlib/`.
fn is_valid_host_triple(host: &str) -> bool {
    !host.is_empty()
        && host != "."
        && host != ".."
        && host
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'-'))
}

fn is_rustc_driver_filename(name: &str) -> bool {
    name.starts_with("librustc_driver-") && name.ends_with(".so")
}

/// Return `true` for shared-library filenames belonging to the Rust compiler,
/// LLVM, or Rust standard-library toolchain closure (covering both `.so` and
/// versioned SONAMEs such as `libLLVM.so.22.1-rust-1.98.0-nightly`).
#[cfg(any(target_os = "linux", test))]
fn is_toolchain_dso_filename(name: &str) -> bool {
    let is_shared_obj = name.ends_with(".so") || name.contains(".so.");
    is_shared_obj
        && (name.starts_with("librustc_driver-")
            || name.starts_with("librustc_")
            || name.starts_with("libLLVM")
            || name.starts_with("libstd-")
            || name.starts_with("libtest-")
            || name.starts_with("libproc_macro-"))
}

/// Extract the UTF-8 basename of a raw `/proc/self/maps` pathname slice.
#[cfg(any(target_os = "linux", test))]
fn maps_pathname_basename(pathname: &[u8]) -> Option<&str> {
    let stripped = pathname.strip_suffix(b" (deleted)").unwrap_or(pathname);
    let base = match stripped.iter().rposition(|&b| b == b'/') {
        Some(pos) => &stripped[pos + 1..],
        None => stripped,
    };
    std::str::from_utf8(base).ok()
}

/// Standard OS C/loader library roots allowed for non-toolchain runtime DSOs
/// (`libc`, `libm`, `libdl`, `libgcc_s`, `libz`, `ld-linux`, etc.).
///
/// Blanket `/nix/store/` is intentionally excluded so unrelated user-added Nix
/// store paths cannot shadow non-toolchain DSOs (`libz.so.1`, `libgcc_s.so.1`,
/// etc.); Nix-packaged binaries authenticate their exact store library
/// directories via `PT_INTERP` and `DT_RUNPATH`/`DT_RPATH`.
#[cfg(any(target_os = "linux", test))]
const ALLOWED_SYSTEM_RUNTIME_PREFIXES: &[&[u8]] = &[
    b"/lib/",
    b"/lib64/",
    b"/usr/lib/",
    b"/usr/lib64/",
];

/// Return `true` if a non-deleted `/proc/self/maps` pathname refers to a
/// standard system C/loader runtime library (or sibling of a custom ELF
/// `PT_INTERP` loader directory) and is strictly NOT a Rust/LLVM toolchain
/// DSO.
#[cfg(any(target_os = "linux", test))]
fn is_allowed_system_runtime_path(pathname: &[u8], pt_interp_dirs: &[PathBuf]) -> bool {
    if pathname.ends_with(b" (deleted)") || !pathname.starts_with(b"/") {
        return false;
    }
    if maps_pathname_basename(pathname).is_some_and(is_toolchain_dso_filename) {
        return false;
    }
    if ALLOWED_SYSTEM_RUNTIME_PREFIXES
        .iter()
        .any(|prefix| pathname.starts_with(prefix))
    {
        return true;
    }
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        let path = Path::new(OsStr::from_bytes(pathname));
        pt_interp_dirs.iter().any(|dir| path.starts_with(dir))
    }
    #[cfg(not(unix))]
    {
        let _ = pt_interp_dirs;
        false
    }
}

/// Broad host directories that must never be admitted as custom `PT_INTERP`
/// runtime library prefixes (mirroring `cargo-anneal`'s
/// `validate_toolchain_mount_dir` guard).
#[cfg(any(target_os = "linux", test))]
const FORBIDDEN_BROAD_PT_INTERP_DIRS: &[&str] = &[
    "/bin",
    "/boot",
    "/dev",
    "/etc",
    "/home",
    "/mnt",
    "/media",
    "/nix/store",
    "/opt",
    "/proc",
    "/root",
    "/run",
    "/sbin",
    "/srv",
    "/sys",
    "/tmp",
    "/usr",
    "/usr/bin",
    "/usr/local",
    "/usr/local/bin",
    "/usr/share",
    "/Users",
    "/var",
    "/var/tmp",
];

/// Return `true` if `dir` is a dedicated, normalized absolute directory that
/// does not match a broad host prefix or encompass `$HOME` or the current
/// working directory.
#[cfg(any(target_os = "linux", test))]
fn is_allowed_pt_interp_dir(dir: &Path) -> bool {
    use std::path::Component;

    if !dir.is_absolute() {
        return false;
    }
    if dir
        .components()
        .any(|c| matches!(c, Component::CurDir | Component::ParentDir))
    {
        return false;
    }
    let normal_count = dir
        .components()
        .filter(|c| matches!(c, Component::Normal(_)))
        .count();
    if normal_count < 2
        || FORBIDDEN_BROAD_PT_INTERP_DIRS
            .iter()
            .any(|bad| dir == Path::new(bad))
    {
        return false;
    }
    if let Some(home_os) = std::env::var_os("HOME")
        && !home_os.is_empty()
    {
        let home_raw = PathBuf::from(home_os);
        let canon_home = fs::canonicalize(&home_raw).unwrap_or(home_raw);
        if canon_home.starts_with(dir) {
            return false;
        }
    }
    if let Ok(cwd) = std::env::current_dir() {
        let canon_cwd = fs::canonicalize(&cwd).unwrap_or(cwd);
        if canon_cwd.starts_with(dir) {
            return false;
        }
    }
    true
}

/// Translate an ELF64 virtual address range `[vaddr, vaddr + len)` into a file
/// offset using the binary's `PT_LOAD` program headers.
#[cfg(all(any(target_os = "linux", test), unix))]
fn elf64_vaddr_to_offset(loads: &[(u64, u64, u64)], vaddr: u64, len: u64) -> Option<u64> {
    for &(p_vaddr, p_offset, p_filesz) in loads {
        let Some(rel) = vaddr.checked_sub(p_vaddr) else {
            continue;
        };
        let Some(end) = rel.checked_add(len) else {
            continue;
        };
        if end <= p_filesz {
            return p_offset.checked_add(rel);
        }
    }
    None
}

/// Expand ELF `$ORIGIN` / `${ORIGIN}` tokens in a single `DT_RUNPATH` /
/// `DT_RPATH` entry relative to `origin_dir`, lexically normalizing any
/// `..` segments (such as `$ORIGIN/../rust/lib`) without touching the
/// filesystem, and insert validated logical and canonical directories.
#[cfg(all(any(target_os = "linux", test), unix))]
fn insert_validated_runpath_dir(entry: &str, origin_dir: Option<&Path>, dirs: &mut BTreeSet<PathBuf>) {
    if entry.is_empty() {
        return;
    }
    let expanded = if entry.contains("$ORIGIN") || entry.contains("${ORIGIN}") {
        let Some(origin_str) = origin_dir.and_then(|p| p.to_str()) else {
            return;
        };
        entry
            .replace("${ORIGIN}", origin_str)
            .replace("$ORIGIN", origin_str)
    } else {
        entry.to_owned()
    };
    let candidate = Path::new(&expanded);
    if !candidate.is_absolute() {
        return;
    }
    if let Ok(normalized) = candidate.normalize_lexically()
        && is_allowed_pt_interp_dir(&normalized)
    {
        dirs.insert(normalized);
    }
    if let Ok(canon) = fs::canonicalize(candidate)
        && is_allowed_pt_interp_dir(&canon)
    {
        dirs.insert(canon);
    }
}

/// Result of inspecting an ELF64 little-endian binary's `PT_INTERP` and
/// `DT_RUNPATH`/`DT_RPATH` headers.
#[cfg(any(target_os = "linux", test))]
struct Elf64PtInterp {
    has_pt_interp: bool,
    dirs: Vec<PathBuf>,
}

/// Parse an ELF64 little-endian binary's `PT_INTERP` and `PT_DYNAMIC`
/// (`DT_RUNPATH` / `DT_RPATH`) headers (optionally authenticating the opened
/// descriptor against `expected_dev_ino`) and return whether a `PT_INTERP`
/// segment exists together with the validated runtime library directories
/// (logical and canonical, deduplicated).
#[cfg(all(any(target_os = "linux", test), unix))]
fn inspect_elf64_pt_interp(
    exec_path: &Path,
    expected_dev_ino: Option<DevIno>,
) -> Option<Elf64PtInterp> {
    use std::io::{Read, Seek, SeekFrom};
    use std::os::unix::fs::MetadataExt;

    let mut file = fs::File::open(exec_path).ok()?;
    let meta = file.metadata().ok()?;
    if !meta.is_file() {
        return None;
    }
    if let Some(expected) = expected_dev_ino
        && (meta.dev(), meta.ino()) != expected
    {
        return None;
    }
    let file_len = meta.len();
    if file_len < 64 {
        return None;
    }
    let mut ehdr = [0u8; 64];
    if file.read_exact(&mut ehdr).is_err()
        || &ehdr[0..4] != b"\x7fELF"
        || ehdr[4] != 2
        || ehdr[5] != 1
    {
        return None;
    }
    let e_phoff = u64::from_le_bytes(ehdr[32..40].try_into().unwrap());
    let e_phentsize = u16::from_le_bytes(ehdr[54..56].try_into().unwrap()) as u64;
    let e_phnum = u16::from_le_bytes(ehdr[56..58].try_into().unwrap()) as u64;
    if e_phnum == 0 || e_phentsize < 56 {
        return None;
    }
    let ph_table_bytes = e_phentsize.checked_mul(e_phnum)?;
    let ph_end = e_phoff.checked_add(ph_table_bytes)?;
    if ph_end > file_len || ph_table_bytes > 4 * 1024 * 1024 {
        return None;
    }
    if file.seek(SeekFrom::Start(e_phoff)).is_err() {
        return None;
    }
    let mut table = vec![0u8; ph_table_bytes as usize];
    if file.read_exact(&mut table).is_err() {
        return None;
    }
    const PT_LOAD: u32 = 1;
    const PT_DYNAMIC: u32 = 2;
    const PT_INTERP: u32 = 3;
    let mut has_pt_interp = false;
    let mut dirs = BTreeSet::new();
    let mut loads: Vec<(u64, u64, u64)> = Vec::new();
    let mut dynamic_seg: Option<(u64, u64)> = None;
    for i in 0..(e_phnum as usize) {
        let base = i * (e_phentsize as usize);
        let p_type = u32::from_le_bytes(table[base..base + 4].try_into().unwrap());
        let p_offset = u64::from_le_bytes(table[base + 8..base + 16].try_into().unwrap());
        let p_vaddr = u64::from_le_bytes(table[base + 16..base + 24].try_into().unwrap());
        let p_filesz = u64::from_le_bytes(table[base + 32..base + 40].try_into().unwrap());
        match p_type {
            PT_LOAD => loads.push((p_vaddr, p_offset, p_filesz)),
            PT_DYNAMIC => {
                if dynamic_seg.is_none() {
                    dynamic_seg = Some((p_offset, p_filesz));
                }
            }
            PT_INTERP if !has_pt_interp => {
                has_pt_interp = true;
                if p_filesz == 0 || p_filesz > 4096 {
                    continue;
                }
                let Some(end) = p_offset.checked_add(p_filesz) else {
                    continue;
                };
                if end > file_len || file.seek(SeekFrom::Start(p_offset)).is_err() {
                    continue;
                }
                let mut raw = vec![0u8; p_filesz as usize];
                if file.read_exact(&mut raw).is_err() {
                    continue;
                }
                let nul_pos = raw.iter().position(|&b| b == 0).unwrap_or(raw.len());
                let Ok(interp_str) = std::str::from_utf8(&raw[..nul_pos]) else {
                    continue;
                };
                if interp_str.is_empty() {
                    continue;
                }
                let interp_path = Path::new(interp_str);
                if let Some(parent) = interp_path.parent()
                    && is_allowed_pt_interp_dir(parent)
                {
                    dirs.insert(parent.to_path_buf());
                }
                if let Ok(canon) = fs::canonicalize(interp_path)
                    && let Some(parent) = canon.parent()
                    && is_allowed_pt_interp_dir(parent)
                {
                    dirs.insert(parent.to_path_buf());
                }
            }
            _ => {}
        }
    }

    // Parse `DT_RUNPATH` (preferred per ELF spec) or `DT_RPATH` from
    // `PT_DYNAMIC` so Nix-packaged and `$ORIGIN`-relative binaries authenticate
    // their pinned C runtime library directories without opening all of
    // `/nix/store/`.
    if let Some((dyn_off, dyn_sz)) = dynamic_seg
        && (16..=1024 * 1024).contains(&dyn_sz)
        && let Some(dyn_end) = dyn_off.checked_add(dyn_sz)
        && dyn_end <= file_len
        && file.seek(SeekFrom::Start(dyn_off)).is_ok()
    {
        let mut dyn_bytes = vec![0u8; dyn_sz as usize];
        if file.read_exact(&mut dyn_bytes).is_ok() {
            const DT_NULL: i64 = 0;
            const DT_STRTAB: i64 = 5;
            const DT_STRSZ: i64 = 10;
            const DT_RPATH: i64 = 15;
            const DT_RUNPATH: i64 = 29;
            let mut strtab_vaddr = None;
            let mut strsz = None;
            let mut rpath_off = None;
            let mut runpath_off = None;
            for chunk in dyn_bytes.chunks_exact(16) {
                let d_tag = i64::from_le_bytes(chunk[0..8].try_into().unwrap());
                let d_val = u64::from_le_bytes(chunk[8..16].try_into().unwrap());
                match d_tag {
                    DT_NULL => break,
                    DT_STRTAB => strtab_vaddr = Some(d_val),
                    DT_STRSZ => strsz = Some(d_val),
                    DT_RPATH => rpath_off = Some(d_val),
                    DT_RUNPATH => runpath_off = Some(d_val),
                    _ => {}
                }
            }
            if let (Some(sv), Some(ss), Some(path_off)) =
                (strtab_vaddr, strsz, runpath_off.or(rpath_off))
                && ss > 0
                && ss <= 4 * 1024 * 1024
                && path_off < ss
                && let Some(strtab_file_off) = elf64_vaddr_to_offset(&loads, sv, ss)
                && let Some(strtab_end) = strtab_file_off.checked_add(ss)
                && strtab_end <= file_len
                && file.seek(SeekFrom::Start(strtab_file_off)).is_ok()
            {
                let mut strtab = vec![0u8; ss as usize];
                if file.read_exact(&mut strtab).is_ok() {
                    let tail = &strtab[path_off as usize..];
                    let nul = tail.iter().position(|&b| b == 0).unwrap_or(tail.len());
                    if let Ok(runpath_str) = std::str::from_utf8(&tail[..nul]) {
                        let canon_exec = fs::canonicalize(exec_path).ok();
                        let origin_dir = canon_exec
                            .as_deref()
                            .and_then(Path::parent)
                            .or_else(|| exec_path.parent());
                        for entry in runpath_str.split(':') {
                            insert_validated_runpath_dir(entry, origin_dir, &mut dirs);
                        }
                    }
                }
            }
        }
    }

    Some(Elf64PtInterp {
        has_pt_interp,
        dirs: dirs.into_iter().collect(),
    })
}

/// Resolve validated custom dynamic-loader runtime library directories for
/// both direct launches (`/proc/self/exe` is the capture binary) and explicit
/// dynamic-loader launches (`/proc/self/exe` is `ld-linux-*.so.*` without a
/// `PT_INTERP` segment while `self_addr` maps the capture binary itself).
#[cfg(all(any(target_os = "linux", test), unix))]
fn resolve_runtime_pt_interp_dirs(
    maps_bytes: &[u8],
    self_addr: usize,
    self_exe: &Path,
) -> Vec<PathBuf> {
    resolve_runtime_pt_interp_dirs_with(maps_bytes, self_addr, self_exe, &LiveProcess::default())
}

/// [`resolve_runtime_pt_interp_dirs`] against an explicit [`ProcessView`].
#[cfg(all(any(target_os = "linux", test), unix))]
fn resolve_runtime_pt_interp_dirs_with(
    maps_bytes: &[u8],
    self_addr: usize,
    self_exe: &Path,
    process: &dyn ProcessView,
) -> Vec<PathBuf> {
    use std::os::unix::ffi::OsStrExt;

    let mut dirs = BTreeSet::new();
    let Ok((self_dev_ino, self_vma_path)) =
        resolve_mapping_dev_ino(maps_bytes, self_addr, "capture executable")
    else {
        return Vec::new();
    };
    // Classify the launch by either identity under which `/proc/self/maps`
    // may report `/proc/self/exe` (see `regular_file_maps_ids`), so a direct
    // launch on Btrfs is not mistaken for an explicit dynamic-loader launch.
    // A superblock-only match may name a different file, but the direct-launch
    // branch then reads `PT_INTERP` only on an exact `fstat(2)` match, so a
    // misclassification can only drop directories, never add them.
    let self_exe_is_capture = regular_file_maps_ids(self_exe, process)
        .is_ok_and(|(stat_id, superblock_id)| {
            stat_id == self_dev_ino || superblock_id == Some(self_dev_ino)
        });
    if self_exe_is_capture {
        if let Some(info) = inspect_elf64_pt_interp(self_exe, Some(self_dev_ino)) {
            dirs.extend(info.dirs);
        }
    } else {
        // Explicit dynamic-loader launch (`ld-linux.so /path/to/binary`):
        // read `PT_INTERP` from the capture binary VMA (verified by open-FD
        // `(st_dev, st_ino)`), and when `/proc/self/exe` is an ELF dynamic
        // linker without `PT_INTERP`, also admit its validated parent library
        // directory so custom-sysroot loaders and sibling `libc.so.6` resolve.
        let vma_path = Path::new(OsStr::from_bytes(self_vma_path));
        if let Some(info) = inspect_elf64_pt_interp(vma_path, Some(self_dev_ino)) {
            dirs.extend(info.dirs);
        }
        if let Some(loader_info) = inspect_elf64_pt_interp(self_exe, None)
            && !loader_info.has_pt_interp
        {
            if let Ok(canon_loader) = fs::canonicalize(self_exe)
                && let Some(parent) = canon_loader.parent()
                && is_allowed_pt_interp_dir(parent)
            {
                dirs.insert(parent.to_path_buf());
            }
            if self_exe != Path::new("/proc/self/exe")
                && let Some(parent) = self_exe.parent()
                && is_allowed_pt_interp_dir(parent)
            {
                dirs.insert(parent.to_path_buf());
            }
        }
    }
    dirs.into_iter().collect()
}

/// Encode Linux kernel `(major, minor)` device numbers into the userspace
/// `st_dev` (`dev_t`) representation returned by `MetadataExt::dev()`.
#[cfg(any(target_os = "linux", test))]
fn linux_makedev(major: u64, minor: u64) -> u64 {
    ((major & 0xffff_f000) << 32)
        | ((major & 0x0000_0fff) << 8)
        | ((minor & 0xffff_ff00) << 12)
        | (minor & 0x0000_00ff)
}

#[cfg(any(target_os = "linux", test))]
#[derive(Debug, PartialEq, Eq)]
struct MapsEntry<'a> {
    start: usize,
    end: usize,
    perms: &'a [u8],
    offset: u64,
    dev: u64,
    inode: u64,
    pathname: Option<&'a [u8]>,
}

/// Parse one raw `/proc/self/maps` line without requiring UTF-8 or trimming
/// trailing bytes from file paths.
///
/// The kernel escapes only newlines in printed pathnames, so trailing spaces
/// and carriage returns are part of the file's name and must be kept.
#[cfg(any(target_os = "linux", test))]
fn parse_maps_line(raw_line: &[u8]) -> Option<MapsEntry<'_>> {
    let mut rest = strip_leading_ascii_ws(raw_line);
    let mut fields: [&[u8]; 5] = [b""; 5];
    for (idx, slot) in fields.iter_mut().enumerate() {
        let end = rest
            .iter()
            .position(|b| b.is_ascii_whitespace())
            .unwrap_or(rest.len());
        if end == 0 {
            return None;
        }
        *slot = &rest[..end];
        rest = strip_leading_ascii_ws(&rest[end..]);
        if idx < 4 && rest.is_empty() {
            return None;
        }
    }
    let (start_hex, end_hex) = split_once_byte(fields[0], b'-')?;
    let start = parse_hex_usize(start_hex)?;
    let end = parse_hex_usize(end_hex)?;
    if start >= end {
        return None;
    }
    let offset = parse_hex_u64(fields[2])?;
    let (maj_hex, min_hex) = split_once_byte(fields[3], b':')?;
    let major = parse_hex_u64(maj_hex)?;
    let minor = parse_hex_u64(min_hex)?;
    let inode = parse_dec_u64(fields[4])?;
    let pathname = if rest.is_empty() { None } else { Some(rest) };
    Some(MapsEntry {
        start,
        end,
        perms: fields[1],
        offset,
        dev: linux_makedev(major, minor),
        inode,
        pathname,
    })
}

#[cfg(any(target_os = "linux", test))]
fn strip_leading_ascii_ws(mut bytes: &[u8]) -> &[u8] {
    while let Some((first, tail)) = bytes.split_first() {
        if first.is_ascii_whitespace() {
            bytes = tail;
        } else {
            break;
        }
    }
    bytes
}

#[cfg(any(target_os = "linux", test))]
fn split_once_byte(bytes: &[u8], needle: u8) -> Option<(&[u8], &[u8])> {
    let pos = bytes.iter().position(|&b| b == needle)?;
    Some((&bytes[..pos], &bytes[pos + 1..]))
}

#[cfg(any(target_os = "linux", test))]
fn parse_hex_usize(bytes: &[u8]) -> Option<usize> {
    let text = std::str::from_utf8(bytes).ok()?;
    usize::from_str_radix(text, 16).ok()
}

#[cfg(any(target_os = "linux", test))]
fn parse_hex_u64(bytes: &[u8]) -> Option<u64> {
    let text = std::str::from_utf8(bytes).ok()?;
    u64::from_str_radix(text, 16).ok()
}

#[cfg(any(target_os = "linux", test))]
fn parse_dec_u64(bytes: &[u8]) -> Option<u64> {
    let text = std::str::from_utf8(bytes).ok()?;
    text.parse::<u64>().ok()
}

/// Locate the executable, file-backed, non-deleted `/proc/self/maps` mapping
/// containing `target_addr` and return its kernel `(st_dev, st_ino)` together
/// with its backing pathname slice.
#[cfg(any(target_os = "linux", test))]
fn resolve_mapping_dev_ino<'a>(
    maps_bytes: &'a [u8],
    target_addr: usize,
    role: &str,
) -> Result<((u64, u64), &'a [u8]), Failure> {
    let mut found: Option<((u64, u64), &'a [u8])> = None;
    for raw_line in maps_bytes.split(|&b| b == b'\n') {
        let Some(entry) = parse_maps_line(raw_line) else {
            continue;
        };
        if !(entry.start <= target_addr && target_addr < entry.end) {
            continue;
        }
        if !entry.perms.contains(&b'x') {
            return Err(Failure::tool(format!(
                "loaded {role} mapping is not executable"
            )));
        }
        if entry.inode == 0 {
            return Err(Failure::tool(format!(
                "loaded {role} mapping is not file-backed"
            )));
        }
        let Some(pathname) = entry.pathname else {
            return Err(Failure::tool(format!(
                "loaded {role} mapping has no backing pathname"
            )));
        };
        if pathname.ends_with(b" (deleted)") {
            return Err(Failure::tool(format!(
                "loaded {role} mapping is deleted: {}",
                String::from_utf8_lossy(pathname)
            )));
        }
        let dev_ino = (entry.dev, entry.inode);
        match found {
            None => found = Some((dev_ino, pathname)),
            Some((prev, _)) if prev == dev_ino => {}
            Some(_) => {
                return Err(Failure::tool(format!(
                    "multiple overlapping {role} mappings match target address"
                )));
            }
        }
    }
    found.ok_or_else(|| {
        Failure::tool(format!(
            "cannot locate loaded {role} mapping for target address"
        ))
    })
}

/// Locate the executable, file-backed, non-deleted `/proc/self/maps` mapping
/// containing `driver_addr` and return its kernel `(st_dev, st_ino)`.
#[cfg(test)]
fn resolve_driver_mapping_dev_ino(
    maps_bytes: &[u8],
    driver_addr: usize,
) -> Result<(u64, u64), Failure> {
    resolve_mapping_dev_ino(maps_bytes, driver_addr, "rustc driver").map(|(dev_ino, _)| dev_ino)
}

/// Map from a `/proc/self/maps` identity to every sysroot library that may
/// back it. A superblock identity can be shared by several files on Btrfs and
/// multi-filesystem OverlayFS, so every candidate is kept and confirmed
/// individually.
#[cfg(all(any(target_os = "linux", test), unix))]
type SysrootLibMap = BTreeMap<DevIno, Vec<SysrootCandidate>>;

/// A sysroot library file indexed under some identity in [`SysrootLibMap`].
#[cfg(all(any(target_os = "linux", test), unix))]
struct SysrootCandidate {
    name: String,
    path: PathBuf,
    /// Whether the identity is the file's own `fstat(2)` identity, which no
    /// other file shares, rather than its superblock identity.
    exact: bool,
}

/// Every distinct `(identity, pathname)` pair of the file-backed executable
/// mappings in `/proc/self/maps`. Pathnames are kept per identity, not just
/// the first, because on Btrfs and multi-filesystem OverlayFS one identity
/// can name several files, and admission by pathname must hold for each.
#[cfg(all(any(target_os = "linux", test), unix))]
type ExecMappings = BTreeSet<(DevIno, Vec<u8>)>;

/// Collect all regular library files under `<sysroot>/lib` and
/// `<sysroot>/lib/rustlib/<host>/lib`, indexed by every `(st_dev, st_ino)`
/// under which `/proc/self/maps` may report a mapping of them (see
/// [`regular_file_maps_ids`]). Symlinks (such as virtual CAS symlink forests)
/// are followed so their backing inode matches `/proc/self/maps`.
#[cfg(all(any(target_os = "linux", test), unix))]
fn collect_sysroot_library_entries(
    sysroot: &Path,
    host: &str,
    process: &dyn ProcessView,
) -> Result<SysrootLibMap, Failure> {
    if !is_valid_host_triple(host) {
        return Err(Failure::tool(format!(
            "invalid rustc host triple: {host:?}"
        )));
    }
    let mut search_dirs = vec![sysroot.join("lib")];
    let host_lib = sysroot.join("lib/rustlib").join(host).join("lib");
    if host_lib.is_dir() {
        search_dirs.push(host_lib);
    }
    let mut entries_by_id = BTreeMap::new();
    for dir in search_dirs {
        let entries = match fs::read_dir(&dir) {
            Ok(entries) => entries,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => return Err(Failure::io(error)),
        };
        for entry in entries {
            let entry = entry.map_err(Failure::io)?;
            let path = entry.path();
            let Some(name) = path.file_name().and_then(|n| n.to_str()).map(str::to_owned) else {
                continue;
            };
            let Ok((stat_id, superblock_id)) = regular_file_maps_ids(&path, process) else {
                continue;
            };
            let ids = std::iter::once((stat_id, true)).chain(superblock_id.map(|id| (id, false)));
            for (id, exact) in ids {
                entries_by_id.entry(id).or_insert_with(Vec::new).push(SysrootCandidate {
                    name: name.clone(),
                    path: path.clone(),
                    exact,
                });
            }
        }
    }
    Ok(entries_by_id)
}

/// Return the `(st_dev, st_ino)` that `fstat(2)` reports for the regular file
/// at `path`, plus the distinct superblock identity `(s_dev, st_ino)` when the
/// two differ.
///
/// `/proc/self/maps` prints the device of the inode's superblock. `fstat(2)`
/// instead reports a per-subvolume anonymous device on Btrfs, and a per-layer
/// device on an OverlayFS whose layers span several filesystems without
/// `xino` (where `/proc/self/maps` reports the overlay's device since Linux
/// 6.8). A mapping of the file may therefore appear in `/proc/self/maps`
/// under either identity. Only the `fstat(2)` identity is unique; a match on
/// the superblock identity must be confirmed by
/// [`open_and_hash_if_dev_ino_matches`].
#[cfg(all(any(target_os = "linux", test), unix))]
fn regular_file_maps_ids(
    path: &Path,
    process: &dyn ProcessView,
) -> io::Result<(DevIno, Option<DevIno>)> {
    use std::os::unix::fs::MetadataExt;

    // Check the type before opening so a FIFO or device node in a library
    // directory is skipped instead of blocking or being opened.
    if !fs::metadata(path)?.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "path is not a regular file",
        ));
    }
    let file = fs::File::open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "path is not a regular file",
        ));
    }
    let stat_id = (meta.dev(), meta.ino());
    let superblock_id = process
        .superblock_dev(&file)
        .ok()
        .map(|dev| (dev, meta.ino()))
        .filter(|id| *id != stat_id);
    Ok((stat_id, superblock_id))
}

/// Open each `librustc_driver-*.so` under `<sysroot>/lib` or
/// `<sysroot>/lib/rustlib/<host>/lib` once, match it against the loaded
/// driver's `/proc/self/maps` identity `loaded_dev_ino` via
/// [`open_and_hash_if_dev_ino_matches`], and return the matching file's name
/// and the digest hashed from that same handle.
#[cfg(any(target_os = "linux", test))]
fn match_and_hash_sysroot_driver(
    sysroot: &Path,
    host: &str,
    loaded_dev_ino: (u64, u64),
    maps: MapsView<'_>,
) -> Result<(String, String), Failure> {
    if !is_valid_host_triple(host) {
        return Err(Failure::tool(format!(
            "invalid rustc host triple: {host:?}"
        )));
    }
    let mut search_dirs = vec![sysroot.join("lib")];
    let host_lib = sysroot.join("lib/rustlib").join(host).join("lib");
    if host_lib.is_dir() {
        search_dirs.push(host_lib);
    }
    let mut saw_candidate = false;
    for dir in search_dirs {
        let entries = match fs::read_dir(&dir) {
            Ok(entries) => entries,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => return Err(Failure::io(error)),
        };
        for entry in entries {
            let entry = entry.map_err(Failure::io)?;
            let path = entry.path();
            let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
                continue;
            };
            if !is_rustc_driver_filename(name) {
                continue;
            }
            let Ok(matched_digest) = open_and_hash_if_dev_ino_matches(&path, loaded_dev_ino, maps)
            else {
                continue;
            };
            saw_candidate = true;
            if let Some(digest) = matched_digest {
                return Ok((name.to_owned(), digest));
            }
        }
    }
    if !saw_candidate {
        return Err(Failure::tool(format!(
            "no librustc_driver-*.so found in sysroot {}",
            sysroot.display()
        )));
    }
    Err(Failure::tool(format!(
        "loaded rustc driver does not match any librustc_driver-*.so in sysroot {}",
        sysroot.display()
    )))
}

/// Return `true` if `dir` lies under a standard system runtime root (`/lib`,
/// `/lib64`, `/usr/lib`, `/usr/lib64`) that needs no custom symlink scanning.
#[cfg(all(any(target_os = "linux", test), unix))]
fn is_standard_runtime_dir(dir: &Path) -> bool {
    use std::os::unix::ffi::OsStrExt;
    let bytes = dir.as_os_str().as_bytes();
    matches!(bytes, b"/lib" | b"/lib64" | b"/usr/lib" | b"/usr/lib64")
        || ALLOWED_SYSTEM_RUNTIME_PREFIXES
            .iter()
            .any(|prefix| bytes.starts_with(prefix))
}

/// Return `true` if a canonical symlink target inside an authenticated runtime
/// directory is non-toolchain and resolves under either a standard OS runtime
/// root or a validated runtime directory.
#[cfg(all(any(target_os = "linux", test), unix))]
fn is_allowed_runtime_symlink_target(canon: &Path) -> bool {
    use std::os::unix::ffi::OsStrExt;
    if !canon.is_absolute() {
        return false;
    }
    if canon
        .file_name()
        .and_then(|name| name.to_str())
        .is_some_and(is_toolchain_dso_filename)
    {
        return false;
    }
    let bytes = canon.as_os_str().as_bytes();
    if ALLOWED_SYSTEM_RUNTIME_PREFIXES
        .iter()
        .any(|prefix| bytes.starts_with(prefix))
    {
        return true;
    }
    canon.parent().is_some_and(is_allowed_pt_interp_dir)
}

/// Record `(st_dev, st_ino)` -> canonical path for non-toolchain symlinked
/// runtime libraries directly inside `dir` whose canonical target passes
/// [`is_allowed_runtime_symlink_target`].
///
/// Nix packages split outputs such as `gcc-lib` and `gcc-libgcc` place a
/// `libgcc_s.so.1` symlink inside `gcc-lib/lib` (the binary's `DT_RUNPATH`
/// directory) targeting `gcc-libgcc/lib/libgcc_s.so.1`; Linux records the
/// canonical target in `/proc/self/maps`, so authenticating symlink targets
/// reachable directly from validated `PT_INTERP`/`DT_RUNPATH` directories by
/// `(st_dev, st_ino)` admits split-package runtime DSOs without reopening
/// blanket `/nix/store/` access.
#[cfg(all(any(target_os = "linux", test), unix))]
fn collect_dir_runtime_symlinks(
    dir: &Path,
    symlink_targets: &mut BTreeMap<DevIno, PathBuf>,
) {
    const MAX_SYMLINK_TARGETS: usize = 1024;

    if is_standard_runtime_dir(dir) || symlink_targets.len() >= MAX_SYMLINK_TARGETS {
        return;
    }
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        if symlink_targets.len() >= MAX_SYMLINK_TARGETS {
            break;
        }
        let Ok(ft) = entry.file_type() else {
            continue;
        };
        if !ft.is_symlink() {
            continue;
        }
        let entry_path = entry.path();
        let Some(entry_name) = entry_path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if is_toolchain_dso_filename(entry_name) {
            continue;
        }
        let Ok(canon) = fs::canonicalize(&entry_path) else {
            continue;
        };
        if !is_allowed_runtime_symlink_target(&canon) {
            continue;
        }
        let Ok(dev_ino) = regular_file_dev_ino(&canon) else {
            continue;
        };
        symlink_targets.entry(dev_ino).or_insert(canon);
    }
}

/// Authenticated non-toolchain runtime directory closure and per-file symlink
/// `(st_dev, st_ino)` allowlist derived from `PT_INTERP` and transitive
/// `DT_RUNPATH`/`DT_RPATH` dependencies.
#[cfg(all(any(target_os = "linux", test), unix))]
struct RuntimeClosure {
    dirs: Vec<PathBuf>,
    symlink_dev_inos: BTreeSet<DevIno>,
}

#[cfg(all(any(target_os = "linux", test), unix))]
impl RuntimeClosure {
    /// Resolve the transitive runtime closure across `pt_interp_dirs`,
    /// symlinks inside those directories, and `DT_RUNPATH`/`DT_RPATH` headers
    /// of already-authenticated mapped ELF binaries.
    fn resolve(
        pt_interp_dirs: &[PathBuf],
        exec_mappings: &ExecMappings,
        sysroot_libs: &SysrootLibMap,
        self_dev_ino: DevIno,
        driver_dev_ino: DevIno,
    ) -> Self {
        use std::os::unix::ffi::OsStrExt;

        const MAX_DIRS: usize = 256;
        const MAX_INSPECTED_ELFS: usize = 256;

        let mut dirs: BTreeSet<PathBuf> = pt_interp_dirs.iter().cloned().collect();
        let mut symlink_targets: BTreeMap<DevIno, PathBuf> = BTreeMap::new();
        let mut scanned_dirs: BTreeSet<PathBuf> = BTreeSet::new();
        let mut inspected_dev_inos: BTreeSet<DevIno> = BTreeSet::new();

        let has_unmatched_mapping =
            |dirs_vec: &[PathBuf], symlink_targets: &BTreeMap<DevIno, PathBuf>| {
                exec_mappings.iter().any(|(dev_ino, pathname)| {
                    let dev_ino = *dev_ino;
                    if dev_ino == self_dev_ino
                        || dev_ino == driver_dev_ino
                        || sysroot_libs.contains_key(&dev_ino)
                    {
                        return false;
                    }
                    if is_allowed_system_runtime_path(pathname, dirs_vec) {
                        return false;
                    }
                    let is_toolchain = maps_pathname_basename(pathname)
                        .is_some_and(is_toolchain_dso_filename);
                    is_toolchain || !symlink_targets.contains_key(&dev_ino)
                })
            };

        let initial_dirs: Vec<PathBuf> = dirs.iter().cloned().collect();
        if !has_unmatched_mapping(&initial_dirs, &symlink_targets) {
            return Self {
                dirs: initial_dirs,
                symlink_dev_inos: BTreeSet::new(),
            };
        }

        loop {
            let mut progressed = false;
            let pending_dirs: Vec<PathBuf> = dirs
                .iter()
                .filter(|dir| !scanned_dirs.contains(*dir))
                .cloned()
                .collect();
            for dir in pending_dirs {
                scanned_dirs.insert(dir.clone());
                let before = symlink_targets.len();
                collect_dir_runtime_symlinks(&dir, &mut symlink_targets);
                if symlink_targets.len() > before {
                    progressed = true;
                }
            }

            if inspected_dev_inos.len() < MAX_INSPECTED_ELFS && dirs.len() < MAX_DIRS {
                for (dev_ino, pathname) in exec_mappings {
                    let dev_ino = *dev_ino;
                    if inspected_dev_inos.len() >= MAX_INSPECTED_ELFS || dirs.len() >= MAX_DIRS {
                        break;
                    }
                    if inspected_dev_inos.contains(&dev_ino) {
                        continue;
                    }
                    let elf_path: Option<&Path> =
                        if let Some(candidate) =
                            sysroot_libs.get(&dev_ino).and_then(|candidates| candidates.first())
                        {
                            Some(candidate.path.as_path())
                        } else if let Some(sym_path) = symlink_targets.get(&dev_ino) {
                            Some(sym_path.as_path())
                        } else if !pathname.ends_with(b" (deleted)")
                            && !maps_pathname_basename(pathname)
                                .is_some_and(is_toolchain_dso_filename)
                        {
                            let raw_path = Path::new(OsStr::from_bytes(pathname));
                            if dirs.iter().any(|dir| raw_path.starts_with(dir)) {
                                Some(raw_path)
                            } else {
                                None
                            }
                        } else {
                            None
                        };
                    let Some(path) = elf_path else {
                        continue;
                    };
                    inspected_dev_inos.insert(dev_ino);
                    if let Some(info) = inspect_elf64_pt_interp(path, Some(dev_ino)) {
                        for dir in info.dirs {
                            if dirs.len() >= MAX_DIRS {
                                break;
                            }
                            if dirs.insert(dir) {
                                progressed = true;
                            }
                        }
                    }
                }
            }

            let dirs_vec: Vec<PathBuf> = dirs.iter().cloned().collect();
            if !progressed || !has_unmatched_mapping(&dirs_vec, &symlink_targets) {
                return Self {
                    dirs: dirs_vec,
                    symlink_dev_inos: symlink_targets.into_keys().collect(),
                };
            }
        }
    }

    fn is_allowed(&self, dev_ino: DevIno, pathname: &[u8]) -> bool {
        if is_allowed_system_runtime_path(pathname, &self.dirs) {
            return true;
        }
        !pathname.ends_with(b" (deleted)")
            && pathname.starts_with(b"/")
            && !maps_pathname_basename(pathname).is_some_and(is_toolchain_dso_filename)
            && self.symlink_dev_inos.contains(&dev_ino)
    }
}

/// Authenticate non-self, non-driver executable mappings in `/proc/self/maps`
/// against `sysroot_libs` and `runtime_closure`, hashing via
/// [`open_and_hash_if_dev_ino_matches`] every mapped sysroot library whose
/// identity is not already in `verified_ids`.
#[cfg(all(any(target_os = "linux", test), unix))]
#[allow(clippy::too_many_arguments)]
fn verify_exec_mappings_residency(
    maps: MapsView<'_>,
    exec_mappings: &ExecMappings,
    sysroot_libs: &SysrootLibMap,
    runtime_closure: &RuntimeClosure,
    self_dev_ino: DevIno,
    driver_dev_ino: DevIno,
    sysroot: &Path,
    verified_ids: &mut BTreeSet<DevIno>,
    dso_digests: &mut BTreeMap<String, String>,
) -> Result<(), Failure> {
    for (dev_ino, pathname) in exec_mappings {
        let dev_ino = *dev_ino;
        if dev_ino == self_dev_ino || dev_ino == driver_dev_ino {
            continue;
        }
        // Skip by identity, not by name: a same-named library digested under
        // another identity does not vouch for this mapping, which may have
        // matched only by superblock and inode number.
        if verified_ids.contains(&dev_ino) {
            continue;
        }
        let candidates = sysroot_libs.get(&dev_ino).map_or(&[][..], Vec::as_slice);
        if let Some((name, digest)) = hash_matching_sysroot_candidate(candidates, dev_ino, maps)? {
            verified_ids.insert(dev_ino);
            record_dso_digest(dso_digests, name, digest)?;
            continue;
        }
        // An exact identity names that sysroot file alone, so failing to
        // confirm it means the file changed during verification. A sysroot
        // file sharing only a superblock identity may be an unrelated file in
        // another Btrfs subvolume or OverlayFS layer, so a mapping that no such
        // candidate backs is judged like any other non-sysroot mapping.
        if candidates.iter().any(|candidate| candidate.exact) {
            return Err(Failure::tool(format!(
                "sysroot library mapping {} changed during residency verification",
                String::from_utf8_lossy(pathname)
            )));
        }
        if !runtime_closure.is_allowed(dev_ino, pathname) {
            return Err(Failure::tool(format!(
                "loaded executable mapping {} does not belong to verified sysroot {} or standard system libraries",
                String::from_utf8_lossy(pathname),
                sysroot.display()
            )));
        }
    }
    Ok(())
}

/// Return the name and digest of the first of `candidates` that backs the
/// mappings of `dev_ino` per [`open_and_hash_if_dev_ino_matches`], or `None`
/// if none does.
#[cfg(all(any(target_os = "linux", test), unix))]
fn hash_matching_sysroot_candidate<'a>(
    candidates: &'a [SysrootCandidate],
    dev_ino: DevIno,
    maps: MapsView<'_>,
) -> Result<Option<(&'a str, String)>, Failure> {
    for candidate in candidates {
        if let Some(digest) =
            open_and_hash_if_dev_ino_matches(&candidate.path, dev_ino, maps).map_err(Failure::io)?
        {
            return Ok(Some((&candidate.name, digest)));
        }
    }
    Ok(None)
}

/// Hash the capture executable mapped as `self_dev_ino`, opening it through
/// `self_exe_path` and, failing that, through the mapping's own pathname.
#[cfg(all(any(target_os = "linux", test), unix))]
fn hash_capture_executable(
    self_exe_path: &Path,
    self_vma_path: &[u8],
    self_dev_ino: DevIno,
    maps: MapsView<'_>,
) -> Result<String, Failure> {
    use std::os::unix::ffi::OsStrExt;

    if let Ok(Some(digest)) = open_and_hash_if_dev_ino_matches(self_exe_path, self_dev_ino, maps) {
        return Ok(digest);
    }
    let vma_path = Path::new(OsStr::from_bytes(self_vma_path));
    open_and_hash_if_dev_ino_matches(vma_path, self_dev_ino, maps)
        .map_err(Failure::io)?
        .ok_or_else(|| {
            Failure::tool("capture executable failed open-FD (st_dev, st_ino) verification")
        })
}

/// Record `digest` for the sysroot library `name`, failing if a different
/// library with the same name was already recorded with another digest, since
/// the manifest could then describe only one of them.
#[cfg(all(any(target_os = "linux", test), unix))]
fn record_dso_digest(
    dso_digests: &mut BTreeMap<String, String>,
    name: &str,
    digest: String,
) -> Result<(), Failure> {
    match dso_digests.get(name) {
        Some(previous) if *previous != digest => Err(Failure::tool(format!(
            "loaded sysroot libraries named {name} have different contents"
        ))),
        Some(_) => Ok(()),
        None => {
            dso_digests.insert(name.to_owned(), digest);
            Ok(())
        }
    }
}

/// Verify closed-world executable DSO residency across `/proc/self/maps` for
/// both dynamically linked (`librustc_driver-*.so` + transitive toolchain
/// DSOs such as `libLLVM*.so*`) and statically linked (`rustc_driver` linked
/// directly into the capture executable) `rustc_private` drivers.
///
/// Self identity is resolved by function-pointer VMA lookup (`self_addr`)
/// rather than pathname string matching so explicit dynamic-loader launches
/// and flat-CAS symlink forests authenticate strictly by kernel
/// `(st_dev, st_ino)` and open-FD SHA-256.
#[cfg(all(any(target_os = "linux", test), unix))]
fn verify_maps_residency(
    maps_bytes: &[u8],
    sysroot: &Path,
    host: &str,
    self_addr: usize,
    driver_addr: usize,
    self_exe_path: &Path,
    pt_interp_dirs: &[PathBuf],
) -> Result<DriverIdentity, Failure> {
    let process = LiveProcess::default();
    verify_maps_residency_with(
        MapsView {
            bytes: maps_bytes,
            process: &process,
        },
        sysroot,
        host,
        self_addr,
        driver_addr,
        self_exe_path,
        pt_interp_dirs,
    )
}

/// [`verify_maps_residency`] against an explicit [`MapsView`].
#[cfg(all(any(target_os = "linux", test), unix))]
fn verify_maps_residency_with(
    maps: MapsView<'_>,
    sysroot: &Path,
    host: &str,
    self_addr: usize,
    driver_addr: usize,
    self_exe_path: &Path,
    pt_interp_dirs: &[PathBuf],
) -> Result<DriverIdentity, Failure> {
    let maps_bytes = maps.bytes;
    let (self_dev_ino, self_vma_path) =
        resolve_mapping_dev_ino(maps_bytes, self_addr, "capture executable")?;
    let (driver_dev_ino, _) = resolve_mapping_dev_ino(maps_bytes, driver_addr, "rustc driver")?;
    let sysroot_libs = collect_sysroot_library_entries(sysroot, host, maps.process)?;

    // Collect every file-backed executable mapping and any file-backed
    // toolchain-DSO mapping across `/proc/self/maps`.
    let mut exec_mappings = ExecMappings::new();
    let mut toolchain_mappings: BTreeMap<(u64, u64), Vec<u8>> = BTreeMap::new();
    for raw_line in maps_bytes.split(|&b| b == b'\n') {
        let Some(entry) = parse_maps_line(raw_line) else {
            continue;
        };
        if entry.inode == 0 {
            continue;
        }
        let dev_ino = (entry.dev, entry.inode);
        let is_exec = entry.perms.contains(&b'x');
        let is_toolchain_named = entry
            .pathname
            .and_then(maps_pathname_basename)
            .is_some_and(is_toolchain_dso_filename);
        if is_exec {
            let Some(pathname) = entry.pathname else {
                return Err(Failure::tool(
                    "loaded executable mapping has no backing pathname",
                ));
            };
            if pathname.ends_with(b" (deleted)") {
                return Err(Failure::tool(format!(
                    "loaded executable mapping is deleted: {}",
                    String::from_utf8_lossy(pathname)
                )));
            }
            exec_mappings.insert((dev_ino, pathname.to_vec()));
        }
        if is_toolchain_named {
            let pathname = entry.pathname.unwrap_or_default();
            if pathname.ends_with(b" (deleted)") {
                return Err(Failure::tool(format!(
                    "loaded toolchain DSO mapping is deleted: {}",
                    String::from_utf8_lossy(pathname)
                )));
            }
            toolchain_mappings
                .entry(dev_ino)
                .or_insert_with(|| pathname.to_vec());
        }
    }

    let mut dso_digests = BTreeMap::new();
    let runtime_closure = RuntimeClosure::resolve(
        pt_interp_dirs,
        &exec_mappings,
        &sysroot_libs,
        self_dev_ino,
        driver_dev_ino,
    );

    if driver_dev_ino == self_dev_ino {
        // Static-linked `rustc_private` driver: `rustc_driver::run_compiler`
        // resides inside the capture executable itself. Refuse any stray
        // dynamically loaded toolchain DSO (`librustc_*`, `libLLVM*`, etc.),
        // validate all remaining executable mappings against sysroot or
        // standard/authenticated runtime paths, and hash the capture
        // executable via an open-FD `(st_dev, st_ino)` match.
        if let Some((_, stray_path)) = toolchain_mappings.iter().next() {
            return Err(Failure::tool(format!(
                "statically linked capture driver unexpectedly mapped toolchain DSO: {}",
                String::from_utf8_lossy(stray_path)
            )));
        }
        verify_exec_mappings_residency(
            maps,
            &exec_mappings,
            &sysroot_libs,
            &runtime_closure,
            self_dev_ino,
            driver_dev_ino,
            sysroot,
            &mut BTreeSet::new(),
            &mut dso_digests,
        )?;
        let exe_sha256 = hash_capture_executable(self_exe_path, self_vma_path, self_dev_ino, maps)?;
        return Ok(DriverIdentity {
            linkage: DriverLinkage::StaticExe,
            driver_sha256: exe_sha256,
            dso_digests,
        });
    }

    // Dynamic `librustc_driver-*.so` mode: authenticate `driver_dev_ino`
    // against `<sysroot>` and verify the closed-world set of every executable
    // and toolchain-named mapping in `/proc/self/maps`.
    let (driver_name, driver_sha256) =
        match_and_hash_sysroot_driver(sysroot, host, driver_dev_ino, maps)?;
    record_dso_digest(&mut dso_digests, &driver_name, driver_sha256.clone())?;

    // Mappings that share the capture executable's identity are exempt from
    // the closed-world checks below. That identity is unique only if it is the
    // executable's own `fstat(2)` identity; otherwise confirm that every such
    // mapping is the capture executable.
    if regular_file_dev_ino(self_exe_path).ok() != Some(self_dev_ino) {
        hash_capture_executable(self_exe_path, self_vma_path, self_dev_ino, maps)?;
    }

    let mut verified_ids = BTreeSet::new();
    for (&dev_ino, pathname) in &toolchain_mappings {
        if dev_ino == self_dev_ino || dev_ino == driver_dev_ino {
            continue;
        }
        let Some(candidates) = sysroot_libs.get(&dev_ino) else {
            return Err(Failure::tool(format!(
                "loaded toolchain DSO {} does not match any library in sysroot {}",
                String::from_utf8_lossy(pathname),
                sysroot.display()
            )));
        };
        let (name, digest) =
            hash_matching_sysroot_candidate(candidates, dev_ino, maps)?.ok_or_else(|| {
                Failure::tool(format!(
                    "sysroot toolchain DSO mapping {} does not match its sysroot file",
                    String::from_utf8_lossy(pathname)
                ))
            })?;
        record_dso_digest(&mut dso_digests, name, digest)?;
        verified_ids.insert(dev_ino);
    }

    verify_exec_mappings_residency(
        maps,
        &exec_mappings,
        &sysroot_libs,
        &runtime_closure,
        self_dev_ino,
        driver_dev_ino,
        sysroot,
        &mut verified_ids,
        &mut dso_digests,
    )?;

    Ok(DriverIdentity {
        linkage: DriverLinkage::DynamicDso,
        driver_sha256,
        dso_digests,
    })
}

/// Open the regular file at `path` and, if a mapping reported by
/// `/proc/self/maps` as `expected` is backed by it, return the SHA-256 of its
/// contents read from that same handle; return `Ok(None)` otherwise.
///
/// A file whose `fstat(2)` `(st_dev, st_ino)` equals `expected` matches
/// outright, because the kernel guarantees that identity is unique.
///
/// On Btrfs, `fstat(2)` reports a per-subvolume anonymous device while
/// `/proc/self/maps` reports the filesystem's superblock device, and inode
/// numbers repeat across subvolumes; OverlayFS over several filesystems
/// without `xino` behaves likewise across layers. There, `expected` names the
/// superblock and inode number but not which of possibly several inodes was
/// mapped, so an `(st_ino, superblock)` match alone would accept a different
/// file that happens to share both. Such a match is accepted only if every
/// page of every accessible mapping of `expected` that still shares the kernel
/// page cache equals the bytes hashed from this handle at the same file
/// offset, and at least one executable page was compared. Comparing in the
/// same pass that hashes makes the digest describe exactly the bytes found to
/// be mapped. Non-executable pages that the process has privately modified
/// (relocated `PT_GNU_RELRO` data, written `.data`) are skipped, since their
/// mapped contents no longer come from the file; executable pages are never
/// expected to be modified, so any such page fails the match.
///
/// Because skipped pages leave a substitute's initialized data unchecked,
/// every such mapping's pathname must also open, at the time of the check, to
/// this same inode by full `fstat(2)` identity, which is unique. The kernel
/// prints a mapping's current pathname, so a substitute that stays put fails
/// this check. Defeating it requires replacing the substitute's path (for
/// example, moving the substitute aside and putting a symlink to the candidate
/// in its place) between reading `/proc/self/maps` and opening the pathname,
/// and the substitute must still match the candidate's code and read-only
/// data.
#[cfg(all(any(target_os = "linux", test), unix))]
fn open_and_hash_if_dev_ino_matches(
    path: &Path,
    expected: (u64, u64),
    maps: MapsView<'_>,
) -> io::Result<Option<String>> {
    use std::os::unix::fs::MetadataExt;

    let mut file = fs::File::open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "path is not a regular file",
        ));
    }
    if (meta.dev(), meta.ino()) == expected {
        let digest = sha256_reader(&mut file)?;
        return Ok(Some(digest));
    }
    if meta.ino() != expected.1 || maps.process.superblock_dev(&file).ok() != Some(expected.0) {
        return Ok(None);
    }
    let page_size = maps.process.page_size()?;
    let segments = collect_mapped_segments(maps, expected, page_size)?;
    if !segments
        .iter()
        .all(|segment| maps_pathname_opens_to(segment.pathname.as_deref(), &meta))
    {
        return Ok(None);
    }
    hash_and_compare_mapped_pages(&mut file, meta.len(), &segments, page_size, maps.process)
}

/// Return whether a `/proc/self/maps` pathname currently opens to a regular
/// file with the same `fstat(2)` `(st_dev, st_ino)` as `meta`.
///
/// The kernel prints a newline in a mapped file's name as the four bytes
/// `\012` without escaping backslashes, so a printed pathname containing a
/// backslash may name a different file than the one mapped; such pathnames
/// are rejected rather than unescaped.
#[cfg(all(any(target_os = "linux", test), unix))]
fn maps_pathname_opens_to(pathname: Option<&[u8]>, meta: &fs::Metadata) -> bool {
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::fs::MetadataExt;

    let Some(pathname) = pathname else {
        return false;
    };
    if !pathname.starts_with(b"/")
        || pathname.ends_with(b" (deleted)")
        || pathname.contains(&b'\\')
    {
        return false;
    }
    fs::File::open(Path::new(OsStr::from_bytes(pathname)))
        .and_then(|file| file.metadata())
        .is_ok_and(|opened| {
            opened.is_file() && (opened.dev(), opened.ino()) == (meta.dev(), meta.ino())
        })
}

#[cfg(all(test, not(unix)))]
fn open_and_hash_if_dev_ino_matches(
    _path: &Path,
    _expected: (u64, u64),
    _maps: MapsView<'_>,
) -> io::Result<Option<String>> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "residency hashing requires unix metadata",
    ))
}

/// Process state consulted to confirm the file behind a `/proc/self/maps`
/// entry when the entry's `(st_dev, st_ino)` does not identify it uniquely.
#[cfg(any(target_os = "linux", test))]
trait ProcessView {
    /// Return the device number of the superblock of the mount through which
    /// `file` was opened. This is the device `/proc/self/maps` prints for
    /// mappings of `file`.
    fn superblock_dev(&self, file: &fs::File) -> io::Result<u64>;

    /// Return the base page size in which `/proc/self/maps` ranges and
    /// `/proc/self/pagemap` entries are expressed.
    fn page_size(&self) -> io::Result<usize>;

    /// Return the `/proc/self/pagemap` entries of the `count` pages starting
    /// at the page-aligned address `addr`.
    fn pagemap(&self, addr: usize, count: usize) -> io::Result<Vec<u64>>;

    /// Fill `buf` with this process's memory starting at `addr`.
    fn read_memory(&self, addr: usize, buf: &mut [u8]) -> io::Result<()>;
}

/// Raw `/proc/self/maps` contents paired with the [`ProcessView`] that
/// confirms ambiguous entries.
#[cfg(any(target_os = "linux", test))]
#[derive(Clone, Copy)]
struct MapsView<'a> {
    bytes: &'a [u8],
    process: &'a dyn ProcessView,
}

/// [`ProcessView`] of the running process, backed by `/proc/self`.
#[cfg(any(target_os = "linux", test))]
#[derive(Default)]
struct LiveProcess {
    /// `/proc/self/mountinfo`, read once per verification; `None` if it was
    /// unreadable.
    mountinfo: std::cell::OnceCell<Option<Vec<u8>>>,
    /// `AT_PAGESZ` from `/proc/self/auxv`; `None` if it was unavailable.
    page_size: std::cell::OnceCell<Option<usize>>,
    /// Open `/proc/self/mem`; `None` if it could not be opened.
    mem: std::cell::OnceCell<Option<fs::File>>,
}

#[cfg(any(target_os = "linux", test))]
impl ProcessView for LiveProcess {
    // Linux prints the inode's superblock device `i_sb->s_dev` both in
    // `/proc/<pid>/maps` (`show_map_vma`) and in the third field of
    // `/proc/<pid>/mountinfo` (`show_mountinfo`), and `/proc/<pid>/fdinfo/<fd>`
    // names the mount of an open file in its `mnt_id` field. Resolving through
    // the open descriptor rather than a path keeps the answer tied to the
    // inode that was opened and hashed.
    #[cfg(unix)]
    fn superblock_dev(&self, file: &fs::File) -> io::Result<u64> {
        use std::os::fd::AsRawFd;

        let fdinfo = fs::read(format!("/proc/self/fdinfo/{}", file.as_raw_fd()))?;
        let mnt_id = parse_fdinfo_mnt_id(&fdinfo).ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "fdinfo has no mnt_id")
        })?;
        let mountinfo = self
            .mountinfo
            .get_or_init(|| fs::read("/proc/self/mountinfo").ok())
            .as_deref()
            .ok_or_else(|| io::Error::other("cannot read /proc/self/mountinfo"))?;
        parse_mountinfo_dev(mountinfo, mnt_id).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                format!("mount {mnt_id} not found in /proc/self/mountinfo"),
            )
        })
    }

    fn page_size(&self) -> io::Result<usize> {
        self.page_size
            .get_or_init(|| parse_auxv_page_size(&fs::read("/proc/self/auxv").ok()?))
            .ok_or_else(|| {
                io::Error::new(io::ErrorKind::InvalidData, "auxv has no valid AT_PAGESZ")
            })
    }

    #[cfg(unix)]
    fn pagemap(&self, addr: usize, count: usize) -> io::Result<Vec<u64>> {
        use std::os::unix::fs::FileExt;

        const ENTRY_BYTES: usize = 8;
        let page_size = self.page_size()?;
        let overflow = || io::Error::new(io::ErrorKind::InvalidInput, "pagemap range overflows");
        let len = count.checked_mul(ENTRY_BYTES).ok_or_else(overflow)?;
        let offset = u64::try_from(addr / page_size)
            .ok()
            .and_then(|page| page.checked_mul(ENTRY_BYTES as u64))
            .ok_or_else(overflow)?;
        let mut raw = vec![0u8; len];
        fs::File::open("/proc/self/pagemap")?.read_exact_at(&mut raw, offset)?;
        Ok(raw
            .chunks_exact(ENTRY_BYTES)
            .map(|entry| u64::from_ne_bytes(entry.try_into().unwrap()))
            .collect())
    }

    #[cfg(unix)]
    fn read_memory(&self, addr: usize, buf: &mut [u8]) -> io::Result<()> {
        use std::os::unix::fs::FileExt;

        let offset = u64::try_from(addr)
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "address overflows"))?;
        self.mem
            .get_or_init(|| fs::File::open("/proc/self/mem").ok())
            .as_ref()
            .ok_or_else(|| io::Error::other("cannot open /proc/self/mem"))?
            .read_exact_at(buf, offset)
    }

    #[cfg(not(unix))]
    fn superblock_dev(&self, _file: &fs::File) -> io::Result<u64> {
        Err(io::Error::from(io::ErrorKind::Unsupported))
    }

    #[cfg(not(unix))]
    fn pagemap(&self, _addr: usize, _count: usize) -> io::Result<Vec<u64>> {
        Err(io::Error::from(io::ErrorKind::Unsupported))
    }

    #[cfg(not(unix))]
    fn read_memory(&self, _addr: usize, _buf: &mut [u8]) -> io::Result<()> {
        Err(io::Error::from(io::ErrorKind::Unsupported))
    }
}

/// Return the `mnt_id` field of a `/proc/<pid>/fdinfo/<fd>` file.
#[cfg(any(target_os = "linux", test))]
fn parse_fdinfo_mnt_id(fdinfo: &[u8]) -> Option<u64> {
    fdinfo.split(|&b| b == b'\n').find_map(|line| {
        let value = line.strip_prefix(b"mnt_id:")?;
        parse_dec_u64(value.trim_ascii())
    })
}

/// Return the superblock device of mount `mnt_id` in a
/// `/proc/<pid>/mountinfo` file, encoded like `MetadataExt::dev()`.
///
/// The third field is the superblock's `major:minor` in decimal, unlike the
/// hexadecimal device numbers in `/proc/<pid>/maps`.
#[cfg(any(target_os = "linux", test))]
fn parse_mountinfo_dev(mountinfo: &[u8], mnt_id: u64) -> Option<u64> {
    let mut found = None;
    for line in mountinfo.split(|&b| b == b'\n') {
        let mut fields = line.split(|&b| b == b' ');
        if fields.next().and_then(parse_dec_u64) != Some(mnt_id) {
            continue;
        }
        let (major, minor) = split_once_byte(fields.nth(1)?, b':')?;
        let dev = linux_makedev(parse_dec_u64(major)?, parse_dec_u64(minor)?);
        if found.replace(dev).is_some() {
            return None;
        }
    }
    found
}

/// Return the `AT_PAGESZ` value from a native-endian `/proc/<pid>/auxv`.
#[cfg(any(target_os = "linux", test))]
fn parse_auxv_page_size(auxv: &[u8]) -> Option<usize> {
    const AT_NULL: usize = 0;
    const AT_PAGESZ: usize = 6;
    const WORD: usize = size_of::<usize>();
    for pair in auxv.chunks_exact(2 * WORD) {
        let key = usize::from_ne_bytes(pair[..WORD].try_into().ok()?);
        let value = usize::from_ne_bytes(pair[WORD..].try_into().ok()?);
        match key {
            AT_NULL => break,
            AT_PAGESZ => return value.is_power_of_two().then_some(value),
            _ => {}
        }
    }
    None
}

/// Return whether a `/proc/self/pagemap` entry describes a page whose mapped
/// contents still come from the kernel page cache of the backing file.
///
/// A private file mapping's page is either not yet faulted in (reads fault in
/// the page-cache page), present as the page-cache page itself (the
/// "file-page" bit), or a private anonymous copy made by a write (present
/// without the file-page bit, or swapped out). Only the last kind can differ
/// from the file. Bit assignments follow
/// <https://docs.kernel.org/admin-guide/mm/pagemap.html>.
#[cfg(any(target_os = "linux", test))]
fn pagemap_entry_reflects_file(entry: u64) -> bool {
    const PRESENT: u64 = 1 << 63;
    const SWAPPED: u64 = 1 << 62;
    const FILE_PAGE: u64 = 1 << 61;
    if entry & SWAPPED != 0 {
        return false;
    }
    entry & PRESENT == 0 || entry & FILE_PAGE != 0
}

/// One accessible `/proc/self/maps` range of a file, with the pagemap entry
/// of each of its pages.
#[cfg(any(target_os = "linux", test))]
struct MappedSegment {
    start: usize,
    file_offset: u64,
    /// File offset one past the last byte the range maps.
    file_end: u64,
    executable: bool,
    pagemap: Vec<u64>,
    /// Pathname `/proc/self/maps` printed for the range, if any.
    pathname: Option<Vec<u8>>,
}

/// Collect every range of `maps` whose identity is `maps_id` and that grants
/// any access. Only `---` guard ranges, which the process cannot touch, are
/// omitted; a range that grants access but cannot be read through
/// `/proc/self/mem` fails the comparison with an error.
///
/// The pagemap is sampled before any memory is compared, so a page that the
/// process privately modifies after sampling is compared as file-backed and
/// fails rather than being skipped.
#[cfg(any(target_os = "linux", test))]
fn collect_mapped_segments(
    maps: MapsView<'_>,
    maps_id: (u64, u64),
    page_size: usize,
) -> io::Result<Vec<MappedSegment>> {
    let misaligned = || io::Error::new(io::ErrorKind::InvalidData, "misaligned maps range");
    let mut segments = Vec::new();
    for raw_line in maps.bytes.split(|&b| b == b'\n') {
        let Some(entry) = parse_maps_line(raw_line) else {
            continue;
        };
        if (entry.dev, entry.inode) != maps_id || entry.perms.starts_with(b"---") {
            continue;
        }
        if entry.start % page_size != 0
            || entry.end % page_size != 0
            || entry.offset % (page_size as u64) != 0
        {
            return Err(misaligned());
        }
        let count = (entry.end - entry.start) / page_size;
        let file_end = u64::try_from(entry.end - entry.start)
            .ok()
            .and_then(|len| entry.offset.checked_add(len))
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "maps range overflows"))?;
        let pagemap = maps.process.pagemap(entry.start, count)?;
        if pagemap.len() != count {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short pagemap read",
            ));
        }
        segments.push(MappedSegment {
            start: entry.start,
            file_offset: entry.offset,
            file_end,
            executable: entry.perms.contains(&b'x'),
            pagemap,
            pathname: entry.pathname.map(<[u8]>::to_vec),
        });
    }
    Ok(segments)
}

/// Hash `file` from offset zero and compare `segments` against the hashed
/// bytes as described on [`open_and_hash_if_dev_ino_matches`]. Return the
/// digest, or `Ok(None)` on any mismatch.
#[cfg(any(target_os = "linux", test))]
fn hash_and_compare_mapped_pages(
    file: &mut fs::File,
    file_len: u64,
    segments: &[MappedSegment],
    page_size: usize,
    process: &dyn ProcessView,
) -> io::Result<Option<String>> {
    use std::io::Read;

    let mut hasher = Sha256::new();
    let mut buffer = vec![0u8; 1 << 20];
    let mut memory = Vec::new();
    let mut compared_executable = false;
    let mut pos = 0u64;
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        let chunk = &buffer[..read];
        hasher.update(chunk);
        for segment in segments {
            if !compare_mapped_range(
                segment,
                pos,
                chunk,
                page_size,
                process,
                &mut memory,
                &mut compared_executable,
            )? {
                return Ok(None);
            }
        }
        pos += read as u64;
    }
    if pos != file_len {
        return Err(io::Error::other("file length changed while hashing"));
    }
    // The kernel zero-fills the part of a mapping's final page that lies past
    // end-of-file; pages wholly past end-of-file cannot be accessed at all.
    for segment in segments {
        let tail_start = pos.max(segment.file_offset);
        let tail_len = segment.file_end.saturating_sub(tail_start);
        if tail_len >= page_size as u64 {
            return Ok(None);
        }
        let zeros = vec![0u8; tail_len as usize];
        if !compare_mapped_range(
            segment,
            tail_start,
            &zeros,
            page_size,
            process,
            &mut memory,
            &mut compared_executable,
        )? {
            return Ok(None);
        }
    }
    if !compared_executable {
        return Ok(None);
    }
    Ok(Some(digest_to_hex(hasher.finalize().as_ref())))
}

/// Compare the part of `segment` that maps file bytes
/// `[chunk_offset, chunk_offset + chunk.len())` against `chunk`, page by page.
/// Return `Ok(false)` if a file-backed page differs or an executable page has
/// been privately modified.
#[cfg(any(target_os = "linux", test))]
fn compare_mapped_range(
    segment: &MappedSegment,
    chunk_offset: u64,
    chunk: &[u8],
    page_size: usize,
    process: &dyn ProcessView,
    memory: &mut Vec<u8>,
    compared_executable: &mut bool,
) -> io::Result<bool> {
    let lo = segment.file_offset.max(chunk_offset);
    let hi = segment
        .file_end
        .min(chunk_offset.saturating_add(chunk.len() as u64));
    if lo >= hi {
        return Ok(true);
    }
    memory.resize((hi - lo) as usize, 0);
    process.read_memory(segment.start + (lo - segment.file_offset) as usize, memory)?;
    let mut cursor = lo;
    while cursor < hi {
        let page_index = ((cursor - segment.file_offset) / page_size as u64) as usize;
        let page_end = (segment.file_offset + (page_index as u64 + 1) * page_size as u64).min(hi);
        if pagemap_entry_reflects_file(segment.pagemap[page_index]) {
            let expected =
                &chunk[(cursor - chunk_offset) as usize..(page_end - chunk_offset) as usize];
            let actual = &memory[(cursor - lo) as usize..(page_end - lo) as usize];
            if expected != actual {
                return Ok(false);
            }
            *compared_executable |= segment.executable;
        } else if segment.executable {
            return Ok(false);
        }
        cursor = page_end;
    }
    Ok(true)
}

#[cfg(target_os = "linux")]
fn verify_driver_residency(sysroot: &Path, host: &str) -> Result<DriverIdentity, Failure> {
    let self_addr = verify_driver_residency as *const () as usize;
    let driver_addr = rustc_driver::run_compiler as *const () as usize;
    let maps_bytes = fs::read("/proc/self/maps").map_err(Failure::io)?;
    let self_exe = Path::new("/proc/self/exe");
    let pt_interp_dirs = resolve_runtime_pt_interp_dirs(&maps_bytes, self_addr, self_exe);
    verify_maps_residency(
        &maps_bytes,
        sysroot,
        host,
        self_addr,
        driver_addr,
        self_exe,
        &pt_interp_dirs,
    )
}

#[cfg(not(target_os = "linux"))]
fn verify_driver_residency(_sysroot: &Path, _host: &str) -> Result<DriverIdentity, Failure> {
    Err(Failure::unsupported(
        "typed MIR capture requires Linux to authenticate the loaded rustc driver",
    ))
}

/// Verify ambient loader hygiene, sysroot layout, pinned linked driver
/// version, sanitized `<sysroot>/bin/rustc --version --verbose` agreement with
/// the pinned commit, pre/post `<sysroot>/bin/rustc` TOCTOU identity, and
/// Linux closed-world driver residency before entering `rustc`'s fatal-error
/// handler.
///
/// Returns the pinned sysroot directory `(st_dev, st_ino)` together with the
/// authenticated `rustc` and driver/DSO SHA-256 digests so downstream capture
/// checks can detect symlink retargeting and emit the digests in the manifest.
pub(crate) fn verify_compiler(sysroot: &Path, target: &str) -> Result<VerifiedCompiler, Failure> {
    reject_ambient_loader_env()?;
    #[cfg(unix)]
    let sysroot_id = dir_dev_ino(sysroot).map_err(|error| {
        Failure::tool(format!(
            "invalid Rust sysroot layout at {}: {error}",
            sysroot.display()
        ))
    })?;
    if !sysroot.is_dir()
        || !sysroot.join("lib").is_dir()
        || !sysroot.join("lib/rustlib").is_dir()
        || !sysroot
            .join("lib/rustlib")
            .join(target)
            .join("lib")
            .is_dir()
    {
        return Err(Failure::tool(format!(
            "invalid Rust sysroot layout at {}",
            sysroot.display()
        )));
    }
    let rustc_bin = sysroot.join("bin/rustc");
    let (rustc_sha256, rustc_id_before) = open_regular_and_hash(&rustc_bin).map_err(|error| {
        Failure::tool(format!(
            "invalid sysroot rustc binary at {}: {error}",
            rustc_bin.display()
        ))
    })?;

    // `rustc_version_str` reports the "version string for `rustc` itself".
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_interface/src/util.rs#L688-L691
    let linked_version = rustc_interface::util::rustc_version_str()
        .ok_or_else(|| Failure::tool("capture was linked against an unknown rustc revision"))?;
    if linked_version != ir::COMPILER_VERSION {
        return Err(Failure::tool(
            "capture was linked against an unexpected rustc revision",
        ));
    }

    let output = Command::new(&rustc_bin)
        .env_clear()
        .args(["--version", "--verbose"])
        .output()
        .map_err(Failure::io)?;
    if !output.status.success() {
        return Err(Failure::tool(format!(
            "sysroot rustc --version --verbose failed with status {}",
            output.status
        )));
    }
    let (rustc_sha256_after, rustc_id_after) =
        open_regular_and_hash(&rustc_bin).map_err(|error| {
            Failure::tool(format!(
                "cannot re-verify sysroot rustc binary at {}: {error}",
                rustc_bin.display()
            ))
        })?;
    if rustc_sha256 != rustc_sha256_after || rustc_id_before != rustc_id_after {
        return Err(Failure::tool(
            "sysroot rustc binary changed during compiler identity verification",
        ));
    }

    let text =
        String::from_utf8(output.stdout).map_err(|error| Failure::tool(error.to_string()))?;
    let verbose = parse_rustc_version_verbose(&text)?;
    if verbose.version != linked_version {
        return Err(Failure::tool(format!(
            "sysroot rustc version ({}) does not match linked rustc driver ({linked_version})",
            verbose.version
        )));
    }
    if verbose.commit != ir::COMPILER_COMMIT {
        return Err(Failure::tool(
            "sysroot rustc does not match the pinned full compiler commit",
        ));
    }
    if !is_valid_host_triple(&verbose.host) {
        return Err(Failure::tool(format!(
            "sysroot rustc reported invalid host triple: {:?}",
            verbose.host
        )));
    }
    let linked_host = rustc_session::config::host_tuple();
    if verbose.host != linked_host {
        return Err(Failure::tool(format!(
            "sysroot rustc host ({}) does not match linked rustc host ({linked_host})",
            verbose.host
        )));
    }

    let driver = verify_driver_residency(sysroot, &verbose.host)?;
    #[cfg(unix)]
    {
        let sysroot_id_after = dir_dev_ino(sysroot).map_err(Failure::io)?;
        if sysroot_id_after != sysroot_id {
            return Err(Failure::tool(
                "sysroot directory changed during compiler identity verification",
            ));
        }
    }
    Ok(VerifiedCompiler {
        #[cfg(unix)]
        sysroot_id,
        rustc_sha256,
        driver,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_maps_preserves_trailing_spaces_handles_non_utf8_and_decodes_dev() {
        let normal = parse_maps_line(
            b"7f1234560000-7f1234570000 r-xp 00000000 fd:01 12345   /usr/lib/librustc_driver-abc.so",
        )
        .unwrap();
        assert_eq!(normal.start, 0x7f12_3456_0000);
        assert_eq!(normal.end, 0x7f12_3457_0000);
        assert_eq!(normal.perms, b"r-xp");
        assert_eq!(normal.dev, linux_makedev(0xfd, 0x01));
        assert_eq!(normal.inode, 12345);
        assert_eq!(
            normal.pathname,
            Some(b"/usr/lib/librustc_driver-abc.so".as_slice())
        );

        let trailing_space = parse_maps_line(
            b"7f1234560000-7f1234570000 r-xp 00000000 08:01 12345   /opt/my rust dir/librustc_driver-a.so ",
        )
        .unwrap();
        assert_eq!(
            trailing_space.pathname,
            Some(b"/opt/my rust dir/librustc_driver-a.so ".as_slice())
        );

        let trailing_cr = parse_maps_line(
            b"7f1234560000-7f1234570000 r-xp 00000000 08:01 12345   /opt/librustc_driver-a.so\r",
        )
        .unwrap();
        assert_eq!(
            trailing_cr.pathname,
            Some(b"/opt/librustc_driver-a.so\r".as_slice())
        );

        let non_utf8 =
            parse_maps_line(b"7f1234560000-7f1234570000 r-xp 00000000 08:01 99   /tmp/\xff/blob")
                .unwrap();
        assert_eq!(non_utf8.inode, 99);
        assert_eq!(non_utf8.pathname, Some(b"/tmp/\xff/blob".as_slice()));

        let anon = parse_maps_line(b"7f1234560000-7f1234570000 rw-p 00000000 00:00 0   ").unwrap();
        assert_eq!(anon.pathname, None);
    }

    #[test]
    fn address_residency_ignores_decoys_and_rejects_deleted_non_exec_and_anonymous() {
        let addr: usize = 0x7f00_0025_0000;
        let maps = b"\
555555554000-555555558000 r--p 00000000 08:01 100   /usr/bin/anneal-rustc-capture\n\
7f0000000000-7f0000100000 r--p 00000000 08:01 200   /sysroot/lib/librustc_driver-decoy.so\n\
7f0000100000-7f0000200000 r-xp 00000000 08:01 201   /lib/x86_64-linux-gnu/libc.so.6\n\
7f0000200000-7f0000500000 r-xp 00100000 fd:01 300   /cas/blob-non-utf8-\xff\n\
7fff00000000-7fff00010000 rw-p 00000000 00:00 0     [stack]\n";
        assert_eq!(
            resolve_driver_mapping_dev_ino(maps, addr).unwrap(),
            (linux_makedev(0xfd, 0x01), 300)
        );

        let deleted =
            b"7f0000200000-7f0000500000 r-xp 00100000 fd:01 300   /opt/librustc_driver-1.so (deleted)\n";
        let err = resolve_driver_mapping_dev_ino(deleted, addr).unwrap_err();
        assert!(err.diagnostics[0].contains("deleted"), "{err:?}");

        let non_exec =
            b"7f0000200000-7f0000500000 r--p 00100000 fd:01 300   /opt/librustc_driver-1.so\n";
        let err = resolve_driver_mapping_dev_ino(non_exec, addr).unwrap_err();
        assert!(err.diagnostics[0].contains("not executable"), "{err:?}");

        let anon = b"7f0000200000-7f0000500000 r-xp 00000000 00:00 0\n";
        let err = resolve_driver_mapping_dev_ino(anon, addr).unwrap_err();
        assert!(err.diagnostics[0].contains("not file-backed"), "{err:?}");

        let missing = b"7fff00000000-7fff00010000 rw-p 00000000 00:00 0 [stack]\n";
        let err = resolve_driver_mapping_dev_ino(missing, addr).unwrap_err();
        assert!(err.diagnostics[0].contains("cannot locate"), "{err:?}");
    }

    #[cfg(unix)]
    #[test]
    fn symlinked_sysroot_matches_by_dev_ino_and_rejects_decoy_and_host_traversal() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().unwrap();
        let cas = dir.path().join("cas");
        let sysroot = dir.path().join("runfiles-sysroot");
        fs::create_dir_all(&cas).unwrap();
        fs::create_dir_all(sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap();

        let real_driver = cas.join("blob-driver");
        fs::write(&real_driver, b"driver-elf-bytes").unwrap();
        let real_dev_ino = regular_file_dev_ino(&real_driver).unwrap();
        let link_driver = sysroot.join("lib/librustc_driver-deadbeef.so");
        symlink(&real_driver, &link_driver).unwrap();

        // Decoy file symlinked to an unrelated file does not satisfy residency
        // when the executing driver address maps `real_dev_ino`.
        let decoy_target = cas.join("libc.so.6");
        fs::write(&decoy_target, b"decoy-libc").unwrap();
        let decoy_sysroot = dir.path().join("decoy-sysroot");
        fs::create_dir_all(decoy_sysroot.join("lib")).unwrap();
        symlink(
            &decoy_target,
            decoy_sysroot.join("lib/librustc_driver-0123.so"),
        )
        .unwrap();

        let process = LiveProcess::default();
        let maps = MapsView {
            bytes: b"",
            process: &process,
        };
        let digest =
            match_and_hash_sysroot_driver(&sysroot, "x86_64-unknown-linux-gnu", real_dev_ino, maps)
                .unwrap()
                .1;
        assert_eq!(digest, sha256_bytes(b"driver-elf-bytes"));

        let err = match_and_hash_sysroot_driver(
            &decoy_sysroot,
            "x86_64-unknown-linux-gnu",
            real_dev_ino,
            maps,
        )
        .unwrap_err();
        assert!(err.diagnostics[0].contains("does not match"), "{err:?}");

        // Host path traversal must be rejected before joining paths.
        for bad_host in ["", ".", "..", "/tmp/evil", "../../tmp/evil", "a/b"] {
            let err =
                match_and_hash_sysroot_driver(&sysroot, bad_host, real_dev_ino, maps).unwrap_err();
            assert!(
                err.diagnostics[0].contains("invalid rustc host triple"),
                "{bad_host:?}: {err:?}"
            );
        }
    }

    #[test]
    fn pinned_compiler_version_embeds_pinned_commit_prefix() {
        assert_eq!(ir::COMPILER_COMMIT.len(), 40);
        assert!(ir::COMPILER_COMMIT.bytes().all(|b| b.is_ascii_hexdigit()));
        let prefix = &ir::COMPILER_COMMIT[..9];
        assert!(
            ir::COMPILER_VERSION.contains(prefix),
            "ir::COMPILER_VERSION ({}) must contain pinned commit prefix ({prefix})",
            ir::COMPILER_VERSION
        );
    }

    #[test]
    fn parses_rustc_version_verbose_and_rejects_incomplete_output() {
        let valid = "\
rustc 1.98.0-nightly (f8a08b688 2026-05-30)\n\
binary: rustc\n\
commit-hash: f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\n\
commit-date: 2026-05-30\n\
host: x86_64-unknown-linux-gnu\n\
release: 1.98.0-nightly\n\
LLVM version: 22.1.6\n";
        let parsed = parse_rustc_version_verbose(valid).unwrap();
        assert_eq!(parsed.version, "1.98.0-nightly (f8a08b688 2026-05-30)");
        assert_eq!(parsed.commit, "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1");
        assert_eq!(parsed.host, "x86_64-unknown-linux-gnu");

        assert!(parse_rustc_version_verbose("rustc 1.98.0\n").is_err());
        assert!(parse_rustc_version_verbose("commit-hash: abc\nhost: x\n").is_err());
    }

    #[test]
    fn loader_env_guards_behave_as_specified() {
        // Ambient loader injection variables must fail closed on presence
        // (including empty strings for presence-triggered flags such as
        // `LD_DYNAMIC_WEAK=""` and `DYLD_FORCE_FLAT_NAMESPACE=""`), while clean
        // environments pass.
        assert!(reject_loader_env_in([("PATH", "/usr/bin"), ("LANG", "C")]).is_ok());
        for bad in FORBIDDEN_LOADER_ENV_VARS {
            for val in ["", "/tmp/injected.so"] {
                let err = reject_loader_env_in([(*bad, val)]).unwrap_err();
                assert!(
                    err.diagnostics[0].contains(bad),
                    "{bad}={val:?}: {err:?}"
                );
            }
        }
    }

    #[cfg(unix)]
    #[test]
    fn pt_interp_resolution_handles_explicit_loader_and_filters_broad_dirs() {
        let make_elf64 = |pt_interp: Option<&[u8]>| {
            let mut bytes = vec![0u8; 64 + 56];
            bytes[0..4].copy_from_slice(b"\x7fELF");
            bytes[4] = 2; // ELFCLASS64
            bytes[5] = 1; // ELFDATA2LSB
            bytes[32..40].copy_from_slice(&64u64.to_le_bytes()); // e_phoff
            bytes[54..56].copy_from_slice(&56u16.to_le_bytes()); // e_phentsize
            bytes[56..58].copy_from_slice(&1u16.to_le_bytes()); // e_phnum
            if let Some(interp) = pt_interp {
                let offset = bytes.len() as u64;
                let mut nul_terminated = interp.to_vec();
                nul_terminated.push(0);
                let filesz = nul_terminated.len() as u64;
                bytes[64..68].copy_from_slice(&3u32.to_le_bytes()); // PT_INTERP
                bytes[64 + 8..64 + 16].copy_from_slice(&offset.to_le_bytes());
                bytes[64 + 32..64 + 40].copy_from_slice(&filesz.to_le_bytes());
                bytes.extend_from_slice(&nul_terminated);
            } else {
                // Single PT_LOAD segment, zero PT_INTERP segments (as on ld-linux.so).
                bytes[64..68].copy_from_slice(&1u32.to_le_bytes());
            }
            bytes
        };

        let dir = tempfile::tempdir().unwrap();
        let custom_lib = dir.path().join("custom-glibc/lib64");
        let capture_dir = dir.path().join("bin");
        fs::create_dir_all(&custom_lib).unwrap();
        fs::create_dir_all(&capture_dir).unwrap();

        let custom_loader = custom_lib.join("ld-linux-x86-64.so.2");
        fs::write(&custom_loader, make_elf64(None)).unwrap();

        let capture_with_custom_interp = capture_dir.join("capture-custom");
        fs::write(
            &capture_with_custom_interp,
            make_elf64(Some(custom_loader.to_str().unwrap().as_bytes())),
        )
        .unwrap();

        let capture_with_std_interp = capture_dir.join("capture-std");
        fs::write(
            &capture_with_std_interp,
            make_elf64(Some(b"/lib64/ld-linux-x86-64.so.2")),
        )
        .unwrap();

        let capture_with_broad_interp = capture_dir.join("capture-broad");
        fs::write(
            &capture_with_broad_interp,
            make_elf64(Some(b"/tmp/ld-linux-x86-64.so.2")),
        )
        .unwrap();

        // 1. Broad directories and traversal paths are filtered out.
        for bad in [
            Path::new("/"),
            Path::new("/tmp"),
            Path::new("/home"),
            Path::new("/nix/store"),
            Path::new("/usr"),
            Path::new("/usr/local"),
            Path::new("/opt"),
            Path::new("/var/tmp"),
            Path::new("/opt/foo/../bar"),
            Path::new("relative/lib"),
        ] {
            assert!(!is_allowed_pt_interp_dir(bad), "expected broad dir rejected: {}", bad.display());
        }
        // Arbitrary unauthenticated `/nix/store/` DSOs are refused unless
        // their specific store directory is authenticated via `PT_INTERP` or
        // `DT_RUNPATH`.
        assert!(!is_allowed_system_runtime_path(
            b"/nix/store/attacker-evil-zlib/lib/libz.so.1",
            &[]
        ));
        assert!(is_allowed_system_runtime_path(
            b"/nix/store/pinned-zlib/lib/libz.so.1",
            &[PathBuf::from("/nix/store/pinned-zlib/lib")]
        ));

        // Verify `DT_RUNPATH` extraction (including `$ORIGIN/../rust/lib` and
        // pinned `/nix/store/<pkg>/lib`, while still filtering `/nix/store`).
        let runpath_elf = capture_dir.join("capture-runpath");
        let runpath_str = b"/nix/store/pinned-zlib/lib:$ORIGIN/../custom-glibc/lib64:/nix/store:/tmp\0";
        let mut elf = vec![0u8; 64 + 56 * 2];
        elf[0..4].copy_from_slice(b"\x7fELF");
        elf[4] = 2;
        elf[5] = 1;
        elf[32..40].copy_from_slice(&64u64.to_le_bytes()); // e_phoff
        elf[54..56].copy_from_slice(&56u16.to_le_bytes()); // e_phentsize
        elf[56..58].copy_from_slice(&2u16.to_le_bytes()); // e_phnum
        let dyn_offset = elf.len() as u64;
        let dyn_size = (4 * 16) as u64;
        let strtab_offset = dyn_offset + dyn_size;
        let strtab_size = runpath_str.len() as u64;
        let total_size = strtab_offset + strtab_size;
        // PHDR 0: PT_LOAD covering the entire file at vaddr == file offset.
        elf[64..68].copy_from_slice(&1u32.to_le_bytes());
        elf[64 + 8..64 + 16].copy_from_slice(&0u64.to_le_bytes());
        elf[64 + 16..64 + 24].copy_from_slice(&0u64.to_le_bytes());
        elf[64 + 32..64 + 40].copy_from_slice(&total_size.to_le_bytes());
        // PHDR 1: PT_DYNAMIC
        let p1 = 64 + 56;
        elf[p1..p1 + 4].copy_from_slice(&2u32.to_le_bytes());
        elf[p1 + 8..p1 + 16].copy_from_slice(&dyn_offset.to_le_bytes());
        elf[p1 + 32..p1 + 40].copy_from_slice(&dyn_size.to_le_bytes());
        // Dynamic table entries: DT_STRTAB(5), DT_STRSZ(10), DT_RUNPATH(29), DT_NULL(0)
        for (tag, val) in [
            (5i64, strtab_offset),
            (10i64, strtab_size),
            (29i64, 0u64),
            (0i64, 0u64),
        ] {
            elf.extend_from_slice(&tag.to_le_bytes());
            elf.extend_from_slice(&val.to_le_bytes());
        }
        elf.extend_from_slice(runpath_str);
        fs::write(&runpath_elf, &elf).unwrap();
        let runpath_info = inspect_elf64_pt_interp(&runpath_elf, None).unwrap();
        assert!(
            runpath_info
                .dirs
                .contains(&PathBuf::from("/nix/store/pinned-zlib/lib")),
            "expected pinned nix store runpath dir in {:?}",
            runpath_info.dirs
        );
        assert!(
            runpath_info.dirs.contains(&fs::canonicalize(&custom_lib).unwrap()),
            "expected $ORIGIN-expanded dir in {:?}",
            runpath_info.dirs
        );
        assert!(!runpath_info.dirs.contains(&PathBuf::from("/nix/store")));
        assert!(!runpath_info.dirs.contains(&PathBuf::from("/tmp")));
        assert!(is_allowed_pt_interp_dir(&custom_lib));
        let broad_info = inspect_elf64_pt_interp(&capture_with_broad_interp, None).unwrap();
        assert!(broad_info.has_pt_interp);
        assert!(broad_info.dirs.is_empty());

        let fmt_dev_ino = |p: &Path| {
            let (dev, ino) = regular_file_dev_ino(p).unwrap();
            let major = ((dev >> 8) & 0xfff) | ((dev >> 32) & !0xfff);
            let minor = (dev & 0xff) | ((dev >> 12) & !0xff);
            format!("{major:02x}:{minor:02x} {ino}")
        };

        // 2. Explicit dynamic-loader launch (`/proc/self/exe` = custom loader
        //    without `PT_INTERP`, `self_vma_path` = capture binary with
        //    standard `PT_INTERP`) discovers `custom_lib` and passes residency.
        let std_cap_id = fmt_dev_ino(&capture_with_std_interp);
        let loader_id = fmt_dev_ino(&custom_loader);
        let explicit_maps = format!(
            "555555554000-555555558000 r-xp 00000000 {std_cap_id}   {}\n\
             7f0000300000-7f0000400000 r-xp 00000000 {loader_id}   {}\n\
             7f0000400000-7f0000500000 r-xp 00000000 08:01 778   {}/libc.so.6\n",
            capture_with_std_interp.display(),
            custom_loader.display(),
            custom_lib.display(),
        );
        let resolved_dirs = resolve_runtime_pt_interp_dirs(
            explicit_maps.as_bytes(),
            0x5555_5555_5000,
            &custom_loader,
        );
        let canon_custom_lib = fs::canonicalize(&custom_lib).unwrap();
        assert!(
            resolved_dirs.contains(&canon_custom_lib),
            "expected explicit loader dir in {resolved_dirs:?}"
        );

        let static_sysroot = dir.path().join("static-sysroot");
        fs::create_dir_all(static_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib"))
            .unwrap();
        let id = verify_maps_residency(
            explicit_maps.as_bytes(),
            &static_sysroot,
            "x86_64-unknown-linux-gnu",
            0x5555_5555_5000,
            0x5555_5555_6000,
            &custom_loader,
            &resolved_dirs,
        )
        .unwrap();
        assert_eq!(id.linkage, DriverLinkage::StaticExe);

        // 3. Explicit launch via a different loader where `self_vma_path` has a
        //    custom `PT_INTERP` still extracts `self_vma_path`'s `PT_INTERP`
        //    directory even when `self_exe` itself has no `PT_INTERP`.
        let other_loader = dir.path().join("alt-loader/ld-linux.so");
        fs::create_dir_all(other_loader.parent().unwrap()).unwrap();
        fs::write(&other_loader, make_elf64(None)).unwrap();
        let custom_cap_id = fmt_dev_ino(&capture_with_custom_interp);
        let custom_vma_maps = format!(
            "555555554000-555555558000 r-xp 00000000 {custom_cap_id}   {}\n",
            capture_with_custom_interp.display(),
        );
        let vma_dirs = resolve_runtime_pt_interp_dirs(
            custom_vma_maps.as_bytes(),
            0x5555_5555_5000,
            &other_loader,
        );
        assert!(
            vma_dirs.contains(&canon_custom_lib),
            "expected capture VMA PT_INTERP dir in {vma_dirs:?}"
        );

        // 4. A direct launch whose `/proc/self/maps` device is the superblock
        //    device (as on Btrfs) is still classified as a direct launch, so a
        //    capture binary without `PT_INTERP` does not get its own directory
        //    admitted as a dynamic-loader directory.
        let static_dir = dir.path().join("static-capture");
        fs::create_dir_all(&static_dir).unwrap();
        let static_capture = static_dir.join("capture-static");
        fs::write(&static_capture, make_elf64(None)).unwrap();
        let (static_dev, static_ino) = regular_file_dev_ino(&static_capture).unwrap();
        let superblock_minor = if static_dev == linux_makedev(0, 0x57) { 0x58 } else { 0x57 };
        let process = FakeProcess {
            superblock_dev: linux_makedev(0, superblock_minor),
            memory: Vec::new(),
            modified_pages: BTreeSet::new(),
        };
        let superblock_maps = format!(
            "555555554000-555555558000 r-xp 00000000 00:{superblock_minor:02x} {static_ino}   {}\n",
            static_capture.display(),
        );
        assert!(is_allowed_pt_interp_dir(&fs::canonicalize(&static_dir).unwrap()));
        let static_dirs = resolve_runtime_pt_interp_dirs_with(
            superblock_maps.as_bytes(),
            0x5555_5555_5000,
            &static_capture,
            &process,
        );
        assert!(static_dirs.is_empty(), "{static_dirs:?}");
    }

    #[cfg(unix)]
    #[test]
    fn closed_world_maps_residency_verifies_dso_closure_and_static_driver() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().unwrap();
        let cas = dir.path().join("cas");
        let sysroot = dir.path().join("sysroot");
        let outside = dir.path().join("other-nightly/lib");
        fs::create_dir_all(&cas).unwrap();
        fs::create_dir_all(sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap();
        fs::create_dir_all(&outside).unwrap();

        let self_bin = cas.join("blob-self");
        let driver_blob = cas.join("blob-driver");
        let llvm_blob = cas.join("blob-llvm");
        let rogue_llvm = outside.join("libLLVM.so.22.1-rust-1.98.0-nightly");
        let rogue_cas = cas.join("blob-rogue-unnamed");
        fs::write(&self_bin, b"self-exe-bytes").unwrap();
        fs::write(&driver_blob, b"driver-so-bytes").unwrap();
        fs::write(&llvm_blob, b"llvm-so-bytes").unwrap();
        fs::write(&rogue_llvm, b"mismatched-llvm-bytes").unwrap();
        fs::write(&rogue_cas, b"rogue-cas-dso-bytes").unwrap();

        symlink(&driver_blob, sysroot.join("lib/librustc_driver-abc.so")).unwrap();
        symlink(
            &llvm_blob,
            sysroot.join("lib/libLLVM.so.22.1-rust-1.98.0-nightly"),
        )
        .unwrap();

        let fmt_dev_ino = |p: &Path| {
            let (dev, ino) = regular_file_dev_ino(p).unwrap();
            let major = ((dev >> 8) & 0xfff) | ((dev >> 32) & !0xfff);
            let minor = (dev & 0xff) | ((dev >> 12) & !0xff);
            format!("{major:02x}:{minor:02x} {ino}")
        };

        let self_id = fmt_dev_ino(&self_bin);
        let driver_id = fmt_dev_ino(&driver_blob);
        let llvm_id = fmt_dev_ino(&llvm_blob);
        let rogue_llvm_id = fmt_dev_ino(&rogue_llvm);
        let rogue_cas_id = fmt_dev_ino(&rogue_cas);

        // 1. Dynamic driver with CAS-backed driver + libLLVM + system libc passes.
        let valid_dynamic_maps = format!(
            "555555554000-555555558000 r-xp 00000000 {self_id}   {}\n\
             7f0000100000-7f0000200000 r-xp 00000000 {driver_id}   {}\n\
             7f0000200000-7f0000300000 r-xp 00000000 {llvm_id}   {}\n\
             7f0000300000-7f0000400000 r-xp 00000000 08:01 777   /usr/lib/x86_64-linux-gnu/libc.so.6\n",
            self_bin.display(),
            driver_blob.display(),
            llvm_blob.display(),
        );
        let id = verify_maps_residency(
            valid_dynamic_maps.as_bytes(),
            &sysroot,
            "x86_64-unknown-linux-gnu",
            0x5555_5555_5000,
            0x7f00_0015_0000,
            &self_bin,
            &[],
        )
        .unwrap();
        assert_eq!(id.linkage, DriverLinkage::DynamicDso);
        assert_eq!(id.driver_sha256, sha256_bytes(b"driver-so-bytes"));
        assert_eq!(
            id.dso_digests
                .get("libLLVM.so.22.1-rust-1.98.0-nightly")
                .map(String::as_str),
            Some(sha256_bytes(b"llvm-so-bytes").as_str())
        );

        // 2. Spliced mismatched `libLLVM.so` (even with matching driver) fails closed.
        let spliced_llvm_maps = format!(
            "555555554000-555555558000 r-xp 00000000 {self_id}   {}\n\
             7f0000100000-7f0000200000 r-xp 00000000 {driver_id}   {}\n\
             7f0000200000-7f0000300000 r-xp 00000000 {rogue_llvm_id}   {}\n",
            self_bin.display(),
            driver_blob.display(),
            rogue_llvm.display(),
        );
        let err = verify_maps_residency(
            spliced_llvm_maps.as_bytes(),
            &sysroot,
            "x86_64-unknown-linux-gnu",
            0x5555_5555_5000,
            0x7f00_0015_0000,
            &self_bin,
            &[],
        )
        .unwrap_err();
        assert!(err.diagnostics[0].contains("does not match any library in sysroot"), "{err:?}");

        // 3. Unnamed flat-CAS rogue executable DSO outside sysroot fails closed.
        let rogue_cas_maps = format!(
            "555555554000-555555558000 r-xp 00000000 {self_id}   {}\n\
             7f0000100000-7f0000200000 r-xp 00000000 {driver_id}   {}\n\
             7f0000200000-7f0000300000 r-xp 00000000 {rogue_cas_id}   {}\n",
            self_bin.display(),
            driver_blob.display(),
            rogue_cas.display(),
        );
        let err = verify_maps_residency(
            rogue_cas_maps.as_bytes(),
            &sysroot,
            "x86_64-unknown-linux-gnu",
            0x5555_5555_5000,
            0x7f00_0015_0000,
            &self_bin,
            &[],
        )
        .unwrap_err();
        assert!(
            err.diagnostics[0].contains("does not belong to verified sysroot"),
            "{err:?}"
        );

        // 4. Static-linked `rustc_private` driver (`driver_addr` in self VMA,
        //    zero `librustc_driver-*.so` in sysroot) succeeds by hashing self exe.
        let static_sysroot = dir.path().join("static-sysroot");
        fs::create_dir_all(static_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib"))
            .unwrap();
        let custom_loader_dir = dir.path().join("custom-sysroot/lib64");
        let static_maps = format!(
            "555555554000-555555558000 r-xp 00000000 {self_id}   {}\n\
             7f0000300000-7f0000400000 r-xp 00000000 08:01 778   {}/libc.so.6\n",
            self_bin.display(),
            custom_loader_dir.display(),
        );
        let static_id = verify_maps_residency(
            static_maps.as_bytes(),
            &static_sysroot,
            "x86_64-unknown-linux-gnu",
            0x5555_5555_5000,
            0x5555_5555_6000,
            &self_bin,
            &[custom_loader_dir],
        )
        .unwrap();
        assert_eq!(static_id.linkage, DriverLinkage::StaticExe);
        assert_eq!(static_id.driver_sha256, sha256_bytes(b"self-exe-bytes"));

        // 5. Static-linked driver with a stray `libLLVM` DSO mapped fails closed.
        let static_stray_maps = format!(
            "555555554000-555555558000 r-xp 00000000 {self_id}   {}\n\
             7f0000200000-7f0000300000 r-xp 00000000 {rogue_llvm_id}   {}\n",
            self_bin.display(),
            rogue_llvm.display(),
        );
        let err = verify_maps_residency(
            static_stray_maps.as_bytes(),
            &static_sysroot,
            "x86_64-unknown-linux-gnu",
            0x5555_5555_5000,
            0x5555_5555_6000,
            &self_bin,
            &[],
        )
        .unwrap_err();
        assert!(
            err.diagnostics[0].contains("statically linked capture driver unexpectedly mapped"),
            "{err:?}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn runtime_closure_authenticates_split_symlinks_and_transitive_runpath() {
        use std::os::unix::fs::symlink;

        let make_runpath_elf = |runpath: &[u8]| {
            let mut elf = vec![0u8; 64 + 56 * 2];
            elf[0..4].copy_from_slice(b"\x7fELF");
            elf[4] = 2; // ELFCLASS64
            elf[5] = 1; // ELFDATA2LSB
            elf[32..40].copy_from_slice(&64u64.to_le_bytes()); // e_phoff
            elf[54..56].copy_from_slice(&56u16.to_le_bytes()); // e_phentsize
            elf[56..58].copy_from_slice(&2u16.to_le_bytes()); // e_phnum
            let dyn_offset = elf.len() as u64;
            let dyn_size = (4 * 16) as u64;
            let strtab_offset = dyn_offset + dyn_size;
            let mut strtab = runpath.to_vec();
            strtab.push(0);
            let strtab_size = strtab.len() as u64;
            let total_size = strtab_offset + strtab_size;
            // PHDR 0: PT_LOAD covering the entire file at vaddr == file offset.
            elf[64..68].copy_from_slice(&1u32.to_le_bytes());
            elf[64 + 8..64 + 16].copy_from_slice(&0u64.to_le_bytes());
            elf[64 + 16..64 + 24].copy_from_slice(&0u64.to_le_bytes());
            elf[64 + 32..64 + 40].copy_from_slice(&total_size.to_le_bytes());
            // PHDR 1: PT_DYNAMIC
            let p1 = 64 + 56;
            elf[p1..p1 + 4].copy_from_slice(&2u32.to_le_bytes());
            elf[p1 + 8..p1 + 16].copy_from_slice(&dyn_offset.to_le_bytes());
            elf[p1 + 32..p1 + 40].copy_from_slice(&dyn_size.to_le_bytes());
            for (tag, val) in [
                (5i64, strtab_offset), // DT_STRTAB
                (10i64, strtab_size),  // DT_STRSZ
                (29i64, 0u64),         // DT_RUNPATH
                (0i64, 0u64),          // DT_NULL
            ] {
                elf.extend_from_slice(&tag.to_le_bytes());
                elf.extend_from_slice(&val.to_le_bytes());
            }
            elf.extend_from_slice(&strtab);
            elf
        };

        let dir = tempfile::tempdir().unwrap();
        let sysroot = dir.path().join("sysroot");
        let gcc_lib = dir.path().join("gcc-15.2.0-lib/lib");
        let gcc_libgcc = dir.path().join("gcc-15.2.0-libgcc/lib");
        let trans_dep_lib = dir.path().join("trans-dep/lib");
        let evil_lib = dir.path().join("attacker-evil/lib");
        fs::create_dir_all(sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap();
        fs::create_dir_all(&gcc_lib).unwrap();
        fs::create_dir_all(&gcc_libgcc).unwrap();
        fs::create_dir_all(&trans_dep_lib).unwrap();
        fs::create_dir_all(&evil_lib).unwrap();

        let self_bin = dir.path().join("anneal-rustc-capture");
        let driver_so = sysroot.join("lib/librustc_driver-abc.so");
        // `libstdc++.so.6` in `gcc_lib` declares a transitive `DT_RUNPATH` to `trans_dep_lib`.
        let libstdcxx = gcc_lib.join("libstdc++.so.6");
        let real_libgcc = gcc_libgcc.join("libgcc_s.so.1");
        let unrelated_libgcc_pkg = gcc_libgcc.join("libunrelated.so");
        let trans_so = trans_dep_lib.join("libtrans.so.1");
        let evil_libgcc = evil_lib.join("libgcc_s.so.1");
        let llvm_target = dir.path().join("outside/libLLVM.so.22");
        fs::create_dir_all(llvm_target.parent().unwrap()).unwrap();

        fs::write(&self_bin, b"self").unwrap();
        fs::write(&driver_so, b"driver").unwrap();
        fs::write(
            &libstdcxx,
            make_runpath_elf(trans_dep_lib.to_str().unwrap().as_bytes()),
        )
        .unwrap();
        fs::write(&real_libgcc, b"real-libgcc").unwrap();
        fs::write(&unrelated_libgcc_pkg, b"unrelated").unwrap();
        fs::write(&trans_so, b"trans").unwrap();
        fs::write(&evil_libgcc, b"evil-libgcc").unwrap();
        fs::write(&llvm_target, b"evil-llvm").unwrap();

        // Split-output Nix symlink: `gcc-lib/lib/libgcc_s.so.1 -> gcc-libgcc/lib/libgcc_s.so.1`.
        symlink(&real_libgcc, gcc_lib.join("libgcc_s.so.1")).unwrap();
        // Symlink inside `gcc-lib/lib` pointing to a toolchain DSO or `cwd` must NEVER admit it.
        symlink(&llvm_target, gcc_lib.join("libnot_llvm_alias.so")).unwrap();
        if let Ok(cwd) = std::env::current_dir() {
            assert!(!is_allowed_runtime_symlink_target(&cwd.join("libcwd.so")));
        }
        assert!(!is_allowed_runtime_symlink_target(Path::new("/tmp/libbad.so")));
        assert!(!is_allowed_runtime_symlink_target(Path::new("/nix/store/libbad.so")));
        assert!(!is_allowed_runtime_symlink_target(&llvm_target));

        let fmt_dev_ino = |p: &Path| {
            let (dev, ino) = regular_file_dev_ino(p).unwrap();
            let major = ((dev >> 8) & 0xfff) | ((dev >> 32) & !0xfff);
            let minor = (dev & 0xff) | ((dev >> 12) & !0xff);
            format!("{major:02x}:{minor:02x} {ino}")
        };

        let self_id = fmt_dev_ino(&self_bin);
        let driver_id = fmt_dev_ino(&driver_so);
        let stdcxx_id = fmt_dev_ino(&libstdcxx);
        let libgcc_id = fmt_dev_ino(&real_libgcc);
        let unrelated_id = fmt_dev_ino(&unrelated_libgcc_pkg);
        let trans_id = fmt_dev_ino(&trans_so);
        let evil_id = fmt_dev_ino(&evil_libgcc);
        let llvm_id = fmt_dev_ino(&llvm_target);

        // 1. Valid split-output symlink (`gcc-lib/lib/libgcc_s.so.1 -> gcc-libgcc/...`)
        //    plus transitive `DT_RUNPATH` (`libstdc++.so.6 -> trans-dep/lib/libtrans.so.1`) pass.
        let valid_maps = format!(
            "555555554000-555555558000 r-xp 00000000 {self_id}   {}\n\
             7f0000100000-7f0000200000 r-xp 00000000 {driver_id}   {}\n\
             7f0000200000-7f0000300000 r-xp 00000000 {stdcxx_id}   {}\n\
             7f0000300000-7f0000400000 r-xp 00000000 {libgcc_id}   {}\n\
             7f0000400000-7f0000500000 r-xp 00000000 {trans_id}   {}\n",
            self_bin.display(),
            driver_so.display(),
            libstdcxx.display(),
            real_libgcc.display(),
            trans_so.display(),
        );
        verify_maps_residency(
            valid_maps.as_bytes(),
            &sysroot,
            "x86_64-unknown-linux-gnu",
            0x5555_5555_5000,
            0x7f00_0015_0000,
            &self_bin,
            std::slice::from_ref(&gcc_lib),
        )
        .unwrap();

        // 2. Unrelated sibling file inside `gcc-libgcc/lib` (never symlinked from `gcc-lib/lib`) fails.
        let sibling_maps = format!(
            "555555554000-555555558000 r-xp 00000000 {self_id}   {}\n\
             7f0000100000-7f0000200000 r-xp 00000000 {driver_id}   {}\n\
             7f0000300000-7f0000400000 r-xp 00000000 {unrelated_id}   {}\n",
            self_bin.display(),
            driver_so.display(),
            unrelated_libgcc_pkg.display(),
        );
        assert!(
            verify_maps_residency(
                sibling_maps.as_bytes(),
                &sysroot,
                "x86_64-unknown-linux-gnu",
                0x5555_5555_5000,
                0x7f00_0015_0000,
                &self_bin,
                std::slice::from_ref(&gcc_lib),
            )
            .is_err()
        );

        // 3. Unauthenticated `/nix/store/attacker-evil/lib/libgcc_s.so.1` fails closed.
        let evil_maps = format!(
            "555555554000-555555558000 r-xp 00000000 {self_id}   {}\n\
             7f0000100000-7f0000200000 r-xp 00000000 {driver_id}   {}\n\
             7f0000300000-7f0000400000 r-xp 00000000 {evil_id}   {}\n",
            self_bin.display(),
            driver_so.display(),
            evil_libgcc.display(),
        );
        assert!(
            verify_maps_residency(
                evil_maps.as_bytes(),
                &sysroot,
                "x86_64-unknown-linux-gnu",
                0x5555_5555_5000,
                0x7f00_0015_0000,
                &self_bin,
                std::slice::from_ref(&gcc_lib),
            )
            .is_err()
        );

        // 4. Symlink inside `gcc-lib/lib` targeting a toolchain DSO (`libLLVM*`) is rejected.
        let llvm_symlink_maps = format!(
            "555555554000-555555558000 r-xp 00000000 {self_id}   {}\n\
             7f0000100000-7f0000200000 r-xp 00000000 {driver_id}   {}\n\
             7f0000300000-7f0000400000 r-xp 00000000 {llvm_id}   {}\n",
            self_bin.display(),
            driver_so.display(),
            llvm_target.display(),
        );
        assert!(
            verify_maps_residency(
                llvm_symlink_maps.as_bytes(),
                &sysroot,
                "x86_64-unknown-linux-gnu",
                0x5555_5555_5000,
                0x7f00_0015_0000,
                &self_bin,
                std::slice::from_ref(&gcc_lib),
            )
            .is_err()
        );
    }

    #[test]
    fn parses_fdinfo_mount_ids_mountinfo_devices_and_auxv_page_size() {
        assert_eq!(
            parse_fdinfo_mnt_id(b"pos:\t0\nflags:\t02100000\nmnt_id:\t965\nino:\t151003\n"),
            Some(965)
        );
        assert_eq!(parse_fdinfo_mnt_id(b"pos:\t0\nflags:\t02100000\n"), None);

        // Recorded from a host whose home directory is a Btrfs subvolume.
        // `/proc/self/maps` printed `00:57` for a file under `/home/user`,
        // while `fstat(2)` reported `0:59`. `mountinfo` prints `major:minor`
        // in decimal, so `0:87` is the `0x57` device that maps reports.
        let mountinfo = b"\
919 391 0:49 / / rw,relatime shared:755 - overlay overlay rw,lowerdir=/l1:/l2,upperdir=/u,workdir=/w,uuid=on\n\
943 919 7:0 /tmp /tmp rw,relatime shared:780 - ext4 /dev/loop0 rw\n\
964 919 0:87 / /var/lib/pool rw,nosuid,nodev,noatime shared:800 - btrfs /dev/loop1 rw,subvolid=5,subvol=/\n\
965 919 0:87 /@home /home/user rw,nosuid,nodev,noatime shared:801 - btrfs /dev/loop1 rw,subvolid=256,subvol=/@home\n";
        let maps_dev = parse_maps_line(
            b"7f0000100000-7f0000101000 r--p 00000000 00:57 151003   /home/user/f",
        )
        .unwrap()
        .dev;
        assert_eq!(parse_mountinfo_dev(mountinfo, 965), Some(maps_dev));
        assert_eq!(parse_mountinfo_dev(mountinfo, 964), Some(maps_dev));
        assert_eq!(parse_mountinfo_dev(mountinfo, 943), Some(linux_makedev(7, 0)));
        assert_eq!(parse_mountinfo_dev(mountinfo, 1), None);
        // A duplicated mount ID is ambiguous and must not resolve.
        let duplicated = b"5 1 0:40 / /a rw - ext4 a rw\n5 1 0:41 / /b rw - ext4 b rw\n";
        assert_eq!(parse_mountinfo_dev(duplicated, 5), None);

        let word = size_of::<usize>();
        let mut auxv = Vec::new();
        for (key, value) in [(33usize, 0x7fffusize), (6, 16384), (0, 0)] {
            auxv.extend_from_slice(&key.to_ne_bytes());
            auxv.extend_from_slice(&value.to_ne_bytes());
        }
        assert_eq!(parse_auxv_page_size(&auxv), Some(16384));
        assert_eq!(parse_auxv_page_size(&auxv[2 * word..][..2 * word]), Some(16384));
        assert_eq!(parse_auxv_page_size(&auxv[..2 * word]), None);
        let mut bad_page = Vec::new();
        for (key, value) in [(6usize, 4095usize), (0, 0)] {
            bad_page.extend_from_slice(&key.to_ne_bytes());
            bad_page.extend_from_slice(&value.to_ne_bytes());
        }
        assert_eq!(parse_auxv_page_size(&bad_page), None);

        let present = 1u64 << 63;
        let swapped = 1u64 << 62;
        let file_page = 1u64 << 61;
        assert!(pagemap_entry_reflects_file(0));
        assert!(pagemap_entry_reflects_file(present | file_page));
        assert!(!pagemap_entry_reflects_file(present));
        assert!(!pagemap_entry_reflects_file(swapped));
        assert!(!pagemap_entry_reflects_file(swapped | file_page));
    }

    /// Page size of [`FakeProcess`].
    const FAKE_PAGE: usize = 4096;

    /// [`ProcessView`] in which every file appears to live on one superblock,
    /// as all subvolumes of a Btrfs filesystem do.
    struct FakeProcess {
        superblock_dev: u64,
        /// Mapped address ranges and their contents.
        memory: Vec<(usize, Vec<u8>)>,
        /// Start addresses of pages that hold private anonymous copies.
        modified_pages: BTreeSet<usize>,
    }

    impl ProcessView for FakeProcess {
        fn superblock_dev(&self, _file: &fs::File) -> io::Result<u64> {
            Ok(self.superblock_dev)
        }

        fn page_size(&self) -> io::Result<usize> {
            Ok(FAKE_PAGE)
        }

        fn pagemap(&self, addr: usize, count: usize) -> io::Result<Vec<u64>> {
            Ok((0..count)
                .map(|i| {
                    if self.modified_pages.contains(&(addr + i * FAKE_PAGE)) {
                        1 << 63
                    } else {
                        (1 << 63) | (1 << 61)
                    }
                })
                .collect())
        }

        fn read_memory(&self, addr: usize, buf: &mut [u8]) -> io::Result<()> {
            for (start, bytes) in &self.memory {
                if addr >= *start && addr + buf.len() <= start + bytes.len() {
                    buf.copy_from_slice(&bytes[addr - start..][..buf.len()]);
                    return Ok(());
                }
            }
            Err(io::Error::new(io::ErrorKind::InvalidInput, "unmapped address"))
        }
    }

    /// Return `bytes` zero-padded to a whole number of [`FAKE_PAGE`] pages, as
    /// the kernel maps a file's final partial page.
    fn page_padded(bytes: &[u8]) -> Vec<u8> {
        let mut padded = bytes.to_vec();
        padded.resize(bytes.len().div_ceil(FAKE_PAGE) * FAKE_PAGE, 0);
        padded
    }

    #[cfg(unix)]
    #[test]
    fn superblock_device_matches_require_mapped_contents_to_equal_hashed_file() {
        use std::os::unix::fs::MetadataExt;

        const DRIVER_ADDR: usize = 0x7f00_0010_0000;
        const DRIVER_RODATA_ADDR: usize = 0x7f00_0011_0000;
        const DRIVER_DATA_ADDR: usize = 0x7f00_0012_0000;
        const LLVM_ADDR: usize = 0x7f00_0020_0000;
        const SELF_ADDR: usize = 0x5555_5555_4000;

        let dir = tempfile::tempdir().unwrap();
        let sysroot = dir.path().join("sysroot");
        fs::create_dir_all(sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap();
        let self_bin = dir.path().join("anneal-rustc-capture");
        let driver_so = sysroot.join("lib/librustc_driver-abc.so");
        let llvm_so = sysroot.join("lib/libLLVM.so.22.1-rust-1.98.0-nightly");

        // Three pages: text, read-only data, and writable data.
        let driver_bytes: Vec<u8> = (0..3 * FAKE_PAGE - 100).map(|i| (i % 251) as u8).collect();
        let llvm_bytes: Vec<u8> = (0..FAKE_PAGE + 7).map(|i| (i % 241) as u8).collect();
        let self_bytes: Vec<u8> = (0..FAKE_PAGE / 2).map(|i| (i % 239) as u8).collect();
        fs::write(&driver_so, &driver_bytes).unwrap();
        fs::write(&llvm_so, &llvm_bytes).unwrap();
        fs::write(&self_bin, &self_bytes).unwrap();

        // Report every file under a superblock device that differs from what
        // `fstat(2)` returns, as on a Btrfs subvolume.
        let stat_dev = fs::metadata(&driver_so).unwrap().dev();
        let superblock_dev = if stat_dev == linux_makedev(0, 0x57) {
            linux_makedev(0, 0x58)
        } else {
            linux_makedev(0, 0x57)
        };
        let fmt_id = |p: &Path| {
            let ino = fs::metadata(p).unwrap().ino();
            let major = ((superblock_dev >> 8) & 0xfff) | ((superblock_dev >> 32) & !0xfff);
            let minor = (superblock_dev & 0xff) | ((superblock_dev >> 12) & !0xff);
            format!("{major:02x}:{minor:02x} {ino}")
        };
        let maps_for = |driver_id: &str, llvm_id: &str, self_id: &str| {
            format!(
                "555555554000-555555555000 r-xp 00000000 {self_id}   {self}\n\
                 7f0000100000-7f0000101000 r-xp 00000000 {driver_id}   {driver}\n\
                 7f0000110000-7f0000111000 r--p 00001000 {driver_id}   {driver}\n\
                 7f0000120000-7f0000121000 rw-p 00002000 {driver_id}   {driver}\n\
                 7f0000200000-7f0000202000 r-xp 00000000 {llvm_id}   {llvm}\n\
                 7f0000300000-7f0000400000 r-xp 00000000 08:01 777   /usr/lib/x86_64-linux-gnu/libc.so.6\n",
                self = self_bin.display(),
                driver = driver_so.display(),
                llvm = llvm_so.display(),
            )
        };
        let driver_id = fmt_id(&driver_so);
        let llvm_id = fmt_id(&llvm_so);
        let self_id = fmt_id(&self_bin);
        let maps = maps_for(&driver_id, &llvm_id, &self_id);

        let padded_driver = page_padded(&driver_bytes);
        let genuine_memory = |driver_text: &[u8], driver_rodata: &[u8]| {
            // The writable page holds relocated data that differs from the
            // file and is marked as a private copy below.
            let relocated = vec![0xa5u8; FAKE_PAGE];
            vec![
                (SELF_ADDR, page_padded(&self_bytes)),
                (DRIVER_ADDR, driver_text.to_vec()),
                (DRIVER_RODATA_ADDR, driver_rodata.to_vec()),
                (DRIVER_DATA_ADDR, relocated),
                (LLVM_ADDR, page_padded(&llvm_bytes)),
            ]
        };
        let process = |memory: Vec<(usize, Vec<u8>)>, modified: &[usize]| FakeProcess {
            superblock_dev,
            memory,
            modified_pages: modified.iter().copied().collect(),
        };
        let verify = |maps: &str, process: &FakeProcess| {
            verify_maps_residency_with(
                MapsView {
                    bytes: maps.as_bytes(),
                    process,
                },
                &sysroot,
                "x86_64-unknown-linux-gnu",
                SELF_ADDR,
                DRIVER_ADDR + 0x10,
                &self_bin,
                &[],
            )
        };
        let text = &padded_driver[..FAKE_PAGE];
        let rodata = &padded_driver[FAKE_PAGE..2 * FAKE_PAGE];

        // 1. The genuine sysroot files pass even though no `fstat(2)` device
        //    equals the device printed in `/proc/self/maps`.
        let genuine = process(genuine_memory(text, rodata), &[DRIVER_DATA_ADDR]);
        let id = verify(&maps, &genuine).unwrap();
        assert_eq!(id.linkage, DriverLinkage::DynamicDso);
        assert_eq!(id.driver_sha256, sha256_bytes(&driver_bytes));
        assert_eq!(
            id.dso_digests
                .get("libLLVM.so.22.1-rust-1.98.0-nightly")
                .map(String::as_str),
            Some(sha256_bytes(&llvm_bytes).as_str())
        );

        // 2. A writable page that still shares the page cache must match too.
        let unmodified_data = process(genuine_memory(text, rodata), &[]);
        let err = verify(&maps, &unmodified_data).unwrap_err();
        assert!(err.diagnostics[0].contains("does not match"), "{err:?}");

        // 3. A different inode with the same superblock and inode number (a
        //    file in another Btrfs subvolume) mapped in place of the driver
        //    fails, whether it differs in code or only in read-only data.
        let mut evil_text = text.to_vec();
        evil_text[17] ^= 0xff;
        let swapped_text = process(genuine_memory(&evil_text, rodata), &[DRIVER_DATA_ADDR]);
        let err = verify(&maps, &swapped_text).unwrap_err();
        assert!(err.diagnostics[0].contains("does not match"), "{err:?}");
        let mut evil_rodata = rodata.to_vec();
        evil_rodata[FAKE_PAGE - 1] ^= 0x01;
        let swapped_rodata = process(genuine_memory(text, &evil_rodata), &[DRIVER_DATA_ADDR]);
        let err = verify(&maps, &swapped_rodata).unwrap_err();
        assert!(err.diagnostics[0].contains("does not match"), "{err:?}");

        // 4. A privately modified executable page fails even if its contents
        //    happen to equal the file.
        let patched_text = process(
            genuine_memory(text, rodata),
            &[DRIVER_ADDR, DRIVER_DATA_ADDR],
        );
        let err = verify(&maps, &patched_text).unwrap_err();
        assert!(err.diagnostics[0].contains("does not match"), "{err:?}");

        // 5. A swapped toolchain DSO fails.
        let mut memory = genuine_memory(text, rodata);
        memory[4].1[3] ^= 0xff;
        let swapped_llvm = process(memory, &[DRIVER_DATA_ADDR]);
        let err = verify(&maps, &swapped_llvm).unwrap_err();
        assert!(err.diagnostics[0].contains("sysroot toolchain DSO"), "{err:?}");

        // 6. A file on a different superblock fails without comparing memory.
        let other_superblock = FakeProcess {
            superblock_dev: superblock_dev + 1,
            ..process(genuine_memory(text, rodata), &[DRIVER_DATA_ADDR])
        };
        let err = verify(&maps, &other_superblock).unwrap_err();
        assert!(
            err.diagnostics[0].contains("loaded rustc driver does not match"),
            "{err:?}"
        );

        // 7. A different file at the sysroot path fails even with identical
        //    contents. The displaced file stays alive so its inode number is
        //    not reused.
        let displaced = dir.path().join("displaced-driver");
        fs::rename(&driver_so, &displaced).unwrap();
        fs::write(&driver_so, &driver_bytes).unwrap();
        let err = verify(&maps, &genuine).unwrap_err();
        assert!(err.diagnostics[0].contains("does not match"), "{err:?}");
        fs::rename(&displaced, &driver_so).unwrap();
        verify(&maps, &genuine).unwrap();

        // 8. Two same-named non-toolchain sysroot libraries are each confirmed
        //    by their own contents; digesting one never vouches for the other,
        //    and the manifest cannot record both if their contents differ.
        const HELPER_ADDR: usize = 0x7f00_0050_0000;
        const HOST_HELPER_ADDR: usize = 0x7f00_0060_0000;
        let helper = sysroot.join("lib/libhelper.so.1");
        let host_helper = sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib/libhelper.so.1");
        let helper_bytes = vec![0x11u8; 64];
        let evil_bytes = vec![0x22u8; 64];
        fs::write(&helper, &helper_bytes).unwrap();
        fs::write(&host_helper, &helper_bytes).unwrap();
        let helper_maps = format!(
            "{maps}\
             7f0000500000-7f0000501000 r-xp 00000000 {}   {}\n\
             7f0000600000-7f0000601000 r-xp 00000000 {}   {}\n",
            fmt_id(&helper),
            helper.display(),
            fmt_id(&host_helper),
            host_helper.display(),
        );
        let with_helpers = |host_helper_memory: &[u8]| {
            let mut memory = genuine_memory(text, rodata);
            memory.push((HELPER_ADDR, page_padded(&helper_bytes)));
            memory.push((HOST_HELPER_ADDR, page_padded(host_helper_memory)));
            process(memory, &[DRIVER_DATA_ADDR])
        };
        let id = verify(&helper_maps, &with_helpers(&helper_bytes)).unwrap();
        assert_eq!(
            id.dso_digests.get("libhelper.so.1").map(String::as_str),
            Some(sha256_bytes(&helper_bytes).as_str())
        );
        // A mapping that no candidate backs is then judged as a non-sysroot
        // mapping, which this path is not allowed to be.
        let err = verify(&helper_maps, &with_helpers(&evil_bytes)).unwrap_err();
        assert!(
            err.diagnostics[0].contains("does not belong to verified sysroot"),
            "{err:?}"
        );
        fs::write(&host_helper, &evil_bytes).unwrap();
        let err = verify(&helper_maps, &with_helpers(&evil_bytes)).unwrap_err();
        assert!(err.diagnostics[0].contains("different contents"), "{err:?}");
        fs::remove_file(&helper).unwrap();
        fs::remove_file(&host_helper).unwrap();

        // 9. A mapping whose pathname opens to a different inode fails even if
        //    its contents match, so a substitute that stays at its own path is
        //    rejected regardless of what its skipped pages hold.
        let driver_copy = dir.path().join("driver-copy");
        fs::write(&driver_copy, &driver_bytes).unwrap();
        let moved_rodata_maps = maps.replacen(
            &format!("00001000 {driver_id}   {}", driver_so.display()),
            &format!("00001000 {driver_id}   {}", driver_copy.display()),
            1,
        );
        assert_ne!(moved_rodata_maps, maps);
        let err = verify(&moved_rodata_maps, &genuine).unwrap_err();
        assert!(
            err.diagnostics[0].contains("loaded rustc driver does not match"),
            "{err:?}"
        );
        // The same holds for the writable range, whose modified page is never
        // compared.
        let moved_data_maps = maps.replacen(
            &format!("00002000 {driver_id}   {}", driver_so.display()),
            &format!("00002000 {driver_id}   {}", driver_copy.display()),
            1,
        );
        assert_ne!(moved_data_maps, maps);
        let err = verify(&moved_data_maps, &genuine).unwrap_err();
        assert!(
            err.diagnostics[0].contains("loaded rustc driver does not match"),
            "{err:?}"
        );
        let driver_meta = fs::metadata(&driver_so).unwrap();
        let driver_path = driver_so.as_os_str().as_encoded_bytes().to_vec();
        assert!(maps_pathname_opens_to(Some(&driver_path), &driver_meta));
        let mut deleted = driver_path.clone();
        deleted.extend_from_slice(b" (deleted)");
        let copy_path = driver_copy.as_os_str().as_encoded_bytes().to_vec();
        let dir_path = dir.path().as_os_str().as_encoded_bytes().to_vec();
        // A printed `\012` may stand for a newline in the mapped file's name,
        // so a pathname with a backslash is rejected even when the literal
        // name (here a symlink) opens to the candidate.
        let escaped = dir.path().join("lib\\012x.so");
        std::os::unix::fs::symlink(&driver_so, &escaped).unwrap();
        let escaped_path = escaped.as_os_str().as_encoded_bytes().to_vec();
        for rejected in [
            None,
            Some(b"sysroot/lib/librustc_driver-abc.so".as_slice()),
            Some(deleted.as_slice()),
            Some(copy_path.as_slice()),
            Some(dir_path.as_slice()),
            Some(escaped_path.as_slice()),
        ] {
            assert!(!maps_pathname_opens_to(rejected, &driver_meta), "{rejected:?}");
        }
        fs::remove_file(&escaped).unwrap();
        // A trailing carriage return is likewise part of the printed name, so
        // a mapping of `evil\r` is not confused with a sibling `evil` that
        // links to the candidate.
        let evil = dir.path().join("evil");
        std::os::unix::fs::symlink(&driver_so, &evil).unwrap();
        let cr_maps = maps.replacen(
            &format!("00001000 {driver_id}   {}\n", driver_so.display()),
            &format!("00001000 {driver_id}   {}\r\n", evil.display()),
            1,
        );
        assert_ne!(cr_maps, maps);
        let err = verify(&cr_maps, &genuine).unwrap_err();
        assert!(
            err.diagnostics[0].contains("loaded rustc driver does not match"),
            "{err:?}"
        );
        fs::remove_file(&evil).unwrap();

        // 10a. A rogue executable sharing an admitted system library's
        //      identity is checked under its own pathname rather than hidden
        //      behind the library's.
        let rogue_maps = format!(
            "{maps}7f0000800000-7f0000801000 r-xp 00000000 08:01 777   {}\n",
            driver_copy.display()
        );
        let err = verify(&rogue_maps, &genuine).unwrap_err();
        assert!(
            err.diagnostics[0].contains("does not belong to verified sysroot"),
            "{err:?}"
        );

        let maps_id = |p: &Path| (superblock_dev, fs::metadata(p).unwrap().ino());
        let genuine_view = MapsView {
            bytes: maps.as_bytes(),
            process: &genuine,
        };

        // 10b. A system library whose identity collides with an unmapped
        //      sysroot file is not mistaken for that file; it is admitted by
        //      the ordinary system-library rule.
        let unmapped = sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib/libunmapped.rlib");
        fs::write(&unmapped, b"unmapped rlib").unwrap();
        let colliding_maps = format!(
            "{maps}7f0000900000-7f0000901000 r-xp 00000000 {}   /usr/lib/x86_64-linux-gnu/libz.so.1\n",
            fmt_id(&unmapped)
        );
        let id = verify(&colliding_maps, &genuine).unwrap();
        assert!(!id.dso_digests.contains_key("libunmapped.rlib"), "{:?}", id.dso_digests);
        // A colliding mapping outside the system library directories is
        // still rejected, wherever its pathname sorts.
        let colliding_rogue_maps = format!(
            "{colliding_maps}7f0000a00000-7f0000a01000 r-xp 00000000 {}   /var/evil.so\n",
            fmt_id(&unmapped)
        );
        let err = verify(&colliding_rogue_maps, &genuine).unwrap_err();
        assert!(
            err.diagnostics[0].contains("does not belong to verified sysroot"),
            "{err:?}"
        );
        // An exact identity that no longer confirms is a sysroot file that
        // changed during verification, never a system library.
        let exact_libs: SysrootLibMap = [(
            maps_id(&unmapped),
            vec![SysrootCandidate {
                name: "libunmapped.rlib".to_owned(),
                path: driver_copy.clone(),
                exact: true,
            }],
        )]
        .into_iter()
        .collect();
        let exact_exec: ExecMappings =
            [(maps_id(&unmapped), b"/usr/lib/x86_64-linux-gnu/libz.so.1".to_vec())]
                .into_iter()
                .collect();
        let err = verify_exec_mappings_residency(
            genuine_view,
            &exact_exec,
            &exact_libs,
            &RuntimeClosure {
                dirs: Vec::new(),
                symlink_dev_inos: BTreeSet::new(),
            },
            (0, 0),
            (0, 1),
            &sysroot,
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
        )
        .unwrap_err();
        assert!(err.diagnostics[0].contains("changed during residency"), "{err:?}");
        fs::remove_file(&unmapped).unwrap();

        // 10. Mappings sharing the capture executable's identity are exempt
        //     from the closed-world checks, so each must be confirmed as the
        //     capture executable by path and contents.
        const SHADOW_ADDR: usize = 0x7f00_0070_0000;
        let shadow_maps = |path: &Path| {
            format!(
                "{maps}7f0000700000-7f0000701000 r-xp 00000000 {self_id}   {}\n",
                path.display()
            )
        };
        let with_shadow = |bytes: &[u8]| {
            let mut memory = genuine_memory(text, rodata);
            memory.push((SHADOW_ADDR, page_padded(bytes)));
            process(memory, &[DRIVER_DATA_ADDR])
        };
        verify(&shadow_maps(&self_bin), &with_shadow(&self_bytes)).unwrap();
        let err = verify(&shadow_maps(&driver_copy), &with_shadow(&self_bytes)).unwrap_err();
        assert!(err.diagnostics[0].contains("capture executable failed"), "{err:?}");
        let mut evil_self = self_bytes.clone();
        evil_self[0] ^= 0xff;
        let err = verify(&shadow_maps(&self_bin), &with_shadow(&evil_self)).unwrap_err();
        assert!(err.diagnostics[0].contains("capture executable failed"), "{err:?}");

        // 11. Every sysroot candidate sharing an identity is tried, and the
        //     driver's digest is recorded under the driver's own name even
        //     when another name for the same inode exists.
        let candidates = vec![
            SysrootCandidate {
                name: "libother.so".to_owned(),
                path: driver_copy.clone(),
                exact: false,
            },
            SysrootCandidate {
                name: "librustc_driver-abc.so".to_owned(),
                path: driver_so.clone(),
                exact: false,
            },
        ];
        let (name, digest) =
            hash_matching_sysroot_candidate(&candidates, maps_id(&driver_so), genuine_view)
                .unwrap()
                .unwrap();
        assert_eq!(name, "librustc_driver-abc.so");
        assert_eq!(digest, sha256_bytes(&driver_bytes));
        let alias = sysroot.join("lib/libother.so");
        fs::hard_link(&driver_so, &alias).unwrap();
        let id = verify(&maps, &genuine).unwrap();
        assert_eq!(
            id.dso_digests.get("librustc_driver-abc.so").map(String::as_str),
            Some(sha256_bytes(&driver_bytes).as_str())
        );
        assert!(!id.dso_digests.contains_key("libother.so"), "{:?}", id.dso_digests);
        fs::remove_file(&alias).unwrap();

        // 12. A statically linked driver hashes the capture executable under
        //     the same rule.
        let static_sysroot = dir.path().join("static-sysroot");
        fs::create_dir_all(static_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib"))
            .unwrap();
        let static_maps = format!(
            "555555554000-555555555000 r-xp 00000000 {self_id}   {}\n",
            self_bin.display()
        );
        let verify_static = |process: &FakeProcess| {
            verify_maps_residency_with(
                MapsView {
                    bytes: static_maps.as_bytes(),
                    process,
                },
                &static_sysroot,
                "x86_64-unknown-linux-gnu",
                SELF_ADDR,
                SELF_ADDR + 0x10,
                &self_bin,
                &[],
            )
        };
        let id = verify_static(&genuine).unwrap();
        assert_eq!(id.linkage, DriverLinkage::StaticExe);
        assert_eq!(id.driver_sha256, sha256_bytes(&self_bytes));
        let mut memory = genuine_memory(text, rodata);
        memory[0].1[0] ^= 0xff;
        let err = verify_static(&process(memory, &[])).unwrap_err();
        assert!(err.diagnostics[0].contains("capture executable failed"), "{err:?}");
    }

    #[cfg(unix)]
    #[test]
    fn mapped_page_comparison_rejects_vacuous_and_out_of_bounds_mappings() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("lib.so");
        let bytes: Vec<u8> = (0..FAKE_PAGE + 1).map(|i| (i % 253) as u8).collect();
        fs::write(&path, &bytes).unwrap();
        let process = FakeProcess {
            superblock_dev: 0,
            memory: vec![(0x10000, page_padded(&bytes))],
            modified_pages: BTreeSet::new(),
        };
        let compare = |maps: &str| {
            let segments = collect_mapped_segments(
                MapsView {
                    bytes: maps.as_bytes(),
                    process: &process,
                },
                (linux_makedev(0, 0x57), 42),
                FAKE_PAGE,
            )
            .unwrap();
            let mut file = fs::File::open(&path).unwrap();
            hash_and_compare_mapped_pages(
                &mut file,
                bytes.len() as u64,
                &segments,
                FAKE_PAGE,
                &process,
            )
            .unwrap()
        };

        let process_memory_with = |text: &[u8], extra: &[(usize, Vec<u8>)]| FakeProcess {
            superblock_dev: 0,
            memory: std::iter::once((0x10000, text.to_vec()))
                .chain(extra.iter().cloned())
                .collect(),
            modified_pages: BTreeSet::new(),
        };
        let compare_with = |process: &FakeProcess, maps: &str| {
            let segments = collect_mapped_segments(
                MapsView {
                    bytes: maps.as_bytes(),
                    process,
                },
                (linux_makedev(0, 0x57), 42),
                FAKE_PAGE,
            )
            .unwrap();
            hash_and_compare_mapped_pages(
                &mut fs::File::open(&path).unwrap(),
                bytes.len() as u64,
                &segments,
                FAKE_PAGE,
                process,
            )
            .unwrap()
        };

        assert_eq!(
            compare("10000-12000 r-xp 00000000 00:57 42   /lib.so\n"),
            Some(sha256_bytes(&bytes))
        );
        // Without an executable mapping nothing ties the code to the file.
        assert_eq!(compare("10000-12000 r--p 00000000 00:57 42   /lib.so\n"), None);
        assert_eq!(compare(""), None);
        // A mapping extending a whole page past end-of-file cannot be
        // accessed by the process and is rejected.
        assert_eq!(compare("10000-13000 r-xp 00000000 00:57 42   /lib.so\n"), None);
        // A privately modified executable page fails even when another
        // executable page of the same mapping matches.
        let partly_patched = FakeProcess {
            superblock_dev: 0,
            memory: vec![(0x10000, page_padded(&bytes))],
            modified_pages: [0x11000].into_iter().collect(),
        };
        let segments = collect_mapped_segments(
            MapsView {
                bytes: b"10000-12000 r-xp 00000000 00:57 42   /lib.so\n",
                process: &partly_patched,
            },
            (linux_makedev(0, 0x57), 42),
            FAKE_PAGE,
        )
        .unwrap();
        let digest = hash_and_compare_mapped_pages(
            &mut fs::File::open(&path).unwrap(),
            bytes.len() as u64,
            &segments,
            FAKE_PAGE,
            &partly_patched,
        )
        .unwrap();
        assert_eq!(digest, None);
        // An execute-only range of the same identity is compared too.
        let exec_only_memory = [(0x20000, vec![0xccu8; FAKE_PAGE])];
        let with_exec_only = process_memory_with(&page_padded(&bytes), &exec_only_memory);
        assert_eq!(
            compare_with(
                &with_exec_only,
                "10000-12000 r-xp 00000000 00:57 42   /lib.so\n\
                 20000-21000 --xp 00000000 00:57 42   /lib.so\n"
            ),
            None
        );
        // Bytes past end-of-file in the final partial page must be zero.
        let mut dirty_tail = page_padded(&bytes);
        dirty_tail[bytes.len()] = 1;
        let with_dirty_tail = process_memory_with(&dirty_tail, &[]);
        assert_eq!(
            compare_with(
                &with_dirty_tail,
                "10000-12000 r-xp 00000000 00:57 42   /lib.so\n"
            ),
            None
        );
        // A range whose file offsets overflow is malformed.
        let overflowing = collect_mapped_segments(
            MapsView {
                bytes: b"10000-12000 r-xp fffffffffffff000 00:57 42   /lib.so\n",
                process: &process,
            },
            (linux_makedev(0, 0x57), 42),
            FAKE_PAGE,
        );
        assert!(overflowing.is_err());
        // Inaccessible guard mappings are ignored.
        assert_eq!(
            compare(
                "10000-12000 r-xp 00000000 00:57 42   /lib.so\n\
                 20000-30000 ---p 00002000 00:57 42   /lib.so\n"
            ),
            Some(sha256_bytes(&bytes))
        );
        // Misaligned ranges are malformed.
        let misaligned = collect_mapped_segments(
            MapsView {
                bytes: b"10000-12000 r-xp 00000010 00:57 42   /lib.so\n",
                process: &process,
            },
            (linux_makedev(0, 0x57), 42),
            FAKE_PAGE,
        );
        assert!(misaligned.is_err());
    }

    /// Check the live `/proc/self` view against the kernel's own mapping of
    /// this test executable. On any filesystem, including Btrfs subvolumes
    /// where `fstat(2)` reports a different device, the superblock device of
    /// the opened executable must equal the device `/proc/self/maps` prints.
    #[cfg(target_os = "linux")]
    #[test]
    fn live_process_view_agrees_with_kernel_maps_for_test_executable() {
        use std::os::unix::ffi::OsStrExt;

        let maps = fs::read("/proc/self/maps").unwrap();
        let addr = live_process_view_agrees_with_kernel_maps_for_test_executable as *const ()
            as usize;
        let (maps_id, pathname) = resolve_mapping_dev_ino(&maps, addr, "test executable").unwrap();
        let exe = Path::new(OsStr::from_bytes(pathname)).to_path_buf();
        let process = LiveProcess::default();
        let file = fs::File::open(&exe).unwrap();
        assert_eq!(process.superblock_dev(&file).unwrap(), maps_id.0);

        let page_size = process.page_size().unwrap();
        // Compare only non-writable ranges: other test threads may write this
        // executable's data pages between sampling the pagemap and reading
        // memory, which the production check rightly treats as a mismatch.
        let read_only_maps: Vec<u8> = maps
            .split(|&b| b == b'\n')
            .filter(|line| {
                parse_maps_line(line).is_some_and(|entry| !entry.perms.contains(&b'w'))
            })
            .flat_map(|line| line.iter().copied().chain(std::iter::once(b'\n')))
            .collect();
        let view = MapsView {
            bytes: &read_only_maps,
            process: &process,
        };
        let segments = collect_mapped_segments(view, maps_id, page_size).unwrap();
        let file_len = file.metadata().unwrap().len();
        let expected = sha256_reader(fs::File::open(&exe).unwrap()).unwrap();
        let digest = hash_and_compare_mapped_pages(
            &mut fs::File::open(&exe).unwrap(),
            file_len,
            &segments,
            page_size,
            &process,
        )
        .unwrap();
        assert_eq!(digest, Some(expected));

        // A copy differing in one byte of a page-cache-backed executable page
        // is rejected.
        let text = segments.iter().find(|s| s.executable).unwrap();
        let page = text
            .pagemap
            .iter()
            .position(|&entry| pagemap_entry_reflects_file(entry))
            .unwrap();
        let mut tampered = fs::read(&exe).unwrap();
        tampered[text.file_offset as usize + page * page_size] ^= 0xff;
        let dir = tempfile::tempdir().unwrap();
        let tampered_path = dir.path().join("tampered");
        fs::write(&tampered_path, &tampered).unwrap();
        let digest = hash_and_compare_mapped_pages(
            &mut fs::File::open(&tampered_path).unwrap(),
            file_len,
            &segments,
            page_size,
            &process,
        )
        .unwrap();
        assert_eq!(digest, None);
    }
}
