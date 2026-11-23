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

/// Linkage mode observed for `rustc_driver::run_compiler` in the live process.
#[cfg(any(target_os = "linux", test))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DriverLinkage {
    /// `rustc_driver::run_compiler` lives in a dynamically loaded
    /// `librustc_driver-*.so` verified against the sysroot.
    DynamicDso,
    /// `rustc_driver::run_compiler` is statically linked into the capture
    /// executable itself (zero `librustc_driver-*.so` mapped).
    StaticExe,
}

/// Authenticated compiler driver identity returned by Linux residency checks.
#[cfg(any(target_os = "linux", test))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DriverIdentity {
    pub(crate) linkage: DriverLinkage,
    pub(crate) driver_sha256: String,
    pub(crate) dso_digests: BTreeMap<String, String>,
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
fn reject_loader_env_in<I, K, V>(vars: I) -> Result<(), Failure>
where
    I: IntoIterator<Item = (K, V)>,
    K: AsRef<OsStr>,
    V: AsRef<OsStr>,
{
    for (key, value) in vars {
        let Some(key_str) = key.as_ref().to_str() else {
            continue;
        };
        if FORBIDDEN_LOADER_ENV_VARS.contains(&key_str) && !value.as_ref().is_empty() {
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

/// Return `true` for a valid unparenthesized `-dev` compiler version string
/// such as `1.101.0-dev` produced by custom source builds with no embedded
/// parenthesized commit hash.
fn is_unparenthesized_dev_version(version: &str) -> bool {
    let Some(core) = version.strip_suffix("-dev") else {
        return false;
    };
    let mut parts = core.split('.');
    let Some(major) = parts.next() else {
        return false;
    };
    let Some(minor) = parts.next() else {
        return false;
    };
    let Some(patch) = parts.next() else {
        return false;
    };
    parts.next().is_none()
        && [major, minor, patch]
            .into_iter()
            .all(|part| !part.is_empty() && part.bytes().all(|b| b.is_ascii_digit()))
}

/// Confirm that the linked driver's version string agrees with `commit-hash`
/// from `<sysroot>/bin/rustc --version --verbose`.
///
/// Standard builds embed a parenthesized short prefix of the full hex commit
/// hash (`1.98.0-nightly (f8a08b688 2026-05-30)`). Custom source `-dev`
/// builds without parenthesized commit metadata (`1.101.0-dev`) are accepted
/// when `commit-hash` is `"unknown"` or a full 40-digit hex SHA-1; builds
/// carrying parenthesized metadata still require an exact commit-prefix match.
fn linked_version_matches_commit(linked_version: &str, commit: &str) -> bool {
    if is_unparenthesized_dev_version(linked_version) {
        return commit == "unknown"
            || (commit.len() == 40 && commit.bytes().all(|b| b.is_ascii_hexdigit()));
    }
    if commit.len() < 9 || !commit.bytes().all(|b| b.is_ascii_hexdigit()) {
        return false;
    }
    let short = &commit[..9];
    let needle = format!("({short}");
    let Some(pos) = linked_version.find(&needle) else {
        return false;
    };
    let tail = &linked_version[pos + needle.len()..];
    let mut tail_bytes = tail.as_bytes().iter();
    let mut commit_bytes = commit.as_bytes()[9..].iter();
    loop {
        match tail_bytes.next() {
            Some(b' ' | b')') => return true,
            Some(&tb) => match commit_bytes.next() {
                Some(&cb) if tb.eq_ignore_ascii_case(&cb) => continue,
                _ => return false,
            },
            None => return false,
        }
    }
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
#[cfg(any(target_os = "linux", test))]
const ALLOWED_SYSTEM_RUNTIME_PREFIXES: &[&[u8]] = &[
    b"/lib/",
    b"/lib64/",
    b"/usr/lib/",
    b"/usr/lib64/",
    b"/nix/store/",
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

/// Parse an ELF64 little-endian binary's `PT_INTERP` header and return the
/// parent directories (logical and canonical, deduplicated) of its dynamic
/// loader so custom-sysroot/Nix/musl C runtime libraries resolve cleanly.
#[cfg(target_os = "linux")]
fn read_elf64_pt_interp_dirs(exec_path: &Path) -> Vec<PathBuf> {
    use std::io::{Read, Seek, SeekFrom};

    let Ok(mut file) = fs::File::open(exec_path) else {
        return Vec::new();
    };
    let Ok(file_len) = file.metadata().map(|m| m.len()) else {
        return Vec::new();
    };
    if file_len < 64 {
        return Vec::new();
    }
    let mut ehdr = [0u8; 64];
    if file.read_exact(&mut ehdr).is_err()
        || &ehdr[0..4] != b"\x7fELF"
        || ehdr[4] != 2
        || ehdr[5] != 1
    {
        return Vec::new();
    }
    let e_phoff = u64::from_le_bytes(ehdr[32..40].try_into().unwrap());
    let e_phentsize = u16::from_le_bytes(ehdr[54..56].try_into().unwrap()) as u64;
    let e_phnum = u16::from_le_bytes(ehdr[56..58].try_into().unwrap()) as u64;
    if e_phnum == 0 || e_phentsize < 56 {
        return Vec::new();
    }
    let Some(ph_table_bytes) = e_phentsize.checked_mul(e_phnum) else {
        return Vec::new();
    };
    let Some(ph_end) = e_phoff.checked_add(ph_table_bytes) else {
        return Vec::new();
    };
    if ph_end > file_len || ph_table_bytes > 4 * 1024 * 1024 {
        return Vec::new();
    }
    if file.seek(SeekFrom::Start(e_phoff)).is_err() {
        return Vec::new();
    }
    let mut table = vec![0u8; ph_table_bytes as usize];
    if file.read_exact(&mut table).is_err() {
        return Vec::new();
    }
    const PT_INTERP: u32 = 3;
    let mut dirs = BTreeSet::new();
    for i in 0..(e_phnum as usize) {
        let base = i * (e_phentsize as usize);
        let p_type = u32::from_le_bytes(table[base..base + 4].try_into().unwrap());
        if p_type != PT_INTERP {
            continue;
        }
        let p_offset = u64::from_le_bytes(table[base + 8..base + 16].try_into().unwrap());
        let p_filesz = u64::from_le_bytes(table[base + 32..base + 40].try_into().unwrap());
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
            && parent.is_absolute()
            && parent != Path::new("/")
        {
            dirs.insert(parent.to_path_buf());
        }
        if let Ok(canon) = fs::canonicalize(interp_path)
            && let Some(parent) = canon.parent()
            && parent.is_absolute()
            && parent != Path::new("/")
        {
            dirs.insert(parent.to_path_buf());
        }
        break;
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
    dev: u64,
    inode: u64,
    pathname: Option<&'a [u8]>,
}

/// Parse one raw `/proc/self/maps` line without requiring UTF-8 or trimming
/// trailing spaces from file paths.
#[cfg(any(target_os = "linux", test))]
fn parse_maps_line(raw_line: &[u8]) -> Option<MapsEntry<'_>> {
    let line = raw_line.strip_suffix(b"\r").unwrap_or(raw_line);
    let mut rest = strip_leading_ascii_ws(line);
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
    let (maj_hex, min_hex) = split_once_byte(fields[3], b':')?;
    let major = parse_hex_u64(maj_hex)?;
    let minor = parse_hex_u64(min_hex)?;
    let inode = parse_dec_u64(fields[4])?;
    let pathname = if rest.is_empty() { None } else { Some(rest) };
    Some(MapsEntry {
        start,
        end,
        perms: fields[1],
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

/// Collect all regular library files under `<sysroot>/lib` and
/// `<sysroot>/lib/rustlib/<host>/lib`, indexed by kernel `(st_dev, st_ino)`.
/// Symlinks (such as virtual CAS symlink forests) are followed so their
/// backing inode matches `/proc/self/maps`.
#[cfg(all(any(target_os = "linux", test), unix))]
fn collect_sysroot_library_entries(
    sysroot: &Path,
    host: &str,
) -> Result<BTreeMap<(u64, u64), (String, PathBuf)>, Failure> {
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
            let Ok(dev_ino) = regular_file_dev_ino(&path) else {
                continue;
            };
            entries_by_id.entry(dev_ino).or_insert_with(|| (name, path));
        }
    }
    Ok(entries_by_id)
}

/// Open each `librustc_driver-*.so` under `<sysroot>/lib` or
/// `<sysroot>/lib/rustlib/<host>/lib` once, match `(st_dev, st_ino)` on the
/// open descriptor against `loaded_dev_ino`, and hash from that same handle.
#[cfg(any(target_os = "linux", test))]
fn match_and_hash_sysroot_driver(
    sysroot: &Path,
    host: &str,
    loaded_dev_ino: (u64, u64),
) -> Result<String, Failure> {
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
            let Ok(matched_digest) = open_and_hash_if_dev_ino_matches(&path, loaded_dev_ino) else {
                continue;
            };
            saw_candidate = true;
            if let Some(digest) = matched_digest {
                return Ok(digest);
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
    let (self_dev_ino, self_vma_path) =
        resolve_mapping_dev_ino(maps_bytes, self_addr, "capture executable")?;
    let (driver_dev_ino, _) = resolve_mapping_dev_ino(maps_bytes, driver_addr, "rustc driver")?;
    let sysroot_libs = collect_sysroot_library_entries(sysroot, host)?;

    // Collect every file-backed executable mapping and any file-backed
    // toolchain-DSO mapping across `/proc/self/maps`.
    let mut exec_mappings: BTreeMap<(u64, u64), Vec<u8>> = BTreeMap::new();
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
            exec_mappings
                .entry(dev_ino)
                .or_insert_with(|| pathname.to_vec());
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

    if driver_dev_ino == self_dev_ino {
        // Static-linked `rustc_private` driver: `rustc_driver::run_compiler`
        // resides inside the capture executable itself. Refuse any stray
        // dynamically loaded toolchain DSO (`librustc_*`, `libLLVM*`, etc.),
        // validate all remaining executable mappings against sysroot or
        // standard system runtime paths, and hash the capture executable via
        // an open-FD `(st_dev, st_ino)` match.
        if let Some((_, stray_path)) = toolchain_mappings.iter().next() {
            return Err(Failure::tool(format!(
                "statically linked capture driver unexpectedly mapped toolchain DSO: {}",
                String::from_utf8_lossy(stray_path)
            )));
        }
        for (&dev_ino, pathname) in &exec_mappings {
            if dev_ino == self_dev_ino {
                continue;
            }
            if let Some((name, path)) = sysroot_libs.get(&dev_ino) {
                let digest = open_and_hash_if_dev_ino_matches(path, dev_ino)
                    .map_err(Failure::io)?
                    .ok_or_else(|| {
                        Failure::tool(format!(
                            "sysroot library {} changed inode during residency verification",
                            path.display()
                        ))
                    })?;
                dso_digests.insert(name.clone(), digest);
            } else if !is_allowed_system_runtime_path(pathname, pt_interp_dirs) {
                return Err(Failure::tool(format!(
                    "loaded executable mapping {} does not belong to verified sysroot {} or standard system libraries",
                    String::from_utf8_lossy(pathname),
                    sysroot.display()
                )));
            }
        }
        let exe_sha256 = match open_and_hash_if_dev_ino_matches(self_exe_path, self_dev_ino) {
            Ok(Some(digest)) => digest,
            _ => {
                use std::os::unix::ffi::OsStrExt;
                let vma_path = Path::new(OsStr::from_bytes(self_vma_path));
                open_and_hash_if_dev_ino_matches(vma_path, self_dev_ino)
                    .map_err(Failure::io)?
                    .ok_or_else(|| {
                        Failure::tool(
                            "capture executable failed open-FD (st_dev, st_ino) verification",
                        )
                    })?
            }
        };
        return Ok(DriverIdentity {
            linkage: DriverLinkage::StaticExe,
            driver_sha256: exe_sha256,
            dso_digests,
        });
    }

    // Dynamic `librustc_driver-*.so` mode: authenticate `driver_dev_ino`
    // against `<sysroot>` and verify the closed-world set of every executable
    // and toolchain-named mapping in `/proc/self/maps`.
    let driver_sha256 = match_and_hash_sysroot_driver(sysroot, host, driver_dev_ino)?;
    if let Some((driver_name, _)) = sysroot_libs.get(&driver_dev_ino) {
        dso_digests.insert(driver_name.clone(), driver_sha256.clone());
    }

    for (&dev_ino, pathname) in &toolchain_mappings {
        if dev_ino == self_dev_ino || dev_ino == driver_dev_ino {
            continue;
        }
        let Some((name, path)) = sysroot_libs.get(&dev_ino) else {
            return Err(Failure::tool(format!(
                "loaded toolchain DSO {} does not match any library in sysroot {}",
                String::from_utf8_lossy(pathname),
                sysroot.display()
            )));
        };
        let digest = open_and_hash_if_dev_ino_matches(path, dev_ino)
            .map_err(Failure::io)?
            .ok_or_else(|| {
                Failure::tool(format!(
                    "sysroot toolchain DSO {} changed inode during residency verification",
                    path.display()
                ))
            })?;
        dso_digests.insert(name.clone(), digest);
    }

    for (&dev_ino, pathname) in &exec_mappings {
        if dev_ino == self_dev_ino || dev_ino == driver_dev_ino {
            continue;
        }
        if let Some((name, path)) = sysroot_libs.get(&dev_ino) {
            if !dso_digests.contains_key(name) {
                let digest = open_and_hash_if_dev_ino_matches(path, dev_ino)
                    .map_err(Failure::io)?
                    .ok_or_else(|| {
                        Failure::tool(format!(
                            "sysroot library {} changed inode during residency verification",
                            path.display()
                        ))
                    })?;
                dso_digests.insert(name.clone(), digest);
            }
        } else if !is_allowed_system_runtime_path(pathname, pt_interp_dirs) {
            return Err(Failure::tool(format!(
                "loaded executable mapping {} does not belong to verified sysroot {} or standard system libraries",
                String::from_utf8_lossy(pathname),
                sysroot.display()
            )));
        }
    }

    Ok(DriverIdentity {
        linkage: DriverLinkage::DynamicDso,
        driver_sha256,
        dso_digests,
    })
}

#[cfg(all(any(target_os = "linux", test), unix))]
fn open_and_hash_if_dev_ino_matches(
    path: &Path,
    expected: (u64, u64),
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
    if (meta.dev(), meta.ino()) != expected {
        return Ok(None);
    }
    let digest = sha256_reader(&mut file)?;
    Ok(Some(digest))
}

#[cfg(all(test, not(unix)))]
fn open_and_hash_if_dev_ino_matches(
    _path: &Path,
    _expected: (u64, u64),
) -> io::Result<Option<String>> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "residency hashing requires unix metadata",
    ))
}

#[cfg(target_os = "linux")]
fn verify_driver_residency(sysroot: &Path, host: &str) -> Result<DriverIdentity, Failure> {
    let self_addr = verify_driver_residency as *const () as usize;
    let driver_addr = rustc_driver::run_compiler as *const () as usize;
    let maps_bytes = fs::read("/proc/self/maps").map_err(Failure::io)?;
    let self_exe = Path::new("/proc/self/exe");
    let pt_interp_dirs = read_elf64_pt_interp_dirs(self_exe);
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
fn verify_driver_residency(_sysroot: &Path, _host: &str) -> Result<(), Failure> {
    Err(Failure::unsupported(
        "typed MIR capture requires Linux to authenticate the loaded rustc driver",
    ))
}

/// Verify ambient loader hygiene, sysroot layout, pinned linked driver
/// version, sanitized `<sysroot>/bin/rustc --version --verbose` agreement with
/// the pinned commit, pre/post `<sysroot>/bin/rustc` TOCTOU identity, and
/// Linux closed-world driver residency before entering `rustc`'s fatal-error
/// handler.
pub(crate) fn verify_compiler(sysroot: &Path, target: &str) -> Result<(), Failure> {
    reject_ambient_loader_env()?;
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
    if !linked_version_matches_commit(linked_version, &verbose.commit) {
        return Err(Failure::tool(format!(
            "sysroot rustc commit ({}) does not match linked rustc version ({linked_version})",
            verbose.commit
        )));
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
    if verbose.commit != ir::COMPILER_COMMIT {
        return Err(Failure::tool(
            "sysroot rustc does not match the pinned full compiler commit",
        ));
    }

    verify_driver_residency(sysroot, &verbose.host)?;
    Ok(())
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

        let digest =
            match_and_hash_sysroot_driver(&sysroot, "x86_64-unknown-linux-gnu", real_dev_ino)
                .unwrap();
        assert_eq!(digest, sha256_bytes(b"driver-elf-bytes"));

        let err =
            match_and_hash_sysroot_driver(&decoy_sysroot, "x86_64-unknown-linux-gnu", real_dev_ino)
                .unwrap_err();
        assert!(err.diagnostics[0].contains("does not match"), "{err:?}");

        // Host path traversal must be rejected before joining paths.
        for bad_host in ["", ".", "..", "/tmp/evil", "../../tmp/evil", "a/b"] {
            let err = match_and_hash_sysroot_driver(&sysroot, bad_host, real_dev_ino).unwrap_err();
            assert!(
                err.diagnostics[0].contains("invalid rustc host triple"),
                "{bad_host:?}: {err:?}"
            );
        }
    }

    #[test]
    fn linked_version_commit_binding_validates_short_prefix() {
        let ver = "1.98.0-nightly (f8a08b688 2026-05-30)";
        assert!(linked_version_matches_commit(
            ver,
            "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"
        ));
        assert!(linked_version_matches_commit(
            "1.98.0-dev (f8a08b688cbe)",
            "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"
        ));
        assert!(!linked_version_matches_commit(
            ver,
            "0000000000000000000000000000000000000000"
        ));
        assert!(!linked_version_matches_commit(ver, "f8a08b68"));
        assert!(!linked_version_matches_commit(
            "1.98.0-nightly (f8a08b688zzz 2026-05-30)",
            "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"
        ));
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
    fn unparenthesized_dev_versions_and_loader_env_guards_behave_as_specified() {
        // Valid 0-paren `-dev` versions authenticate cleanly with `"unknown"`
        // or a full 40-hex commit-hash, while rejecting malformed commits.
        assert!(linked_version_matches_commit("1.101.0-dev", "unknown"));
        assert!(linked_version_matches_commit(
            "1.101.0-dev",
            "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"
        ));
        assert!(!linked_version_matches_commit("1.101.0-dev", "short"));
        assert!(!linked_version_matches_commit("1.101.0", "unknown"));
        assert!(!linked_version_matches_commit(
            "1.98.0-nightly (f8a08b688 2026-05-30)",
            "unknown"
        ));

        // Ambient loader injection variables must fail closed while clean
        // environments pass.
        assert!(reject_loader_env_in([("PATH", "/usr/bin"), ("LD_PRELOAD", "")]).is_ok());
        for bad in FORBIDDEN_LOADER_ENV_VARS {
            let err = reject_loader_env_in([(*bad, "/tmp/injected.so")]).unwrap_err();
            assert!(err.diagnostics[0].contains(bad), "{bad}: {err:?}");
        }
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
}
