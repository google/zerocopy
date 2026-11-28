// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Shared OS filesystem, atomic-staging, process-environment, and ELF loader
//! sanitization substrate for `cargo-anneal` and `anneal-audit`.

#[cfg(unix)]
use std::os::unix::fs::{OpenOptionsExt as _, PermissionsExt as _};
use std::{
    collections::BTreeMap,
    fs,
    io::{self, Read as _, Seek as _, SeekFrom, Write as _},
    path::{Path, PathBuf},
    process,
    sync::atomic::{AtomicU64, Ordering},
};

use sha2::{Digest as _, Sha256};
#[cfg(unix)]
use walkdir::WalkDir;

use crate::core::{
    digest::{digest_to_hex, sha256_bytes},
    elf::{
        decode_pt_interp_cstr, find_elf64_pt_interp, parse_elf64_ehdr, reject_forbidden_loader_env,
    },
    error::Failure,
};

const MAX_TEMP_ATTEMPTS: usize = 128;
static NEXT_TEMP_ID: AtomicU64 = AtomicU64::new(0);

/// Convert an [`io::Error`] into an operational [`Failure`] preserving
/// `io::ErrorKind` and Unix `EROFS` detection.
pub fn failure_from_io(phase: &str, message: impl Into<String>, err: &io::Error) -> Failure {
    #[cfg(unix)]
    let read_only_fs = err.raw_os_error() == Some(libc::EROFS);
    #[cfg(not(unix))]
    let read_only_fs = false;
    Failure::operational_io_kind(phase, message, err.kind(), read_only_fs)
}

/// Removes an unpublished sibling temporary file on drop unless disarmed after
/// atomic publication.
pub struct TempFileGuard {
    path: PathBuf,
    armed: bool,
}

impl TempFileGuard {
    /// Wrap `path` in a drop guard that deletes it unless [`Self::disarm`] is
    /// called.
    pub fn new(path: PathBuf) -> Self {
        Self { path, armed: true }
    }

    /// Return the guarded temporary file path.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Disarm the drop guard once the temporary file has been atomically
    /// published.
    pub fn disarm(mut self) {
        self.armed = false;
    }
}

impl Drop for TempFileGuard {
    fn drop(&mut self) {
        if self.armed {
            let _ = fs::remove_file(&self.path);
        }
    }
}

/// Symlink-safe, non-blocking, size-bounded filesystem operations shared across
/// Anneal trusted binaries.
pub struct SafeFs;

impl SafeFs {
    fn open_regular_nofollow_nonblock_with_code(
        path: &Path,
        phase: &str,
        non_regular_code: i32,
    ) -> Result<fs::File, Failure> {
        #[cfg(not(unix))]
        {
            let pre_meta = fs::symlink_metadata(path).map_err(|e| {
                failure_from_io(phase, format!("cannot inspect {}: {e}", path.display()), &e)
            })?;
            if pre_meta.file_type().is_symlink() || !pre_meta.file_type().is_file() {
                return Err(Failure::new(
                    non_regular_code,
                    phase,
                    format!("expected a regular file: {}", path.display()),
                ));
            }
        }
        let mut opts = fs::OpenOptions::new();
        opts.read(true);
        #[cfg(unix)]
        opts.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
        let file = opts.open(path).map_err(|e| {
            failure_from_io(phase, format!("cannot read {}: {e}", path.display()), &e)
        })?;
        let meta = file.metadata().map_err(|e| {
            failure_from_io(phase, format!("cannot inspect {}: {e}", path.display()), &e)
        })?;
        if !meta.is_file() {
            return Err(Failure::new(
                non_regular_code,
                phase,
                format!("expected a regular file: {}", path.display()),
            ));
        }
        Ok(file)
    }

    /// Open `path` for reading without following symlinks or blocking on FIFOs
    /// or device nodes (`O_NOFOLLOW | O_NONBLOCK` on Unix; pre-open
    /// `symlink_metadata` check on non-Unix), and verify the opened file
    /// descriptor refers to a regular file.
    pub fn open_regular_nofollow_nonblock(path: &Path, phase: &str) -> Result<fs::File, Failure> {
        Self::open_regular_nofollow_nonblock_with_code(path, phase, 1)
    }

    /// Inspect `path` without following symlinks, returning `Ok(None)` only on
    /// `io::ErrorKind::NotFound` and failing closed on all other metadata
    /// errors.
    pub fn probe_symlink_metadata(
        path: &Path,
        phase: &str,
    ) -> Result<Option<fs::Metadata>, Failure> {
        match fs::symlink_metadata(path) {
            Ok(meta) => Ok(Some(meta)),
            Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(e) => {
                Err(failure_from_io(phase, format!("cannot inspect {}: {e}", path.display()), &e))
            }
        }
    }

    /// Verify that `path` exists and is a regular file (never a symlink,
    /// directory, FIFO, or device node) using `symlink_metadata`.
    pub fn regular(path: &Path, phase: &str) -> Result<(), Failure> {
        let meta = fs::symlink_metadata(path).map_err(|e| {
            failure_from_io(phase, format!("cannot inspect {}: {e}", path.display()), &e)
        })?;
        if meta.file_type().is_symlink() || !meta.file_type().is_file() {
            return Err(Failure::new(
                1,
                phase,
                format!("expected a regular file: {}", path.display()),
            ));
        }
        Ok(())
    }

    fn read_regular_file_deref_with_code(
        path: &Path,
        phase: &str,
        non_regular_code: i32,
    ) -> Result<(Vec<u8>, String), Failure> {
        let canon = fs::canonicalize(path).map_err(|e| {
            failure_from_io(phase, format!("cannot inspect {}: {e}", path.display()), &e)
        })?;
        let pre_meta = fs::metadata(&canon).map_err(|e| {
            failure_from_io(phase, format!("cannot inspect {}: {e}", path.display()), &e)
        })?;
        if !pre_meta.is_file() {
            return Err(Failure::new(
                non_regular_code,
                phase,
                format!("expected a regular file: {}", path.display()),
            ));
        }
        let mut file =
            Self::open_regular_nofollow_nonblock_with_code(&canon, phase, non_regular_code)?;
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes).map_err(|e| {
            failure_from_io(phase, format!("cannot read {}: {e}", path.display()), &e)
        })?;
        let after = fs::canonicalize(path).map_err(|e| {
            failure_from_io(phase, format!("cannot inspect {}: {e}", path.display()), &e)
        })?;
        if after != canon {
            return Err(Failure::operational(
                phase,
                format!("path changed during read: {}", path.display()),
            ));
        }
        let sha = sha256_bytes(&bytes);
        Ok((bytes, sha))
    }

    /// Read and SHA-256 hash a regular file, dereferencing symlinks while
    /// guarding against non-regular targets (FIFOs, sockets, devices) and
    /// TOCTOU swaps.
    pub fn read_regular_file_deref(path: &Path, phase: &str) -> Result<(Vec<u8>, String), Failure> {
        Self::read_regular_file_deref_with_code(path, phase, 1)
    }

    /// Read and return `(bytes, raw_sha256_digest)` for a regular file while
    /// rejecting symlinks and non-regular files, verifying the open fd and
    /// post-read canonical path.
    pub fn read_regular_file_strict_raw(
        path: &Path,
        expected_canon: Option<&Path>,
        phase: &str,
    ) -> Result<(Vec<u8>, [u8; 32]), Failure> {
        Self::regular(path, phase)?;
        let mut file = Self::open_regular_nofollow_nonblock(path, phase)?;
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes).map_err(|e| {
            failure_from_io(phase, format!("cannot read {}: {e}", path.display()), &e)
        })?;
        Self::regular(path, phase)?;
        if let Some(expected) = expected_canon {
            let canon = fs::canonicalize(path).map_err(|e| {
                failure_from_io(phase, format!("cannot inspect {}: {e}", path.display()), &e)
            })?;
            if canon != expected {
                return Err(Failure::policy(
                    phase,
                    format!("expected a regular file: {}", path.display()),
                ));
            }
        }
        let digest: [u8; 32] = Sha256::digest(&bytes).into();
        Ok((bytes, digest))
    }

    /// Read and SHA-256 hash a regular file while rejecting symlinks and
    /// non-regular files, verifying the open fd and post-read canonical path.
    pub fn read_regular_file_strict(
        path: &Path,
        expected_canon: Option<&Path>,
        phase: &str,
    ) -> Result<(Vec<u8>, String), Failure> {
        let (bytes, digest) = Self::read_regular_file_strict_raw(path, expected_canon, phase)?;
        Ok((bytes, digest_to_hex(&digest)))
    }

    /// Read at most `max_bytes` from a non-symlink regular file opened with
    /// `O_NOFOLLOW | O_NONBLOCK`, checking both initial metadata and bounded
    /// stream length (`take(max_bytes + 1)`).
    pub fn read_regular_nofollow_capped(
        path: &Path,
        max_bytes: u64,
        phase: &str,
    ) -> Result<Vec<u8>, Failure> {
        let file = Self::open_regular_nofollow_nonblock_with_code(path, phase, 2)?;
        let meta = file.metadata().map_err(|e| {
            failure_from_io(phase, format!("cannot inspect {}: {e}", path.display()), &e)
        })?;
        if meta.len() > max_bytes {
            return Err(Failure::operational(
                phase,
                format!("regular file exceeds {max_bytes}-byte limit: {}", path.display()),
            ));
        }
        let mut buf = Vec::with_capacity(meta.len().min(64 * 1024) as usize);
        let limit = max_bytes.saturating_add(1);
        file.take(limit).read_to_end(&mut buf).map_err(|e| {
            failure_from_io(phase, format!("cannot read {}: {e}", path.display()), &e)
        })?;
        if (buf.len() as u64) > max_bytes {
            return Err(Failure::operational(
                phase,
                format!("regular file exceeded {max_bytes}-byte limit: {}", path.display()),
            ));
        }
        Ok(buf)
    }

    /// Read at most `max_bytes` UTF-8 text from a non-symlink regular file.
    pub fn read_regular_string_capped(
        path: &Path,
        max_bytes: u64,
        phase: &str,
    ) -> Result<String, Failure> {
        let bytes = Self::read_regular_nofollow_capped(path, max_bytes, phase)?;
        String::from_utf8(bytes).map_err(|e| {
            Failure::operational(phase, format!("{} is not valid UTF-8: {e}", path.display()))
        })
    }

    /// Verify that `path` is a regular file and return its lowercase hex
    /// SHA-256 digest.
    pub fn sha256_file(path: &Path, phase: &str) -> Result<String, Failure> {
        Self::read_regular_file_strict(path, None, phase).map(|(_, sha)| sha)
    }

    /// Hash a file, dereferencing symlinks (for sysroot libraries/sources and
    /// tool binaries).
    pub fn sha256_file_deref(path: &Path, phase: &str) -> Result<String, Failure> {
        Self::read_regular_file_deref(path, phase).map(|(_, sha)| sha)
    }

    /// Copy a regular source file `src` to `dst`, creating parent directories
    /// as needed, and return the SHA-256 digest of the copied bytes.
    pub fn stage_regular_file(src: &Path, dst: &Path, phase: &str) -> Result<String, Failure> {
        let (bytes, sha) = Self::read_regular_file_strict(src, None, phase)?;
        if let Some(parent) = dst.parent() {
            fs::create_dir_all(parent).map_err(|e| {
                failure_from_io(phase, format!("cannot create {}: {e}", parent.display()), &e)
            })?;
        }
        fs::write(dst, &bytes).map_err(|e| {
            failure_from_io(phase, format!("cannot write {}: {e}", dst.display()), &e)
        })?;
        Ok(sha)
    }

    /// Create a directory (and parents if needed) with an explicit Unix mode.
    pub fn create_dir_mode(path: &Path, mode: u32, phase: &str) -> Result<(), Failure> {
        fs::create_dir_all(path).map_err(|e| {
            failure_from_io(phase, format!("cannot create {}: {e}", path.display()), &e)
        })?;
        Self::set_mode(path, mode, phase)
    }

    /// Set Unix file or directory mode bits; no-op on non-Unix targets.
    pub fn set_mode(path: &Path, mode: u32, phase: &str) -> Result<(), Failure> {
        #[cfg(unix)]
        {
            fs::set_permissions(path, fs::Permissions::from_mode(mode)).map_err(|e| {
                failure_from_io(
                    phase,
                    format!("cannot set mode {:o} on {}: {e}", mode, path.display()),
                    &e,
                )
            })?;
        }
        #[cfg(not(unix))]
        {
            let _ = (path, mode, phase);
        }
        Ok(())
    }

    /// Restore owner write/execute permissions recursively across `root`
    /// without following symlinks so read-only staging trees can be removed.
    pub fn make_tree_writable(root: &Path) {
        #[cfg(unix)]
        {
            for entry in WalkDir::new(root).follow_links(false).into_iter().flatten() {
                let ft = entry.file_type();
                if ft.is_symlink() {
                    continue;
                }
                let mode = if ft.is_dir() { 0o700 } else { 0o600 };
                let _ = fs::set_permissions(entry.path(), fs::Permissions::from_mode(mode));
            }
        }
        #[cfg(not(unix))]
        {
            let _ = root;
        }
    }

    /// Physically copy a regular file (dereferencing admitted host/Nix
    /// symlinks cleanly while checking regular-file and TOCTOU invariants,
    /// never hardlinking) and, on Unix, mark the non-symlink destination
    /// read-only (`0o444` via descriptor `fchmod`; non-Unix permission bits
    /// are left untouched, matching [`Self::set_mode`] and
    /// [`Self::make_tree_writable`]).
    pub fn copy_readonly_file(src: &Path, dest: &Path, phase: &str) -> Result<(), Failure> {
        let (bytes, _) = Self::read_regular_file_deref_with_code(src, phase, 2)?;
        if let Some(parent) = dest.parent() {
            fs::create_dir_all(parent).map_err(|e| {
                failure_from_io(phase, format!("cannot create {}: {e}", parent.display()), &e)
            })?;
        }
        #[cfg(not(unix))]
        if let Ok(meta) = fs::symlink_metadata(dest)
            && meta.file_type().is_symlink()
        {
            return Err(Failure::operational(
                phase,
                format!("refusing to follow symlink destination: {}", dest.display()),
            ));
        }
        let mut opts = fs::OpenOptions::new();
        opts.write(true).create(true).truncate(true);
        #[cfg(unix)]
        opts.mode(0o600).custom_flags(libc::O_NOFOLLOW);
        let mut out = opts.open(dest).map_err(|e| {
            failure_from_io(phase, format!("cannot write {}: {e}", dest.display()), &e)
        })?;
        out.write_all(&bytes).map_err(|e| {
            failure_from_io(phase, format!("cannot write {}: {e}", dest.display()), &e)
        })?;
        #[cfg(unix)]
        {
            out.set_permissions(fs::Permissions::from_mode(0o444)).map_err(|e| {
                failure_from_io(
                    phase,
                    format!("cannot set mode 444 on {}: {e}", dest.display()),
                    &e,
                )
            })?;
        }
        Ok(())
    }

    /// Create a unique sibling temporary file in `parent` using
    /// `create_new(true)` (`O_CREAT | O_EXCL`) and private `0o600` permissions
    /// on Unix.
    ///
    /// POSIX guarantees `O_CREAT | O_EXCL` never follows a trailing symlink,
    /// failing with `EEXIST` instead; retrying across bounded sequence numbers
    /// recovers from stale or external filename collisions without exposing a
    /// writable symlink.
    pub fn create_unique_temp(
        parent: &Path,
        dst_name: &str,
        phase: &str,
    ) -> Result<(TempFileGuard, fs::File), Failure> {
        let pid = process::id();
        for _ in 0..MAX_TEMP_ATTEMPTS {
            let seq = NEXT_TEMP_ID.fetch_add(1, Ordering::Relaxed);
            let prefix = format!(".tmp-{pid}-{seq}-");
            let name = if prefix.len() + dst_name.len() <= 240 {
                format!("{prefix}{dst_name}")
            } else {
                format!(".tmp-{pid}-{seq}")
            };
            let tmp_path = parent.join(name);
            let mut opts = fs::OpenOptions::new();
            opts.write(true).create_new(true);
            #[cfg(unix)]
            opts.mode(0o600);
            match opts.open(&tmp_path) {
                Ok(file) => return Ok((TempFileGuard::new(tmp_path), file)),
                Err(e) if e.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(e) => {
                    return Err(failure_from_io(
                        phase,
                        format!("cannot create temporary cache entry {}: {e}", tmp_path.display()),
                        &e,
                    ));
                }
            }
        }
        Err(Failure::operational(
            phase,
            format!(
                "exhausted {MAX_TEMP_ATTEMPTS} attempts creating temporary cache entry in {}",
                parent.display()
            ),
        ))
    }
}

/// Process-environment and ELF loader sanitization helpers shared across
/// sandboxed execution boundaries.
pub struct SysSanitizer;

impl SysSanitizer {
    /// Refuse any dynamic-linker environment variable (`LD_*`, `DYLD_*`) in a
    /// child environment override map before spawning a process.
    pub fn reject_forbidden_loader_env(
        extra_env: &BTreeMap<String, String>,
    ) -> Result<(), Failure> {
        reject_forbidden_loader_env(extra_env)
    }

    /// Parse an ELF64 little-endian binary's `PT_INTERP` dynamic linker path.
    /// Returns `Ok(None)` for static ELF64 binaries and `Err` for non-ELF or
    /// malformed binaries.
    pub fn parse_elf64_pt_interp(path: &Path) -> Result<Option<PathBuf>, String> {
        let mut file = fs::File::open(path).map_err(|e| format!("open {}: {e}", path.display()))?;
        let file_len = file.metadata().map_err(|e| format!("stat {}: {e}", path.display()))?.len();
        if file_len < 64 {
            return Err(format!("{} is smaller than an ELF64 header", path.display()));
        }
        let mut ehdr = [0u8; 64];
        file.read_exact(&mut ehdr)
            .map_err(|e| format!("read ELF header {}: {e}", path.display()))?;
        let label = path.display().to_string();
        let Some(phdr_info) = parse_elf64_ehdr(&ehdr, file_len, &label)? else {
            return Ok(None);
        };
        file.seek(SeekFrom::Start(phdr_info.e_phoff))
            .map_err(|e| format!("seek phdr table: {e}"))?;
        let mut table = vec![0u8; phdr_info.table_bytes];
        file.read_exact(&mut table).map_err(|e| format!("read phdr table: {e}"))?;
        let Some((p_offset, p_filesz)) = find_elf64_pt_interp(&table, phdr_info, file_len)? else {
            return Ok(None);
        };
        file.seek(SeekFrom::Start(p_offset)).map_err(|e| format!("seek PT_INTERP: {e}"))?;
        let mut raw = vec![0u8; p_filesz];
        file.read_exact(&mut raw).map_err(|e| format!("read PT_INTERP: {e}"))?;
        let s = decode_pt_interp_cstr(&raw)?;
        Ok(Some(PathBuf::from(s)))
    }

    /// Resolve both the declared `PT_INTERP` path and its canonicalized target.
    pub fn resolve_pt_interp_paths(exec_bin: &Path) -> Result<Vec<PathBuf>, String> {
        let Some(interp) = Self::parse_elf64_pt_interp(exec_bin)? else {
            return Ok(Vec::new());
        };
        let mut paths = vec![interp.clone()];
        if let Ok(canon) = fs::canonicalize(&interp)
            && canon != interp
        {
            paths.push(canon);
        }
        Ok(paths)
    }
}

/// Overwrite `buf` with zeroes using volatile writes and a compiler fence so
/// secret key scrubbing during `Drop` is never optimized away.
pub fn volatile_zero(buf: &mut [u8]) {
    for byte in buf {
        // SAFETY: `byte` is a unique mutable reference to initialized memory.
        unsafe {
            std::ptr::write_volatile(byte, 0);
        }
    }
    std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::SeqCst);
}

/// Overwrite `buf` of `u64` limbs with zeroes using volatile writes and a
/// compiler fence so accumulator/key scrubbing during `Drop` is not elided.
pub fn volatile_zero_u64(buf: &mut [u64]) {
    for word in buf {
        // SAFETY: `word` is a unique mutable reference to initialized memory.
        unsafe {
            std::ptr::write_volatile(word, 0);
        }
    }
    std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::SeqCst);
}

#[cfg(unix)]
fn read_dev_urandom_32(dst: &mut [u8; 32]) -> Result<(), Failure> {
    let mut opts = fs::OpenOptions::new();
    opts.read(true);
    opts.custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC);
    let mut file = opts
        .open("/dev/urandom")
        .map_err(|e| failure_from_io("it-mac", "open /dev/urandom", &e))?;
    file.read_exact(dst)
        .map_err(|e| failure_from_io("it-mac", "read 32-byte key from /dev/urandom", &e))?;
    Ok(())
}

/// Fill a 32-byte key buffer from the host OS CSPRNG (`getrandom(2)` with
/// `flags = 0` on Linux, falling back to `/dev/urandom` on `ENOSYS` or other
/// Unix platforms).
pub fn fill_os_random_32(dst: &mut [u8; 32]) -> Result<(), Failure> {
    #[cfg(target_os = "linux")]
    {
        let mut offset = 0usize;
        while offset < dst.len() {
            // SAFETY: `dst[offset..]` is a valid writable byte slice.
            let rc = unsafe {
                libc::getrandom(
                    dst[offset..].as_mut_ptr().cast::<libc::c_void>(),
                    dst.len() - offset,
                    0,
                )
            };
            if rc > 0 {
                offset += rc as usize;
                continue;
            }
            let err = io::Error::last_os_error();
            if err.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            if err.raw_os_error() == Some(libc::ENOSYS) {
                return read_dev_urandom_32(dst);
            }
            return Err(failure_from_io("it-mac", "read 32-byte key from getrandom", &err));
        }
        Ok(())
    }
    #[cfg(all(unix, not(target_os = "linux")))]
    {
        read_dev_urandom_32(dst)
    }
    #[cfg(not(unix))]
    {
        let _ = dst;
        Err(Failure::operational("it-mac", "OS entropy source unavailable on non-Unix host"))
    }
}

/// Mark an open Unix descriptor non-blocking (`O_NONBLOCK`) via `fcntl`.
#[cfg(unix)]
pub fn set_fd_nonblocking(fd: std::os::unix::io::BorrowedFd<'_>) -> Result<(), Failure> {
    use std::os::unix::io::AsRawFd as _;

    let raw = fd.as_raw_fd();
    // SAFETY: `fd` is a valid borrowed descriptor for this call.
    let flags = unsafe { libc::fcntl(raw, libc::F_GETFL) };
    if flags < 0 {
        let err = io::Error::last_os_error();
        return Err(failure_from_io("it-mac", "fcntl(F_GETFL)", &err));
    }
    // SAFETY: `fd` is a valid borrowed descriptor and `flags | O_NONBLOCK`
    // preserves all existing file status flags while enabling non-blocking I/O.
    if unsafe { libc::fcntl(raw, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0 {
        let err = io::Error::last_os_error();
        return Err(failure_from_io("it-mac", "fcntl(F_SETFL, O_NONBLOCK)", &err));
    }
    Ok(())
}

/// Create an anonymous pipe `(read_fd, write_fd)` with `FD_CLOEXEC` set
/// atomically on Linux (`pipe2`) or immediately on other Unix platforms.
#[cfg(unix)]
pub fn create_cloexec_pipe()
-> Result<(std::os::unix::io::OwnedFd, std::os::unix::io::OwnedFd), Failure> {
    use std::os::unix::io::{FromRawFd, OwnedFd};

    let mut fds = [0 as libc::c_int; 2];
    #[cfg(target_os = "linux")]
    {
        // SAFETY: `fds` is a valid writable 2-element `c_int` array.
        if unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) } != 0 {
            let err = io::Error::last_os_error();
            return Err(failure_from_io("it-mac", "pipe2(O_CLOEXEC)", &err));
        }
    }
    #[cfg(not(target_os = "linux"))]
    {
        // SAFETY: `fds` is a valid writable 2-element `c_int` array.
        if unsafe { libc::pipe(fds.as_mut_ptr()) } != 0 {
            let err = io::Error::last_os_error();
            return Err(failure_from_io("it-mac", "pipe", &err));
        }
        for fd in fds {
            // SAFETY: `fd` is a valid newly opened descriptor.
            if unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) } != 0 {
                let err = io::Error::last_os_error();
                // SAFETY: both fds were just returned by `pipe(2)`, are owned
                // only here, and are not yet wrapped in `OwnedFd`, so closing
                // each once is sound.
                unsafe {
                    let _ = libc::close(fds[0]);
                    let _ = libc::close(fds[1]);
                }
                return Err(failure_from_io("it-mac", "fcntl(FD_CLOEXEC)", &err));
            }
        }
    }
    // SAFETY: both descriptors are freshly created unique owned pipe ends.
    unsafe { Ok((OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1]))) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn capped_reads_and_copy_preserve_operational_code_and_readonly_fd_mode() {
        let dir = tempfile::tempdir().unwrap();
        let src = dir.path().join("src.txt");
        fs::write(&src, b"hello").unwrap();
        let dst = dir.path().join("dst.txt");
        SafeFs::copy_readonly_file(&src, &dst, "copy-test").unwrap();
        assert_eq!(fs::read(&dst).unwrap(), b"hello");

        #[cfg(unix)]
        {
            use std::{os::unix::fs::symlink, process::Command};

            let mode = fs::symlink_metadata(&dst).unwrap().permissions().mode() & 0o777;
            assert_eq!(mode, 0o444);

            let link_dst = dir.path().join("link_dst.txt");
            symlink(dir.path().join("missing"), &link_dst).unwrap();
            let err_link = SafeFs::copy_readonly_file(&src, &link_dst, "copy-test").unwrap_err();
            assert_eq!(err_link.code, 2, "unexpected symlink dest error: {err_link}");

            let fifo = dir.path().join("pipe");
            assert!(Command::new("mkfifo").arg(&fifo).status().unwrap().success());
            let err_capped =
                SafeFs::read_regular_nofollow_capped(&fifo, 1024, "olean-cache").unwrap_err();
            assert_eq!(err_capped.code, 2, "expected operational code 2 on FIFO: {err_capped}");
            let err_copy_fifo =
                SafeFs::copy_readonly_file(&fifo, &dir.path().join("out"), "stage").unwrap_err();
            assert_eq!(
                err_copy_fifo.code, 2,
                "expected operational code 2 on FIFO src: {err_copy_fifo}"
            );
        }
    }
}
