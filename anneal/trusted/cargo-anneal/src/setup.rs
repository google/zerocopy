// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Toolchain installation and bundle layout via `exocrate`
//! (`cargo anneal setup`).
//!
//! Manages the versioned omnibus archive containing:
//! - `bin/anneal-rustc-capture`, the standalone MIR capture driver;
//! - `lean/`, the pinned Lean toolchain;
//! - `rust/`, the pinned Rust toolchain (`rustc`, `rust-std`, and `rustc-dev`);
//!   and
//! - `share/anneal/`, the `trusted/lean/` foundation metadata.

use std::{
    ffi::{OsStr, OsString},
    fs, io,
    path::{Path, PathBuf},
};

exocrate::config! {
    const CONFIG: Config = Config {
        rel_dir_path: ["anneal", "toolchain"],
        versioned_files: &["../Cargo.toml"],
    };
}

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
exocrate::parse_remote_archive! {
    const REMOTE_ARCHIVE: RemoteArchive = "Cargo.toml";
}

fn remote_archive() -> Result<exocrate::RemoteArchive, String> {
    #[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
    {
        if REMOTE_ARCHIVE.sha256 == [0; 32] {
            return Err("the alpha archive has not been pinned; use --local-archive".into());
        }
        Ok(REMOTE_ARCHIVE)
    }
    #[cfg(not(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu")))]
    Err("the downloadable alpha toolchain requires x86-64 Linux with glibc".into())
}

/// Directory layout of an unpacked Anneal omnibus toolchain bundle.
///
/// When acquired through [`installed_bundle_at`], holds a shared flock on
/// `<slug>.lock` so concurrent `cargo anneal setup --local-archive` installs
/// wait until verification finishes reading this toolchain.
#[derive(Debug)]
pub(crate) struct Bundle {
    root: PathBuf,
    _lock: Option<fs::File>,
}

impl Bundle {
    #[cfg(test)]
    fn new(root: PathBuf) -> Self {
        Self { root, _lock: None }
    }

    fn capture(&self) -> PathBuf {
        self.root.join("bin/anneal-rustc-capture")
    }

    fn sysroot(&self) -> PathBuf {
        self.root.join("rust")
    }

    fn lean(&self) -> PathBuf {
        self.root.join("lean/bin/lean")
    }
}

/// Installs or resolves the Anneal toolchain archive in the user-global cache.
///
/// Reuses an installed toolchain when `local_archive` is `None` (installing the
/// pinned remote archive when absent and configured). When `local_archive` is
/// `Some(path)`, extracts and atomically installs `path`, replacing an
/// existing installation for this version only after extraction succeeds.
pub fn install(local_archive: Option<PathBuf>) -> Result<PathBuf, String> {
    install_at(local_archive, exocrate::Location::UserGlobal)
}

fn clone_location(location: &exocrate::Location) -> exocrate::Location {
    match location {
        exocrate::Location::UserGlobal => exocrate::Location::UserGlobal,
        exocrate::Location::LocalDev => exocrate::Location::LocalDev,
        exocrate::Location::Custom(path) => exocrate::Location::Custom(path.clone()),
    }
}

fn sibling_lock_path(dir: &Path, suffix: &str) -> io::Result<PathBuf> {
    let parent = dir.parent().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "installation path has no parent",
        )
    })?;
    let slug = dir.file_name().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "installation path has no file name",
        )
    })?;
    let mut lock_name = slug.to_os_string();
    lock_name.push(suffix);
    Ok(parent.join(lock_name))
}

fn open_exclusive_lock(lock_path: &Path) -> io::Result<fs::File> {
    let file = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(lock_path)?;
    file.lock()?;
    Ok(file)
}

#[cfg(unix)]
fn normalize_dir_permissions(root: &Path) -> io::Result<()> {
    use std::os::unix::fs::PermissionsExt;

    let ensure_owner_rwx = |path: &Path| -> io::Result<()> {
        let meta = fs::symlink_metadata(path)?;
        let file_type = meta.file_type();
        if file_type.is_dir() && !file_type.is_symlink() {
            let mode = meta.permissions().mode();
            if mode & 0o700 != 0o700 {
                fs::set_permissions(path, fs::Permissions::from_mode(mode | 0o700))?;
            }
        }
        Ok(())
    };

    ensure_owner_rwx(root)?;
    for entry in walkdir::WalkDir::new(root).follow_links(false) {
        let entry = entry.map_err(|e| {
            let msg = e.to_string();
            e.into_io_error().unwrap_or_else(|| io::Error::other(msg))
        })?;
        let file_type = entry.file_type();
        if file_type.is_dir() && !file_type.is_symlink() {
            ensure_owner_rwx(entry.path())?;
        }
    }
    Ok(())
}

#[cfg(not(unix))]
fn normalize_dir_permissions(_root: &Path) -> io::Result<()> {
    Ok(())
}

fn read_entry_names(dir: &Path) -> io::Result<Vec<OsString>> {
    let mut names = Vec::new();
    for entry in fs::read_dir(dir)? {
        names.push(entry?.file_name());
    }
    Ok(names)
}

fn move_entries_back(names: &[OsString], from: &Path, to: &Path) -> io::Result<()> {
    let mut first_err: Option<io::Error> = None;
    for name in names.iter().rev() {
        if let Err(err) = fs::rename(from.join(name), to.join(name))
            && first_err.is_none()
        {
            first_err = Some(err);
        }
    }
    match first_err {
        Some(err) => Err(err),
        None => Ok(()),
    }
}

fn remove_temp_dir_best_effort(dir: tempfile::TempDir, kind: &str) {
    remove_temp_dir_best_effort_with(dir, kind, |path| fs::remove_dir_all(path));
}

fn remove_temp_dir_best_effort_with(
    dir: tempfile::TempDir,
    kind: &str,
    remove_dir: impl FnOnce(&Path) -> io::Result<()>,
) {
    let path = dir.keep();
    if let Err(err) = remove_dir(&path) {
        eprintln!(
            "warning: failed to clean up {kind} directory {}: {err}",
            path.display()
        );
    }
}

fn validate_real_dir(dir: &Path) -> Result<(), String> {
    let meta = fs::symlink_metadata(dir)
        .map_err(|err| format!("cannot inspect installed toolchain {}: {err}", dir.display()))?;
    if meta.file_type().is_symlink() {
        return Err(format!(
            "installed toolchain path {} is a symlink",
            dir.display()
        ));
    }
    if !meta.file_type().is_dir() {
        return Err(format!(
            "installed toolchain path {} is not a directory",
            dir.display()
        ));
    }
    Ok(())
}

// Deterministic USTAR tar archive containing a single empty `.incomplete`
// regular file, compressed with zstd (`SEED_TAR_ZST`). Used by `install_local`
// to initialize a cold `<slug>` directory + `<slug>.lock` in sub-millisecond
// time so concurrent `setup --local-archive` callers converge onto the single
// serialized `reinstall_existing` pipeline without `exocrate` skipping losers.
const SEED_TAR_ZST: &[u8] = &[
    0x28, 0xb5, 0x2f, 0xfd, 0x04, 0x68, 0xdd, 0x01, 0x00, 0x54, 0x02, 0x2e,
    0x69, 0x6e, 0x63, 0x6f, 0x6d, 0x70, 0x6c, 0x65, 0x74, 0x65, 0x00, 0x30,
    0x36, 0x34, 0x34, 0x00, 0x30, 0x31, 0x30, 0x30, 0x37, 0x33, 0x00, 0x20,
    0x30, 0x00, 0x00, 0x75, 0x73, 0x74, 0x61, 0x72, 0x00, 0x30, 0x30, 0x00,
    0x07, 0x20, 0x20, 0x37, 0x1c, 0xf3, 0x06, 0x7f, 0xbe, 0x27, 0x7c, 0x1f,
    0x78, 0xc0, 0xa0, 0x00, 0x56, 0x13, 0xa6, 0x03, 0x52, 0x1c, 0x31, 0x5e,
];

fn marker_present(path: &Path) -> Result<bool, String> {
    match fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(err) if err.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(err) => Err(format!(
            "cannot inspect toolchain completion marker {}: {err}",
            path.display()
        )),
    }
}

fn check_bundle_complete(dir: &Path) -> Result<(), String> {
    let inner_marker = dir.join(".incomplete");
    let sibling_marker = sibling_lock_path(dir, ".incomplete")
        .map_err(|err| format!("cannot locate toolchain marker for {}: {err}", dir.display()))?;
    if marker_present(&inner_marker)? || marker_present(&sibling_marker)? {
        return Err(format!(
            "Anneal toolchain installation at {} is incomplete; run `cargo anneal setup`",
            dir.display()
        ));
    }
    Ok(())
}

fn is_cold_seed_only(dir: &Path) -> bool {
    let Ok(meta) = fs::symlink_metadata(dir) else {
        return false;
    };
    if !meta.file_type().is_dir() || meta.file_type().is_symlink() {
        return false;
    }
    let Ok(entries) = read_entry_names(dir) else {
        return false;
    };
    if entries.as_slice() != [OsStr::new(".incomplete")] {
        return false;
    }
    fs::symlink_metadata(dir.join(".incomplete"))
        .map(|m| m.file_type().is_file() && !m.file_type().is_symlink())
        .unwrap_or(false)
}

fn cleanup_cold_seed_if_uncommitted(dir: &Path) {
    if let Ok(lock_path) = sibling_lock_path(dir, ".lock")
        && let Ok(_guard) = open_exclusive_lock(&lock_path)
        && is_cold_seed_only(dir)
    {
        let _ = fs::remove_dir_all(dir);
    }
}

const INCOMPLETE_MARKER: &str = ".incomplete";

/// Stage `source` inside `dir`'s parent directory, then swap its top-level
/// entries into `dir` while keeping `dir` continuously present as a real
/// directory, preserving any previous installation if staging fails, and
/// cleaning up an uncommitted cold seed if staging or pre-commit setup fails.
///
/// When `reinstall_only_if_incomplete` is `true`, returns early once
/// `.reinstall.lock` is held if `dir` is already a complete real directory
/// (avoiding overwriting a concurrent install that finished repairing `dir`).
fn reinstall_existing(
    dir: &Path,
    source: exocrate::Source,
    reinstall_only_if_incomplete: bool,
) -> io::Result<PathBuf> {
    let parent = dir.parent().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "installation path has no parent",
        )
    })?;
    // Serialize reinstalls separately from exocrate's `<slug>.lock` so readers
    // and exocrate cold-installers never block on archive decompression and we
    // never self-deadlock while staging via `CONFIG` into `staging_holder`.
    let reinstall_lock = open_exclusive_lock(&sibling_lock_path(dir, ".reinstall.lock")?)?;
    if reinstall_only_if_incomplete
        && validate_real_dir(dir).is_ok()
        && check_bundle_complete(dir).is_ok()
    {
        return Ok(dir.to_path_buf());
    }

    let staging_holder = tempfile::Builder::new()
        .prefix(".staging-")
        .tempdir_in(parent)?;
    let (staged_dir, _) = match CONFIG.resolve_installation_dir_or_install(
        exocrate::Location::Custom(staging_holder.path().to_path_buf()),
        source,
    ) {
        Ok(staged) => staged,
        Err(err) => {
            cleanup_cold_seed_if_uncommitted(dir);
            return Err(err);
        }
    };
    // Ensure extracted directories carry owner RWX before taking `<slug>.lock`
    // so read-only archive directories cannot fail cleanup or future swaps.
    if let Err(err) = normalize_dir_permissions(&staged_dir) {
        cleanup_cold_seed_if_uncommitted(dir);
        return Err(err);
    }
    // Enumerate and validate staged top-level entries before touching `dir` or
    // moving any existing installation out to backup.
    let new_entries = match read_entry_names(&staged_dir) {
        Ok(entries) => entries,
        Err(err) => {
            cleanup_cold_seed_if_uncommitted(dir);
            return Err(err);
        }
    };
    if new_entries
        .iter()
        .any(|name| name == OsStr::new(INCOMPLETE_MARKER))
    {
        cleanup_cold_seed_if_uncommitted(dir);
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "archive must not contain reserved top-level .incomplete entry",
        ));
    }

    // Hold exocrate's directory lock exclusively across the entry swap so
    // readers and cold installs wait until the replacement is complete.
    let exocrate_lock = open_exclusive_lock(&sibling_lock_path(dir, ".lock")?)?;
    match fs::symlink_metadata(dir) {
        Ok(meta) if meta.file_type().is_symlink() => {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "installation path is a symlink",
            ));
        }
        Ok(meta) if meta.file_type().is_dir() => {}
        Ok(_) => {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "installation path exists and is not a directory",
            ));
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            fs::rename(&staged_dir, dir)?;
            drop(exocrate_lock);
            remove_temp_dir_best_effort(staging_holder, "staging");
            drop(reinstall_lock);
            return Ok(dir.to_path_buf());
        }
        Err(e) => return Err(e),
    };

    // Normalize existing directory permissions and read current entries before
    // recording `.incomplete` or moving any entry out of `dir`.
    if let Err(err) = normalize_dir_permissions(dir) {
        if is_cold_seed_only(dir) {
            let _ = fs::remove_dir_all(dir);
        }
        return Err(err);
    }
    let old_entries = match read_entry_names(dir) {
        Ok(entries) => entries,
        Err(err) => {
            if is_cold_seed_only(dir) {
                let _ = fs::remove_dir_all(dir);
            }
            return Err(err);
        }
    };

    let backup_holder = match tempfile::Builder::new().prefix(".backup-").tempdir_in(parent) {
        Ok(holder) => holder,
        Err(err) => {
            if is_cold_seed_only(dir) {
                let _ = fs::remove_dir_all(dir);
            }
            return Err(err);
        }
    };
    let backup_dir = backup_holder.path().join("previous");
    if let Err(err) = fs::create_dir(&backup_dir) {
        if is_cold_seed_only(dir) {
            let _ = fs::remove_dir_all(dir);
        }
        return Err(err);
    }

    let sibling_incomplete = sibling_lock_path(dir, INCOMPLETE_MARKER)?;
    let had_sibling_incomplete = fs::symlink_metadata(&sibling_incomplete).is_ok();
    // Record crash-detectable `.incomplete` marker before moving any entry out
    // of `dir` so a process kill mid-swap leaves the bundle flagged incomplete.
    if let Err(err) = fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&sibling_incomplete)
    {
        if is_cold_seed_only(dir) {
            let _ = fs::remove_dir_all(dir);
        }
        return Err(err);
    }

    // Keep `dir` itself at its path throughout the swap so concurrent discovery
    // still resolves `dir` and waits on `<slug>.lock` instead of falling back
    // to unbundled tools mid-reinstall.
    let mut moved_old = Vec::with_capacity(old_entries.len());
    for name in old_entries {
        if let Err(err) = fs::rename(dir.join(&name), backup_dir.join(&name)) {
            if let Err(restore_err) = move_entries_back(&moved_old, &backup_dir, dir) {
                let retained = backup_holder.keep();
                return Err(io::Error::new(
                    err.kind(),
                    format!(
                        "failed to move existing toolchain entry {} ({err}) and failed to \
                         restore previous installation ({restore_err}; preserved at {})",
                        Path::new(&name).display(),
                        retained.display()
                    ),
                ));
            }
            if !had_sibling_incomplete {
                let _ = fs::remove_file(&sibling_incomplete);
            }
            return Err(err);
        }
        moved_old.push(name);
    }

    let mut moved_new = Vec::with_capacity(new_entries.len());
    for name in new_entries {
        if let Err(err) = fs::rename(staged_dir.join(&name), dir.join(&name)) {
            let mut rollback_errs = Vec::new();
            if let Err(revert_new) = move_entries_back(&moved_new, dir, &staged_dir) {
                rollback_errs.push(format!("revert staged entries: {revert_new}"));
            }
            if let Err(restore_old) = move_entries_back(&moved_old, &backup_dir, dir) {
                rollback_errs.push(format!("restore previous installation: {restore_old}"));
            }
            if !rollback_errs.is_empty() {
                let retained = backup_holder.keep();
                return Err(io::Error::new(
                    err.kind(),
                    format!(
                        "failed to swap staged archive ({err}) and failed to roll back ({}; \
                         preserved at {})",
                        rollback_errs.join("; "),
                        retained.display()
                    ),
                ));
            }
            if !had_sibling_incomplete {
                let _ = fs::remove_file(&sibling_incomplete);
            }
            return Err(err);
        }
        moved_new.push(name);
    }

    if let Err(err) = fs::remove_file(&sibling_incomplete)
        && err.kind() != io::ErrorKind::NotFound
    {
        return Err(err);
    }

    drop(exocrate_lock);
    remove_temp_dir_best_effort(backup_holder, "backup");
    remove_temp_dir_best_effort(staging_holder, "staging");
    drop(reinstall_lock);
    Ok(dir.to_path_buf())
}

fn ensure_local_archive_readable(path: &Path) -> io::Result<()> {
    let file = fs::File::open(path)?;
    if !file.metadata()?.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "local archive path is not a regular file",
        ));
    }
    Ok(())
}

fn install_local(path: PathBuf, location: exocrate::Location) -> io::Result<PathBuf> {
    install_local_with_seed_hook(path, location, || {})
}

fn install_local_with_seed_hook(
    path: PathBuf,
    location: exocrate::Location,
    after_resolve_absent: impl FnOnce(),
) -> io::Result<PathBuf> {
    // Validate the caller's archive before initializing any cache directory.
    ensure_local_archive_readable(&path)?;
    let dir = match CONFIG.resolve_installation_dir(clone_location(&location)) {
        Ok(existing) => existing,
        Err(err) if err.kind() == io::ErrorKind::NotFound => {
            after_resolve_absent();
            let mut seed_file = tempfile::NamedTempFile::new()?;
            io::Write::write_all(&mut seed_file, SEED_TAR_ZST)?;
            let seed_path = seed_file.into_temp_path();
            // Seed cold installs with an `.incomplete` marker so concurrent
            // cold callers wait/converge on `<slug>` and unconditionally enter
            // `reinstall_existing` under `.reinstall.lock` (last-writer-wins).
            let (seeded_dir, _) = CONFIG.resolve_installation_dir_or_install(
                location,
                exocrate::Source::Local(seed_path.to_path_buf()),
            )?;
            drop(seed_path);
            seeded_dir
        }
        Err(err) => return Err(err),
    };
    reinstall_existing(&dir, exocrate::Source::Local(path), false)
}

fn resolve_complete_existing(
    location: exocrate::Location,
    missing_reason: String,
) -> Result<PathBuf, String> {
    match installed_bundle_at(location)? {
        Some(bundle) => Ok(bundle.root),
        None => Err(missing_reason),
    }
}

fn install_remote(
    get_remote: impl Fn() -> Result<exocrate::RemoteArchive, String>,
    location: exocrate::Location,
) -> Result<PathBuf, String> {
    let archive = get_remote()?;
    match installed_bundle_at(clone_location(&location)) {
        Ok(Some(bundle)) => Ok(bundle.root),
        Ok(None) => {
            let (dir, _) = CONFIG
                .resolve_installation_dir_or_install(
                    clone_location(&location),
                    exocrate::Source::Remote(archive),
                )
                .map_err(|e| format!("failed to install Anneal toolchain: {e}"))?;
            if check_bundle_complete(&dir).is_err() {
                return reinstall_existing(&dir, exocrate::Source::Remote(get_remote()?), true)
                    .map_err(|e| format!("failed to install Anneal toolchain: {e}"));
            }
            Ok(dir)
        }
        Err(err) => match CONFIG.resolve_installation_dir(location) {
            Ok(dir) if validate_real_dir(&dir).is_ok() && check_bundle_complete(&dir).is_err() => {
                reinstall_existing(&dir, exocrate::Source::Remote(archive), true)
                    .map_err(|e| format!("failed to install Anneal toolchain: {e}"))
            }
            _ => Err(err),
        },
    }
}

/// Installs or resolves the archive at an explicit exocrate location.
///
/// Unit tests use a fresh `Custom` location for each synthetic local archive.
/// Production setup uses the user-global cache above.
pub(crate) fn install_at(
    local_archive: Option<PathBuf>,
    location: exocrate::Location,
) -> Result<PathBuf, String> {
    install_at_with_remote(local_archive, location, remote_archive)
}

fn install_at_with_remote(
    local_archive: Option<PathBuf>,
    location: exocrate::Location,
    get_remote: impl Fn() -> Result<exocrate::RemoteArchive, String>,
) -> Result<PathBuf, String> {
    match local_archive {
        Some(path) => install_local(path, location)
            .map_err(|e| format!("failed to install Anneal toolchain: {e}")),
        None => match get_remote() {
            Ok(_) => install_remote(get_remote, location),
            Err(reason) => resolve_complete_existing(location, reason),
        },
    }
}

/// Explicit tool overrides passed to [`resolve_tools`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ToolOverrides {
    pub(crate) capture: Option<PathBuf>,
    pub(crate) sysroot: Option<PathBuf>,
    pub(crate) lean: Option<PathBuf>,
}

/// Resolved capture, sysroot, and Lean locations from [`resolve_tools`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ResolvedTools {
    pub(crate) capture: PathBuf,
    pub(crate) sysroot: Option<PathBuf>,
    pub(crate) lean: Option<PathBuf>,
}

/// Resolves capture, Rust sysroot, and Lean paths in one precedence order:
/// explicit override, then `installed` (using bundle `lean/bin/lean` only when
/// it is an existing file), then fallback (`anneal-rustc-capture` beside the
/// running executable for capture; `None` for sysroot and Lean so callers fall
/// back to `default_lean_path` or `rustup`).
///
/// `current_exe` is the result of [`std::env::current_exe`]. Only the capture
/// fallback reads it, and that fallback returns an error when the executable
/// path is unknown or relative.
pub(crate) fn resolve_tools(
    overrides: ToolOverrides,
    installed: Option<&Bundle>,
    current_exe: io::Result<PathBuf>,
) -> Result<ResolvedTools, String> {
    let capture = match overrides.capture.or_else(|| installed.map(Bundle::capture)) {
        Some(capture) => capture,
        None => sibling_capture(current_exe)?,
    };
    Ok(ResolvedTools {
        capture,
        sysroot: overrides.sysroot.or_else(|| installed.map(Bundle::sysroot)),
        lean: overrides
            .lean
            .or_else(|| installed.map(Bundle::lean).filter(|p| p.is_file())),
    })
}

/// Returns the `anneal-rustc-capture` path beside the running executable.
///
/// The sibling of an empty or relative path is itself relative. It would
/// resolve against the working directory, which can be the checkout under
/// verification, and a file there must not run as the trusted capture driver.
fn sibling_capture(current_exe: io::Result<PathBuf>) -> Result<PathBuf, String> {
    let cli = current_exe.map_err(|e| {
        format!("cannot find anneal-rustc-capture beside cargo-anneal: {e}; pass --capture")
    })?;
    if !cli.is_absolute() {
        return Err(format!(
            "cannot find anneal-rustc-capture beside cargo-anneal: executable path {cli:?} is not \
             absolute; pass --capture"
        ));
    }
    Ok(cli.with_file_name("anneal-rustc-capture"))
}

/// Resolves an already installed bundle at `location`, holding a shared flock
/// on `<slug>.lock` for the lifetime of the returned [`Bundle`].
///
/// Returns `Ok(None)` without creating files or directories when no bundle is
/// installed or no user cache base is configured. Fails closed if the resolved
/// path is a symlink or non-directory, or if `<slug>.lock` cannot be opened
/// read-only and shared-locked.
pub(crate) fn installed_bundle_at(location: exocrate::Location) -> Result<Option<Bundle>, String> {
    // Verification discovery must not turn a missing installation into an
    // implicit download or installation. None lets the caller use its explicit
    // development tool or sibling executable instead.
    let dir = match CONFIG.resolve_installation_dir(location) {
        Ok(dir) => dir,
        Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(err) => {
            return Err(format!("cannot inspect installed Anneal toolchain: {err}"));
        }
    };
    validate_real_dir(&dir)?;
    let lock_path = sibling_lock_path(&dir, ".lock")
        .map_err(|err| format!("cannot locate toolchain lock for {}: {err}", dir.display()))?;
    let lock_file = fs::File::open(&lock_path)
        .map_err(|err| format!("cannot open toolchain lock {}: {err}", lock_path.display()))?;
    lock_file
        .lock_shared()
        .map_err(|err| format!("cannot lock toolchain {}: {err}", lock_path.display()))?;
    validate_real_dir(&dir)?;
    check_bundle_complete(&dir)?;
    Ok(Some(Bundle { root: dir, _lock: Some(lock_file) }))
}

/// Resolves an already installed user-global bundle without downloading it.
pub(crate) fn installed_bundle() -> Result<Option<Bundle>, String> {
    installed_bundle_at(exocrate::Location::UserGlobal)
}

#[cfg(test)]
mod tests {
    use std::{
        fs, io,
        path::{Path, PathBuf},
    };

    use super::*;

    /// Return a successful `current_exe` result for a workspace-built CLI.
    fn cli() -> io::Result<PathBuf> {
        Ok(PathBuf::from("/workspace/target/debug/cargo-anneal"))
    }

    /// Return a failed `current_exe` result.
    fn unknown_cli() -> io::Result<PathBuf> {
        Err(io::Error::other("executable path unavailable"))
    }

    fn write_archive(path: &Path) {
        write_archive_with(path, b"archive under test");
    }

    fn write_archive_with(path: &Path, contents: &[u8]) {
        write_archive_entries(path, &[("marker.txt", contents)]);
    }

    fn write_archive_entries(path: &Path, entries: &[(&str, &[u8])]) {
        let file = fs::File::create(path).expect("create archive");
        let encoder = zstd::Encoder::new(file, 1).expect("create compressor");
        let mut archive = tar::Builder::new(encoder);
        for (name, contents) in entries {
            let mut header = tar::Header::new_gnu();
            header.set_size(contents.len() as u64);
            header.set_mode(0o644);
            header.set_cksum();
            archive
                .append_data(&mut header, name, *contents)
                .expect("write archive entry");
        }
        archive
            .into_inner()
            .expect("finish tar archive")
            .finish()
            .expect("finish compressed archive");
    }

    #[test]
    fn bundle_paths_follow_omnibus_archive_layout() {
        let bundle = Bundle::new(PathBuf::from("/opt/anneal-bundle"));
        assert_eq!(
            bundle.capture(),
            Path::new("/opt/anneal-bundle/bin/anneal-rustc-capture")
        );
        assert_eq!(bundle.sysroot(), Path::new("/opt/anneal-bundle/rust"));
        assert_eq!(bundle.lean(), Path::new("/opt/anneal-bundle/lean/bin/lean"));
    }

    #[test]
    fn resolve_tools_prefers_explicit_then_installed_then_sibling() {
        let bundle_dir = tempfile::tempdir().expect("create synthetic bundle");
        let installed = Bundle::new(bundle_dir.path().to_path_buf());
        fs::create_dir_all(installed.lean().parent().unwrap()).expect("create lean bin dir");
        fs::write(installed.lean(), b"lean").expect("write synthetic lean binary");

        let explicit = resolve_tools(
            ToolOverrides {
                capture: Some(PathBuf::from("/explicit/capture")),
                sysroot: Some(PathBuf::from("/explicit/sysroot")),
                lean: Some(PathBuf::from("/explicit/lean")),
            },
            Some(&installed),
            cli(),
        )
        .expect("resolve explicit tools");
        assert_eq!(explicit.capture, Path::new("/explicit/capture"));
        assert_eq!(
            explicit.sysroot.as_deref(),
            Some(Path::new("/explicit/sysroot"))
        );
        assert_eq!(explicit.lean.as_deref(), Some(Path::new("/explicit/lean")));

        let from_installed = resolve_tools(ToolOverrides::default(), Some(&installed), cli())
            .expect("resolve installed tools");
        assert_eq!(from_installed.capture, installed.capture());
        assert_eq!(from_installed.sysroot, Some(installed.sysroot()));
        assert_eq!(from_installed.lean, Some(installed.lean()));

        let fallback =
            resolve_tools(ToolOverrides::default(), None, cli()).expect("resolve sibling capture");
        assert_eq!(
            fallback.capture,
            Path::new("/workspace/target/debug/anneal-rustc-capture")
        );
        assert_eq!(fallback.sysroot, None);
        assert_eq!(fallback.lean, None);
    }

    #[test]
    fn resolve_tools_falls_back_when_installed_bundle_lacks_lean() {
        let bundle_dir = tempfile::tempdir().expect("create bundle without lean");
        let installed = Bundle::new(bundle_dir.path().to_path_buf());

        let without_lean = resolve_tools(ToolOverrides::default(), Some(&installed), cli())
            .expect("resolve installed tools");
        assert_eq!(without_lean.capture, installed.capture());
        assert_eq!(without_lean.sysroot, Some(installed.sysroot()));
        assert_eq!(without_lean.lean, None);

        let with_override = resolve_tools(
            ToolOverrides {
                lean: Some(PathBuf::from("/explicit/lean")),
                ..ToolOverrides::default()
            },
            Some(&installed),
            cli(),
        )
        .expect("resolve explicit Lean");
        assert_eq!(
            with_override.lean.as_deref(),
            Some(Path::new("/explicit/lean"))
        );

        fs::create_dir_all(installed.lean().parent().unwrap()).expect("create lean bin dir");
        fs::write(installed.lean(), b"lean").expect("write synthetic lean binary");
        let with_lean = resolve_tools(ToolOverrides::default(), Some(&installed), cli())
            .expect("resolve installed Lean");
        assert_eq!(with_lean.lean, Some(installed.lean()));
    }

    #[test]
    fn sibling_capture_requires_an_absolute_executable_path() {
        let unknown = sibling_capture(unknown_cli())
            .expect_err("an unknown executable must not select a capture driver");
        assert!(
            unknown.starts_with("cannot find anneal-rustc-capture beside cargo-anneal: "),
            "{unknown}"
        );
        assert!(unknown.contains("executable path unavailable"), "{unknown}");

        for relative in [
            "",
            "cargo-anneal",
            "./cargo-anneal",
            "target/debug/cargo-anneal",
        ] {
            let failure = sibling_capture(Ok(PathBuf::from(relative)))
                .expect_err("a relative executable must not select a capture driver");
            assert!(
                failure.starts_with("cannot find anneal-rustc-capture beside cargo-anneal: "),
                "{relative:?}: {failure}"
            );
            assert!(
                failure.contains("is not absolute"),
                "{relative:?}: {failure}"
            );
        }

        assert_eq!(
            sibling_capture(cli()),
            Ok(PathBuf::from(
                "/workspace/target/debug/anneal-rustc-capture"
            ))
        );
    }

    #[test]
    fn resolve_tools_needs_the_executable_path_only_for_the_sibling() {
        let explicit = resolve_tools(
            ToolOverrides {
                capture: Some(PathBuf::from("/explicit/capture")),
                ..ToolOverrides::default()
            },
            None,
            unknown_cli(),
        )
        .expect("an explicit capture driver needs no executable path");
        assert_eq!(explicit.capture, Path::new("/explicit/capture"));

        let bundle_dir = tempfile::tempdir().expect("create synthetic bundle");
        let installed = Bundle::new(bundle_dir.path().to_path_buf());
        let from_installed =
            resolve_tools(ToolOverrides::default(), Some(&installed), unknown_cli())
                .expect("an installed capture driver needs no executable path");
        assert_eq!(from_installed.capture, installed.capture());

        for current_exe in [
            unknown_cli(),
            Ok(PathBuf::new()),
            Ok(PathBuf::from("cargo-anneal")),
        ] {
            let failure = resolve_tools(ToolOverrides::default(), None, current_exe)
                .expect_err("the sibling fallback must fail closed");
            assert!(
                failure.starts_with("cannot find anneal-rustc-capture beside cargo-anneal: "),
                "{failure}"
            );
        }
    }

    #[test]
    fn custom_locations_install_only_the_requested_archive() {
        let temp = tempfile::tempdir().expect("create owned fixture");
        let archive = temp.path().join("current-run.tar.zst");
        write_archive(&archive);
        let ordinary = temp.path().join("ordinary-cache");
        let root = install_at(Some(archive), exocrate::Location::Custom(ordinary.clone()))
            .expect("install requested local archive");
        assert!(root.starts_with(&ordinary), "{}", root.display());
        assert_eq!(
            fs::read(root.join("marker.txt")).expect("read installed marker"),
            b"archive under test"
        );

        for (name, contents) in [("missing", None), ("broken", Some(b"bad"))] {
            let archive = temp.path().join(format!("{name}.tar.zst"));
            if let Some(contents) = contents {
                fs::write(&archive, contents).expect("write broken archive");
            }
            let fresh = temp.path().join(format!("{name}-cache"));
            let error = install_at(Some(archive), exocrate::Location::Custom(fresh))
                .expect_err("another location's installation must not satisfy setup");
            assert!(error.contains("failed to install Anneal toolchain"));
        }

        assert_eq!(
            fs::read(root.join("marker.txt")).expect("ordinary cache survives"),
            b"archive under test"
        );
    }

    #[test]
    fn setup_reuses_a_locally_installed_toolchain() {
        let temp = tempfile::tempdir().expect("create owned fixture");
        let archive = temp.path().join("toolchain.tar.zst");
        write_archive(&archive);
        let cache = temp.path().join("cache");
        let installed = install_at(
            Some(archive.clone()),
            exocrate::Location::Custom(cache.clone()),
        )
        .expect("install local archive");
        fs::remove_file(archive).expect("remove original archive");

        assert_eq!(
            install_at(None, exocrate::Location::Custom(cache))
                .expect("reuse the installed toolchain"),
            installed
        );
        if let Err(reason) = remote_archive() {
            let fresh = exocrate::Location::Custom(temp.path().join("fresh-cache"));
            assert_eq!(install_at(None, fresh), Err(reason));
        }
    }

    #[test]
    fn explicit_local_archive_reinstalls_and_preserves_existing_on_failure() {
        let temp = tempfile::tempdir().expect("create owned fixture");
        let v1 = temp.path().join("v1.tar.zst");
        let v2 = temp.path().join("v2.tar.zst");
        let corrupt = temp.path().join("corrupt.tar.zst");
        let missing = temp.path().join("missing.tar.zst");
        write_archive_with(&v1, b"archive v1");
        write_archive_with(&v2, b"archive v2");
        fs::write(&corrupt, b"not valid zstd").expect("write corrupt archive");

        let cache = temp.path().join("cache");
        let root_v1 = install_at(Some(v1), exocrate::Location::Custom(cache.clone()))
            .expect("install v1 archive");
        assert_eq!(fs::read(root_v1.join("marker.txt")).unwrap(), b"archive v1");

        let root_v2 = install_at(Some(v2), exocrate::Location::Custom(cache.clone()))
            .expect("reinstall v2 archive");
        assert_eq!(root_v2, root_v1);
        assert_eq!(fs::read(root_v2.join("marker.txt")).unwrap(), b"archive v2");
        assert_eq!(
            install_at(None, exocrate::Location::Custom(cache.clone()))
                .expect("resolve reinstalled v2 toolchain"),
            root_v2
        );

        let toolchain_parent = root_v2.parent().expect("toolchain parent dir");
        assert_eq!(
            child_dirs(toolchain_parent),
            vec![root_v2.file_name().unwrap().to_os_string()]
        );

        for bad in [&missing, &corrupt] {
            let err = install_at(Some(bad.clone()), exocrate::Location::Custom(cache.clone()))
                .expect_err("broken reinstall must fail closed");
            assert!(err.contains("failed to install Anneal toolchain:"), "{err}");
            assert_eq!(
                fs::read(root_v2.join("marker.txt")).unwrap(),
                b"archive v2",
                "existing installation must stay intact when {bad:?} fails"
            );
            assert_eq!(
                child_dirs(toolchain_parent),
                vec![root_v2.file_name().unwrap().to_os_string()]
            );
        }
    }

    fn child_dirs(parent: &Path) -> Vec<OsString> {
        fs::read_dir(parent)
            .unwrap()
            .map(|entry| entry.unwrap())
            .filter(|entry| entry.path().is_dir())
            .map(|entry| entry.file_name())
            .collect()
    }

    #[cfg(unix)]
    fn write_readonly_dir_archive(path: &Path, marker: &[u8]) {
        let file = fs::File::create(path).expect("create archive");
        let encoder = zstd::Encoder::new(file, 1).expect("create compressor");
        let mut archive = tar::Builder::new(encoder);

        let mut dir_header = tar::Header::new_gnu();
        dir_header.set_entry_type(tar::EntryType::Directory);
        dir_header.set_size(0);
        dir_header.set_mode(0o555);
        dir_header.set_cksum();
        archive
            .append_data(&mut dir_header, "ro_dir", io::empty())
            .expect("write readonly directory header");

        let mut file_header = tar::Header::new_gnu();
        file_header.set_size(marker.len() as u64);
        file_header.set_mode(0o444);
        file_header.set_cksum();
        archive
            .append_data(&mut file_header, "ro_dir/marker.txt", marker)
            .expect("write readonly marker header");

        archive
            .into_inner()
            .expect("finish tar archive")
            .finish()
            .expect("finish compressed archive");
    }

    #[cfg(unix)]
    #[test]
    fn explicit_local_archive_reinstalls_readonly_directories_cleanly() {
        use std::os::unix::fs::PermissionsExt;

        let temp = tempfile::tempdir().expect("create owned fixture");
        let v1 = temp.path().join("v1.tar.zst");
        let v2 = temp.path().join("v2.tar.zst");
        write_readonly_dir_archive(&v1, b"readonly v1");
        write_readonly_dir_archive(&v2, b"readonly v2");

        let cache = temp.path().join("cache");
        let root_v1 = install_at(Some(v1), exocrate::Location::Custom(cache.clone()))
            .expect("install archive containing 0o555 dir");
        assert_eq!(
            fs::symlink_metadata(root_v1.join("ro_dir"))
                .unwrap()
                .permissions()
                .mode()
                & 0o700,
            0o700,
            "initial install normalizes staged archive directories"
        );
        // Simulate an unnormalized read-only directory from an earlier
        // installation and verify pre-commit normalization replaces it cleanly.
        fs::set_permissions(root_v1.join("ro_dir"), fs::Permissions::from_mode(0o555))
            .expect("mark installed subdirectory 0o555");
        assert_eq!(
            fs::symlink_metadata(root_v1.join("ro_dir"))
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o555
        );
        assert_eq!(
            fs::symlink_metadata(root_v1.join("ro_dir/marker.txt"))
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o444
        );

        let root_v2 = install_at(Some(v2), exocrate::Location::Custom(cache))
            .expect("reinstall over 0o555 directory must succeed cleanly");
        assert_eq!(root_v2, root_v1);
        assert_eq!(
            fs::read(root_v2.join("ro_dir/marker.txt")).unwrap(),
            b"readonly v2"
        );
        assert_eq!(
            fs::symlink_metadata(root_v2.join("ro_dir"))
                .unwrap()
                .permissions()
                .mode()
                & 0o700,
            0o700,
            "staged directories must be normalized to owner-writable"
        );
        let parent = root_v2.parent().expect("toolchain parent dir");
        assert_eq!(
            child_dirs(parent),
            vec![root_v2.file_name().unwrap().to_os_string()]
        );
    }

    #[cfg(unix)]
    #[test]
    fn reinstall_rejects_symlink_and_non_directory_install_paths() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("create owned fixture");
        let v1 = temp.path().join("v1.tar.zst");
        let v2 = temp.path().join("v2.tar.zst");
        write_archive_with(&v1, b"archive v1");
        write_archive_with(&v2, b"archive v2");

        // Symlink collision: both `install_at` and `reinstall_existing` fail
        // closed without following or overwriting the target directory.
        let sym_cache = temp.path().join("sym-cache");
        let slug_path = install_at(Some(v1.clone()), exocrate::Location::Custom(sym_cache.clone()))
            .expect("install v1 to discover slug path");
        fs::remove_dir_all(&slug_path).expect("remove v1 dir");
        let target_dir = temp.path().join("outside-target");
        fs::create_dir(&target_dir).expect("create target dir");
        fs::write(target_dir.join("keep.txt"), b"outside").expect("write target file");
        symlink(&target_dir, &slug_path).expect("replace slug with symlink");

        let err = install_at(Some(v2.clone()), exocrate::Location::Custom(sym_cache))
            .expect_err("install_at must reject symlinked install root");
        assert!(err.contains("symlink"), "{err}");
        let direct_err = reinstall_existing(&slug_path, exocrate::Source::Local(v2.clone()), false)
            .expect_err("reinstall_existing must reject symlinked install root");
        assert_eq!(direct_err.kind(), io::ErrorKind::AlreadyExists);
        assert!(
            fs::symlink_metadata(&slug_path)
                .unwrap()
                .file_type()
                .is_symlink()
        );
        assert_eq!(fs::read(target_dir.join("keep.txt")).unwrap(), b"outside");

        // Regular file collision: both `install_at` and `reinstall_existing`
        // fail closed while preserving the file.
        let file_cache = temp.path().join("file-cache");
        let file_slug = install_at(Some(v1), exocrate::Location::Custom(file_cache.clone()))
            .expect("install v1 to discover slug path");
        fs::remove_dir_all(&file_slug).expect("remove v1 dir");
        fs::write(&file_slug, b"not a directory").expect("replace slug with file");

        let file_err = install_at(Some(v2.clone()), exocrate::Location::Custom(file_cache))
            .expect_err("install_at must reject non-directory install root");
        assert!(file_err.contains("failed to install Anneal toolchain:"), "{file_err}");
        let direct_file_err = reinstall_existing(&file_slug, exocrate::Source::Local(v2), false)
            .expect_err("reinstall_existing must reject non-directory install root");
        assert_eq!(direct_file_err.kind(), io::ErrorKind::AlreadyExists);
        assert_eq!(fs::read(&file_slug).unwrap(), b"not a directory");
    }

    #[test]
    fn installed_bundle_at_validates_real_dir_and_stays_read_only_when_absent() {
        let temp = tempfile::tempdir().expect("create owned fixture");
        let empty = temp.path().join("empty");
        fs::create_dir(&empty).expect("create empty cache dir");
        assert!(
            installed_bundle_at(exocrate::Location::Custom(empty.clone()))
                .expect("absent bundle resolves to Ok(None)")
                .is_none()
        );
        assert_eq!(fs::read_dir(&empty).unwrap().count(), 0);

        let v1 = temp.path().join("v1.tar.zst");
        write_archive(&v1);
        let cache = temp.path().join("cache");
        let slug_dir = install_at(Some(v1), exocrate::Location::Custom(cache.clone()))
            .expect("install v1 bundle");

        let bundle = installed_bundle_at(exocrate::Location::Custom(cache.clone()))
            .expect("resolve installed bundle")
            .expect("bundle present");
        assert_eq!(bundle.root, slug_dir);
        drop(bundle);

        let lock_path = sibling_lock_path(&slug_dir, ".lock").unwrap();
        fs::remove_file(&lock_path).expect("remove sibling lock file");
        assert!(
            installed_bundle_at(exocrate::Location::Custom(cache.clone())).is_err(),
            "missing sibling .lock file must fail closed"
        );
        fs::write(&lock_path, b"").expect("restore placeholder lock file");

        fs::remove_dir_all(&slug_dir).expect("remove bundle dir");
        fs::write(&slug_dir, b"file").expect("replace slug with regular file");
        assert!(
            installed_bundle_at(exocrate::Location::Custom(cache.clone())).is_err(),
            "regular file at slug path must fail closed"
        );

        #[cfg(unix)]
        {
            use std::os::unix::fs::symlink;
            fs::remove_file(&slug_dir).expect("remove placeholder file");
            let real = temp.path().join("real");
            fs::create_dir(&real).expect("create target dir");
            symlink(&real, &slug_dir).expect("symlink slug");
            let err = installed_bundle_at(exocrate::Location::Custom(cache))
                .expect_err("symlinked slug path must fail closed");
            assert!(err.contains("symlink"), "{err}");
        }
    }

    #[test]
    fn reinstall_keeps_dir_present_and_coordinates_with_shared_bundle_lease() {
        use std::{sync::mpsc, thread, time::Duration};

        let temp = tempfile::tempdir().expect("create owned fixture");
        let v1 = temp.path().join("v1.tar.zst");
        let v2 = temp.path().join("v2.tar.zst");
        write_archive_with(&v1, b"archive v1");
        write_archive_with(&v2, b"archive v2");

        let cache = temp.path().join("cache");
        let root_v1 = install_at(Some(v1), exocrate::Location::Custom(cache.clone()))
            .expect("install v1 bundle");

        let lease = installed_bundle_at(exocrate::Location::Custom(cache.clone()))
            .expect("acquire v1 lease")
            .expect("v1 bundle present");

        let (started_tx, started_rx) = mpsc::channel();
        let (done_tx, done_rx) = mpsc::channel();
        let cache_for_writer = cache.clone();
        let writer = thread::spawn(move || {
            started_tx.send(()).unwrap();
            let result = install_at(Some(v2), exocrate::Location::Custom(cache_for_writer));
            done_tx.send(result).unwrap();
        });

        started_rx.recv().unwrap();
        let reinstall_lock = sibling_lock_path(&root_v1, ".reinstall.lock").unwrap();
        let deadline = std::time::Instant::now() + Duration::from_secs(5);
        loop {
            if let Ok(file) = fs::OpenOptions::new()
                .read(true)
                .write(true)
                .open(&reinstall_lock)
                && matches!(file.try_lock(), Err(fs::TryLockError::WouldBlock))
            {
                break;
            }
            assert!(
                std::time::Instant::now() < deadline,
                "writer thread never entered reinstall_existing"
            );
            thread::sleep(Duration::from_millis(10));
        }
        // Let the writer finish staging `v2` and block at `<slug>.lock`, then
        // confirm the shared lease keeps `v1` completely intact until dropped.
        thread::sleep(Duration::from_millis(100));
        assert!(
            matches!(done_rx.try_recv(), Err(mpsc::TryRecvError::Empty)),
            "reinstall must wait for shared reader lease on <slug>.lock"
        );
        assert!(root_v1.is_dir(), "installed directory must remain a dir");
        assert_eq!(fs::read(lease.root.join("marker.txt")).unwrap(), b"archive v1");

        drop(lease);
        let root_v2 = done_rx
            .recv_timeout(Duration::from_secs(10))
            .expect("writer finishes once lease drops")
            .expect("reinstall succeeds");
        writer.join().unwrap();
        assert_eq!(root_v2, root_v1);

        let lease_v2 = installed_bundle_at(exocrate::Location::Custom(cache))
            .expect("acquire v2 lease")
            .expect("v2 bundle present");
        assert_eq!(
            fs::read(lease_v2.root.join("marker.txt")).unwrap(),
            b"archive v2"
        );
    }

    #[test]
    fn remove_temp_dir_best_effort_retains_directory_on_cleanup_error() {
        let container = tempfile::tempdir().expect("create owned container");
        let victim = tempfile::Builder::new()
            .prefix(".backup-")
            .tempdir_in(container.path())
            .expect("create victim tempdir");
        let victim_path = victim.path().to_path_buf();

        remove_temp_dir_best_effort_with(victim, "backup", |_| {
            Err(io::Error::from(io::ErrorKind::PermissionDenied))
        });

        assert!(
            victim_path.exists(),
            "best-effort cleanup failure must preserve dir path instead of panicking"
        );
    }

    #[test]
    fn seed_archive_contains_only_incomplete_marker() {
        let decoder = zstd::Decoder::new(SEED_TAR_ZST).expect("decode SEED_TAR_ZST");
        let mut archive = tar::Archive::new(decoder);
        let mut names = Vec::new();
        for entry in archive.entries().expect("read tar entries") {
            let entry = entry.expect("valid tar entry");
            assert_eq!(entry.header().entry_type(), tar::EntryType::Regular);
            assert_eq!(entry.header().size().unwrap(), 0);
            names.push(entry.path().unwrap().to_path_buf());
        }
        assert_eq!(names, vec![PathBuf::from(".incomplete")]);
    }

    #[test]
    fn concurrent_cold_local_archive_installs_apply_both_and_last_writer_wins() {
        use std::{sync::Arc, sync::Barrier, thread};

        let temp = tempfile::tempdir().expect("create owned fixture");
        let v1 = temp.path().join("v1.tar.zst");
        let v2 = temp.path().join("v2.tar.zst");
        let corrupt = temp.path().join("corrupt.tar.zst");
        write_archive_with(&v1, b"archive v1");
        write_archive_with(&v2, b"archive v2");
        fs::write(&corrupt, b"invalid zstd").expect("write corrupt archive");

        // Deterministic cold-race check: `v2` observes an absent cache, then
        // `v1` installs cleanly before `v2` reaches `exocrate`; `v2` must still
        // replace `v1` via the unified `reinstall_existing` path.
        let hook_cache = temp.path().join("hook-cache");
        let v1_for_hook = v1.clone();
        let hook_cache_for_v1 = hook_cache.clone();
        let root_after_hook = install_local_with_seed_hook(
            v2.clone(),
            exocrate::Location::Custom(hook_cache.clone()),
            move || {
                install_at(
                    Some(v1_for_hook),
                    exocrate::Location::Custom(hook_cache_for_v1),
                )
                .expect("concurrent v1 winner succeeds");
            },
        )
        .expect("losing v2 cold caller must still apply its archive");
        assert_eq!(
            fs::read(root_after_hook.join("marker.txt")).unwrap(),
            b"archive v2"
        );
        assert!(!root_after_hook.join(".incomplete").exists());
        assert!(!sibling_lock_path(&root_after_hook, ".incomplete").unwrap().exists());

        // Parallel two-thread cold race against the same fresh cache.
        let race_cache = temp.path().join("race-cache");
        let barrier = Arc::new(Barrier::new(2));
        let b1 = Arc::clone(&barrier);
        let b2 = Arc::clone(&barrier);
        let c1 = race_cache.clone();
        let c2 = race_cache.clone();
        let t1 = thread::spawn(move || {
            b1.wait();
            install_at(Some(v1), exocrate::Location::Custom(c1))
        });
        let t2 = thread::spawn(move || {
            b2.wait();
            install_at(Some(v2), exocrate::Location::Custom(c2))
        });
        let r1 = t1.join().unwrap().expect("thread 1 cold setup succeeds");
        let r2 = t2.join().unwrap().expect("thread 2 cold setup succeeds");
        assert_eq!(r1, r2);
        let final_marker = fs::read(r1.join("marker.txt")).expect("read winner marker");
        assert!(
            final_marker == b"archive v1" || final_marker == b"archive v2",
            "expected complete archive contents, got {final_marker:?}"
        );
        assert!(!r1.join(".incomplete").exists());
        assert!(!sibling_lock_path(&r1, ".incomplete").unwrap().exists());
        let parent = r1.parent().expect("toolchain parent");
        assert_eq!(child_dirs(parent), vec![r1.file_name().unwrap().to_os_string()]);

        // Failed cold setup on a broken archive must clean up the cold seed.
        let failed_cache = temp.path().join("failed-cold-cache");
        assert!(
            install_at(Some(corrupt), exocrate::Location::Custom(failed_cache.clone())).is_err()
        );
        assert!(
            installed_bundle_at(exocrate::Location::Custom(failed_cache))
                .expect("absent after failed cold install")
                .is_none()
        );
    }

    #[test]
    fn incomplete_markers_fail_closed_in_discovery_and_repair_cleanly() {
        let temp = tempfile::tempdir().expect("create owned fixture");
        let v1 = temp.path().join("v1.tar.zst");
        let v2 = temp.path().join("v2.tar.zst");
        write_archive_with(&v1, b"archive v1");
        write_archive_with(&v2, b"archive v2");

        let cache = temp.path().join("cache");
        let root = install_at(Some(v1), exocrate::Location::Custom(cache.clone()))
            .expect("install v1 bundle");
        let inner_marker = root.join(".incomplete");
        let sibling_marker = sibling_lock_path(&root, ".incomplete").unwrap();

        fs::write(&inner_marker, b"").expect("create inner incomplete marker");
        let err = installed_bundle_at(exocrate::Location::Custom(cache.clone()))
            .expect_err("inner .incomplete marker must fail closed");
        assert!(err.contains("incomplete"), "{err}");
        let reuse_err = install_at_with_remote(
            None,
            exocrate::Location::Custom(cache.clone()),
            || Err("offline".into()),
        )
        .expect_err("setup reuse must reject inner .incomplete marker");
        assert!(reuse_err.contains("incomplete"), "{reuse_err}");

        fs::remove_file(&inner_marker).unwrap();
        fs::write(&sibling_marker, b"").expect("create sibling incomplete marker");
        let sib_err = installed_bundle_at(exocrate::Location::Custom(cache.clone()))
            .expect_err("sibling .incomplete marker must fail closed");
        assert!(sib_err.contains("incomplete"), "{sib_err}");
        let reuse_sib_err = install_at_with_remote(
            None,
            exocrate::Location::Custom(cache.clone()),
            || Err("offline".into()),
        )
        .expect_err("setup reuse must reject sibling .incomplete marker");
        assert!(reuse_sib_err.contains("incomplete"), "{reuse_sib_err}");

        // Explicit local setup repairs both markers and restores reuse.
        fs::write(&inner_marker, b"").unwrap();
        let repaired = install_at(Some(v2), exocrate::Location::Custom(cache.clone()))
            .expect("setup --local-archive repairs incomplete bundle");
        assert_eq!(repaired, root);
        assert!(!inner_marker.exists());
        assert!(!sibling_marker.exists());
        assert_eq!(fs::read(repaired.join("marker.txt")).unwrap(), b"archive v2");
        assert_eq!(
            install_at_with_remote(
                None,
                exocrate::Location::Custom(cache.clone()),
                || Err("offline".into()),
            )
            .expect("repaired bundle is reusable"),
            repaired
        );
        let bundle = installed_bundle_at(exocrate::Location::Custom(cache))
            .expect("repaired bundle resolves")
            .expect("repaired bundle present");
        assert_eq!(bundle.root, repaired);
    }

    #[test]
    fn rejects_archive_containing_reserved_incomplete_marker() {
        let temp = tempfile::tempdir().expect("create owned fixture");
        let v1 = temp.path().join("v1.tar.zst");
        let reserved = temp.path().join("reserved.tar.zst");
        write_archive_with(&v1, b"archive v1");
        write_archive_entries(&reserved, &[("marker.txt", b"poison"), (".incomplete", b"")]);

        // Cold cache: reserved `.incomplete` fails closed and drops the seed.
        let cold_cache = temp.path().join("cold-cache");
        let cold_err =
            install_at(Some(reserved.clone()), exocrate::Location::Custom(cold_cache.clone()))
                .expect_err("cold install must reject archive with top-level .incomplete");
        assert!(cold_err.contains(".incomplete"), "{cold_err}");
        assert!(
            installed_bundle_at(exocrate::Location::Custom(cold_cache.clone()))
                .expect("absent after rejected cold install")
                .is_none()
        );
        let resolved_err = CONFIG
            .resolve_installation_dir(exocrate::Location::Custom(cold_cache.clone()))
            .expect_err("rejected cold install must leave no version directory");
        assert_eq!(resolved_err.kind(), io::ErrorKind::NotFound);

        // Warm cache: reserved `.incomplete` fails closed before moving `v1`.
        let warm_cache = temp.path().join("warm-cache");
        let root = install_at(Some(v1), exocrate::Location::Custom(warm_cache.clone()))
            .expect("install v1 bundle");
        let warm_err = install_at(Some(reserved), exocrate::Location::Custom(warm_cache.clone()))
            .expect_err("warm reinstall must reject archive with top-level .incomplete");
        assert!(warm_err.contains(".incomplete"), "{warm_err}");
        assert_eq!(fs::read(root.join("marker.txt")).unwrap(), b"archive v1");
        assert!(!root.join(".incomplete").exists());
        assert!(!sibling_lock_path(&root, ".incomplete").unwrap().exists());
        let bundle = installed_bundle_at(exocrate::Location::Custom(warm_cache))
            .expect("warm bundle stays valid")
            .expect("warm bundle remains present");
        assert_eq!(bundle.root, root);
        assert_eq!(
            child_dirs(root.parent().expect("toolchain parent")),
            vec![root.file_name().unwrap().to_os_string()]
        );
    }

    #[test]
    fn reinstall_only_if_incomplete_reuses_complete_install_without_overwriting() {
        let temp = tempfile::tempdir().expect("create owned fixture");
        let v1 = temp.path().join("v1.tar.zst");
        let v2 = temp.path().join("v2.tar.zst");
        let missing = temp.path().join("missing.tar.zst");
        write_archive_with(&v1, b"archive v1");
        write_archive_with(&v2, b"archive v2");

        let cache = temp.path().join("cache");
        let root =
            install_at(Some(v1), exocrate::Location::Custom(cache)).expect("install v1 bundle");

        // When already complete, `reinstall_only_if_incomplete = true` returns
        // before touching or even opening `source`.
        let reused_missing = reinstall_existing(&root, exocrate::Source::Local(missing), true)
            .expect("complete bundle skips opening source");
        assert_eq!(reused_missing, root);
        let reused_v2 = reinstall_existing(&root, exocrate::Source::Local(v2.clone()), true)
            .expect("complete bundle is reused without overwriting");
        assert_eq!(reused_v2, root);
        assert_eq!(fs::read(root.join("marker.txt")).unwrap(), b"archive v1");

        // Negative controls: incomplete marker or absent dir still installs
        // `v2`.
        let sibling_marker = sibling_lock_path(&root, ".incomplete").unwrap();
        fs::write(&sibling_marker, b"").expect("mark bundle incomplete");
        let repaired = reinstall_existing(&root, exocrate::Source::Local(v2.clone()), true)
            .expect("incomplete bundle is repaired");
        assert_eq!(repaired, root);
        assert_eq!(fs::read(root.join("marker.txt")).unwrap(), b"archive v2");
        assert!(!sibling_marker.exists());

        fs::remove_dir_all(&root).expect("remove directory before retry");
        let recreated = reinstall_existing(&root, exocrate::Source::Local(v2), true)
            .expect("absent directory is not treated as complete");
        assert_eq!(recreated, root);
        assert_eq!(fs::read(root.join("marker.txt")).unwrap(), b"archive v2");
    }
}
