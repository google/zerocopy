// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Discovery and removal of old toolchain versions (`--clear-old`).

use std::{
    ffi::OsStr,
    fs, io,
    path::{Path, PathBuf},
};

use super::{
    install_dir::{normalize_dir_permissions, open_regular_lock_file, sibling_lock_path},
    lease::INCOMPLETE_MARKER,
};

/// Controls how [`install_at_with_prune`] handles older cached toolchain
/// directories beside the current version.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PruneMode {
    /// Remove all unlocked old toolchain directories without prompting.
    ClearOld,
    /// Prompt interactively before removing old toolchain directories.
    Interactive,
    /// Leave old toolchain directories untouched and emit a note.
    NonInteractive,
    /// Leave old toolchain directories untouched without emitting the note.
    NonInteractiveQuiet,
}

/// Summary of an old-toolchain pruning pass for diagnostics and tests.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct PruneReport {
    pub(crate) found: Vec<PathBuf>,
    pub(crate) removed: Vec<PathBuf>,
    pub(crate) skipped_busy: Vec<PathBuf>,
    pub(crate) warnings: Vec<String>,
}

pub(super) enum TryLockOutcome {
    Acquired(fs::File),
    Busy,
}

pub(super) enum RemoveOldOutcome {
    Removed { cleanup_warnings: Vec<String> },
    AlreadyGone,
    SkippedUnmanaged,
    Busy,
}

fn is_internal_temp_dir_name(name: &OsStr) -> bool {
    let bytes = name.as_encoded_bytes();
    bytes.starts_with(b".staging-")
        || bytes.starts_with(b".backup-")
        || bytes.ends_with(b".staging")
}

pub(super) fn open_try_exclusive_lock(
    lock_path: &Path,
    create: bool,
) -> io::Result<Option<TryLockOutcome>> {
    let Some(file) = open_regular_lock_file(lock_path, true, create)? else {
        return Ok(None);
    };
    match file.try_lock() {
        Ok(()) => Ok(Some(TryLockOutcome::Acquired(file))),
        Err(fs::TryLockError::WouldBlock) => Ok(Some(TryLockOutcome::Busy)),
        Err(fs::TryLockError::Error(err)) => Err(err),
    }
}

pub(super) fn create_incomplete_marker_nofollow(path: &Path) -> io::Result<()> {
    match fs::symlink_metadata(path) {
        Ok(meta) if meta.file_type().is_symlink() => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("marker path {} is a symlink", path.display()),
            ));
        }
        Ok(meta) if !meta.file_type().is_file() => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("marker path {} is not a regular file", path.display()),
            ));
        }
        Ok(_) => {}
        Err(err) if err.kind() == io::ErrorKind::NotFound => {}
        Err(err) => return Err(err),
    }

    let mut opts = fs::OpenOptions::new();
    opts.write(true).create(true).truncate(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        opts.custom_flags(libc::O_NOFOLLOW);
    }
    let file = opts.open(path)?;
    if !file.metadata()?.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("marker path {} is not a regular file", path.display()),
        ));
    }
    Ok(())
}

pub(super) fn remove_regular_sibling_if_present(path: &Path) -> io::Result<()> {
    match fs::symlink_metadata(path) {
        Ok(meta) if meta.file_type().is_symlink() => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("refusing to remove symlink {}", path.display()),
        )),
        Ok(meta) if !meta.file_type().is_file() => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("refusing to remove non-file {}", path.display()),
        )),
        Ok(_) => match fs::remove_file(path) {
            Ok(()) => Ok(()),
            Err(err) if err.kind() == io::ErrorKind::NotFound => Ok(()),
            Err(err) => Err(err),
        },
        Err(err) if err.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(err) => Err(err),
    }
}

fn discover_old_toolchains(
    current_dir: &Path,
    warnings: &mut Vec<String>,
) -> Result<(PathBuf, Vec<PathBuf>), String> {
    let parent = current_dir.parent().ok_or_else(|| {
        format!("installed toolchain {} has no parent directory", current_dir.display())
    })?;
    let current_name = current_dir.file_name().ok_or_else(|| {
        format!("installed toolchain {} has no directory name", current_dir.display())
    })?;
    let parent_meta = fs::symlink_metadata(parent).map_err(|err| {
        format!("cannot inspect toolchain cache directory {}: {err}", parent.display())
    })?;
    if parent_meta.file_type().is_symlink() || !parent_meta.file_type().is_dir() {
        return Err(format!(
            "toolchain cache directory {} is not a real directory",
            parent.display()
        ));
    }

    let entries = fs::read_dir(parent).map_err(|err| {
        format!("cannot scan toolchain cache directory {}: {err}", parent.display())
    })?;
    let mut old_dirs = Vec::new();
    for entry_res in entries {
        let entry = match entry_res {
            Ok(entry) => entry,
            Err(err) => {
                warnings.push(format!(
                    "cannot read entry in toolchain cache {}: {err}",
                    parent.display()
                ));
                continue;
            }
        };
        let name = entry.file_name();
        if name == current_name || is_internal_temp_dir_name(&name) {
            continue;
        }
        let path = entry.path();
        let meta = match fs::symlink_metadata(&path) {
            Ok(meta) => meta,
            Err(err) if err.kind() == io::ErrorKind::NotFound => continue,
            Err(err) => {
                warnings.push(format!("cannot inspect {}: {err}", path.display()));
                continue;
            }
        };
        let ft = meta.file_type();
        if !ft.is_dir() || ft.is_symlink() {
            continue;
        }
        // Only treat directories with a pre-existing regular `<slug>.lock` as
        // exocrate-managed Anneal toolchains so unrelated or in-flight staging
        // directories are never selected.
        let lock_path = match sibling_lock_path(&path, ".lock") {
            Ok(lock_path) => lock_path,
            Err(err) => {
                warnings.push(format!("cannot locate lock path for {}: {err}", path.display()));
                continue;
            }
        };
        match fs::symlink_metadata(&lock_path) {
            Ok(lock_meta) if lock_meta.file_type().is_symlink() => {
                warnings.push(format!(
                    "skipping {}: lock path {} is a symlink",
                    path.display(),
                    lock_path.display()
                ));
            }
            Ok(lock_meta) if !lock_meta.file_type().is_file() => {
                warnings.push(format!(
                    "skipping {}: lock path {} is not a regular file",
                    path.display(),
                    lock_path.display()
                ));
            }
            Ok(_) => old_dirs.push(path),
            Err(err) if err.kind() == io::ErrorKind::NotFound => {}
            Err(err) => {
                warnings.push(format!("cannot inspect {}: {err}", lock_path.display()));
            }
        }
    }
    old_dirs.sort();
    Ok((parent.to_path_buf(), old_dirs))
}

pub(super) fn try_remove_old_toolchain(old_dir: &Path) -> io::Result<RemoveOldOutcome> {
    let reinstall_lock_path = sibling_lock_path(old_dir, ".reinstall.lock")?;
    let exocrate_lock_path = sibling_lock_path(old_dir, ".lock")?;
    let incomplete_path = sibling_lock_path(old_dir, INCOMPLETE_MARKER)?;

    // Probe any existing `.reinstall.lock` without creating it first so a busy
    // shared `.lock` (from a concurrent `verify`) skips cleanly without leaving
    // a stray `.reinstall.lock` file behind. Open `.lock` with `create = false`
    // so unmanaged directories without a pre-existing exocrate lock are skipped
    // rather than creating new lock files. All locks are non-blocking, so
    // acquiring `.lock` before creating `.reinstall.lock` cannot deadlock.
    let mut reinstall_lock = match open_try_exclusive_lock(&reinstall_lock_path, false)? {
        Some(TryLockOutcome::Busy) => return Ok(RemoveOldOutcome::Busy),
        Some(TryLockOutcome::Acquired(file)) => Some(file),
        None => None,
    };
    let exocrate_lock = match open_try_exclusive_lock(&exocrate_lock_path, false)? {
        Some(TryLockOutcome::Acquired(file)) => file,
        Some(TryLockOutcome::Busy) => return Ok(RemoveOldOutcome::Busy),
        None => return Ok(RemoveOldOutcome::SkippedUnmanaged),
    };
    if reinstall_lock.is_none() {
        match open_try_exclusive_lock(&reinstall_lock_path, true)? {
            Some(TryLockOutcome::Acquired(file)) => reinstall_lock = Some(file),
            Some(TryLockOutcome::Busy) | None => {
                drop(exocrate_lock);
                return Ok(RemoveOldOutcome::Busy);
            }
        }
    }

    // Re-validate under both exclusive locks to close TOCTOU swaps.
    match fs::symlink_metadata(old_dir) {
        Ok(meta) if meta.file_type().is_symlink() => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "old toolchain path is a symlink",
            ));
        }
        Ok(meta) if !meta.file_type().is_dir() => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "old toolchain path is not a directory",
            ));
        }
        Ok(_) => {}
        Err(err) if err.kind() == io::ErrorKind::NotFound => {
            let _ = remove_regular_sibling_if_present(&incomplete_path);
            drop(exocrate_lock);
            drop(reinstall_lock);
            return Ok(RemoveOldOutcome::AlreadyGone);
        }
        Err(err) => return Err(err),
    }

    // Mark the directory incomplete before starting recursive deletion so an
    // interrupted removal cannot leave a half-deleted bundle looking valid.
    create_incomplete_marker_nofollow(&incomplete_path)?;
    normalize_dir_permissions(old_dir)?;
    fs::remove_dir_all(old_dir)?;

    // Clean up only the `.incomplete` marker and leave `.lock` and
    // `.reinstall.lock` in place: unlinking a held lock file can split mutual
    // exclusion across inodes if another process is already waiting on it.
    let mut cleanup_warnings = Vec::new();
    if let Err(err) = remove_regular_sibling_if_present(&incomplete_path) {
        cleanup_warnings
            .push(format!("failed to clean up sibling file {}: {err}", incomplete_path.display()));
    }
    drop(exocrate_lock);
    drop(reinstall_lock);
    Ok(RemoveOldOutcome::Removed { cleanup_warnings })
}

fn parse_yes_response(line: &str) -> bool {
    matches!(line.trim().to_ascii_lowercase().as_str(), "y" | "yes")
}

pub(super) fn prompt_on_streams(
    parent: &Path,
    old_dirs: &[PathBuf],
    reader: &mut impl io::BufRead,
    writer: &mut impl io::Write,
) -> io::Result<bool> {
    let noun = if old_dirs.len() == 1 { "toolchain" } else { "toolchains" };
    writeln!(writer, "Found {} old cached Anneal {noun} in {}:", old_dirs.len(), parent.display())?;
    for dir in old_dirs {
        writeln!(writer, "  {}", dir.display())?;
    }
    write!(writer, "Remove old cached {noun}? [y/N] ")?;
    writer.flush()?;
    let mut answer = String::new();
    let bytes = reader.read_line(&mut answer)?;
    if bytes == 0 {
        return Ok(false);
    }
    Ok(parse_yes_response(&answer))
}

pub(super) fn prompt_stdin_stdout(parent: &Path, old_dirs: &[PathBuf]) -> io::Result<bool> {
    let stdin = io::stdin();
    let mut reader = stdin.lock();
    let stdout = io::stdout();
    let mut writer = stdout.lock();
    prompt_on_streams(parent, old_dirs, &mut reader, &mut writer)
}

pub(super) fn prune_old_toolchains_with(
    current_dir: &Path,
    mode: PruneMode,
    prompt: impl FnOnce(&Path, &[PathBuf]) -> io::Result<bool>,
    status_out: &mut impl io::Write,
) -> PruneReport {
    let mut report = PruneReport::default();
    let (parent, old_dirs) = match discover_old_toolchains(current_dir, &mut report.warnings) {
        Ok(found) => found,
        Err(msg) => {
            let _ = writeln!(status_out, "warning: {msg}");
            report.warnings.push(msg);
            return report;
        }
    };
    for warning in &report.warnings {
        let _ = writeln!(status_out, "warning: {warning}");
    }
    if old_dirs.is_empty() {
        return report;
    }
    report.found = old_dirs.clone();

    let should_remove = match mode {
        PruneMode::ClearOld => true,
        PruneMode::Interactive => match prompt(&parent, &old_dirs) {
            Ok(confirmed) => confirmed,
            Err(err) => {
                let msg = format!("failed to prompt before clearing old toolchains: {err}");
                let _ = writeln!(status_out, "warning: {msg}");
                report.warnings.push(msg);
                false
            }
        },
        PruneMode::NonInteractive => {
            let (noun, pronoun) =
                if old_dirs.len() == 1 { ("toolchain", "it") } else { ("toolchains", "them") };
            let _ = writeln!(
                status_out,
                "note: found {} old cached Anneal {noun} in {}; re-run \
                 `cargo anneal setup --clear-old` to remove {pronoun}",
                old_dirs.len(),
                parent.display()
            );
            false
        }
        PruneMode::NonInteractiveQuiet => false,
    };
    if !should_remove {
        return report;
    }

    for old_dir in &old_dirs {
        match try_remove_old_toolchain(old_dir) {
            Ok(RemoveOldOutcome::Removed { cleanup_warnings }) => {
                report.removed.push(old_dir.clone());
                let _ =
                    writeln!(status_out, "Removed old Anneal toolchain at {}", old_dir.display());
                for warning in cleanup_warnings {
                    let _ = writeln!(status_out, "warning: {warning}");
                    report.warnings.push(warning);
                }
            }
            Ok(RemoveOldOutcome::AlreadyGone | RemoveOldOutcome::SkippedUnmanaged) => {}
            Ok(RemoveOldOutcome::Busy) => {
                report.skipped_busy.push(old_dir.clone());
                let msg = format!(
                    "skipping old Anneal toolchain {} because it is currently in use",
                    old_dir.display()
                );
                let _ = writeln!(status_out, "warning: {msg}");
                report.warnings.push(msg);
            }
            Err(err) => {
                let msg =
                    format!("failed to remove old Anneal toolchain {}: {err}", old_dir.display());
                let _ = writeln!(status_out, "warning: {msg}");
                report.warnings.push(msg);
            }
        }
    }
    report
}
