// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Installing a bundle from a local archive, the remote archive, or an
//! existing directory.

use std::{
    ffi::OsStr,
    fs, io,
    path::{Path, PathBuf},
};

use super::{
    Bundle, CONFIG,
    install_dir::{
        move_entries_back, normalize_dir_permissions, open_exclusive_lock, read_entry_names,
        remove_temp_dir_best_effort, resolve_installation_dir, sibling_lock_path,
    },
    installed_bundle_at,
    lease::{
        AcquireLeaseError, INCOMPLETE_MARKER, SEED_TAR_ZST, acquire_bundle_lease,
        cleanup_cold_seed_if_uncommitted, is_cold_seed_only,
    },
    prune::{create_incomplete_marker_nofollow, remove_regular_sibling_if_present},
};

/// Stage `source` inside `dir`'s parent directory, then swap its top-level
/// entries into `dir` while keeping `dir` continuously present as a real
/// directory, preserving any previous installation if staging fails, and
/// cleaning up an uncommitted cold seed if staging or pre-commit setup fails.
///
/// Returns a [`Bundle`] holding a shared flock on `<slug>.lock` acquired before
/// releasing `<slug>.reinstall.lock`, leaving no unlocked gap during which a
/// concurrent cross-version `setup --clear-old` could delete `dir`.
///
/// When `reinstall_only_if_incomplete` is `true`, returns early once
/// `.reinstall.lock` is held if `dir` is already a complete real directory
/// (avoiding overwriting a concurrent install that finished repairing `dir`).
pub(super) fn reinstall_existing(
    dir: &Path,
    source: exocrate::Source,
    reinstall_only_if_incomplete: bool,
) -> io::Result<Bundle> {
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
    if reinstall_only_if_incomplete {
        match acquire_bundle_lease(dir) {
            Ok(bundle) => return Ok(bundle),
            Err(AcquireLeaseError::MissingOrIncomplete(_)) => {}
            Err(AcquireLeaseError::Fatal(err)) => return Err(io::Error::other(err)),
        }
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
            let sibling_incomplete = sibling_lock_path(dir, INCOMPLETE_MARKER)?;
            remove_regular_sibling_if_present(&sibling_incomplete)?;
            fs::rename(&staged_dir, dir)?;
            drop(exocrate_lock);
            let bundle =
                acquire_bundle_lease(dir).map_err(|err| io::Error::other(err.into_message()))?;
            remove_temp_dir_best_effort(staging_holder, "staging");
            drop(reinstall_lock);
            return Ok(bundle);
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
    if let Err(err) = create_incomplete_marker_nofollow(&sibling_incomplete) {
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

    remove_regular_sibling_if_present(&sibling_incomplete)?;

    // Hand off directly from exclusive `<slug>.lock` to a shared lease while
    // `.reinstall.lock` is still held so concurrent pruners never observe an
    // unlocked window on `dir`.
    drop(exocrate_lock);
    let bundle = acquire_bundle_lease(dir).map_err(|err| io::Error::other(err.into_message()))?;
    remove_temp_dir_best_effort(backup_holder, "backup");
    remove_temp_dir_best_effort(staging_holder, "staging");
    drop(reinstall_lock);
    Ok(bundle)
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

pub(super) fn install_local(path: PathBuf, location: exocrate::Location) -> io::Result<Bundle> {
    install_local_with_seed_hook(path, location, || {})
}

pub(super) fn install_local_with_seed_hook(
    path: PathBuf,
    location: exocrate::Location,
    after_resolve_absent: impl FnOnce(),
) -> io::Result<Bundle> {
    // Validate the caller's archive before initializing any cache directory.
    ensure_local_archive_readable(&path)?;
    let dir = match resolve_installation_dir(&location) {
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

pub(super) fn resolve_complete_existing(
    location: exocrate::Location,
    missing_reason: String,
) -> Result<Bundle, String> {
    match installed_bundle_at(location)? {
        Some(bundle) => Ok(bundle),
        None => Err(missing_reason),
    }
}

pub(super) fn install_remote(
    get_remote: impl Fn() -> Result<exocrate::RemoteArchive, String>,
    location: exocrate::Location,
) -> Result<Bundle, String> {
    install_from_source(|| get_remote().map(exocrate::Source::Remote), location)
}

pub(super) fn install_from_source(
    get_source: impl Fn() -> Result<exocrate::Source, String>,
    location: exocrate::Location,
) -> Result<Bundle, String> {
    let source = get_source()?;
    match resolve_installation_dir(&location) {
        Ok(dir) => match acquire_bundle_lease(&dir) {
            Ok(bundle) => Ok(bundle),
            Err(AcquireLeaseError::MissingOrIncomplete(_)) => {
                reinstall_existing(&dir, source, true)
                    .map_err(|e| format!("failed to install Anneal toolchain: {e}"))
            }
            Err(AcquireLeaseError::Fatal(err)) => Err(err),
        },
        Err(err) if err.kind() == io::ErrorKind::NotFound => {
            let (dir, _) = CONFIG
                .resolve_installation_dir_or_install(location, source)
                .map_err(|e| format!("failed to install Anneal toolchain: {e}"))?;
            // Immediately take a shared lease on `dir`. If a concurrent pruner
            // deleted `dir` after `exocrate` dropped `<slug>.lock` (or left it
            // incomplete), recover via `reinstall_existing` for a gap-free
            // leased `Bundle`.
            match acquire_bundle_lease(&dir) {
                Ok(bundle) => Ok(bundle),
                Err(AcquireLeaseError::MissingOrIncomplete(_)) => {
                    reinstall_existing(&dir, get_source()?, true)
                        .map_err(|e| format!("failed to install Anneal toolchain: {e}"))
                }
                Err(AcquireLeaseError::Fatal(err)) => Err(err),
            }
        }
        Err(err) => Err(format!("cannot inspect installed Anneal toolchain: {err}")),
    }
}
