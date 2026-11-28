// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The `.incomplete` marker, the cold seed archive, and shared bundle leases.

use std::{ffi::OsStr, fs, io, path::Path};

use super::{
    Bundle,
    install_dir::{
        open_exclusive_lock, open_regular_lock_file, read_entry_names, sibling_lock_path,
    },
};

pub(super) const INCOMPLETE_MARKER: &str = ".incomplete";

pub(super) enum AcquireLeaseError {
    MissingOrIncomplete(String),
    Fatal(String),
}

impl AcquireLeaseError {
    pub(super) fn into_message(self) -> String {
        match self {
            Self::MissingOrIncomplete(msg) | Self::Fatal(msg) => msg,
        }
    }
}

fn validate_real_dir_for_lease(dir: &Path) -> Result<(), AcquireLeaseError> {
    match fs::symlink_metadata(dir) {
        Ok(meta) if meta.file_type().is_symlink() => Err(AcquireLeaseError::Fatal(format!(
            "installed toolchain path {} is a symlink",
            dir.display()
        ))),
        Ok(meta) if !meta.file_type().is_dir() => Err(AcquireLeaseError::Fatal(format!(
            "installed toolchain path {} is not a directory",
            dir.display()
        ))),
        Ok(_) => Ok(()),
        Err(err) if err.kind() == io::ErrorKind::NotFound => {
            Err(AcquireLeaseError::MissingOrIncomplete(format!(
                "cannot inspect installed toolchain {}: {err}",
                dir.display()
            )))
        }
        Err(err) => Err(AcquireLeaseError::Fatal(format!(
            "cannot inspect installed toolchain {}: {err}",
            dir.display()
        ))),
    }
}

// Deterministic USTAR tar archive containing a single empty `.incomplete`
// regular file, compressed with zstd (`SEED_TAR_ZST`). Used by `install_local`
// to initialize a cold `<slug>` directory + `<slug>.lock` in sub-millisecond
// time so concurrent `setup --local-archive` callers converge onto the single
// serialized `reinstall_existing` pipeline without `exocrate` skipping losers.

pub(super) const SEED_TAR_ZST: &[u8] = &[
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

fn check_bundle_complete_for_lease(dir: &Path) -> Result<(), AcquireLeaseError> {
    let inner_marker = dir.join(INCOMPLETE_MARKER);
    let sibling_marker = sibling_lock_path(dir, INCOMPLETE_MARKER).map_err(|err| {
        AcquireLeaseError::Fatal(format!(
            "cannot locate toolchain marker for {}: {err}",
            dir.display()
        ))
    })?;
    if marker_present(&inner_marker).map_err(AcquireLeaseError::Fatal)?
        || marker_present(&sibling_marker).map_err(AcquireLeaseError::Fatal)?
    {
        return Err(AcquireLeaseError::MissingOrIncomplete(format!(
            "Anneal toolchain installation at {} is incomplete; run `cargo anneal setup`",
            dir.display()
        )));
    }
    Ok(())
}

/// Validates `dir` as a real directory, acquires a shared flock on its regular
/// sibling `<slug>.lock`, re-validates `dir`, and verifies completion markers
/// are absent.
pub(super) fn acquire_bundle_lease(dir: &Path) -> Result<Bundle, AcquireLeaseError> {
    validate_real_dir_for_lease(dir)?;
    let lock_path = sibling_lock_path(dir, ".lock").map_err(|err| {
        AcquireLeaseError::Fatal(format!(
            "cannot locate toolchain lock for {}: {err}",
            dir.display()
        ))
    })?;
    let lock_file = match open_regular_lock_file(&lock_path, false, false).map_err(|err| {
        AcquireLeaseError::Fatal(format!(
            "cannot open toolchain lock {}: {err}",
            lock_path.display()
        ))
    })? {
        Some(file) => file,
        None => {
            // If `<slug>.lock` is absent on a missing or `.incomplete`
            // directory (for example after an interrupted install), classify it
            // as recoverable so remote setup can repair the bundle and recreate
            // the lock; complete directories without a lock still fail closed.
            validate_real_dir_for_lease(dir)?;
            check_bundle_complete_for_lease(dir)?;
            return Err(AcquireLeaseError::Fatal(format!(
                "cannot open toolchain lock {}: No such file or directory",
                lock_path.display()
            )));
        }
    };
    lock_file.lock_shared().map_err(|err| {
        AcquireLeaseError::Fatal(format!("cannot lock toolchain {}: {err}", lock_path.display()))
    })?;
    validate_real_dir_for_lease(dir)?;
    check_bundle_complete_for_lease(dir)?;
    Ok(Bundle { root: dir.to_path_buf(), _lock: Some(lock_file) })
}

pub(super) fn is_cold_seed_only(dir: &Path) -> bool {
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

pub(super) fn cleanup_cold_seed_if_uncommitted(dir: &Path) {
    if let Ok(lock_path) = sibling_lock_path(dir, ".lock")
        && let Ok(_guard) = open_exclusive_lock(&lock_path)
        && is_cold_seed_only(dir)
    {
        let _ = fs::remove_dir_all(dir);
    }
}
