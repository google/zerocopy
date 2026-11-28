// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Installation directory resolution, lock files, permission normalization,
//! and temporary-directory cleanup for `cargo anneal setup`.

use std::{
    ffi::OsString,
    fs, io,
    path::{Path, PathBuf},
};

use super::CONFIG;

fn clone_location(location: &exocrate::Location) -> exocrate::Location {
    match location {
        exocrate::Location::UserGlobal => exocrate::Location::UserGlobal,
        exocrate::Location::LocalDev => exocrate::Location::LocalDev,
        exocrate::Location::Custom(path) => exocrate::Location::Custom(path.clone()),
    }
}

pub(super) fn resolve_installation_dir_with(
    mut resolve: impl FnMut() -> io::Result<PathBuf>,
) -> io::Result<PathBuf> {
    // `exocrate 0.3.0`'s `check_exists` performs `is_dir()` then
    // `try_exists()`, so a concurrent `fs::rename` between those two stats
    // produces a spurious `AlreadyExists`. A single retry resolves the newly
    // renamed directory while still failing closed on real non-directories.
    match resolve() {
        Err(err) if err.kind() == io::ErrorKind::AlreadyExists => resolve(),
        res => res,
    }
}

pub(super) fn resolve_installation_dir(location: &exocrate::Location) -> io::Result<PathBuf> {
    resolve_installation_dir_with(|| CONFIG.resolve_installation_dir(clone_location(location)))
}

pub(super) fn sibling_lock_path(dir: &Path, suffix: &str) -> io::Result<PathBuf> {
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

pub(super) fn open_regular_lock_file(
    lock_path: &Path,
    write: bool,
    create: bool,
) -> io::Result<Option<fs::File>> {
    match fs::symlink_metadata(lock_path) {
        Ok(meta) if meta.file_type().is_symlink() => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("lock path {} is a symlink", lock_path.display()),
            ));
        }
        Ok(meta) if !meta.file_type().is_file() => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("lock path {} is not a regular file", lock_path.display()),
            ));
        }
        Ok(_) => {}
        Err(err) if err.kind() == io::ErrorKind::NotFound => {
            if !create {
                return Ok(None);
            }
        }
        Err(err) => return Err(err),
    }

    let mut opts = fs::OpenOptions::new();
    opts.read(true).write(write).create(create).truncate(false);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        opts.custom_flags(libc::O_NOFOLLOW);
    }
    let file = match opts.open(lock_path) {
        Ok(file) => file,
        Err(err) if !create && err.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(err) => return Err(err),
    };
    if !file.metadata()?.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("lock path {} is not a regular file", lock_path.display()),
        ));
    }
    Ok(Some(file))
}

pub(super) fn open_exclusive_lock(lock_path: &Path) -> io::Result<fs::File> {
    let file = open_regular_lock_file(lock_path, true, true)?.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::NotFound,
            format!("lock path {} does not exist", lock_path.display()),
        )
    })?;
    file.lock()?;
    Ok(file)
}

#[cfg(unix)]
pub(super) fn normalize_dir_permissions(root: &Path) -> io::Result<()> {
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
pub(super) fn normalize_dir_permissions(_root: &Path) -> io::Result<()> {
    Ok(())
}

pub(super) fn read_entry_names(dir: &Path) -> io::Result<Vec<OsString>> {
    let mut names = Vec::new();
    for entry in fs::read_dir(dir)? {
        names.push(entry?.file_name());
    }
    Ok(names)
}

pub(super) fn move_entries_back(names: &[OsString], from: &Path, to: &Path) -> io::Result<()> {
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

pub(super) fn remove_temp_dir_best_effort(dir: tempfile::TempDir, kind: &str) {
    remove_temp_dir_best_effort_with(dir, kind, |path| fs::remove_dir_all(path));
}

pub(super) fn remove_temp_dir_best_effort_with(
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
