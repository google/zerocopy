// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Manifest validation and symlink-safe, create-new file writing for
//! `cargo anneal init`.

use std::{
    fs::{self, OpenOptions},
    io::Write,
    path::{Component, Path, PathBuf},
};

use super::ScaffoldFile;

fn has_toml_table(contents: &str, header: &str) -> bool {
    contents.lines().any(|line| {
        let stripped = line.split('#').next().unwrap_or("").trim();
        stripped == header
    })
}

pub(super) fn validate_manifest(manifest: &Path) -> Result<(), String> {
    let meta = match fs::symlink_metadata(manifest) {
        Ok(meta) => meta,
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            return Err(format!(
                "no Cargo.toml found at {}; run inside a Cargo package, pass --manifest-path \
                 <Cargo.toml>, or run `cargo anneal init --standalone` for a standalone example",
                manifest.display()
            ));
        }
        Err(err) => {
            return Err(format!("cannot inspect {}: {err}", manifest.display()));
        }
    };
    if meta.file_type().is_symlink() || !meta.is_file() {
        return Err(format!(
            "manifest path {} must be a regular non-symlink file",
            manifest.display()
        ));
    }
    let contents = fs::read_to_string(manifest)
        .map_err(|err| format!("cannot read {}: {err}", manifest.display()))?;
    if has_toml_table(&contents, "[workspace]") && !has_toml_table(&contents, "[package]") {
        return Err(format!(
            "{} appears to be a virtual workspace without [package]; pass --manifest-path \
             <member>/Cargo.toml",
            manifest.display()
        ));
    }
    Ok(())
}

/// Validate an existing directory component or create a missing one,
/// returning `Ok(true)` if `create_dir` created this component.
///
/// When `allow_symlink_ancestor` is `true`, an existing symlink is resolved
/// with `fs::metadata` (matching OS resolution of caller-chosen ancestor
/// directories such as macOS `/tmp -> private/tmp` or symlinked `$TMPDIR`).
/// Otherwise, symlinks are rejected via `fs::symlink_metadata`.
fn ensure_dir_component(prefix: &Path, allow_symlink_ancestor: bool) -> Result<bool, String> {
    match fs::symlink_metadata(prefix) {
        Ok(lmeta) if allow_symlink_ancestor && lmeta.file_type().is_symlink() => {
            let meta = fs::metadata(prefix).map_err(|err| {
                format!("cannot inspect symlink directory ancestor {}: {err}", prefix.display())
            })?;
            if !meta.is_dir() {
                return Err(format!(
                    "expected directory at {}, found non-directory",
                    prefix.display()
                ));
            }
            Ok(false)
        }
        Ok(lmeta) => {
            if lmeta.file_type().is_symlink() {
                return Err(format!("refusing symlink directory {}", prefix.display()));
            }
            if !lmeta.is_dir() {
                return Err(format!(
                    "expected directory at {}, found non-directory",
                    prefix.display()
                ));
            }
            Ok(false)
        }
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            fs::create_dir(prefix).map_err(|create_err| {
                format!("cannot create directory {}: {create_err}", prefix.display())
            })?;
            let meta = fs::symlink_metadata(prefix).map_err(|meta_err| {
                format!("cannot inspect directory {}: {meta_err}", prefix.display())
            })?;
            if meta.file_type().is_symlink() || !meta.is_dir() {
                return Err(format!(
                    "directory {} changed unexpectedly after creation",
                    prefix.display()
                ));
            }
            Ok(true)
        }
        Err(err) => Err(format!("cannot inspect directory {}: {err}", prefix.display())),
    }
}

pub(super) fn ensure_non_symlink_dir(dir: &Path) -> Result<(), String> {
    if dir.as_os_str().is_empty() {
        return Err("directory path cannot be empty".into());
    }
    // Rebuild from `components()` to trim trailing separators (and trailing
    // `/.`) while preserving root `/` and `.`, so `symlink_metadata` inspects
    // a final symlink entry itself rather than following a trailing slash.
    let trimmed: PathBuf = dir.components().collect();
    if trimmed.as_os_str().is_empty() {
        return Err("directory path cannot be empty".into());
    }
    if matches!(trimmed.components().next_back(), Some(Component::ParentDir)) {
        return Err(format!("refusing directory path ending in '..': {}", dir.display()));
    }

    let mut prefix = PathBuf::new();
    let mut created_missing = false;
    let mut components = trimmed.components().peekable();
    while let Some(component) = components.next() {
        prefix.push(component.as_os_str());
        if matches!(component, Component::RootDir | Component::Prefix(_)) {
            continue;
        }
        let is_last = components.peek().is_none();
        if ensure_dir_component(&prefix, !created_missing && !is_last)? {
            created_missing = true;
        }
    }

    let meta = fs::symlink_metadata(&trimmed)
        .map_err(|err| format!("cannot inspect directory {}: {err}", trimmed.display()))?;
    if meta.file_type().is_symlink() {
        return Err(format!("refusing symlink directory {}", trimmed.display()));
    }
    if !meta.is_dir() {
        return Err(format!("expected directory at {}, found non-directory", trimmed.display()));
    }
    Ok(())
}

pub(super) fn write_create_new_files(
    dir: &Path,
    files: &[ScaffoldFile],
) -> Result<Vec<PathBuf>, String> {
    ensure_non_symlink_dir(dir)?;

    for file in files {
        let dest = dir.join(file.name);
        match fs::symlink_metadata(&dest) {
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => {}
            Ok(_) => {
                return Err(format!("refusing to overwrite existing file {}", dest.display()));
            }
            Err(err) => {
                return Err(format!("cannot inspect {}: {err}", dest.display()));
            }
        }
    }

    let mut created = Vec::with_capacity(files.len());
    for file in files {
        let dest = dir.join(file.name);
        let write_result = (|| -> std::io::Result<()> {
            let mut opts = OpenOptions::new();
            opts.write(true).create_new(true);
            #[cfg(unix)]
            {
                use std::os::unix::fs::OpenOptionsExt;
                opts.custom_flags(libc::O_NOFOLLOW);
            }
            let mut handle = opts.open(&dest)?;
            handle.write_all(file.contents.as_bytes())?;
            handle.flush()
        })();
        if let Err(err) = write_result {
            for path in created.iter().rev() {
                let _ = fs::remove_file(path);
            }
            return Err(format!("cannot write {}: {err}", dest.display()));
        }
        created.push(dest);
    }
    Ok(created)
}
