// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Retained-handle boundary for repository-owned input files.
//!
//! A path can change between canonicalization, identity inspection, and the
//! eventual read. Keep those operations in one place, then make every caller
//! consume the same retained operating-system handle whose containment and
//! identity were checked. Callers remain responsible for deciding whether an
//! in-repository symbolic link is allowed for their particular input.

use std::{
    fs::File,
    io::{self, Read},
    path::{Path, PathBuf},
};

use same_file::Handle;
use thiserror::Error;

/// One repository input whose path, identity, and bytes share an open handle.
#[derive(Debug)]
pub(crate) struct OpenedRepositoryFile {
    path: PathBuf,
    file: File,
    // Retain this independently open handle for callers which compare file
    // identity. Some platforms may reuse an identifier once its last handle
    // closes, so a numeric identity captured and then dropped is insufficient.
    identity: Handle,
}

impl OpenedRepositoryFile {
    /// Returns the canonical path checked immediately after the open.
    pub(crate) fn path(&self) -> &Path {
        &self.path
    }

    /// Returns the retained file used for all subsequent structured reads.
    pub(crate) fn file(&self) -> &File {
        &self.file
    }

    /// Returns the retained filesystem identity derived from [`Self::file`].
    pub(crate) fn identity(&self) -> &Handle {
        &self.identity
    }

    /// Reads text from the retained file rather than reopening its path.
    pub(crate) fn read_to_string(&self) -> io::Result<String> {
        let mut file = &self.file;
        let mut source = String::new();
        file.read_to_string(&mut source)?;
        Ok(source)
    }
}

/// Opens one repository input through canonical containment and identity
/// checks.
///
/// `repository_root` must already be canonical. The configured path may pass
/// through a symbolic link whose target remains inside that root; callers for
/// which any redirection is invalid must additionally compare [`OpenedRepositoryFile::path`]
/// with the direct path formed from `repository_root` and `configured`.
///
/// These path operations are not one atomic filesystem transaction. This
/// boundary detects ordinary replacement observed by its lookups, but assumes
/// that no hostile process deliberately performs an ABA race. Preventing that
/// requires platform-specific capability-relative opening.
pub(crate) fn open(
    repository_root: &Path,
    configured: &Path,
) -> Result<OpenedRepositoryFile, OpenRepositoryFileError> {
    let path = repository_root.join(configured);
    let resolved = path
        .canonicalize()
        .map_err(|source| OpenRepositoryFileError::Path { path: path.clone(), source })?;
    if !resolved.starts_with(repository_root) {
        return Err(OpenRepositoryFileError::OutsideRepository {
            path,
            resolved,
            repository_root: repository_root.to_path_buf(),
        });
    }

    // Open the already-resolved in-tree spelling. If the configured path is
    // replaced after the first lookup, that replacement therefore cannot
    // redirect this open; the post-open lookup below instead reports it.
    let file = File::open(&resolved)
        .map_err(|source| OpenRepositoryFileError::Path { path: resolved.clone(), source })?;
    let metadata = file
        .metadata()
        .map_err(|source| OpenRepositoryFileError::Path { path: resolved.clone(), source })?;
    if !metadata.is_file() {
        return Err(OpenRepositoryFileError::NotFile { path: resolved });
    }
    let identity_file = file
        .try_clone()
        .map_err(|source| OpenRepositoryFileError::Identity { path: resolved.clone(), source })?;
    let identity = Handle::from_file(identity_file)
        .map_err(|source| OpenRepositoryFileError::Identity { path: resolved.clone(), source })?;

    let rechecked = path
        .canonicalize()
        .map_err(|source| OpenRepositoryFileError::Path { path: path.clone(), source })?;
    if !rechecked.starts_with(repository_root) {
        return Err(OpenRepositoryFileError::OutsideRepository {
            path,
            resolved: rechecked,
            repository_root: repository_root.to_path_buf(),
        });
    }
    let current_identity = Handle::from_path(&rechecked)
        .map_err(|source| OpenRepositoryFileError::Identity { path: rechecked.clone(), source })?;
    if rechecked != resolved || current_identity != identity {
        return Err(OpenRepositoryFileError::ChangedDuringOpen {
            path,
            first: resolved,
            second: rechecked,
        });
    }

    Ok(OpenedRepositoryFile { path: rechecked, file, identity })
}

/// A failure to open and retain one repository file safely.
#[derive(Debug, Error)]
pub(crate) enum OpenRepositoryFileError {
    /// A configured input could not be resolved, opened, or inspected.
    #[error("failed to resolve repository input `{path}`: {source}")]
    Path {
        path: PathBuf,
        #[source]
        source: io::Error,
    },
    /// A configured input's stable filesystem identity could not be read.
    #[error("failed to inspect filesystem identity of repository input `{path}`: {source}")]
    Identity {
        path: PathBuf,
        #[source]
        source: io::Error,
    },
    /// A path no longer named the file which was opened and retained.
    #[error(
        "repository input `{path}` changed while it was opened: first resolved to `{first}`, then to `{second}`"
    )]
    ChangedDuringOpen { path: PathBuf, first: PathBuf, second: PathBuf },
    /// A configured input resolved outside the checkout.
    #[error(
        "repository input `{path}` resolves to `{resolved}`, outside repository `{repository_root}`"
    )]
    OutsideRepository { path: PathBuf, resolved: PathBuf, repository_root: PathBuf },
    /// A configured input resolved to a directory or other non-file object.
    #[error("repository input `{path}` is not a regular file")]
    NotFile { path: PathBuf },
}

#[cfg(test)]
mod tests {
    use std::{
        fs, process,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::{open, OpenRepositoryFileError};

    static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    fn temporary_directory(label: &str) -> std::path::PathBuf {
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        std::env::temp_dir()
            .join(format!("zerocopy-repository-file-{label}-{}-{unique}", process::id()))
    }

    #[cfg(unix)]
    #[test]
    fn rejects_an_input_symlink_which_escapes_the_repository() {
        use std::os::unix::fs::symlink;

        let temporary = temporary_directory("outside");
        let repository = temporary.join("repository");
        let outside = temporary.join("outside.txt");
        fs::create_dir_all(repository.join("ci")).unwrap();
        fs::write(&outside, "external\n").unwrap();
        symlink(&outside, repository.join("ci/input.txt")).unwrap();
        let repository = repository.canonicalize().unwrap();

        let error = open(&repository, std::path::Path::new("ci/input.txt")).unwrap_err();
        assert!(matches!(error, OpenRepositoryFileError::OutsideRepository { .. }));

        fs::remove_dir_all(temporary).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn path_replacement_cannot_change_bytes_read_from_an_open_input() {
        use std::os::unix::fs::symlink;

        let temporary = temporary_directory("retained");
        let repository = temporary.join("repository");
        let configured = repository.join("ci/input.txt");
        let retained = repository.join("ci/retained.txt");
        let outside = temporary.join("outside.txt");
        fs::create_dir_all(configured.parent().unwrap()).unwrap();
        fs::write(&configured, "validated bytes\n").unwrap();
        fs::write(&outside, "replacement bytes\n").unwrap();
        let repository = repository.canonicalize().unwrap();

        let input = open(&repository, std::path::Path::new("ci/input.txt")).unwrap();
        fs::rename(&configured, &retained).unwrap();
        symlink(&outside, &configured).unwrap();

        assert_eq!(input.read_to_string().unwrap(), "validated bytes\n");

        drop(input);
        fs::remove_dir_all(temporary).unwrap();
    }
}
