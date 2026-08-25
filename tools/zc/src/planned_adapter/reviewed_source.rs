// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Complete-source review boundary for mutable repository-owned CI code.

use std::{
    collections::HashMap,
    fs,
    path::{Path, PathBuf},
};

use same_file::Handle;

use super::{PlannedAdapterAuditError, PlannedAdapterViolations, ViolationSink};
use crate::repository_file::{self, OpenRepositoryFileError, OpenedRepositoryFile};

/// One live CI source and its independent, compiled review copy.
#[derive(Clone, Copy)]
pub(super) struct ReviewedSource {
    /// Repository path which GitHub Actions or Docker executes.
    pub live_path: &'static str,
    /// Independent checked-in copy reviewed with the Rust adapter.
    pub snapshot_path: &'static str,
    /// Snapshot contents captured when this crate was compiled.
    pub expected: &'static str,
}

/// Checks complete contents and distinct file identity for reviewed sources.
///
/// A local `uses` path, Dockerfile, or ignore file remains mutable code from
/// the checkout. Comparing its complete normalized text avoids an incomplete
/// blacklist of dangerous commands. Reading the snapshot at runtime as well
/// as compiling it into the binary prevents either path from changing after
/// compilation without detection.
///
/// The open identity handles stay in `identities` for the whole pass. That
/// makes the comparison stable on platforms which may reuse a file identifier
/// after its last handle closes. It also rejects hard links, which path
/// canonicalization cannot distinguish, while permitting distinct files with
/// identical reviewed contents.
pub(super) fn audit_reviewed_sources(
    repository_root: &Path,
    sources: &[ReviewedSource],
) -> Result<(), PlannedAdapterAuditError> {
    let mut identities = HashMap::new();
    for reviewed in sources {
        for path in [reviewed.snapshot_path, reviewed.live_path] {
            let (resolved, source, handle) = read_reviewed_source(repository_root, path)?;
            if let Some(first_path) = identities.insert(handle, resolved.clone()) {
                return Err(PlannedAdapterAuditError::DuplicateReviewedSource {
                    first_path,
                    second_path: resolved,
                });
            }
            audit_exact_source(&source, path, reviewed.expected, reviewed.snapshot_path)?;
        }
    }
    Ok(())
}

/// Reads one fixed reviewed path without following checked-in symbolic links.
pub(super) fn read_reviewed_source(
    repository_root: &Path,
    relative_path: &str,
) -> Result<(PathBuf, String, Handle), PlannedAdapterAuditError> {
    let path = inspect_reviewed_source_path(repository_root, relative_path)?;
    let opened = open_reviewed_source(repository_root, relative_path, &path)?;
    let source = opened.read_to_string().map_err(|source| {
        PlannedAdapterAuditError::ReadReviewedSource { path: opened.path().to_path_buf(), source }
    })?;
    let resolved = opened.path().to_path_buf();
    Ok((resolved, source, opened.into_identity()))
}

/// Rejects every symbolic-link component visible before a reviewed open.
fn inspect_reviewed_source_path(
    repository_root: &Path,
    relative_path: &str,
) -> Result<PathBuf, PlannedAdapterAuditError> {
    let path = repository_root.join(relative_path);
    let mut component_path = repository_root.to_path_buf();
    for component in Path::new(relative_path) {
        component_path.push(component);
        let metadata = fs::symlink_metadata(&component_path).map_err(|source| {
            PlannedAdapterAuditError::InspectReviewedSource { path: component_path.clone(), source }
        })?;
        if metadata.file_type().is_symlink() {
            return Err(PlannedAdapterAuditError::ReviewedSourceSymlink { path: component_path });
        }
    }
    Ok(path)
}

/// Opens exactly the direct path inspected by [`inspect_reviewed_source_path`].
fn open_reviewed_source(
    repository_root: &Path,
    relative_path: &str,
    path: &Path,
) -> Result<OpenedRepositoryFile, PlannedAdapterAuditError> {
    let opened =
        repository_file::open(repository_root, Path::new(relative_path)).map_err(|error| {
            match error {
                OpenRepositoryFileError::Path { path, source } => {
                    PlannedAdapterAuditError::InspectReviewedSource { path, source }
                }
                OpenRepositoryFileError::Identity { path, source } => {
                    PlannedAdapterAuditError::ReviewedSourceIdentity { path, source }
                }
                OpenRepositoryFileError::ChangedDuringOpen { path, first, second } => {
                    PlannedAdapterAuditError::ReviewedSourceChangedDuringOpen {
                        path,
                        first,
                        second,
                    }
                }
                OpenRepositoryFileError::OutsideRepository { path, resolved, repository_root } => {
                    PlannedAdapterAuditError::ReviewedSourceOutsideRepository {
                        path,
                        resolved,
                        repository_root,
                    }
                }
                OpenRepositoryFileError::NotFile { path } => {
                    PlannedAdapterAuditError::ReviewedSourceNotFile { path }
                }
            }
        })?;
    // The component inspection preserves a precise diagnostic for a static
    // symlink. Requiring exact path equality here closes the later replacement
    // window, including a redirection whose target remains in the repository.
    if opened.path() != path {
        return Err(PlannedAdapterAuditError::ReviewedSourceSymlink { path: path.to_path_buf() });
    }
    Ok(opened)
}

/// Requires one source to equal the snapshot compiled into the audit.
pub(super) fn audit_exact_source(
    source: &str,
    path: &str,
    expected: &str,
    snapshot_path: &str,
) -> Result<(), PlannedAdapterViolations> {
    if source == expected {
        return Ok(());
    }

    let mismatch = source
        .lines()
        .zip(expected.lines())
        .position(|(actual, expected)| actual != expected)
        .map(|index| index + 1)
        .unwrap_or_else(|| source.lines().count().min(expected.lines().count()) + 1);
    let mut errors = ViolationSink::default();
    errors.push(
        format!("{path}:{mismatch}"),
        format!(
            "reviewed CI source must match the complete compiled source snapshot from `{snapshot_path}`"
        ),
    );
    Err(errors.finish())
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::{
        audit_reviewed_sources, inspect_reviewed_source_path, open_reviewed_source, ReviewedSource,
    };

    const EXPECTED: &str = "reviewed source\n";
    const SOURCES: &[ReviewedSource] = &[
        ReviewedSource {
            live_path: "live/matrix-action.yml",
            snapshot_path: "snapshots/matrix-action.yml",
            expected: EXPECTED,
        },
        ReviewedSource {
            live_path: "live/image-action.yml",
            snapshot_path: "snapshots/image-action.yml",
            expected: EXPECTED,
        },
    ];

    #[test]
    fn identity_set_spans_independent_reviewed_source_groups() {
        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary = std::env::temp_dir()
            .join(format!("zerocopy-reviewed-source-{}-{unique}", std::process::id()));
        let root = temporary.join("repository");
        fs::create_dir_all(root.join("live")).unwrap();
        fs::create_dir_all(root.join("snapshots")).unwrap();
        let root = root.canonicalize().unwrap();

        for source in SOURCES {
            fs::write(root.join(source.live_path), EXPECTED).unwrap();
            fs::write(root.join(source.snapshot_path), EXPECTED).unwrap();
        }
        audit_reviewed_sources(&root, SOURCES).unwrap();

        // Model an alias between paths contributed by two different audit
        // modules. Checking each module separately would miss this; the one
        // aggregated identity set must reject it.
        fs::remove_file(root.join(SOURCES[1].live_path)).unwrap();
        fs::hard_link(root.join(SOURCES[0].live_path), root.join(SOURCES[1].live_path)).unwrap();
        let error = audit_reviewed_sources(&root, SOURCES).unwrap_err().to_string();
        assert!(error.contains("resolve to the same file"), "{error}");
        assert!(error.contains(SOURCES[0].live_path), "{error}");
        assert!(error.contains(SOURCES[1].live_path), "{error}");

        fs::remove_dir_all(temporary).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn replacement_after_symlink_inspection_cannot_redirect_the_open() {
        use std::os::unix::fs::symlink;

        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary = std::env::temp_dir()
            .join(format!("zerocopy-reviewed-source-replacement-{}-{unique}", std::process::id()));
        let root = temporary.join("repository");
        let candidate = root.join("live/source.yml");
        let retained = root.join("live/retained.yml");
        let outside = temporary.join("outside.yml");
        fs::create_dir_all(candidate.parent().unwrap()).unwrap();
        fs::write(&candidate, EXPECTED).unwrap();
        fs::write(&outside, EXPECTED).unwrap();
        let root = root.canonicalize().unwrap();

        let path = inspect_reviewed_source_path(&root, "live/source.yml").unwrap();
        fs::rename(&candidate, &retained).unwrap();
        symlink(&outside, &candidate).unwrap();

        let error = open_reviewed_source(&root, "live/source.yml", &path).unwrap_err();
        assert!(matches!(
            error,
            super::PlannedAdapterAuditError::ReviewedSourceOutsideRepository { .. }
        ));

        fs::remove_dir_all(temporary).unwrap();
    }
}
