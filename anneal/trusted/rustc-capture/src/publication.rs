// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Publish the complete capture pair with one directory rename.
//!
//! The destination must not exist, even as an empty directory. Reserving a new
//! empty directory establishes which path this run may replace; compiler
//! outputs and artifact writes remain in private sibling staging until
//! publication. Failure cleanup removes only an empty reservation, never
//! caller contents. A filesystem error can leave that empty reservation for
//! the caller to inspect.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

/// Own a new, empty destination reservation and private sibling staging area.
/// No capture artifacts appear at the destination until both are ready. The
/// compiler's metadata and object files never enter the published directory.
pub(crate) struct Publication {
    destination: PathBuf,
    staging: tempfile::TempDir,
    published: bool,
}

impl Publication {
    pub(crate) fn new(destination: &Path) -> io::Result<Self> {
        let name = destination.file_name().ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "output directory needs a final name",
            )
        })?;
        let parent = destination
            .parent()
            .filter(|path| !path.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."));
        fs::create_dir_all(parent)?;
        let parent = parent.canonicalize()?;
        let destination = parent.join(name);
        // The success receipt serializes this resolved path after publication.
        // A UTF-8 argument can still have a non-UTF-8 canonical parent through
        // the cwd or a symlink. Check the whole destination before reserving
        // its name or creating staging, so receipt encoding cannot fail after
        // rename.
        if destination.to_str().is_none() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "output destination must be UTF-8",
            ));
        }
        let mut staging = tempfile::Builder::new();
        staging.prefix(".anneal-capture-");
        // Temporary directories otherwise inherit the default directory mode.
        // Restrict traversal at creation so other local users cannot inspect
        // unpublished compiler outputs or capture artifacts through this path.
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            staging.permissions(fs::Permissions::from_mode(0o700));
        }
        let staging = staging.tempdir_in(parent)?;
        fs::create_dir(staging.path().join("compiler"))?;
        fs::create_dir(staging.path().join("capture"))?;
        // Atomic creation refuses any pre-existing file, directory, or symlink,
        // including an empty directory. This reservation belongs to this run;
        // publication may replace it but must never remove caller contents.
        fs::create_dir(&destination).map_err(|error| {
            io::Error::new(
                error.kind(),
                format!("capture requires a new output directory: {error}"),
            )
        })?;
        Ok(Self {
            destination,
            staging,
            published: false,
        })
    }

    pub(crate) fn compiler_dir(&self) -> PathBuf {
        self.staging.path().join("compiler")
    }

    fn artifact_dir(&self) -> PathBuf {
        self.staging.path().join("capture")
    }

    pub(crate) fn publish(self, json: &[u8], lean: &[u8]) -> io::Result<PathBuf> {
        self.publish_with_shards(json, lean, None)
    }

    pub(crate) fn publish_with_shards(
        mut self,
        json: &[u8],
        lean: &[u8],
        sharded: Option<ShardedPublication<'_>>,
    ) -> io::Result<PathBuf> {
        let art = self.artifact_dir();
        fs::write(art.join("capture.json"), json)?;
        fs::write(art.join("Captured.lean"), lean)?;
        if let Some(sharded) = sharded {
            fs::write(art.join("capture_shards.json"), sharded.shards_json)?;
            let captured_subdir = art.join("Captured");
            fs::create_dir(&captured_subdir)?;
            for (shard_idx, shard_lean) in sharded.shard_sources {
                fs::write(
                    captured_subdir.join(format!("Shard_{shard_idx:03}.lean")),
                    shard_lean.as_bytes(),
                )?;
            }
        }
        // Both paths are on one filesystem. On the supported Unix hosts,
        // rename replaces our empty reservation in one operation; a nonempty
        // destination makes it fail. Never remove a destination to retry.
        fs::rename(art, &self.destination)?;
        self.published = true;
        Ok(self.destination.clone())
    }
}

pub(crate) struct ShardedPublication<'a> {
    pub(crate) shards_json: &'a [u8],
    pub(crate) shard_sources: &'a [(usize, String)],
}

impl Drop for Publication {
    fn drop(&mut self) {
        if !self.published {
            // Remove only an empty reservation. If another writer added data,
            // preserve it even when that prevents cleanup after a failed run.
            // Drop cannot report cleanup failures. Preserving foreign data
            // takes priority over making a failed output path reusable.
            let _ = fs::remove_dir(&self.destination);
        }
        // TempDir removes only our private staging tree, including any compiler
        // outputs or incomplete artifact pair left by a failure.
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn publication_exposes_both_artifacts_and_keeps_compiler_outputs_private() {
        let root = tempfile::tempdir().unwrap();
        let destination = root.path().join("output");
        let publication = Publication::new(&destination).unwrap();
        let staging = publication.staging.path().to_path_buf();
        fs::write(publication.compiler_dir().join("session.o"), b"object").unwrap();
        assert_eq!(fs::read_dir(&destination).unwrap().count(), 0);
        assert_eq!(publication.publish(b"json", b"lean").unwrap(), destination);
        assert_eq!(fs::read(destination.join("capture.json")).unwrap(), b"json");
        assert_eq!(
            fs::read(destination.join("Captured.lean")).unwrap(),
            b"lean"
        );
        assert_eq!(fs::read_dir(&destination).unwrap().count(), 2);
        assert!(!staging.exists());
    }

    #[test]
    fn incomplete_pair_is_removed_with_the_reservation() {
        let root = tempfile::tempdir().unwrap();
        let destination = root.path().join("output");
        let publication = Publication::new(&destination).unwrap();
        let staging = publication.staging.path().to_path_buf();
        fs::create_dir(publication.artifact_dir().join("Captured.lean")).unwrap();
        assert!(publication.publish(b"json", b"lean").is_err());
        assert!(!destination.exists());
        assert!(!staging.exists());
    }

    #[test]
    fn failed_publication_preserves_data_added_to_the_reservation() {
        let root = tempfile::tempdir().unwrap();
        let destination = root.path().join("output");
        let publication = Publication::new(&destination).unwrap();
        let staging = publication.staging.path().to_path_buf();
        fs::write(destination.join("caller-data"), b"preserve").unwrap();
        assert!(publication.publish(b"json", b"lean").is_err());
        assert_eq!(
            fs::read(destination.join("caller-data")).unwrap(),
            b"preserve"
        );
        assert!(!destination.join("capture.json").exists());
        assert!(!destination.join("Captured.lean").exists());
        assert!(!staging.exists());
    }

    #[cfg(unix)]
    #[test]
    fn staging_excludes_other_users() {
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let publication = Publication::new(&root.path().join("output")).unwrap();
        let mode = fs::metadata(publication.staging.path())
            .unwrap()
            .permissions()
            .mode();
        assert_eq!(
            mode & 0o077,
            0,
            "staging mode {mode:o} exposes another user"
        );
    }
}
