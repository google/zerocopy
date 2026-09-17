// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{
    fs::{self, File, OpenOptions},
    io::{Read as _, Result as IoResult, Seek as _, SeekFrom, Write as _},
    path::{Path, PathBuf},
};

const STAGING_MARKER: u8 = b'@';
const STAGING_WORK_NAME: &str = "@@stage.tmp";
const STAGING_LOCK_NAME: &str = "@@stage.lck";
const STAGING_PROTOCOL_CLAIM: &[u8] = b"exocrate staging protocol 1\n";

/// Returns whether `name` belongs to the namespace reserved for staging
/// directories.
///
/// Staging names contain `@`, and no managed target may do so. Reserving the
/// marker wherever it appears, including its two Unicode compatibility forms
/// (U+FE6B and U+FF20), avoids relying on platform-specific case folding,
/// Unicode normalization, ignored formatting characters, or
/// trailing-dot-and-space normalization when deciding whether a target can
/// alias a staging directory.
pub(crate) const fn is_reserved_staging_name(name: &str) -> bool {
    contains_staging_marker(name.as_bytes())
}

/// Returns whether any part of `path` belongs to the staging namespace.
pub(crate) fn path_contains_reserved_staging_marker(path: &Path) -> bool {
    contains_staging_marker(path.as_os_str().as_encoded_bytes())
}

const fn contains_staging_marker(bytes: &[u8]) -> bool {
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == STAGING_MARKER {
            return true;
        }
        if bytes.len() - i >= 3
            && bytes[i] == 0xef
            && ((bytes[i + 1] == 0xb9 && bytes[i + 2] == 0xab)
                || (bytes[i + 1] == 0xbc && bytes[i + 2] == 0xa0))
        {
            return true;
        }
        i += 1;
    }
    false
}

/// A directory managed by this library.
///
/// A `ManagedDir` has the following properties:
/// - The directory itself is guaranteed to be atomic. That is, if a directory
///   at the path exists, then it has already been fully populated. This means
///   that no locking is required to check whether the directory exists.
/// - Populating and installing the directory requires a lock. In other words,
///   writers are required to actively synchronize with one another. This
///   simplifies the writer implementation by avoiding the necessity for
///   complex wait-free synchronization logic.
/// - The name of the lock file shares the same prefix with the name of the
///   guarded directory. As long as two directories have different names, their
///   lock files can never conflict.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) struct ManagedDir<'a> {
    path: &'a Path,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) struct ManagedDirName<'a> {
    // INVARIANT: `path.file_name()` exists and contains no reserved staging
    // marker.
    path: &'a Path,
}

impl<'a> ManagedDirName<'a> {
    pub(crate) fn new(path: &'a Path) -> Self {
        let file_name = path.file_name().expect("ManagedDirName path must have a filename");
        assert!(
            !contains_staging_marker(file_name.as_encoded_bytes()),
            "ManagedDirName filename must not contain a reserved staging marker",
        );
        Self { path }
    }

    /// Checks if the directory exists.
    pub(crate) fn check_exists(self) -> IoResult<ManagedDir<'a>> {
        if self.path.is_dir() {
            Ok(ManagedDir { path: self.path })
        } else if self.path.try_exists()? {
            Err(std::io::Error::new(
                std::io::ErrorKind::AlreadyExists,
                "Path exists but is not a directory",
            ))
        } else {
            Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "Managed directory does not exist",
            ))
        }
    }

    /// Checks if the directory exists, creating it if not.
    ///
    /// `populate` is always given a freshly-created staging directory. A later
    /// installation in the same parent removes a staging directory abandoned
    /// by an earlier installation before atomically creating the empty
    /// directory passed to `populate`.
    ///
    /// # Concurrency
    ///
    /// `check_exists_or_create` is **not** concurrency-safe if multiple
    /// concurrent calls are made *from the same process*.
    /// Missing-target installations in separate processes which share a parent
    /// directory serialize while they use that parent's staging path.
    pub(crate) fn check_exists_or_create(
        self,
        populate: impl FnOnce(&Path) -> IoResult<()>,
    ) -> IoResult<ManagedDir<'a>> {
        if let Ok(dir) = self.check_exists() {
            return Ok(dir);
        }

        let parent = self
            .path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."));

        // NOTE: `create_dir_all` is safe to call concurrently with other
        // processes attempting to create the same directory:
        //
        //  Notable exception [to the error conditions] is made for situations
        //  where any of the directories specified in the path could not be
        //  created as it was being created concurrently. Such cases are
        //  considered to be successful. That is, calling create_dir_all
        //  concurrently from multiple threads or processes is guaranteed not
        //  to fail due to a race condition with itself.
        fs::create_dir_all(parent)?;

        let lock_file_path = self.lock_path();
        let lock_file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&lock_file_path)?;

        <_ as fs2::FileExt>::lock_exclusive(&lock_file)?;

        struct LockGuard(File);

        impl Drop for LockGuard {
            fn drop(&mut self) {
                let _ = <_ as fs2::FileExt>::unlock(&self.0);
            }
        }

        let _lock_guard = LockGuard(lock_file);

        // Handle the case where another process populated the directory while
        // we were waiting for the target lock. Do this before creating staging
        // infrastructure so an already-complete target is not hidden by an
        // unrelated staging-path error.
        if let Ok(dir) = self.check_exists() {
            return Ok(dir);
        }

        let (staging_path, staging_lock_path) = self.staging_paths();

        // The target lock synchronizes installations of this target. The
        // persistent parent-wide lock additionally ensures that every
        // cooperating process which uses this staging protocol is excluded
        // before the shared path is inspected, removed, populated, or
        // promoted.
        let staging_lock = match OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(&staging_lock_path)
        {
            Ok(lock) => lock,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
                let metadata = fs::symlink_metadata(&staging_lock_path)?;
                if !metadata.file_type().is_file() {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "Exocrate staging lock is not a regular file",
                    ));
                }
                OpenOptions::new()
                    .read(true)
                    .write(true)
                    .truncate(false)
                    .open(&staging_lock_path)?
            }
            Err(error) => return Err(error),
        };
        <_ as fs2::FileExt>::lock_exclusive(&staging_lock)?;
        let mut staging_lock_guard = LockGuard(staging_lock);

        // The lock file also claims this parent-wide staging namespace. Before
        // the first claim, an older Exocrate version could legitimately have
        // installed a target named `STAGING_WORK_NAME`. Refuse to delete such
        // a pre-existing occupant. Once claimed, cooperating versions reserve
        // both staging names and may reclaim the work path after process
        // death.
        claim_staging_protocol(&mut staging_lock_guard.0, &staging_path)?;

        // Handle the case where another process populated the directory while
        // we were waiting for either lock.
        if let Ok(dir) = self.check_exists() {
            return Ok(dir);
        }

        remove_staging_work(&staging_path)?;

        // Unlike `create_dir_all`, `create_dir` proves that this attempt starts
        // with a new, empty directory rather than reusing residual contents.
        fs::create_dir(&staging_path)?;

        struct StagingGuard(Option<PathBuf>);

        impl Drop for StagingGuard {
            fn drop(&mut self) {
                if let Some(path) = &self.0 {
                    let _ = remove_staging_work(path);
                }
            }
        }

        let mut staging_guard = StagingGuard(Some(staging_path));
        populate(staging_guard.0.as_deref().expect("staging cleanup must be armed"))?;

        // Disarm path-based cleanup before the rename. If the process exits in
        // this small window, the next lock holder reclaims the work path. After
        // a successful rename, no cleanup guard remains which could delete a
        // later occupant of the now-vacant source path.
        let staging_path = staging_guard.0.take().expect("staging cleanup must be armed");
        if let Err(e) = fs::rename(&staging_path, self.path) {
            let _ = remove_staging_work(&staging_path);
            return Err(std::io::Error::new(
                e.kind(),
                format!(
                    "Failed to rename staging directory to target path (this indicates a {}): {}",
                    if cfg!(windows) {
                        "manual modification, concurrency bug, or open file handle"
                    } else {
                        "manual modification or concurrency bug"
                    },
                    e
                ),
            ));
        }

        Ok(ManagedDir { path: self.path })
    }

    /// Returns the parent-wide work-directory and lock-file paths.
    pub(super) fn staging_paths(&self) -> (PathBuf, PathBuf) {
        // All names are valid 8.3 filenames and contain the reserved staging
        // marker. The doubled marker also makes the work path disjoint from the
        // single-marker random namespace used by earlier Exocrate versions.
        // They are a versioned cross-process protocol and must remain stable.
        (self.path.with_file_name(STAGING_WORK_NAME), self.path.with_file_name(STAGING_LOCK_NAME))
    }

    // NOTE: It's important that `lock_path` returns a lock path whose name
    // has the directory name as a prefix. See the comment on `ManagedDir`.
    fn lock_path(&self) -> PathBuf {
        let mut file_name =
            self.path.file_name().expect("ManagedDirName path must have a filename").to_os_string();
        file_name.push(".lock");
        self.path.with_file_name(file_name)
    }
}

/// Claims the parent-wide staging namespace, or validates an earlier claim.
///
/// The caller holds `lock` exclusively. An empty lock file represents either
/// an interrupted first claim or an as-yet-unclaimed parent. In that state, a
/// work-path occupant is preserved and reported instead of deleted. Exact
/// versioned claim bytes authorize compatible Exocrate processes to reclaim
/// the shared work path; every other lock-file state fails closed.
fn claim_staging_protocol(lock: &mut File, work_path: &Path) -> IoResult<()> {
    let len = lock.metadata()?.len();
    if len == STAGING_PROTOCOL_CLAIM.len() as u64 {
        let mut claim = [0; STAGING_PROTOCOL_CLAIM.len()];
        lock.seek(SeekFrom::Start(0))?;
        lock.read_exact(&mut claim)?;
        if claim.as_slice() == STAGING_PROTOCOL_CLAIM {
            return Ok(());
        }
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "Unrecognized Exocrate staging protocol claim",
        ));
    }
    if len != 0 {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "Unrecognized Exocrate staging protocol claim",
        ));
    }

    match fs::symlink_metadata(work_path) {
        Ok(_) => {
            return Err(std::io::Error::new(
                std::io::ErrorKind::AlreadyExists,
                "Unclaimed path occupies Exocrate's reserved staging namespace",
            ));
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }

    lock.seek(SeekFrom::Start(0))?;
    lock.write_all(STAGING_PROTOCOL_CLAIM)?;
    lock.sync_data()
}

/// Makes every directory in a protocol-owned staging tree traversable and
/// every non-symlink Windows entry writable, without following symlinks.
///
/// Archive entries can legitimately have mode 000 on Unix or the read-only
/// attribute on Windows. If a process exits after extracting such an entry,
/// these permissions must not make the single shared work path permanently
/// unreclaimable. The caller holds the parent-wide lock, and Exocrate's public
/// contract excludes concurrent mutation, non-symbolic aliases, and mounts in
/// this reserved tree; those premises make the path-based metadata and
/// permission operations stable.
fn make_staging_tree_removable(path: &Path) -> IoResult<()> {
    let mut pending = vec![path.to_owned()];
    while let Some(path) = pending.pop() {
        let metadata = match fs::symlink_metadata(&path) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(error) => return Err(error),
        };
        if metadata.file_type().is_symlink() {
            continue;
        }

        #[cfg(unix)]
        if metadata.is_dir() {
            use std::os::unix::fs::PermissionsExt as _;

            let mut permissions = metadata.permissions();
            permissions.set_mode(permissions.mode() | 0o700);
            fs::set_permissions(&path, permissions)?;
        }

        #[cfg(windows)]
        if metadata.permissions().readonly() {
            let mut permissions = metadata.permissions();
            permissions.set_readonly(false);
            fs::set_permissions(&path, permissions)?;
        }

        if metadata.is_dir() {
            for entry in fs::read_dir(&path)? {
                pending.push(entry?.path());
            }
        }
    }
    Ok(())
}

/// Removes an earlier attempt's staging path without following symlinks.
fn remove_staging_work(path: &Path) -> IoResult<()> {
    match fs::remove_dir_all(path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(_) => {
            make_staging_tree_removable(path)?;
            let metadata = match fs::symlink_metadata(path) {
                Ok(metadata) => metadata,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
                Err(error) => return Err(error),
            };
            let result =
                if metadata.is_dir() { fs::remove_dir_all(path) } else { fs::remove_file(path) };
            match result {
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
                Ok(()) => Ok(()),
                Err(error) => Err(error),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, path::Path};

    use super::*;

    fn has_old_random_staging_shape(name: &str) -> bool {
        let bytes = name.as_bytes();
        bytes.len() == 12
            && bytes[0] == b'@'
            && bytes[1..8].iter().all(u8::is_ascii_alphanumeric)
            && &bytes[8..] == b".tmp"
    }

    fn parent_entries_except_metadata(target: &Path) -> Vec<PathBuf> {
        let managed = ManagedDirName::new(target);
        let target_lock = managed.lock_path();
        let (_, staging_lock) = managed.staging_paths();
        fs::read_dir(target.parent().unwrap())
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path != &target_lock && path != &staging_lock)
            .collect()
    }

    #[test]
    fn test_staging_name_namespace() {
        let managed = ManagedDirName::new(Path::new("install_target"));
        let (staging, staging_lock) = managed.staging_paths();
        let staging = staging.file_name().unwrap().to_str().unwrap();
        let staging_lock = staging_lock.file_name().unwrap().to_str().unwrap();

        // These names are a persistent cross-process protocol. Changing them
        // can strand staging data left by another Exocrate process.
        assert_eq!(staging, "@@stage.tmp");
        assert_eq!(staging_lock, "@@stage.lck");
        assert_eq!(STAGING_PROTOCOL_CLAIM, b"exocrate staging protocol 1\n");
        assert!(is_reserved_staging_name(staging));
        assert!(is_reserved_staging_name(staging_lock));
        assert!(staging.len() <= 12);
        assert!(staging_lock.len() <= 12);
        assert!(staging.split_once('.').unwrap().0.len() <= 8);
        assert!(staging_lock.split_once('.').unwrap().0.len() <= 8);
        assert!(!has_old_random_staging_shape(staging));
        assert!(staging_lock.ends_with(".lck"));

        for name in [
            "@Ab12CdE.tmp",
            "@aB12cDe.TMP",
            "@Ab12CdE.tmp. ",
            "@ABCDEF\u{212a}.tmp",
            " @Ab12CdE.tmp",
            "\u{200c}@Ab12CdE.tmp",
            "\u{fe6b}Ab12CdE.tmp",
            "\u{ff20}Ab12CdE.tmp",
            "other\u{fe6b}reserved_name",
            "other\u{ff20}reserved_name",
            "other@reserved_name",
        ] {
            assert!(is_reserved_staging_name(name), "{name:?}");
        }

        for name in ["", "install_target", "_Ab12CdE.tmp", "v1_tmp", "caf\u{e9}"] {
            assert!(!is_reserved_staging_name(name), "{name:?}");
        }

        assert!(has_old_random_staging_shape("@Ab12CdE.tmp"));
        for name in [
            "@Ab12Cd.tmp",
            "@Ab12CdEf.tmp",
            "@Ab12C-E.tmp",
            "@Ab12CdE.TMP",
            "@Ab12CdE.tmp. ",
            "@ABCDEF\u{212a}.tmp",
            "\u{200c}@Ab12CdE.tmp",
        ] {
            assert!(!has_old_random_staging_shape(name), "{name:?}");
        }
    }

    #[test]
    fn test_reserved_staging_names_cannot_be_managed_targets() {
        for name in [
            STAGING_WORK_NAME,
            STAGING_LOCK_NAME,
            "@Ab12CdE.tmp",
            "@aB12cDe.TMP",
            "@Ab12CdE.tmp. ",
            "@ABCDEF\u{212a}.tmp",
            " @Ab12CdE.tmp",
            "\u{200c}@Ab12CdE.tmp",
            "\u{fe6b}Ab12CdE.tmp",
            "\u{ff20}Ab12CdE.tmp",
            "other\u{fe6b}reserved_name",
            "other\u{ff20}reserved_name",
            "other@reserved_name",
        ] {
            let result = std::panic::catch_unwind(|| ManagedDirName::new(Path::new(name)));
            assert!(result.is_err(), "{name:?}");
        }
    }

    #[test]
    fn test_check_exists_or_create_success() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);

        let dir = managed
            .check_exists_or_create(|staging| {
                fs::write(staging.join("data.txt"), "success content").unwrap();
                Ok(())
            })
            .unwrap();

        assert_eq!(dir.path, dst.as_path());
        assert!(dst.is_dir());
        assert_eq!(fs::read_to_string(dst.join("data.txt")).unwrap(), "success content");
        let (_, staging_lock) = managed.staging_paths();
        assert_eq!(fs::read(staging_lock).unwrap(), STAGING_PROTOCOL_CLAIM);
    }

    #[cfg(unix)]
    #[test]
    fn test_check_exists_or_create_uses_normal_directory_permissions() {
        use std::os::unix::fs::PermissionsExt as _;

        let temp = tempfile::tempdir().unwrap();
        let reference = temp.path().join("reference");
        fs::create_dir(&reference).unwrap();
        let expected = fs::metadata(&reference).unwrap().permissions().mode() & 0o777;

        let dst = temp.path().join("install_target");
        ManagedDirName::new(&dst).check_exists_or_create(|_| Ok(())).unwrap();
        let actual = fs::metadata(&dst).unwrap().permissions().mode() & 0o777;

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_generated_staging_name_cannot_be_managed_target() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);
        let mut observed_staging = false;

        managed
            .check_exists_or_create(|staging| {
                observed_staging = true;
                let name = staging.file_name().unwrap().to_str().unwrap();
                assert_eq!(name, STAGING_WORK_NAME);
                assert!(is_reserved_staging_name(name));

                // Before this namespace was reserved, another configuration
                // could treat this live staging path as its completed target.
                let result = std::panic::catch_unwind(|| ManagedDirName::new(staging));
                assert!(result.is_err());

                fs::write(staging.join("data.txt"), "success content")?;
                Ok(())
            })
            .unwrap();

        assert!(observed_staging);
        assert_eq!(fs::read_to_string(dst.join("data.txt")).unwrap(), "success content");
    }

    #[test]
    fn test_check_exists_or_create_already_exists() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);

        managed
            .check_exists_or_create(|staging| {
                fs::write(staging.join("v1.txt"), "v1").unwrap();
                Ok(())
            })
            .unwrap();

        let dir = managed
            .check_exists_or_create(|_| {
                panic!("should not be called on already existing directory");
            })
            .unwrap();

        assert_eq!(dir.path, dst.as_path());
        assert!(dst.is_dir());
        assert_eq!(fs::read_to_string(dst.join("v1.txt")).unwrap(), "v1");
        assert!(!dst.join("v2.txt").exists());
    }

    #[test]
    fn test_check_exists_or_create_failure_cleanup() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);

        let res = managed.check_exists_or_create(|staging| {
            fs::write(staging.join("partial.txt"), "partial").unwrap();
            Err(std::io::Error::other("simulated error"))
        });
        assert!(res.is_err());

        assert!(!dst.exists());
        let (staging, _) = managed.staging_paths();
        assert!(!staging.exists());
        assert!(parent_entries_except_metadata(&dst).is_empty());
    }

    #[test]
    fn test_unclaimed_staging_occupant_is_preserved() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);
        let (staging, staging_lock) = managed.staging_paths();
        fs::create_dir(&staging).unwrap();
        fs::write(staging.join("old-install.txt"), "preserve").unwrap();

        let mut populated = false;
        let error = managed
            .check_exists_or_create(|_| {
                populated = true;
                Ok(())
            })
            .unwrap_err();

        assert_eq!(error.kind(), std::io::ErrorKind::AlreadyExists);
        assert!(!populated);
        assert_eq!(fs::read_to_string(staging.join("old-install.txt")).unwrap(), "preserve");
        assert_eq!(fs::metadata(staging_lock).unwrap().len(), 0);
        assert!(!dst.exists());
    }

    #[cfg(unix)]
    #[test]
    fn test_unclaimed_dangling_staging_symlink_is_preserved() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);
        let (staging, staging_lock) = managed.staging_paths();
        let missing_referent = temp.path().join("missing");
        symlink(&missing_referent, &staging).unwrap();

        let error = managed.check_exists_or_create(|_| Ok(())).unwrap_err();

        assert_eq!(error.kind(), std::io::ErrorKind::AlreadyExists);
        assert!(fs::symlink_metadata(staging).unwrap().file_type().is_symlink());
        assert_eq!(fs::metadata(staging_lock).unwrap().len(), 0);
        assert!(!dst.exists());
    }

    #[test]
    fn test_non_regular_staging_lock_is_preserved() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);
        let (staging, staging_lock) = managed.staging_paths();
        fs::create_dir(&staging_lock).unwrap();
        fs::create_dir(&staging).unwrap();
        fs::write(staging.join("unknown.txt"), "preserve").unwrap();

        let error = managed.check_exists_or_create(|_| Ok(())).unwrap_err();

        assert_eq!(error.kind(), std::io::ErrorKind::InvalidData);
        assert_eq!(fs::read_to_string(staging.join("unknown.txt")).unwrap(), "preserve");
        assert!(staging_lock.is_dir());
        assert!(!dst.exists());
    }

    #[test]
    fn test_unknown_staging_claim_is_preserved() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);
        let (staging, staging_lock) = managed.staging_paths();
        let unknown_claim = vec![b'x'; STAGING_PROTOCOL_CLAIM.len()];
        fs::write(&staging_lock, &unknown_claim).unwrap();
        fs::create_dir(&staging).unwrap();
        fs::write(staging.join("unknown.txt"), "preserve").unwrap();

        let error = managed.check_exists_or_create(|_| Ok(())).unwrap_err();

        assert_eq!(error.kind(), std::io::ErrorKind::InvalidData);
        assert_eq!(fs::read_to_string(staging.join("unknown.txt")).unwrap(), "preserve");
        assert_eq!(fs::read(staging_lock).unwrap(), unknown_claim);
        assert!(!dst.exists());
    }

    #[test]
    fn test_preexisting_empty_staging_lock_is_claimed() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);
        let (staging, staging_lock) = managed.staging_paths();
        fs::write(&staging_lock, []).unwrap();

        managed.check_exists_or_create(|_| Ok(())).unwrap();

        assert!(dst.is_dir());
        assert!(!staging.exists());
        assert_eq!(fs::read(staging_lock).unwrap(), STAGING_PROTOCOL_CLAIM);
    }

    #[test]
    fn test_existing_staging_claim_allows_recovery() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);
        let (staging, staging_lock) = managed.staging_paths();
        fs::write(&staging_lock, STAGING_PROTOCOL_CLAIM).unwrap();
        fs::create_dir(&staging).unwrap();
        fs::write(staging.join("partial.txt"), "partial").unwrap();

        managed
            .check_exists_or_create(|staging| fs::write(staging.join("complete.txt"), "complete"))
            .unwrap();

        assert_eq!(fs::read_to_string(dst.join("complete.txt")).unwrap(), "complete");
        assert!(!dst.join("partial.txt").exists());
        assert!(!staging.exists());
    }

    #[cfg(unix)]
    #[test]
    fn test_staging_lock_symlink_is_rejected_without_writing_through() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);
        let (_, staging_lock) = managed.staging_paths();
        let referent = temp.path().join("referent");
        fs::write(&referent, []).unwrap();
        symlink(&referent, &staging_lock).unwrap();

        let error = managed.check_exists_or_create(|_| Ok(())).unwrap_err();

        assert_eq!(error.kind(), std::io::ErrorKind::InvalidData);
        assert_eq!(fs::metadata(referent).unwrap().len(), 0);
        assert!(fs::symlink_metadata(staging_lock).unwrap().file_type().is_symlink());
        assert!(!dst.exists());
    }

    #[test]
    fn test_stale_non_directory_staging_is_not_reused() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);
        let (stale_staging, _) = managed.staging_paths();
        let _ = managed.check_exists_or_create(|_| Err(std::io::Error::other("claim only")));
        fs::write(&stale_staging, "poison").unwrap();

        let mut next_staging = None;
        managed
            .check_exists_or_create(|staging| {
                next_staging = Some(staging.to_owned());
                assert!(fs::read_dir(staging)?.next().is_none());
                fs::write(staging.join("official.txt"), "official")?;
                Ok(())
            })
            .unwrap();

        assert_eq!(next_staging.unwrap(), stale_staging);
        assert_eq!(fs::read_to_string(dst.join("official.txt")).unwrap(), "official");
        assert!(!dst.join("poison").exists());
        assert!(!stale_staging.exists());
    }

    #[cfg(unix)]
    #[test]
    fn test_stale_staging_symlink_is_removed_without_following() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);
        let (stale_staging, _) = managed.staging_paths();
        let _ = managed.check_exists_or_create(|_| Err(std::io::Error::other("claim only")));
        let referent = temp.path().join("referent");
        fs::create_dir(&referent).unwrap();
        fs::write(referent.join("preserve.txt"), "preserve").unwrap();
        symlink(&referent, &stale_staging).unwrap();

        managed.check_exists_or_create(|_| Ok(())).unwrap();

        assert_eq!(fs::read_to_string(referent.join("preserve.txt")).unwrap(), "preserve");
        assert!(!stale_staging.exists());
    }

    #[cfg(unix)]
    #[test]
    fn test_make_staging_tree_removable_handles_deep_modes_without_following_symlinks() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let temp = tempfile::tempdir().unwrap();
        let staging = temp.path().join("staging");
        let outer = staging.join("outer");
        let inner = outer.join("inner");
        fs::create_dir_all(&inner).unwrap();
        fs::write(inner.join("entry.txt"), "entry").unwrap();

        let referent = temp.path().join("referent");
        fs::create_dir(&referent).unwrap();
        fs::write(referent.join("preserve.txt"), "preserve").unwrap();
        fs::set_permissions(&referent, fs::Permissions::from_mode(0o500)).unwrap();
        symlink(&referent, inner.join("link")).unwrap();

        fs::set_permissions(&inner, fs::Permissions::from_mode(0o000)).unwrap();
        fs::set_permissions(&outer, fs::Permissions::from_mode(0o000)).unwrap();

        make_staging_tree_removable(&staging).unwrap();

        assert_eq!(fs::metadata(&outer).unwrap().permissions().mode() & 0o700, 0o700);
        assert_eq!(fs::metadata(&inner).unwrap().permissions().mode() & 0o700, 0o700);
        assert!(fs::symlink_metadata(inner.join("link")).unwrap().file_type().is_symlink());
        assert_eq!(fs::metadata(&referent).unwrap().permissions().mode() & 0o777, 0o500);

        remove_staging_work(&staging).unwrap();
        assert_eq!(fs::read_to_string(referent.join("preserve.txt")).unwrap(), "preserve");
        fs::set_permissions(referent, fs::Permissions::from_mode(0o700)).unwrap();
    }

    #[cfg(windows)]
    #[test]
    fn test_make_staging_tree_removable_clears_readonly_entries() {
        let temp = tempfile::tempdir().unwrap();
        let staging = temp.path().join("staging");
        let nested = staging.join("nested");
        let entry = nested.join("entry.txt");
        fs::create_dir_all(&nested).unwrap();
        fs::write(&entry, "entry").unwrap();
        for path in [&nested, &entry] {
            let mut permissions = fs::metadata(path).unwrap().permissions();
            permissions.set_readonly(true);
            fs::set_permissions(path, permissions).unwrap();
        }

        make_staging_tree_removable(&staging).unwrap();

        assert!(!fs::metadata(nested).unwrap().permissions().readonly());
        assert!(!fs::metadata(entry).unwrap().permissions().readonly());
    }

    #[test]
    fn test_check_exists_file_not_dir() {
        let temp = tempfile::tempdir().unwrap();
        let file_path = temp.path().join("not_a_dir");
        fs::write(&file_path, "some data").unwrap();

        let managed = ManagedDirName::new(&file_path);
        let res = managed.check_exists();
        assert!(res.is_err());
    }

    #[test]
    fn test_check_exists_or_create_panic_cleanup() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);

        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = managed.check_exists_or_create(|staging| {
                fs::write(staging.join("partial.txt"), "partial").unwrap();
                panic!("simulated panic");
            });
        }));
        assert!(res.is_err());

        assert!(!dst.exists());
        let (staging, _) = managed.staging_paths();
        assert!(!staging.exists());
        assert!(parent_entries_except_metadata(&dst).is_empty());
    }

    #[test]
    fn test_check_exists_or_create_rename_failure() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);

        let res = managed.check_exists_or_create(|staging| {
            fs::write(staging.join("staged.txt"), "staged").unwrap();
            // Simulate conflicting file at destination
            fs::write(&dst, "conflicting file").unwrap();
            Ok(())
        });
        assert!(res.is_err());

        let (staging, _) = managed.staging_paths();
        assert!(!staging.exists());
        assert_eq!(parent_entries_except_metadata(&dst), [dst]);
    }

    const CRASH_RECOVERY_DST: &str = "EXOCRATE_TEST_CRASH_RECOVERY_DST";
    const CONCURRENT_PARENT_DST: &str = "EXOCRATE_TEST_CONCURRENT_PARENT_DST";

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_check_exists_or_create_recovers_after_process_exit() {
        if let Some(dst) = std::env::var_os(CRASH_RECOVERY_DST) {
            let dst = PathBuf::from(dst);
            let managed = ManagedDirName::new(&dst);
            let _ = managed.check_exists_or_create(|staging| -> IoResult<()> {
                fs::write(staging.join("partial.txt"), "partial")?;
                let protected = staging.join("protected");
                fs::create_dir(&protected)?;
                fs::write(protected.join("entry.txt"), "protected")?;
                #[cfg(unix)]
                {
                    use std::os::unix::fs::PermissionsExt as _;

                    fs::set_permissions(&protected, fs::Permissions::from_mode(0o000))?;
                }
                #[cfg(windows)]
                for path in [protected.join("entry.txt"), protected] {
                    let mut permissions = fs::metadata(&path)?.permissions();
                    permissions.set_readonly(true);
                    fs::set_permissions(path, permissions)?;
                }
                std::process::exit(86);
            });
            panic!("child installation unexpectedly returned");
        }

        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let child = std::process::Command::new(std::env::current_exe().unwrap())
            .arg("--exact")
            .arg("sync::tests::test_check_exists_or_create_recovers_after_process_exit")
            .arg("--nocapture")
            .env(CRASH_RECOVERY_DST, &dst)
            .output()
            .unwrap();
        assert_eq!(
            child.status.code(),
            Some(86),
            "child stdout:\n{}\nchild stderr:\n{}",
            String::from_utf8_lossy(&child.stdout),
            String::from_utf8_lossy(&child.stderr),
        );

        let (staging, _) = ManagedDirName::new(&dst).staging_paths();
        assert_eq!(fs::read_to_string(staging.join("partial.txt")).unwrap(), "partial");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            assert_eq!(
                fs::metadata(staging.join("protected")).unwrap().permissions().mode() & 0o777,
                0
            );
        }
        #[cfg(windows)]
        assert!(
            fs::metadata(staging.join("protected/entry.txt")).unwrap().permissions().readonly()
        );
        assert!(!dst.exists());

        ManagedDirName::new(&dst)
            .check_exists_or_create(|retry_staging| {
                assert_eq!(retry_staging, staging);
                assert!(fs::read_dir(retry_staging)?.next().is_none());
                fs::write(retry_staging.join("official.txt"), "official")?;
                Ok(())
            })
            .unwrap();

        assert_eq!(fs::read_to_string(dst.join("official.txt")).unwrap(), "official");
        assert!(!dst.join("partial.txt").exists());
        assert!(!staging.exists());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_first_use_serializes_across_processes() {
        if let Some(dst) = std::env::var_os(CONCURRENT_PARENT_DST) {
            let dst = PathBuf::from(dst);
            ManagedDirName::new(&dst)
                .check_exists_or_create(|staging| fs::write(staging.join("complete.txt"), "done"))
                .unwrap();
            return;
        }

        let temp = tempfile::tempdir().unwrap();
        let test_name = "sync::tests::test_first_use_serializes_across_processes";
        let mut children = Vec::new();
        for i in 0..8 {
            let dst = temp.path().join(format!("target_{i}"));
            let child = std::process::Command::new(std::env::current_exe().unwrap())
                .arg("--exact")
                .arg(test_name)
                .arg("--nocapture")
                .env(CONCURRENT_PARENT_DST, &dst)
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .spawn()
                .unwrap();
            children.push((dst, child));
        }

        for (dst, child) in children {
            let output = child.wait_with_output().unwrap();
            assert!(
                output.status.success(),
                "child stdout:\n{}\nchild stderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
            );
            assert_eq!(fs::read_to_string(dst.join("complete.txt")).unwrap(), "done");
        }

        let (staging, staging_lock) =
            ManagedDirName::new(&temp.path().join("target_0")).staging_paths();
        assert!(!staging.exists());
        assert_eq!(fs::read(staging_lock).unwrap(), STAGING_PROTOCOL_CLAIM);
    }

    #[test]
    fn test_abandoned_staging_is_reclaimed_by_next_parent_install() {
        let temp = tempfile::tempdir().unwrap();
        let target_a = temp.path().join("target_a");
        let target_b = temp.path().join("target_b");
        let managed_a = ManagedDirName::new(&target_a);
        let managed_b = ManagedDirName::new(&target_b);
        let (staging_a, staging_lock_a) = managed_a.staging_paths();
        let (staging_b, staging_lock_b) = managed_b.staging_paths();
        assert_eq!(staging_a, staging_b);
        assert_eq!(staging_lock_a, staging_lock_b);

        let _ = managed_a.check_exists_or_create(|_| Err(std::io::Error::other("claim only")));
        fs::create_dir(&staging_a).unwrap();
        fs::write(staging_a.join("a.partial"), "partial a").unwrap();

        managed_b
            .check_exists_or_create(|staging| {
                assert_eq!(staging, staging_b);
                assert!(fs::read_dir(staging)?.next().is_none());
                fs::write(staging.join("b.complete"), "complete b")?;
                Ok(())
            })
            .unwrap();
        assert_eq!(fs::read_to_string(target_b.join("b.complete")).unwrap(), "complete b");
        assert!(!target_a.exists());
        assert!(!target_b.join("a.partial").exists());
        assert!(!staging_b.exists());
    }

    #[test]
    #[should_panic(expected = "ManagedDirName path must have a filename")]
    fn test_no_filename() {
        let dst = Path::new("");
        let managed = ManagedDirName::new(dst);
        let _ = managed.check_exists_or_create(|_| Ok(()));
    }

    #[test]
    #[should_panic(expected = "ManagedDirName path must have a filename")]
    fn test_invalid_filename_root() {
        let dst = Path::new("/");
        let managed = ManagedDirName::new(dst);
        let _ = managed.check_exists_or_create(|_| Ok(()));
    }

    #[test]
    #[should_panic(expected = "ManagedDirName path must have a filename")]
    fn test_invalid_filename_dot() {
        let dst = Path::new(".");
        let managed = ManagedDirName::new(dst);
        let _ = managed.check_exists_or_create(|_| Ok(()));
    }

    #[test]
    #[should_panic(expected = "ManagedDirName path must have a filename")]
    fn test_invalid_filename_dotdot() {
        let dst = Path::new("..");
        let managed = ManagedDirName::new(dst);
        let _ = managed.check_exists_or_create(|_| Ok(()));
    }

    #[test]
    fn test_managed_dir() {
        let temp = tempfile::tempdir().unwrap();
        let target = temp.path().join("managed");
        let managed_name = ManagedDirName::new(&target);

        assert!(managed_name.check_exists().is_err());

        let dir = managed_name
            .check_exists_or_create(|staging| {
                fs::write(staging.join("test.txt"), "hello").unwrap();
                Ok(())
            })
            .unwrap();

        assert_eq!(dir.path, target.as_path());
        assert!(target.join("test.txt").exists());

        // Second call should return early via check_exists
        let dir2 = managed_name
            .check_exists_or_create(|_| {
                panic!("should not be called");
            })
            .unwrap();

        assert_eq!(dir2.path, target.as_path());
    }

    // This test exists to verify that the *implementation* of the lockfile
    // is stable across versions of this library. If this test fails, it may
    // indicate a breaking change that would cause two different versions of
    // this code to be incompatible when used to synchronize the same target
    // directory.
    #[test]
    fn test_lockfile_semantics() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("my_target_dir");
        let managed = ManagedDirName::new(&dst);

        let expected_lock = temp.path().join("my_target_dir.lock");

        let is_locked = |path: &Path| {
            #[cfg(unix)]
            {
                use std::os::fd::AsRawFd;
                let file = OpenOptions::new().read(true).write(true).open(path).unwrap();
                let fd = file.as_raw_fd();
                let res = unsafe { libc::flock(fd, libc::LOCK_EX | libc::LOCK_NB) };
                if res == 0 {
                    unsafe { libc::flock(fd, libc::LOCK_UN) };
                    false
                } else {
                    true
                }
            }

            #[cfg(windows)]
            {
                use std::os::windows::io::AsRawHandle;

                use windows_sys::Win32::Storage::FileSystem::{LockFile, UnlockFile};
                let file = OpenOptions::new().read(true).write(true).open(path).unwrap();
                let handle = file.as_raw_handle() as isize;
                let res = unsafe { LockFile(handle, 0, 0, 1, 0) };
                if res != 0 {
                    unsafe { UnlockFile(handle, 0, 0, 1, 0) };
                    false
                } else {
                    true
                }
            }
        };

        assert!(!expected_lock.exists(), "Lockfile must not exist to start");
        let _ = managed
            .check_exists_or_create(|staging| {
                assert!(expected_lock.exists(), "Lockfile must exist at expected path");
                assert!(expected_lock.is_file(), "Lockfile must be a regular file");
                assert!(is_locked(&expected_lock), "Lockfile must be in the 'locked' state");
                fs::write(staging.join("data.txt"), "content").unwrap();
                Ok(())
            })
            .unwrap();
        assert!(
            expected_lock.exists(),
            "Lockfile permanently remains on disk to prevent inode replacement race conditions"
        );
        assert!(!is_locked(&expected_lock), "Lockfile must be in the 'unlocked' state");

        fs::remove_dir_all(&dst).unwrap();
        assert!(expected_lock.exists(), "Lockfile permanently remains on disk");
        assert!(!is_locked(&expected_lock), "Lockfile must be in the 'unlocked' state");

        let _ = managed
            .check_exists_or_create(|staging| {
                assert!(expected_lock.exists(), "Lockfile must exist at expected path");
                assert!(expected_lock.is_file(), "Lockfile must be a regular file");
                assert!(is_locked(&expected_lock), "Lockfile must be in the 'locked' state");
                fs::write(staging.join("recreated.txt"), "recreated").unwrap();
                Ok(())
            })
            .unwrap();
        assert!(expected_lock.exists(), "Lockfile permanently remains on disk");
        assert!(!is_locked(&expected_lock), "Lockfile must be in the 'unlocked' state");
    }
}
