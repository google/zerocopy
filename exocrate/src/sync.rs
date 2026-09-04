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
    io::Result as IoResult,
    path::{Path, PathBuf},
};

const STAGING_MARKER: u8 = b'@';
const STAGING_PREFIX: &str = "@";
const STAGING_RANDOM_LEN: usize = 7;
const STAGING_SUFFIX: &str = ".tmp";

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

/// Returns whether `name` has the canonical staging-directory shape.
const fn has_staging_name_shape(name: &str) -> bool {
    let bytes = name.as_bytes();
    if bytes.len() != 12 || bytes[0] != STAGING_MARKER || bytes[8] != b'.' {
        return false;
    }

    let mut i = 1;
    while i < 8 {
        let byte = bytes[i];
        if !((byte >= b'0' && byte <= b'9')
            || (byte >= b'A' && byte <= b'Z')
            || (byte >= b'a' && byte <= b'z'))
        {
            return false;
        }
        i += 1;
    }

    bytes[9] == b't' && bytes[10] == b'm' && bytes[11] == b'p'
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
    /// `populate` is always given a freshly-created staging directory. If a
    /// failed staging directory remains after cleanup, a later call creates a
    /// different directory rather than reusing its contents.
    ///
    /// # Concurrency
    ///
    /// `check_exists_or_create` is **not** concurrency-safe if multiple
    /// concurrent calls are made *from the same process*.
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

        // Handle the case where, while we were waiting to acquire the lock,
        // another process populated the directory.
        if let Ok(dir) = self.check_exists() {
            return Ok(dir);
        }

        // This creates the directory atomically. If cleaning up an earlier
        // attempt failed, that attempt's path is still occupied and cannot be
        // selected here. Staging basenames occupy a namespace which
        // `ManagedDirName::new` reserves from target directories. The form is
        // also a valid 8.3 filename, preventing Windows from assigning a
        // distinct short-name alias.
        let staging_dir = tempfile::Builder::new()
            .prefix(STAGING_PREFIX)
            .rand_bytes(STAGING_RANDOM_LEN)
            .suffix(STAGING_SUFFIX)
            .tempdir_in(parent)?;
        let staging_name = staging_dir
            .path()
            .file_name()
            .and_then(|name| name.to_str())
            .expect("tempfile must produce a UTF-8 staging filename");
        assert!(
            has_staging_name_shape(staging_name),
            "tempfile must produce an 8.3-compatible staging filename",
        );

        populate(staging_dir.path())?;

        // Disarm automatic cleanup before renaming. After a successful rename,
        // the old staging path is vacant and another process could reuse it;
        // an armed path-based cleanup guard could then delete that process's
        // directory.
        let staging_path = staging_dir.keep();
        if let Err(e) = fs::rename(&staging_path, self.path) {
            let _ = fs::remove_dir_all(&staging_path);
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

    // NOTE: It's important that `lock_path` returns a lock path whose name
    // has the directory name as a prefix. See the comment on `ManagedDir`.
    fn lock_path(&self) -> PathBuf {
        let mut file_name =
            self.path.file_name().expect("ManagedDirName path must have a filename").to_os_string();
        file_name.push(".lock");
        self.path.with_file_name(file_name)
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, path::Path};

    use super::*;

    #[test]
    fn test_staging_name_namespace() {
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

        assert!(has_staging_name_shape("@Ab12CdE.tmp"));
        for name in [
            "@Ab12Cd.tmp",
            "@Ab12CdEf.tmp",
            "@Ab12C-E.tmp",
            "@Ab12CdE.TMP",
            "@Ab12CdE.tmp. ",
            "@ABCDEF\u{212a}.tmp",
            "\u{200c}@Ab12CdE.tmp",
        ] {
            assert!(!has_staging_name_shape(name), "{name:?}");
        }
    }

    #[test]
    fn test_reserved_staging_names_cannot_be_managed_targets() {
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
                assert!(has_staging_name_shape(name));
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
        let entries: Vec<_> = fs::read_dir(temp.path())
            .unwrap()
            .map(|e| e.unwrap().file_name())
            .filter(|n| n != "install_target.lock")
            .collect();
        assert!(entries.is_empty());
    }

    #[test]
    fn test_check_exists_or_create_cleanup_failure_is_not_reused() {
        let temp = tempfile::tempdir().unwrap();
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);
        let mut failed_staging = None;

        let res = managed.check_exists_or_create(|staging| {
            failed_staging = Some(staging.to_owned());

            // `remove_dir_all` cannot remove a regular file. Replacing the
            // staging directory with one deterministically simulates failed
            // cleanup without relying on platform-specific permissions.
            fs::remove_dir(staging)?;
            fs::write(staging, "poison")?;
            Err(std::io::Error::other("simulated error"))
        });
        assert!(res.is_err());

        let failed_staging = failed_staging.unwrap();
        assert!(failed_staging.is_file());

        let mut next_staging = None;
        managed
            .check_exists_or_create(|staging| {
                next_staging = Some(staging.to_owned());
                fs::write(staging.join("official.txt"), "official")?;
                Ok(())
            })
            .unwrap();

        assert_ne!(next_staging.unwrap(), failed_staging);
        assert_eq!(fs::read_to_string(dst.join("official.txt")).unwrap(), "official");
        assert!(!dst.join("poison").exists());

        fs::remove_file(failed_staging).unwrap();
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
        let entries: Vec<_> = fs::read_dir(temp.path())
            .unwrap()
            .map(|e| e.unwrap().file_name())
            .filter(|n| n != "install_target.lock")
            .collect();
        assert!(entries.is_empty());
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

        let entries: Vec<_> = fs::read_dir(temp.path())
            .unwrap()
            .map(|e| e.unwrap().file_name())
            .filter(|n| n != "install_target.lock" && n != "install_target")
            .collect();
        assert!(entries.is_empty());
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
