// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{
    ffi::OsString,
    fs::{self, File, OpenOptions},
    io::Result as IoResult,
    path::{Path, PathBuf},
};

/// Returns the parent directory of `path`, falling back to `.` when `path` is
/// a single relative component (`path.parent() == Some("")`).
pub(crate) fn staging_parent(path: &Path) -> &Path {
    match path.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent,
        _ => Path::new("."),
    }
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
    // INVARIANT: `path.file_name().is_some()`.
    path: &'a Path,
}

impl<'a> ManagedDirName<'a> {
    pub(crate) fn new(path: &'a Path) -> Self {
        assert!(path.file_name().is_some(), "ManagedDirName path must have a filename");
        Self { path }
    }

    /// Checks if the directory exists.
    pub(crate) fn check_exists(self) -> IoResult<ManagedDir<'a>> {
        // Perform one `fs::metadata` call (following symlinks) so a concurrent
        // atomic `fs::rename` into `self.path` cannot fall between `is_dir()`
        // and `try_exists()` and spuriously report `AlreadyExists`.
        match fs::metadata(self.path) {
            Ok(meta) if meta.is_dir() => Ok(ManagedDir { path: self.path }),
            Ok(_) => Err(std::io::Error::new(
                std::io::ErrorKind::AlreadyExists,
                "Path exists but is not a directory",
            )),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "Managed directory does not exist",
            )),
            Err(err) => Err(err),
        }
    }

    /// Checks if the directory exists, creating it if not.
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

        let parent = staging_parent(self.path);
        // NOTE: `create_dir_all` is safe to call concurrently with other
        // processes attempting to create the same directory:
        //
        //  Notable exception [to the error conditions] is made for
        //  situations where any of the directories specified in the path
        //  could not be created as it was being created concurrently. Such
        //  cases are considered to be successful. That is, calling
        //  create_dir_all concurrently from multiple threads or processes
        //  is guaranteed not to fail due to a race condition with itself.
        fs::create_dir_all(parent)?;

        let lock_file_path = self.lock_path();
        if let Ok(pre_meta) = fs::symlink_metadata(&lock_file_path)
            && (pre_meta.file_type().is_symlink() || !pre_meta.file_type().is_file())
        {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "Lock path exists and is not a regular file",
            ));
        }
        let lock_file = open_lock_file(&lock_file_path)?;
        let fd_meta = lock_file.metadata()?;
        if !fd_meta.is_file() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "Opened lock path is not a regular file",
            ));
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            let post_meta = fs::symlink_metadata(&lock_file_path)?;
            if post_meta.file_type().is_symlink()
                || (post_meta.dev(), post_meta.ino()) != (fd_meta.dev(), fd_meta.ino())
            {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    "Lock path changed or became a symlink during open",
                ));
            }
        }

        <_ as fs2::FileExt>::lock_exclusive(&lock_file)?;

        struct StagingGuard {
            staging_dir: Option<tempfile::TempDir>,
            lock_file: File,
        }

        impl Drop for StagingGuard {
            fn drop(&mut self) {
                // Remove any unpromoted staging directory before releasing the
                // exclusive lock so serialized callers observe a clean state.
                drop(self.staging_dir.take());
                let _ = <_ as fs2::FileExt>::unlock(&self.lock_file);
            }
        }

        // A guard that unlocks `lock_file` and cleans up any staging directory
        // even if `populate` errors or panics.
        let mut guard = StagingGuard { staging_dir: None, lock_file };

        // Handle the case where, while we were waiting to acquire the lock,
        // another process populated the directory.
        if let Ok(dir) = self.check_exists() {
            return Ok(dir);
        }

        // Allocate a fresh private (`0o700` on Unix) temporary staging
        // directory per attempt rather than reusing a fixed `<dst>.staging`
        // path. That prevents leftover unwritable files or directories from an
        // earlier failed attempt (or a pre-existing legacy `<dst>.staging`)
        // from poisoning or blocking subsequent installs.
        let staging_prefix = self.staging_prefix();
        let mut builder = tempfile::Builder::new();
        builder.prefix(&staging_prefix).suffix(".staging");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            builder.permissions(fs::Permissions::from_mode(0o700));
        }
        let staging_dir = builder.tempdir_in(parent)?;
        let staging_path = staging_dir.path().to_path_buf();
        guard.staging_dir = Some(staging_dir);

        populate(&staging_path)?;

        fs::rename(&staging_path, self.path).map_err(|e| {
            std::io::Error::new(
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
            )
        })?;

        // Disarm `TempDir`'s delete-on-drop only after the atomic rename has
        // promoted the staging tree to `self.path`.
        if let Some(dir) = guard.staging_dir.take() {
            let _ = dir.keep();
        }
        Ok(ManagedDir { path: self.path })
    }

    fn staging_prefix(&self) -> OsString {
        // Keep a bounded prefix of the target directory name for debuggability
        // while staying well below filesystem `NAME_MAX` limits once
        // `tempfile`'s random suffix and `.staging` suffix are appended.
        const MAX_NAME_PREFIX_BYTES: usize = 64;
        let name = self.path.file_name().expect("ManagedDirName path must have a filename");
        let mut prefix = OsString::from(".staging-");
        if name.len() <= MAX_NAME_PREFIX_BYTES {
            prefix.push(name);
            prefix.push(".");
        } else if let Some(s) = name.to_str() {
            let mut end = MAX_NAME_PREFIX_BYTES;
            while !s.is_char_boundary(end) {
                end -= 1;
            }
            prefix.push(&s[..end]);
            prefix.push(".");
        }
        prefix
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

/// Opens (creating if absent) the lock file at `path`.
///
/// On Unix, the open neither follows a symlink nor blocks, so a symlink or
/// FIFO swapped in after the caller's `lstat` cannot redirect `O_CREAT` to
/// another file or hang the open; the caller still checks what was opened.
fn open_lock_file(path: &Path) -> std::io::Result<File> {
    let mut options = OpenOptions::new();
    options.read(true).write(true).create(true).truncate(false);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    options.open(path)
}

#[cfg(test)]
pub(crate) mod tests {
    use std::{fs, path::Path};

    use super::*;

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

    #[test]
    fn test_staging_parent_handles_single_component_and_nested_paths() {
        assert_eq!(staging_parent(Path::new("install_target")), Path::new("."));
        assert_eq!(staging_parent(Path::new("cache/install_target")), Path::new("cache"));
    }

    #[cfg(unix)]
    pub(crate) struct UnixRestorePermissions<'a> {
        pub(crate) root: &'a Path,
    }

    #[cfg(unix)]
    impl Drop for UnixRestorePermissions<'_> {
        fn drop(&mut self) {
            fn restore(dir: &Path) {
                use std::os::unix::fs::PermissionsExt as _;
                let _ = fs::set_permissions(dir, fs::Permissions::from_mode(0o755));
                if let Ok(entries) = fs::read_dir(dir) {
                    for entry in entries.flatten() {
                        let path = entry.path();
                        if entry.file_type().is_ok_and(|ft| ft.is_dir()) {
                            restore(&path);
                        }
                    }
                }
            }
            restore(self.root);
        }
    }

    #[cfg(unix)]
    #[test]
    fn test_failed_unwritable_staging_dir_does_not_poison_or_block_retry() {
        use std::os::unix::fs::PermissionsExt as _;

        let temp = tempfile::tempdir().unwrap();
        let _restore = UnixRestorePermissions { root: temp.path() };
        let dst = temp.path().join("install_target");
        let managed = ManagedDirName::new(&dst);

        let mut first_staging = None;
        let first = managed.check_exists_or_create(|staging| {
            first_staging = Some(staging.to_path_buf());
            let unexpected = staging.join("unexpected");
            fs::create_dir_all(&unexpected).unwrap();
            fs::write(unexpected.join("marker.txt"), b"UNVERIFIED").unwrap();
            fs::set_permissions(&unexpected, fs::Permissions::from_mode(0o555)).unwrap();

            let blocked_bin = staging.join("bin");
            fs::create_dir_all(&blocked_bin).unwrap();
            fs::set_permissions(&blocked_bin, fs::Permissions::from_mode(0o000)).unwrap();

            Err(std::io::Error::other("simulated failure"))
        });
        assert!(first.is_err());
        assert!(!dst.exists());

        let mut second_staging = None;
        let dir = managed
            .check_exists_or_create(|staging| {
                second_staging = Some(staging.to_path_buf());
                fs::write(staging.join("official.txt"), b"authentic").unwrap();
                Ok(())
            })
            .unwrap();

        assert_eq!(dir.path, dst.as_path());
        assert_ne!(first_staging, second_staging);
        assert_eq!(fs::read_to_string(dst.join("official.txt")).unwrap(), "authentic");
        assert!(!dst.join("unexpected").exists());
        assert!(!dst.join("bin").exists());
    }

    #[cfg(unix)]
    #[test]
    fn test_staging_dir_is_private_and_ignores_legacy_staging_dir() {
        use std::os::unix::fs::PermissionsExt as _;

        let temp = tempfile::tempdir().unwrap();
        let _restore = UnixRestorePermissions { root: temp.path() };
        let dst = temp.path().join("install_target");
        let legacy_staging = temp.path().join("install_target.staging");
        let legacy_unexpected = legacy_staging.join("unexpected");
        fs::create_dir_all(&legacy_unexpected).unwrap();
        fs::write(legacy_unexpected.join("marker.txt"), b"POISON").unwrap();
        fs::set_permissions(&legacy_unexpected, fs::Permissions::from_mode(0o555)).unwrap();
        fs::set_permissions(&legacy_staging, fs::Permissions::from_mode(0o555)).unwrap();

        let managed = ManagedDirName::new(&dst);
        managed
            .check_exists_or_create(|staging| {
                assert_ne!(staging, legacy_staging);
                let mode = fs::metadata(staging).unwrap().permissions().mode() & 0o777;
                assert_eq!(mode, 0o700);
                fs::write(staging.join("official.txt"), b"clean").unwrap();
                Ok(())
            })
            .unwrap();

        assert_eq!(fs::read_to_string(dst.join("official.txt")).unwrap(), "clean");
        assert!(!dst.join("unexpected").exists());
    }

    #[cfg(unix)]
    #[test]
    fn test_check_exists_symlink_semantics() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().unwrap();
        let real_dir = temp.path().join("real_dir");
        fs::create_dir(&real_dir).unwrap();
        let dir_link = temp.path().join("dir_link");
        symlink(&real_dir, &dir_link).unwrap();

        let dir = ManagedDirName::new(&dir_link).check_exists().unwrap();
        assert_eq!(dir.path, dir_link.as_path());

        let real_file = temp.path().join("real_file");
        fs::write(&real_file, b"file").unwrap();
        let file_link = temp.path().join("file_link");
        symlink(&real_file, &file_link).unwrap();

        let file_err = ManagedDirName::new(&file_link).check_exists().unwrap_err();
        assert_eq!(file_err.kind(), std::io::ErrorKind::AlreadyExists);

        let dangling_link = temp.path().join("dangling_link");
        symlink(temp.path().join("missing_target"), &dangling_link).unwrap();

        let dangling_err = ManagedDirName::new(&dangling_link).check_exists().unwrap_err();
        assert_eq!(dangling_err.kind(), std::io::ErrorKind::NotFound);
    }

    #[test]
    fn test_check_exists_concurrent_rename_never_reports_already_exists() {
        use std::{
            sync::{
                Arc, Barrier,
                atomic::{AtomicBool, Ordering},
            },
            thread,
        };

        const ITERATIONS: usize = 500;
        let temp = tempfile::tempdir().unwrap();

        for i in 0..ITERATIONS {
            let staging = temp.path().join(format!("staging-{i}"));
            let dst = temp.path().join(format!("target-{i}"));
            fs::create_dir(&staging).unwrap();
            fs::write(staging.join("ready"), b"ok").unwrap();

            let barrier = Arc::new(Barrier::new(2));
            let renamed = Arc::new(AtomicBool::new(false));
            let b_reader = Arc::clone(&barrier);
            let r_reader = Arc::clone(&renamed);
            let dst_reader = dst.clone();

            let reader = thread::spawn(move || {
                b_reader.wait();
                loop {
                    match ManagedDirName::new(&dst_reader).check_exists() {
                        Ok(dir) => {
                            assert_eq!(dir.path, dst_reader.as_path());
                            break;
                        }
                        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
                            if r_reader.load(Ordering::Acquire) {
                                // One more check after observing `renamed` must
                                // see the renamed directory.
                                let dir = ManagedDirName::new(&dst_reader).check_exists().unwrap();
                                assert_eq!(dir.path, dst_reader.as_path());
                                break;
                            }
                            thread::yield_now();
                        }
                        Err(err) => {
                            panic!("unexpected check_exists error during atomic rename: {err}");
                        }
                    }
                }
            });

            barrier.wait();
            fs::rename(&staging, &dst).unwrap();
            renamed.store(true, Ordering::Release);
            reader.join().unwrap();
        }
    }

    #[cfg(unix)]
    #[test]
    fn test_rejects_symlink_lockfile() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().unwrap();
        let locked_dst = temp.path().join("locked_target");
        let victim_file = temp.path().join("victim.txt");
        fs::write(&victim_file, "do not lock").unwrap();
        symlink(&victim_file, temp.path().join("locked_target.lock")).unwrap();
        let err = ManagedDirName::new(&locked_dst).check_exists_or_create(|_| Ok(())).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidInput);
    }

    #[cfg(unix)]
    #[test]
    fn test_open_lock_file_refuses_swapped_symlink() {
        let temp = tempfile::tempdir().unwrap();
        let target = temp.path().join("target");
        let lock = temp.path().join("dst.lock");
        std::os::unix::fs::symlink(&target, &lock).unwrap();

        // A dangling symlink at the lock path must not make `O_CREAT` create
        // its target.
        assert!(open_lock_file(&lock).is_err());
        assert!(!target.exists());

        // Nor may a symlink to an existing file be followed.
        fs::write(&target, b"").unwrap();
        assert!(open_lock_file(&lock).is_err());

        // A regular lock file is created and reopened.
        let plain = temp.path().join("plain.lock");
        open_lock_file(&plain).unwrap();
        assert!(fs::symlink_metadata(&plain).unwrap().is_file());
        open_lock_file(&plain).unwrap();
    }
}
