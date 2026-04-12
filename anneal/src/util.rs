use std::path::PathBuf;

use anyhow::{Context, Result};
use fs2::FileExt;

/// Represents an active, exclusive lock on a directory.
///
/// This struct guarantees that the process holds an OS-level file lock
/// guarding the specified directory.
pub struct DirLock {
    /// The path to the directory being guarded.
    pub path: PathBuf,
    // Kept alive to hold the flock
    _file: std::fs::File,
}

impl DirLock {
    /// Acquires an exclusive lock on the specified directory.
    ///
    /// This function blocks until the lock can be acquired. We use a
    /// separate `.lock` file within the directory rather than locking
    /// the directory itself to avoid platform-specific issues with
    /// directory locking and to ensure the lock file persists even if
    /// the directory is cleaned.
    pub fn lock_exclusive(path: PathBuf) -> Result<Self> {
        let file = Self::open_lock_file(&path)?;
        file.lock_exclusive()
            .with_context(|| format!("Failed to acquire exclusive lock on {:?}", path))?;
        Ok(Self { path, _file: file })
    }

    /// Acquires a shared lock on the specified directory.
    ///
    /// Multiple processes can hold shared locks simultaneously, but an
    /// exclusive lock will block until all shared locks are released.
    pub fn lock_shared(path: PathBuf) -> Result<Self> {
        let file = Self::open_lock_file(&path)?;
        file.lock_shared()
            .with_context(|| format!("Failed to acquire shared lock on {:?}", path))?;
        Ok(Self { path, _file: file })
    }

    fn open_lock_file(path: &std::path::Path) -> Result<std::fs::File> {
        let lock_path = path.join(".lock");

        // Ensure the directory exists
        if let Some(parent) = lock_path.parent() {
            std::fs::create_dir_all(parent).with_context(|| {
                format!("Failed to create directory for lock file: {:?}", parent)
            })?;
        }
        // If the lock file already exists, we open it in read-only mode.
        // This prevents failures if the file is read-only (e.g., after
        // making the toolchain directory read-only), while still allowing
        // us to acquire shared and exclusive locks on the file descriptor.
        if lock_path.exists() {
            std::fs::OpenOptions::new()
                .read(true)
                .open(&lock_path)
                .with_context(|| format!("Failed to open lock file at {:?}", lock_path))
        } else {
            std::fs::OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .open(&lock_path)
                .with_context(|| format!("Failed to create lock file at {:?}", lock_path))
        }
    }
}
