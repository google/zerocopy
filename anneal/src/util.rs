// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::io::BufRead as _;

use anyhow::Context as _;
use fs2::FileExt as _;

/// Represents an active, exclusive lock on a directory.
///
/// This struct guarantees that the process holds an OS-level file lock
/// guarding the specified directory.
pub(crate) struct DirLock {
    /// The path to the directory being guarded.
    pub(crate) path: std::path::PathBuf,
    // Kept alive to hold the flock.
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
    pub(crate) fn lock_exclusive(path: std::path::PathBuf) -> anyhow::Result<Self> {
        let file = Self::open_lock_file(&path)?;
        file.lock_exclusive()
            .with_context(|| format!("Failed to acquire exclusive lock on {:?}", path))?;
        Ok(Self { path, _file: file })
    }

    /// Acquires a shared lock on the specified directory.
    ///
    /// Multiple processes can hold shared locks simultaneously, but an
    /// exclusive lock will block until all shared locks are released.
    #[cfg(any(test, feature = "exocrate_tests"))]
    pub(crate) fn lock_shared(path: std::path::PathBuf) -> anyhow::Result<Self> {
        let file = Self::open_lock_file(&path)?;
        file.lock_shared()
            .with_context(|| format!("Failed to acquire shared lock on {:?}", path))?;
        Ok(Self { path, _file: file })
    }

    fn open_lock_file(path: &std::path::Path) -> anyhow::Result<std::fs::File> {
        let lock_path = path.join(".lock");

        // Ensure the directory exists.
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

pub(crate) struct ProcessOutput {
    pub status: std::process::ExitStatus,
    pub stderr_lines: Vec<String>,
}

/// Spawns a child process, drains its stderr in a background thread, and processes
/// its stdout line-by-line in the main thread while showing a progress spinner.
pub(crate) fn run_command_with_progress<F>(
    mut cmd: std::process::Command,
    pb: Option<indicatif::ProgressBar>,
    mut process_stdout_line: F,
) -> anyhow::Result<ProcessOutput>
where
    F: FnMut(&str, Option<&indicatif::ProgressBar>) -> anyhow::Result<()>,
{
    cmd.stdout(std::process::Stdio::piped());
    cmd.stderr(std::process::Stdio::piped());

    let mut child = cmd.spawn().context("Failed to spawn child process")?;

    let stderr_buffer = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let stderr_buffer_clone = std::sync::Arc::clone(&stderr_buffer);

    let mut stderr_thread = None;
    if let Some(stderr) = child.stderr.take() {
        stderr_thread = Some(std::thread::spawn(move || {
            let reader = std::io::BufReader::new(stderr);
            for line in reader.lines().map_while(Result::ok) {
                stderr_buffer_clone.lock().unwrap().push(line);
            }
        }));
    }

    if let Some(ref p) = pb {
        p.enable_steady_tick(std::time::Duration::from_millis(100));
    }

    if let Some(stdout) = child.stdout.take() {
        let reader = std::io::BufReader::new(stdout);
        for line in reader.lines().map_while(Result::ok) {
            process_stdout_line(&line, pb.as_ref())?;
            if let Some(ref p) = pb {
                p.tick();
            }
        }
    }

    if let Some(ref p) = pb {
        p.finish_and_clear();
    }

    let status = child.wait().context("Failed to wait for child process")?;

    if let Some(thread) = stderr_thread {
        let _ = thread.join();
    }

    let stderr_lines = std::sync::Arc::try_unwrap(stderr_buffer).unwrap().into_inner().unwrap();

    Ok(ProcessOutput { status, stderr_lines })
}

/// Performs a lock test action according to the `role` of the current actor. Actors may:
///
/// - Obtain an exclusive or shared lock for `lock_dir`,
/// - Log actions in `log_file`,
/// - Wait for a signal from `sig_file`.
///
/// Individual tests compose multiple role-based actions and verify the resulting action log.
#[cfg(feature = "exocrate_tests")]
pub(crate) fn run_test_lock_helper(
    role: &str,
    lock_dir: &std::path::Path,
    log_file: &std::path::Path,
    sig_file: &std::path::Path,
) -> anyhow::Result<()> {
    use std::io::Write as _;

    let append_log = |msg: &str| -> anyhow::Result<()> {
        let mut file = std::fs::OpenOptions::new().create(true).append(true).open(log_file)?;
        writeln!(file, "{}", msg)?;
        Ok(())
    };

    let wait_for_sig = || -> anyhow::Result<()> {
        let start = std::time::Instant::now();
        while !sig_file.exists() {
            if start.elapsed() > std::time::Duration::from_secs(3) {
                anyhow::bail!("Timeout waiting for signal file {:?}", sig_file);
            }
            std::thread::sleep(std::time::Duration::from_millis(50));
        }
        Ok(())
    };

    match role {
        "reader-a" => {
            let _lock = DirLock::lock_shared(lock_dir.to_path_buf())?;
            append_log("SHARED_START_A")?;
            wait_for_sig()?;
            append_log("SHARED_END_A")?;
        }
        "reader-b" => {
            let _lock = DirLock::lock_shared(lock_dir.to_path_buf())?;
            append_log("SHARED_START_B")?;
            std::fs::write(sig_file, "")?;
            append_log("SHARED_END_B")?;
        }
        "writer-a" => {
            let _lock = DirLock::lock_exclusive(lock_dir.to_path_buf())?;
            append_log("EXCLUSIVE_START_A")?;
            wait_for_sig()?;
            append_log("EXCLUSIVE_END_A")?;
        }
        "reader-exclusion" => {
            std::fs::write(sig_file, "")?;
            let _lock = DirLock::lock_shared(lock_dir.to_path_buf())?;
            append_log("SHARED_START_B")?;
            append_log("SHARED_END_B")?;
        }
        _ => anyhow::bail!("Unknown test-lock-helper role: {}", role),
    }

    Ok(())
}

#[cfg(test)]
#[macro_export]
macro_rules! workspace_fixture {
    ($dir:expr, { $($path:expr => $content:expr),* $(,)? }) => {{
        let root = $dir.path();
        $(
            let file_path = root.join($path);
            if let Some(parent) = file_path.parent() {
                std::fs::create_dir_all(parent).unwrap();
            }
            std::fs::write(&file_path, $content).unwrap();
        )*
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dir_lock_exclusive_mutual_exclusion() {
        let temp_dir = tempfile::tempdir().unwrap();
        let lock_path = temp_dir.path().to_path_buf();

        let barrier = std::sync::Arc::new(std::sync::Barrier::new(2));
        let barrier_clone = std::sync::Arc::clone(&barrier);
        let lock_path_clone = lock_path.clone();

        let lock_released = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let lock_released_clone = std::sync::Arc::clone(&lock_released);

        // Thread A acquires the lock.
        let thread_a = std::thread::spawn(move || {
            let _lock = DirLock::lock_exclusive(lock_path_clone).expect("Failed to lock exclusive");
            barrier_clone.wait(); // Signal Thread B that A holds the lock.

            // Simulate brief work holding the lock.
            std::thread::sleep(std::time::Duration::from_millis(100));
            lock_released_clone.store(true, std::sync::atomic::Ordering::Relaxed);
            // _lock drops here, releasing the lock.
        });

        // Thread B waits for Thread A to acquire the lock, then tries to acquire it itself.
        let thread_b = std::thread::spawn(move || {
            barrier.wait(); // Wait for Thread A to acquire lock.

            // Attempt to acquire lock. This should block until Thread A releases it.
            let _lock = DirLock::lock_exclusive(lock_path).expect("Failed to lock exclusive in B");

            // Assert that B only successfully locked the directory AFTER A released it.
            assert!(
                lock_released.load(std::sync::atomic::Ordering::Relaxed),
                "Thread B acquired lock before Thread A released it!"
            );
        });

        thread_a.join().unwrap();
        thread_b.join().unwrap();
    }

    #[test]
    fn test_dir_lock_shared_coexistence() {
        let temp_dir = tempfile::tempdir().unwrap();
        let lock_path = temp_dir.path().to_path_buf();

        // Thread A acquires shared lock.
        let lock_a = DirLock::lock_shared(lock_path.clone()).expect("Failed to lock shared");

        // Thread B should be able to acquire shared lock immediately without blocking.
        let lock_b = DirLock::lock_shared(lock_path).expect("Failed to lock shared concurrently");

        // Both locks are held.
        drop(lock_a);
        drop(lock_b);
    }
}
