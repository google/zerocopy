// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![cfg(feature = "exocrate_tests")]

use std::{fs, process::Command};

fn wait_with_timeout(
    child: &mut std::process::Child,
    timeout: std::time::Duration,
) -> anyhow::Result<std::process::ExitStatus> {
    let start = std::time::Instant::now();
    loop {
        if let Some(status) = child.try_wait()? {
            return Ok(status);
        }
        if start.elapsed() > timeout {
            child.kill()?;
            anyhow::bail!("Child process timed out after {:?}", timeout);
        }
        std::thread::sleep(std::time::Duration::from_millis(50));
    }
}

#[test]
fn test_dir_lock_coexistence_integration() {
    let temp_dir = tempfile::tempdir().unwrap();
    let lock_dir = temp_dir.path().join("lock_dir");
    let log_file = temp_dir.path().join("concurrency_log.txt");
    let sig_file = temp_dir.path().join("sig_b_active.tmp");

    let bin_path = std::env::var("CARGO_BIN_EXE_cargo-anneal")
        .or_else(|_| std::env::var("CARGO_BIN_EXE_cargo_anneal"))
        .expect("CARGO_BIN_EXE_* not set");

    // 1. Spawn Reader A
    let mut child_a = Command::new(&bin_path)
        .arg("test-lock-helper")
        .arg("--role")
        .arg("reader-a")
        .arg("--lock-dir")
        .arg(&lock_dir)
        .arg("--log-file")
        .arg(&log_file)
        .arg("--sig-file")
        .arg(&sig_file)
        .spawn()
        .expect("failed to spawn reader-a");

    // Give A a tiny bit of time to acquire the lock.
    std::thread::sleep(std::time::Duration::from_millis(100));

    // 2. Spawn Reader B
    let mut child_b = Command::new(&bin_path)
        .arg("test-lock-helper")
        .arg("--role")
        .arg("reader-b")
        .arg("--lock-dir")
        .arg(&lock_dir)
        .arg("--log-file")
        .arg(&log_file)
        .arg("--sig-file")
        .arg(&sig_file)
        .spawn()
        .expect("failed to spawn reader-b");

    // 3. Wait for both with a strict timeout.
    let status_a = wait_with_timeout(&mut child_a, std::time::Duration::from_secs(5))
        .expect("Reader A failed or timed out");
    let status_b = wait_with_timeout(&mut child_b, std::time::Duration::from_secs(5))
        .expect("Reader B failed or timed out");

    assert!(status_a.success(), "Reader A exited with failure");
    assert!(status_b.success(), "Reader B exited with failure");

    // 4. Read trace and assert overlap.
    let trace = fs::read_to_string(&log_file).expect("failed to read log");
    let lines: Vec<&str> = trace.lines().collect();
    assert_eq!(lines.len(), 4, "Expected exactly 4 log lines");

    // Expected overlap trace:
    // SHARED_START_A
    // SHARED_START_B
    // SHARED_END_B
    // SHARED_END_A
    assert_eq!(lines[0], "SHARED_START_A");
    assert_eq!(lines[1], "SHARED_START_B");
    assert_eq!(lines[2], "SHARED_END_B");
    assert_eq!(lines[3], "SHARED_END_A");
}

#[test]
fn test_dir_lock_exclusion_integration() {
    let temp_dir = tempfile::tempdir().unwrap();
    let lock_dir = temp_dir.path().join("lock_dir");
    let log_file = temp_dir.path().join("concurrency_log.txt");
    let sig_file = temp_dir.path().join("sig_b_attempt.tmp");

    let bin_path = std::env::var("CARGO_BIN_EXE_cargo-anneal")
        .or_else(|_| std::env::var("CARGO_BIN_EXE_cargo_anneal"))
        .expect("CARGO_BIN_EXE_* not set");

    // 1. Spawn Writer A
    let mut child_a = Command::new(&bin_path)
        .arg("test-lock-helper")
        .arg("--role")
        .arg("writer-a")
        .arg("--lock-dir")
        .arg(&lock_dir)
        .arg("--log-file")
        .arg(&log_file)
        .arg("--sig-file")
        .arg(&sig_file)
        .spawn()
        .expect("failed to spawn writer-a");

    // Give A a tiny bit of time to acquire the lock.
    std::thread::sleep(std::time::Duration::from_millis(100));

    // 2. Spawn Reader B
    let mut child_b = Command::new(&bin_path)
        .arg("test-lock-helper")
        .arg("--role")
        .arg("reader-exclusion")
        .arg("--lock-dir")
        .arg(&lock_dir)
        .arg("--log-file")
        .arg(&log_file)
        .arg("--sig-file")
        .arg(&sig_file)
        .spawn()
        .expect("failed to spawn reader-exclusion");

    // 3. Wait for both with a strict timeout.
    let status_a = wait_with_timeout(&mut child_a, std::time::Duration::from_secs(5))
        .expect("Writer A failed or timed out");
    let status_b = wait_with_timeout(&mut child_b, std::time::Duration::from_secs(5))
        .expect("Reader B failed or timed out");

    assert!(status_a.success(), "Writer A exited with failure");
    assert!(status_b.success(), "Reader B exited with failure");

    // 4. Read trace and assert exclusion.
    let trace = fs::read_to_string(&log_file).expect("failed to read log");
    let lines: Vec<&str> = trace.lines().collect();
    assert_eq!(lines.len(), 4, "Expected exactly 4 log lines");

    // Expected sequential trace (since A blocks B):
    // EXCLUSIVE_START_A
    // EXCLUSIVE_END_A
    // SHARED_START_B
    // SHARED_END_B
    assert_eq!(lines[0], "EXCLUSIVE_START_A");
    assert_eq!(lines[1], "EXCLUSIVE_END_A");
    assert_eq!(lines[2], "SHARED_START_B");
    assert_eq!(lines[3], "SHARED_END_B");
}
