// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Tests: The seed archive, `.incomplete` markers, and concurrent cold
//! installs.

use std::{fs, io};

use super::*;

#[test]
fn concurrent_cold_local_archive_installs_apply_both_and_last_writer_wins() {
    use std::{sync::Arc, sync::Barrier, thread};

    let temp = tempfile::tempdir().expect("create owned fixture");
    let v1 = temp.path().join("v1.tar.zst");
    let v2 = temp.path().join("v2.tar.zst");
    let corrupt = temp.path().join("corrupt.tar.zst");
    write_archive_with(&v1, b"archive v1");
    write_archive_with(&v2, b"archive v2");
    fs::write(&corrupt, b"invalid zstd").expect("write corrupt archive");

    // Deterministic cold-race check: `v2` observes an absent cache, then
    // `v1` installs cleanly before `v2` reaches `exocrate`; `v2` must still
    // replace `v1` via the unified `reinstall_existing` path.
    let hook_cache = temp.path().join("hook-cache");
    let v1_for_hook = v1.clone();
    let hook_cache_for_v1 = hook_cache.clone();
    let root_after_hook = install_local_with_seed_hook(
        v2.clone(),
        exocrate::Location::Custom(hook_cache.clone()),
        move || {
            install_at(
                Some(v1_for_hook),
                exocrate::Location::Custom(hook_cache_for_v1),
            )
            .expect("concurrent v1 winner succeeds");
        },
    )
    .expect("losing v2 cold caller must still apply its archive")
    .root;
    assert_eq!(
        fs::read(root_after_hook.join("marker.txt")).unwrap(),
        b"archive v2"
    );
    assert!(!root_after_hook.join(".incomplete").exists());
    assert!(!sibling_lock_path(&root_after_hook, ".incomplete").unwrap().exists());

    // Parallel two-thread cold race against the same fresh cache.
    let race_cache = temp.path().join("race-cache");
    let barrier = Arc::new(Barrier::new(2));
    let b1 = Arc::clone(&barrier);
    let b2 = Arc::clone(&barrier);
    let c1 = race_cache.clone();
    let c2 = race_cache.clone();
    let t1 = thread::spawn(move || {
        b1.wait();
        install_at(Some(v1), exocrate::Location::Custom(c1))
    });
    let t2 = thread::spawn(move || {
        b2.wait();
        install_at(Some(v2), exocrate::Location::Custom(c2))
    });
    let r1 = t1.join().unwrap().expect("thread 1 cold setup succeeds");
    let r2 = t2.join().unwrap().expect("thread 2 cold setup succeeds");
    assert_eq!(r1, r2);
    let final_marker = fs::read(r1.join("marker.txt")).expect("read winner marker");
    assert!(
        final_marker == b"archive v1" || final_marker == b"archive v2",
        "expected complete archive contents, got {final_marker:?}"
    );
    assert!(!r1.join(".incomplete").exists());
    assert!(!sibling_lock_path(&r1, ".incomplete").unwrap().exists());
    let parent = r1.parent().expect("toolchain parent");
    assert_eq!(child_dirs(parent), vec![r1.file_name().unwrap().to_os_string()]);

    // Failed cold setup on a broken archive must clean up the cold seed.
    let failed_cache = temp.path().join("failed-cold-cache");
    assert!(
        install_at(Some(corrupt), exocrate::Location::Custom(failed_cache.clone())).is_err()
    );
    assert!(
        installed_bundle_at(exocrate::Location::Custom(failed_cache))
            .expect("absent after failed cold install")
            .is_none()
    );
}

#[test]
fn incomplete_markers_fail_closed_in_discovery_and_repair_cleanly() {
    let temp = tempfile::tempdir().expect("create owned fixture");
    let v1 = temp.path().join("v1.tar.zst");
    let v2 = temp.path().join("v2.tar.zst");
    write_archive_with(&v1, b"archive v1");
    write_archive_with(&v2, b"archive v2");

    let cache = temp.path().join("cache");
    let root = install_at(Some(v1), exocrate::Location::Custom(cache.clone()))
        .expect("install v1 bundle");
    let inner_marker = root.join(".incomplete");
    let sibling_marker = sibling_lock_path(&root, ".incomplete").unwrap();

    fs::write(&inner_marker, b"").expect("create inner incomplete marker");
    let err = installed_bundle_at(exocrate::Location::Custom(cache.clone()))
        .expect_err("inner .incomplete marker must fail closed");
    assert!(err.contains("incomplete"), "{err}");
    let reuse_err = install_at_with_remote(
        None,
        exocrate::Location::Custom(cache.clone()),
        || Err("offline".into()),
    )
    .expect_err("setup reuse must reject inner .incomplete marker");
    assert!(reuse_err.contains("incomplete"), "{reuse_err}");

    fs::remove_file(&inner_marker).unwrap();
    fs::write(&sibling_marker, b"").expect("create sibling incomplete marker");
    let sib_err = installed_bundle_at(exocrate::Location::Custom(cache.clone()))
        .expect_err("sibling .incomplete marker must fail closed");
    assert!(sib_err.contains("incomplete"), "{sib_err}");
    let reuse_sib_err = install_at_with_remote(
        None,
        exocrate::Location::Custom(cache.clone()),
        || Err("offline".into()),
    )
    .expect_err("setup reuse must reject sibling .incomplete marker");
    assert!(reuse_sib_err.contains("incomplete"), "{reuse_sib_err}");

    // Explicit local setup repairs both markers and restores reuse.
    fs::write(&inner_marker, b"").unwrap();
    let repaired = install_at(Some(v2), exocrate::Location::Custom(cache.clone()))
        .expect("setup --local-archive repairs incomplete bundle");
    assert_eq!(repaired, root);
    assert!(!inner_marker.exists());
    assert!(!sibling_marker.exists());
    assert_eq!(fs::read(repaired.join("marker.txt")).unwrap(), b"archive v2");
    assert_eq!(
        install_at_with_remote(
            None,
            exocrate::Location::Custom(cache.clone()),
            || Err("offline".into()),
        )
        .expect("repaired bundle is reusable"),
        repaired
    );
    let bundle = installed_bundle_at(exocrate::Location::Custom(cache))
        .expect("repaired bundle resolves")
        .expect("repaired bundle present");
    assert_eq!(bundle.root, repaired);
}

#[test]
fn rejects_archive_containing_reserved_incomplete_marker() {
    let temp = tempfile::tempdir().expect("create owned fixture");
    let v1 = temp.path().join("v1.tar.zst");
    let reserved = temp.path().join("reserved.tar.zst");
    write_archive_with(&v1, b"archive v1");
    write_archive_entries(&reserved, &[("marker.txt", b"poison"), (".incomplete", b"")]);

    // Cold cache: reserved `.incomplete` fails closed and drops the seed.
    let cold_cache = temp.path().join("cold-cache");
    let cold_err =
        install_at(Some(reserved.clone()), exocrate::Location::Custom(cold_cache.clone()))
            .expect_err("cold install must reject archive with top-level .incomplete");
    assert!(cold_err.contains(".incomplete"), "{cold_err}");
    assert!(
        installed_bundle_at(exocrate::Location::Custom(cold_cache.clone()))
            .expect("absent after rejected cold install")
            .is_none()
    );
    let resolved_err = CONFIG
        .resolve_installation_dir(exocrate::Location::Custom(cold_cache.clone()))
        .expect_err("rejected cold install must leave no version directory");
    assert_eq!(resolved_err.kind(), io::ErrorKind::NotFound);

    // Warm cache: reserved `.incomplete` fails closed before moving `v1`.
    let warm_cache = temp.path().join("warm-cache");
    let root = install_at(Some(v1), exocrate::Location::Custom(warm_cache.clone()))
        .expect("install v1 bundle");
    let warm_err = install_at(Some(reserved), exocrate::Location::Custom(warm_cache.clone()))
        .expect_err("warm reinstall must reject archive with top-level .incomplete");
    assert!(warm_err.contains(".incomplete"), "{warm_err}");
    assert_eq!(fs::read(root.join("marker.txt")).unwrap(), b"archive v1");
    assert!(!root.join(".incomplete").exists());
    assert!(!sibling_lock_path(&root, ".incomplete").unwrap().exists());
    let bundle = installed_bundle_at(exocrate::Location::Custom(warm_cache))
        .expect("warm bundle stays valid")
        .expect("warm bundle remains present");
    assert_eq!(bundle.root, root);
    assert_eq!(
        child_dirs(root.parent().expect("toolchain parent")),
        vec![root.file_name().unwrap().to_os_string()]
    );
}

#[test]
fn reinstall_only_if_incomplete_reuses_complete_install_without_overwriting() {
    let temp = tempfile::tempdir().expect("create owned fixture");
    let v1 = temp.path().join("v1.tar.zst");
    let v2 = temp.path().join("v2.tar.zst");
    let missing = temp.path().join("missing.tar.zst");
    write_archive_with(&v1, b"archive v1");
    write_archive_with(&v2, b"archive v2");

    let cache = temp.path().join("cache");
    let root =
        install_at(Some(v1), exocrate::Location::Custom(cache)).expect("install v1 bundle");

    // When already complete, `reinstall_only_if_incomplete = true` returns
    // a leased bundle before touching or even opening `source`.
    let reused_missing = reinstall_existing(&root, exocrate::Source::Local(missing), true)
        .expect("complete bundle skips opening source");
    assert_eq!(reused_missing.root, root);
    assert!(matches!(
        try_remove_old_toolchain(&root).expect("probe leased reused bundle"),
        RemoveOldOutcome::Busy
    ));
    drop(reused_missing);
    let reused_v2 = reinstall_existing(&root, exocrate::Source::Local(v2.clone()), true)
        .expect("complete bundle is reused without overwriting");
    assert_eq!(reused_v2.root, root);
    drop(reused_v2);
    assert_eq!(fs::read(root.join("marker.txt")).unwrap(), b"archive v1");

    // Negative controls: incomplete marker or absent dir still installs
    // `v2`.
    let sibling_marker = sibling_lock_path(&root, ".incomplete").unwrap();
    fs::write(&sibling_marker, b"").expect("mark bundle incomplete");
    let repaired = reinstall_existing(&root, exocrate::Source::Local(v2.clone()), true)
        .expect("incomplete bundle is repaired");
    assert_eq!(repaired.root, root);
    drop(repaired);
    assert_eq!(fs::read(root.join("marker.txt")).unwrap(), b"archive v2");
    assert!(!sibling_marker.exists());

    fs::remove_dir_all(&root).expect("remove directory before retry");
    let recreated = reinstall_existing(&root, exocrate::Source::Local(v2), true)
        .expect("absent directory is not treated as complete");
    assert_eq!(recreated.root, root);
    drop(recreated);
    assert_eq!(fs::read(root.join("marker.txt")).unwrap(), b"archive v2");
}

#[test]
fn clear_old_removes_unlocked_old_dirs_and_preserves_current_staging_and_files() {
    let temp = tempfile::tempdir().expect("create owned fixture");
    let archive = temp.path().join("v1.tar.zst");
    write_archive_with(&archive, b"current toolchain");

    let cache = temp.path().join("cache");
    let current = install_at(Some(archive.clone()), exocrate::Location::Custom(cache.clone()))
        .expect("install current toolchain");
    let parent = current.parent().expect("toolchain parent");

    // Control: no old directories -> silent output and prompt never called.
    let mut out = Vec::new();
    let (root_empty, report_empty) = install_at_with_prune(
        Some(archive.clone()),
        exocrate::Location::Custom(cache.clone()),
        PruneMode::Interactive,
        |_, _| panic!("prompt must not run when no old toolchains exist"),
        &mut out,
    )
    .expect("reinstall with no old dirs");
    assert_eq!(root_empty, current);
    assert_eq!(report_empty, PruneReport::default());
    assert!(out.is_empty(), "unexpected output: {}", String::from_utf8_lossy(&out));

    // Populate two old toolchain directories (including a read-only subdir
    // on Unix) plus sibling lock/incomplete markers, internal temp dirs,
    // and an unrelated regular file.
    let old_v1 = parent.join("0.1.0-old");
    let old_v2 = parent.join("0.2.0-old");
    fs::create_dir_all(old_v1.join("readonly")).unwrap();
    fs::write(old_v1.join("readonly/file.txt"), b"old v1").unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        fs::set_permissions(old_v1.join("readonly"), fs::Permissions::from_mode(0o555))
            .unwrap();
    }
    fs::create_dir_all(&old_v2).unwrap();
    fs::write(old_v2.join("marker.txt"), b"old v2").unwrap();
    for old in [&old_v1, &old_v2] {
        for suffix in [".lock", ".reinstall.lock", ".incomplete"] {
            fs::write(sibling_lock_path(old, suffix).unwrap(), b"").unwrap();
        }
    }
    let staging_dir = parent.join(".staging-in-flight");
    let backup_dir = parent.join(".backup-in-flight");
    let exocrate_staging = parent.join("0.3.0-cold.staging");
    let exocrate_staging_with_lock = parent.join("0.3.1-cold.staging");
    let unmanaged_dir = parent.join("unmanaged-user-dir");
    let sibling_file = parent.join("notes.txt");
    fs::create_dir_all(&staging_dir).unwrap();
    fs::create_dir_all(&backup_dir).unwrap();
    fs::create_dir_all(&exocrate_staging).unwrap();
    fs::create_dir_all(&exocrate_staging_with_lock).unwrap();
    fs::write(sibling_lock_path(&exocrate_staging_with_lock, ".lock").unwrap(), b"").unwrap();
    fs::create_dir_all(&unmanaged_dir).unwrap();
    fs::write(&sibling_file, b"keep").unwrap();

    let mut out = Vec::new();
    let (root, report) = install_at_with_prune(
        Some(archive),
        exocrate::Location::Custom(cache),
        PruneMode::ClearOld,
        |_, _| panic!("--clear-old must not prompt"),
        &mut out,
    )
    .expect("install with --clear-old");
    assert_eq!(root, current);
    assert_eq!(report.found, vec![old_v1.clone(), old_v2.clone()]);
    assert_eq!(report.removed, vec![old_v1.clone(), old_v2.clone()]);
    assert!(report.skipped_busy.is_empty(), "{report:?}");
    assert!(report.warnings.is_empty(), "{report:?}");
    let output = String::from_utf8(out).unwrap();
    assert!(output.contains(&format!("Removed old Anneal toolchain at {}", old_v1.display())));
    assert!(output.contains(&format!("Removed old Anneal toolchain at {}", old_v2.display())));

    for old in [&old_v1, &old_v2] {
        assert!(!old.exists(), "old dir still present: {}", old.display());
        assert!(
            !sibling_lock_path(old, ".incomplete").unwrap().exists(),
            ".incomplete marker still present for {}",
            old.display()
        );
        // Leave lock files in place so mutual exclusion never splits.
        assert!(sibling_lock_path(old, ".lock").unwrap().is_file());
        assert!(sibling_lock_path(old, ".reinstall.lock").unwrap().is_file());
    }
    assert!(current.is_dir());
    assert_eq!(fs::read(current.join("marker.txt")).unwrap(), b"current toolchain");
    assert!(sibling_lock_path(&current, ".lock").unwrap().is_file());
    assert!(staging_dir.is_dir());
    assert!(backup_dir.is_dir());
    assert!(exocrate_staging.is_dir());
    assert!(exocrate_staging_with_lock.is_dir());
    assert!(unmanaged_dir.is_dir());
    assert!(!sibling_lock_path(&unmanaged_dir, ".lock").unwrap().exists());
    assert_eq!(fs::read(&sibling_file).unwrap(), b"keep");
}
