// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Tests: `--clear-old` pruning of old toolchain versions.

use std::{fs, io};

use super::*;

#[test]
fn clear_old_skips_busy_locked_old_dirs_and_prunes_unlocked_peers() {
    let temp = tempfile::tempdir().expect("create owned fixture");
    let archive = temp.path().join("v1.tar.zst");
    write_archive_with(&archive, b"current toolchain");

    let cache = temp.path().join("cache");
    let current = install_at(Some(archive.clone()), exocrate::Location::Custom(cache.clone()))
        .expect("install current toolchain");
    let parent = current.parent().expect("toolchain parent");

    let old_busy_reinstall = parent.join("0.1.0-busy-reinstall");
    let old_busy_shared = parent.join("0.1.1-busy-shared");
    let old_idle = parent.join("0.1.2-idle");
    for dir in [&old_busy_reinstall, &old_busy_shared, &old_idle] {
        fs::create_dir_all(dir).unwrap();
        fs::write(dir.join("marker.txt"), b"old").unwrap();
        fs::write(sibling_lock_path(dir, ".lock").unwrap(), b"").unwrap();
    }
    // Simulate an active exocrate 0.3.0 cold install: `<slug>.staging/`
    // populated while `<slug>.lock` is held exclusively.
    let cold_install_staging = parent.join("0.1.3-cold-install.staging");
    fs::create_dir_all(&cold_install_staging).unwrap();
    fs::write(cold_install_staging.join("extracting.txt"), b"in flight").unwrap();
    let cold_install_lock =
        open_exclusive_lock(&parent.join("0.1.3-cold-install.lock")).expect("lock cold slug");

    // Hold an active shared `.lock` (simulating `verify`) without creating
    // `.reinstall.lock`, and hold an exclusive `.reinstall.lock` on another
    // old dir (simulating a concurrent `setup --local-archive`).
    let shared_lock = fs::File::open(sibling_lock_path(&old_busy_shared, ".lock").unwrap())
        .expect("open shared lock");
    shared_lock.lock_shared().expect("acquire shared lock");
    let reinstall_lock = open_exclusive_lock(
        &sibling_lock_path(&old_busy_reinstall, ".reinstall.lock").unwrap(),
    )
    .expect("acquire reinstall lock");

    let mut out = Vec::new();
    let (root, report) = install_at_with_prune(
        Some(archive),
        exocrate::Location::Custom(cache),
        PruneMode::ClearOld,
        |_, _| panic!("--clear-old must not prompt"),
        &mut out,
    )
    .expect("busy locks must not fail current installation");
    assert_eq!(root, current);
    assert_eq!(
        report.found,
        vec![old_busy_reinstall.clone(), old_busy_shared.clone(), old_idle.clone()]
    );
    assert_eq!(report.removed, vec![old_idle.clone()]);
    assert_eq!(report.skipped_busy, vec![old_busy_reinstall.clone(), old_busy_shared.clone()]);
    assert_eq!(report.warnings.len(), 2, "{report:?}");

    assert!(!old_idle.exists());
    assert!(sibling_lock_path(&old_idle, ".lock").unwrap().is_file());
    assert!(old_busy_shared.is_dir());
    assert!(
        !sibling_lock_path(&old_busy_shared, ".reinstall.lock").unwrap().exists(),
        "busy shared lock must skip without creating a stray .reinstall.lock"
    );
    assert!(old_busy_reinstall.is_dir());
    assert!(cold_install_staging.is_dir());
    assert_eq!(fs::read(cold_install_staging.join("extracting.txt")).unwrap(), b"in flight");
    assert!(!sibling_lock_path(&cold_install_staging, ".lock").unwrap().exists());
    let output = String::from_utf8(out).unwrap();
    assert!(output.contains("warning: skipping old Anneal toolchain"), "{output}");

    drop(cold_install_lock);
    drop(shared_lock);
    drop(reinstall_lock);
}

#[cfg(unix)]
#[test]
fn clear_old_never_follows_or_deletes_symlinks_in_parent_or_locks() {
    use std::os::unix::fs::symlink;

    let temp = tempfile::tempdir().expect("create owned fixture");
    let archive = temp.path().join("v1.tar.zst");
    write_archive_with(&archive, b"current toolchain");

    let cache = temp.path().join("cache");
    let current = install_at(Some(archive.clone()), exocrate::Location::Custom(cache.clone()))
        .expect("install current toolchain");
    let parent = current.parent().expect("toolchain parent");

    let outside_dir = temp.path().join("outside-dir");
    fs::create_dir_all(&outside_dir).unwrap();
    let outside_file = outside_dir.join("keep.txt");
    fs::write(&outside_file, b"must survive").unwrap();

    // 1. Top-level symlink directory in `parent` must be ignored.
    let top_symlink = parent.join("0.1.0-symlink");
    symlink(&outside_dir, &top_symlink).unwrap();
    fs::write(sibling_lock_path(&top_symlink, ".lock").unwrap(), b"").unwrap();

    // 2. Old directory containing an internal symlink to `outside_dir` must
    //    unlink only the inner symlink without touching `outside_dir`.
    let old_inner_sym = parent.join("0.1.1-inner-sym");
    fs::create_dir_all(&old_inner_sym).unwrap();
    fs::write(sibling_lock_path(&old_inner_sym, ".lock").unwrap(), b"").unwrap();
    symlink(&outside_dir, old_inner_sym.join("ext-link")).unwrap();

    // 3. Old directory whose sibling `.lock` is a symlink must fail closed
    //    with a warning without removing the dir or following the lock.
    let old_sym_lock = parent.join("0.1.2-sym-lock");
    fs::create_dir_all(&old_sym_lock).unwrap();
    fs::write(old_sym_lock.join("marker.txt"), b"keep").unwrap();
    let outside_lock_target = temp.path().join("outside-lock-target.txt");
    fs::write(&outside_lock_target, b"untouched").unwrap();
    symlink(&outside_lock_target, sibling_lock_path(&old_sym_lock, ".lock").unwrap()).unwrap();

    // 4. Old directory whose `.incomplete` marker is a symlink must fail
    //    closed without truncating the target or deleting the directory.
    let old_sym_incomplete = parent.join("0.1.3-sym-incomplete");
    fs::create_dir_all(&old_sym_incomplete).unwrap();
    fs::write(old_sym_incomplete.join("marker.txt"), b"keep").unwrap();
    fs::write(sibling_lock_path(&old_sym_incomplete, ".lock").unwrap(), b"").unwrap();
    let outside_marker_target = temp.path().join("outside-marker-target.txt");
    fs::write(&outside_marker_target, b"untouched-marker").unwrap();
    symlink(
        &outside_marker_target,
        sibling_lock_path(&old_sym_incomplete, ".incomplete").unwrap(),
    )
    .unwrap();

    let mut out = Vec::new();
    let (root, report) = install_at_with_prune(
        Some(archive),
        exocrate::Location::Custom(cache),
        PruneMode::ClearOld,
        |_, _| panic!("--clear-old must not prompt"),
        &mut out,
    )
    .expect("symlink warnings must not fail current installation");
    assert_eq!(root, current);
    assert_eq!(report.found, vec![old_inner_sym.clone(), old_sym_incomplete.clone()]);
    assert_eq!(report.removed, vec![old_inner_sym.clone()]);
    assert_eq!(report.warnings.len(), 2, "{report:?}");
    assert!(report.warnings.iter().all(|w| w.contains("symlink")), "{report:?}");

    assert!(fs::symlink_metadata(&top_symlink).unwrap().file_type().is_symlink());
    assert!(!old_inner_sym.exists());
    assert!(old_sym_lock.is_dir());
    assert!(old_sym_incomplete.is_dir());
    assert_eq!(fs::read(&outside_file).unwrap(), b"must survive");
    assert_eq!(fs::read(&outside_lock_target).unwrap(), b"untouched");
    assert_eq!(fs::read(&outside_marker_target).unwrap(), b"untouched-marker");
}

#[test]
fn prune_interactive_prompt_and_non_tty_note_behave_as_documented() {
    let temp = tempfile::tempdir().expect("create owned fixture");
    let archive = temp.path().join("v1.tar.zst");
    write_archive_with(&archive, b"current toolchain");

    let cache = temp.path().join("cache");
    let current = install_at(Some(archive.clone()), exocrate::Location::Custom(cache.clone()))
        .expect("install current toolchain");
    let parent = current.parent().expect("toolchain parent");
    let old_v1 = parent.join("0.1.0-old");
    fs::create_dir_all(&old_v1).unwrap();
    fs::write(old_v1.join("marker.txt"), b"old").unwrap();
    fs::write(sibling_lock_path(&old_v1, ".lock").unwrap(), b"").unwrap();
    let unmanaged = parent.join("not-a-toolchain");
    fs::create_dir_all(&unmanaged).unwrap();

    // Direct prompt parser/stream tests.
    for (input, expected) in
        [("y\n", true), ("YES\r\n", true), ("n\n", false), ("\n", false), ("", false)]
    {
        let mut reader = io::Cursor::new(input.as_bytes());
        let mut writer = Vec::new();
        let confirmed =
            prompt_on_streams(parent, std::slice::from_ref(&old_v1), &mut reader, &mut writer)
                .expect("prompt streams");
        assert_eq!(confirmed, expected, "input={input:?}");
        let prompt_text = String::from_utf8(writer).unwrap();
        assert!(prompt_text.contains(&old_v1.display().to_string()), "{prompt_text}");
        assert!(prompt_text.contains("[y/N]"), "{prompt_text}");
    }

    // Non-TTY mode emits a concise note and leaves the old dir untouched.
    let mut out = Vec::new();
    let (_, non_tty) = install_at_with_prune(
        Some(archive.clone()),
        exocrate::Location::Custom(cache.clone()),
        PruneMode::NonInteractive,
        |_, _| panic!("non-TTY mode must never prompt"),
        &mut out,
    )
    .expect("non-TTY setup");
    assert_eq!(non_tty.found, vec![old_v1.clone()]);
    assert!(non_tty.removed.is_empty());
    assert!(old_v1.is_dir());
    let note = String::from_utf8(out).unwrap();
    assert!(note.contains("found 1 old cached Anneal toolchain"), "{note}");
    assert!(note.contains("--clear-old"), "{note}");

    // Interactive decline (`n` / empty) keeps the old dir without warnings.
    let mut out = Vec::new();
    let (_, declined) = install_at_with_prune(
        Some(archive.clone()),
        exocrate::Location::Custom(cache.clone()),
        PruneMode::Interactive,
        |seen_parent, seen_dirs| {
            assert_eq!(seen_parent, parent);
            assert_eq!(seen_dirs, std::slice::from_ref(&old_v1));
            Ok(false)
        },
        &mut out,
    )
    .expect("interactive decline");
    assert_eq!(declined.found, vec![old_v1.clone()]);
    assert!(declined.removed.is_empty());
    assert!(declined.warnings.is_empty());
    assert!(old_v1.is_dir());
    assert!(out.is_empty());

    // Interactive prompt I/O failure warns cleanly and preserves `current`.
    let mut out = Vec::new();
    let (_, prompt_err) = install_at_with_prune(
        Some(archive.clone()),
        exocrate::Location::Custom(cache.clone()),
        PruneMode::Interactive,
        |_, _| Err(io::Error::new(io::ErrorKind::BrokenPipe, "stdin closed")),
        &mut out,
    )
    .expect("prompt I/O failure must not fail setup");
    assert!(prompt_err.removed.is_empty());
    assert_eq!(prompt_err.warnings.len(), 1);
    assert!(old_v1.is_dir());

    // Interactive acceptance (`y`) deletes the old dir.
    let mut out = Vec::new();
    let (_, accepted) = install_at_with_prune(
        Some(archive),
        exocrate::Location::Custom(cache),
        PruneMode::Interactive,
        |_, _| Ok(true),
        &mut out,
    )
    .expect("interactive accept");
    assert_eq!(accepted.removed, vec![old_v1.clone()]);
    assert!(!old_v1.exists());
    assert!(unmanaged.is_dir());
    assert!(String::from_utf8(out).unwrap().contains("Removed old Anneal toolchain at"));
}

#[test]
fn install_at_with_prune_holds_shared_lease_on_current_root_throughout_pruning() {
    let temp = tempfile::tempdir().expect("create owned fixture");
    let archive = temp.path().join("v1.tar.zst");
    write_archive_with(&archive, b"current toolchain");

    let cache = temp.path().join("cache");
    let current = install_at(Some(archive.clone()), exocrate::Location::Custom(cache.clone()))
        .expect("install current toolchain");
    let parent = current.parent().expect("toolchain parent");
    let old_v1 = parent.join("0.1.0-old");
    fs::create_dir_all(&old_v1).unwrap();
    fs::write(old_v1.join("marker.txt"), b"old").unwrap();
    fs::write(sibling_lock_path(&old_v1, ".lock").unwrap(), b"").unwrap();

    // Local-archive install path: while pruning is in progress, a
    // concurrent pruner must see `current` as busy, while a concurrent
    // `verify` reader can still acquire a shared lease without blocking.
    let mut out = Vec::new();
    let (root_local, _) = install_at_with_prune(
        Some(archive),
        exocrate::Location::Custom(cache.clone()),
        PruneMode::Interactive,
        |_, _| {
            assert!(matches!(
                try_remove_old_toolchain(&current).expect("probe current during local prune"),
                RemoveOldOutcome::Busy
            ));
            assert!(current.is_dir());
            let reader = installed_bundle_at(exocrate::Location::Custom(cache.clone()))
                .expect("shared reader must not fail during prune")
                .expect("current bundle present during prune");
            assert_eq!(reader.root, current);
            drop(reader);
            assert!(matches!(
                open_try_exclusive_lock(
                    &sibling_lock_path(&current, ".reinstall.lock").unwrap(),
                    false,
                )
                .expect("probe reinstall lock"),
                Some(TryLockOutcome::Acquired(_))
            ));
            Ok(false)
        },
        &mut out,
    )
    .expect("local install with prune");
    assert_eq!(root_local, current);
    assert!(matches!(
        open_try_exclusive_lock(&sibling_lock_path(&current, ".lock").unwrap(), false)
            .expect("lease released after local prune"),
        Some(TryLockOutcome::Acquired(_))
    ));

    // Cached reuse (`None`) path: also holds the shared lease throughout
    // pruning and releases it cleanly upon return.
    let mut out = Vec::new();
    let (root_reuse, report_reuse) = install_at_with_prune(
        None,
        exocrate::Location::Custom(cache.clone()),
        PruneMode::Interactive,
        |_, _| {
            assert!(matches!(
                try_remove_old_toolchain(&current).expect("probe current during reuse prune"),
                RemoveOldOutcome::Busy
            ));
            Ok(true)
        },
        &mut out,
    )
    .expect("reuse install with prune");
    assert_eq!(root_reuse, current);
    assert_eq!(report_reuse.removed, vec![old_v1.clone()]);
    assert!(!old_v1.exists());
    assert!(current.is_dir());
    assert_eq!(fs::read(current.join("marker.txt")).unwrap(), b"current toolchain");
    assert!(matches!(
        open_try_exclusive_lock(&sibling_lock_path(&current, ".lock").unwrap(), false)
            .expect("lease released after reuse prune"),
        Some(TryLockOutcome::Acquired(_))
    ));
}

#[test]
fn concurrent_different_version_prunes_protect_each_others_roots() {
    use std::{sync::mpsc, thread, time::Duration};

    let temp = tempfile::tempdir().expect("create owned fixture");
    let archive = temp.path().join("v1.tar.zst");
    write_archive_with(&archive, b"version a");

    let cache = temp.path().join("cache");
    let current_a =
        install_at(Some(archive.clone()), exocrate::Location::Custom(cache.clone()))
            .expect("install version a");
    let parent = current_a.parent().expect("toolchain parent").to_path_buf();

    // Populate a concurrent second version root (`current_b`) and an
    // unlocked obsolete directory (`old_c`) in the shared cache parent.
    let current_b = parent.join("0.2.0-concurrent-b");
    let old_c = parent.join("0.0.1-obsolete");
    fs::create_dir_all(&current_b).unwrap();
    fs::write(current_b.join("marker.txt"), b"version b").unwrap();
    fs::write(sibling_lock_path(&current_b, ".lock").unwrap(), b"").unwrap();
    fs::create_dir_all(&old_c).unwrap();
    fs::write(old_c.join("marker.txt"), b"obsolete").unwrap();
    fs::write(sibling_lock_path(&old_c, ".lock").unwrap(), b"").unwrap();

    let (a_in_prune_tx, a_in_prune_rx) = mpsc::channel();
    let (b_pruned_tx, b_pruned_rx) = mpsc::channel();
    let (a_done_tx, a_done_rx) = mpsc::channel();

    let current_b_for_thread = current_b.clone();
    let thread_b = thread::spawn(move || {
        let bundle_b = acquire_bundle_lease(&current_b_for_thread)
            .map_err(AcquireLeaseError::into_message)
            .expect("acquire shared lease on version b");
        a_in_prune_rx
            .recv_timeout(Duration::from_secs(10))
            .expect("version a entered pruning pass");
        let mut out_b = Vec::new();
        let report_b = prune_old_toolchains_with(
            &bundle_b.root,
            PruneMode::ClearOld,
            |_, _| panic!("--clear-old must not prompt"),
            &mut out_b,
        );
        b_pruned_tx.send(()).unwrap();
        // Keep version b's lease alive until version a finishes pruning.
        a_done_rx
            .recv_timeout(Duration::from_secs(10))
            .expect("version a finished pruning pass");
        drop(bundle_b);
        report_b
    });

    let mut out_a = Vec::new();
    let (returned_a, report_a) = install_at_with_prune(
        Some(archive),
        exocrate::Location::Custom(cache.clone()),
        PruneMode::Interactive,
        |_, _| {
            a_in_prune_tx.send(()).unwrap();
            b_pruned_rx
                .recv_timeout(Duration::from_secs(10))
                .expect("version b completed pruning pass");
            Ok(true)
        },
        &mut out_a,
    )
    .expect("version a setup with prune");
    a_done_tx.send(()).unwrap();
    let report_b = thread_b.join().unwrap();

    assert_eq!(returned_a, current_a);
    assert_eq!(report_b.skipped_busy, vec![current_a.clone()]);
    assert_eq!(report_b.removed, vec![old_c.clone()]);
    assert_eq!(report_a.skipped_busy, vec![current_b.clone()]);
    assert!(report_a.removed.is_empty(), "{report_a:?}");

    assert!(!old_c.exists());
    assert_eq!(fs::read(current_a.join("marker.txt")).unwrap(), b"version a");
    assert_eq!(fs::read(current_b.join("marker.txt")).unwrap(), b"version b");
    assert!(acquire_bundle_lease(&current_a).is_ok());
    assert!(acquire_bundle_lease(&current_b).is_ok());

    // Verify `acquire_bundle_lease` classifies missing/incomplete dirs as
    // recoverable and symlinked `.lock` files as fatal.
    fs::remove_dir_all(&current_b).unwrap();
    assert!(matches!(
        acquire_bundle_lease(&current_b),
        Err(AcquireLeaseError::MissingOrIncomplete(_))
    ));
    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        let sym_lock_dir = parent.join("0.3.0-sym-lock");
        fs::create_dir_all(&sym_lock_dir).unwrap();
        let outside = temp.path().join("outside.lock");
        fs::write(&outside, b"").unwrap();
        symlink(&outside, sibling_lock_path(&sym_lock_dir, ".lock").unwrap()).unwrap();
        assert!(matches!(
            acquire_bundle_lease(&sym_lock_dir),
            Err(AcquireLeaseError::Fatal(msg)) if msg.contains("symlink")
        ));
    }
}

#[test]
fn install_from_source_repairs_incomplete_dir_without_lock_and_fails_closed_otherwise() {
    let temp = tempfile::tempdir().expect("create owned fixture");
    let v1 = temp.path().join("v1.tar.zst");
    let v2 = temp.path().join("v2.tar.zst");
    write_archive_with(&v1, b"archive v1");
    write_archive_with(&v2, b"archive v2");

    // Cold install via `install_from_source` returns a leased `Bundle`.
    let cache = temp.path().join("cache");
    let cold_bundle = install_from_source(
        || Ok(exocrate::Source::Local(v1.clone())),
        exocrate::Location::Custom(cache.clone()),
    )
    .expect("cold install_from_source succeeds");
    let root = cold_bundle.root.clone();
    assert!(matches!(
        try_remove_old_toolchain(&root).expect("probe leased cold bundle"),
        RemoveOldOutcome::Busy
    ));
    drop(cold_bundle);
    assert_eq!(fs::read(root.join("marker.txt")).unwrap(), b"archive v1");

    let lock_path = sibling_lock_path(&root, ".lock").unwrap();
    let inner_marker = root.join(".incomplete");
    let sibling_marker = sibling_lock_path(&root, ".incomplete").unwrap();

    // Incomplete directory (inner `.incomplete`) with missing `.lock` must
    // repair cleanly, recreate `.lock`, clear `.incomplete`, and return a
    // leased `Bundle`.
    fs::write(&inner_marker, b"").expect("create inner incomplete marker");
    fs::remove_file(&lock_path).expect("remove sibling .lock");
    let repaired_inner = install_from_source(
        || Ok(exocrate::Source::Local(v2.clone())),
        exocrate::Location::Custom(cache.clone()),
    )
    .expect("incomplete dir without .lock must repair");
    assert_eq!(repaired_inner.root, root);
    assert!(matches!(
        try_remove_old_toolchain(&root).expect("probe repaired inner bundle"),
        RemoveOldOutcome::Busy
    ));
    drop(repaired_inner);
    assert!(lock_path.is_file());
    assert!(!inner_marker.exists());
    assert_eq!(fs::read(root.join("marker.txt")).unwrap(), b"archive v2");

    // Incomplete directory (sibling `.incomplete`) with missing `.lock`
    // must also repair cleanly and recreate `.lock`.
    fs::write(&sibling_marker, b"").expect("create sibling incomplete marker");
    fs::remove_file(&lock_path).expect("remove sibling .lock");
    let repaired_sibling = install_from_source(
        || Ok(exocrate::Source::Local(v1.clone())),
        exocrate::Location::Custom(cache.clone()),
    )
    .expect("sibling-incomplete dir without .lock must repair");
    assert_eq!(repaired_sibling.root, root);
    assert!(matches!(
        try_remove_old_toolchain(&root).expect("probe repaired sibling bundle"),
        RemoveOldOutcome::Busy
    ));
    drop(repaired_sibling);
    assert!(lock_path.is_file());
    assert!(!sibling_marker.exists());
    assert_eq!(fs::read(root.join("marker.txt")).unwrap(), b"archive v1");

    // Complete directory without `.lock` must fail closed without
    // overwriting the existing installation.
    fs::remove_file(&lock_path).expect("remove sibling .lock on complete dir");
    let complete_err = install_from_source(
        || Ok(exocrate::Source::Local(v2.clone())),
        exocrate::Location::Custom(cache.clone()),
    )
    .expect_err("complete dir without .lock must fail closed");
    assert!(complete_err.contains("cannot open toolchain lock"), "{complete_err}");
    assert_eq!(fs::read(root.join("marker.txt")).unwrap(), b"archive v1");
    assert!(!lock_path.exists());

    // Incomplete directory with a symlinked `.lock` must still fail closed
    // without following or overwriting the symlink target.
    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        fs::write(&inner_marker, b"").expect("create inner incomplete marker");
        let outside_target = temp.path().join("outside-lock.txt");
        fs::write(&outside_target, b"untouched").unwrap();
        symlink(&outside_target, &lock_path).unwrap();
        let sym_err = install_from_source(
            || Ok(exocrate::Source::Local(v2.clone())),
            exocrate::Location::Custom(cache),
        )
        .expect_err("symlinked .lock on incomplete dir must fail closed");
        assert!(sym_err.contains("symlink"), "{sym_err}");
        assert_eq!(fs::read(&outside_target).unwrap(), b"untouched");
        assert_eq!(fs::read(root.join("marker.txt")).unwrap(), b"archive v1");
    }
}
