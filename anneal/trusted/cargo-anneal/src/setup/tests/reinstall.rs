// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Tests: Local-archive installs, reinstalls, and shared bundle leases.

use std::{
    fs, io,
    path::{Path, PathBuf},
};

use super::*;

#[test]
fn setup_reuses_a_locally_installed_toolchain() {
    let temp = tempfile::tempdir().expect("create owned fixture");
    let archive = temp.path().join("toolchain.tar.zst");
    write_archive(&archive);
    let cache = temp.path().join("cache");
    let installed = install_at(
        Some(archive.clone()),
        exocrate::Location::Custom(cache.clone()),
    )
    .expect("install local archive");
    fs::remove_file(archive).expect("remove original archive");

    assert_eq!(
        install_at(None, exocrate::Location::Custom(cache))
            .expect("reuse the installed toolchain"),
        installed
    );
    if let Err(reason) = remote_archive() {
        let fresh = exocrate::Location::Custom(temp.path().join("fresh-cache"));
        assert_eq!(install_at(None, fresh), Err(reason));
    }
}

#[test]
fn explicit_local_archive_reinstalls_and_preserves_existing_on_failure() {
    let temp = tempfile::tempdir().expect("create owned fixture");
    let v1 = temp.path().join("v1.tar.zst");
    let v2 = temp.path().join("v2.tar.zst");
    let corrupt = temp.path().join("corrupt.tar.zst");
    let missing = temp.path().join("missing.tar.zst");
    write_archive_with(&v1, b"archive v1");
    write_archive_with(&v2, b"archive v2");
    fs::write(&corrupt, b"not valid zstd").expect("write corrupt archive");

    let cache = temp.path().join("cache");
    let root_v1 = install_at(Some(v1), exocrate::Location::Custom(cache.clone()))
        .expect("install v1 archive");
    assert_eq!(fs::read(root_v1.join("marker.txt")).unwrap(), b"archive v1");

    let root_v2 = install_at(Some(v2), exocrate::Location::Custom(cache.clone()))
        .expect("reinstall v2 archive");
    assert_eq!(root_v2, root_v1);
    assert_eq!(fs::read(root_v2.join("marker.txt")).unwrap(), b"archive v2");
    assert_eq!(
        install_at(None, exocrate::Location::Custom(cache.clone()))
            .expect("resolve reinstalled v2 toolchain"),
        root_v2
    );

    let toolchain_parent = root_v2.parent().expect("toolchain parent dir");
    assert_eq!(
        child_dirs(toolchain_parent),
        vec![root_v2.file_name().unwrap().to_os_string()]
    );

    for bad in [&missing, &corrupt] {
        let err = install_at(Some(bad.clone()), exocrate::Location::Custom(cache.clone()))
            .expect_err("broken reinstall must fail closed");
        assert!(err.contains("failed to install Anneal toolchain:"), "{err}");
        assert_eq!(
            fs::read(root_v2.join("marker.txt")).unwrap(),
            b"archive v2",
            "existing installation must stay intact when {bad:?} fails"
        );
        assert_eq!(
            child_dirs(toolchain_parent),
            vec![root_v2.file_name().unwrap().to_os_string()]
        );
    }
}

#[cfg(unix)]
fn write_readonly_dir_archive(path: &Path, marker: &[u8]) {
    let file = fs::File::create(path).expect("create archive");
    let encoder = zstd::Encoder::new(file, 1).expect("create compressor");
    let mut archive = tar::Builder::new(encoder);

    let mut dir_header = tar::Header::new_gnu();
    dir_header.set_entry_type(tar::EntryType::Directory);
    dir_header.set_size(0);
    dir_header.set_mode(0o555);
    dir_header.set_cksum();
    archive
        .append_data(&mut dir_header, "ro_dir", io::empty())
        .expect("write readonly directory header");

    let mut file_header = tar::Header::new_gnu();
    file_header.set_size(marker.len() as u64);
    file_header.set_mode(0o444);
    file_header.set_cksum();
    archive
        .append_data(&mut file_header, "ro_dir/marker.txt", marker)
        .expect("write readonly marker header");

    archive
        .into_inner()
        .expect("finish tar archive")
        .finish()
        .expect("finish compressed archive");
}

#[cfg(unix)]
#[test]
fn explicit_local_archive_reinstalls_readonly_directories_cleanly() {
    use std::os::unix::fs::PermissionsExt;

    let temp = tempfile::tempdir().expect("create owned fixture");
    let v1 = temp.path().join("v1.tar.zst");
    let v2 = temp.path().join("v2.tar.zst");
    write_readonly_dir_archive(&v1, b"readonly v1");
    write_readonly_dir_archive(&v2, b"readonly v2");

    let cache = temp.path().join("cache");
    let root_v1 = install_at(Some(v1), exocrate::Location::Custom(cache.clone()))
        .expect("install archive containing 0o555 dir");
    assert_eq!(
        fs::symlink_metadata(root_v1.join("ro_dir"))
            .unwrap()
            .permissions()
            .mode()
            & 0o700,
        0o700,
        "initial install normalizes staged archive directories"
    );
    // Simulate an unnormalized read-only directory from an earlier
    // installation and verify pre-commit normalization replaces it cleanly.
    fs::set_permissions(root_v1.join("ro_dir"), fs::Permissions::from_mode(0o555))
        .expect("mark installed subdirectory 0o555");
    assert_eq!(
        fs::symlink_metadata(root_v1.join("ro_dir"))
            .unwrap()
            .permissions()
            .mode()
            & 0o777,
        0o555
    );
    assert_eq!(
        fs::symlink_metadata(root_v1.join("ro_dir/marker.txt"))
            .unwrap()
            .permissions()
            .mode()
            & 0o777,
        0o444
    );

    let root_v2 = install_at(Some(v2), exocrate::Location::Custom(cache))
        .expect("reinstall over 0o555 directory must succeed cleanly");
    assert_eq!(root_v2, root_v1);
    assert_eq!(
        fs::read(root_v2.join("ro_dir/marker.txt")).unwrap(),
        b"readonly v2"
    );
    assert_eq!(
        fs::symlink_metadata(root_v2.join("ro_dir"))
            .unwrap()
            .permissions()
            .mode()
            & 0o700,
        0o700,
        "staged directories must be normalized to owner-writable"
    );
    let parent = root_v2.parent().expect("toolchain parent dir");
    assert_eq!(
        child_dirs(parent),
        vec![root_v2.file_name().unwrap().to_os_string()]
    );
}

#[cfg(unix)]
#[test]
fn reinstall_rejects_symlink_and_non_directory_install_paths() {
    use std::os::unix::fs::symlink;

    let temp = tempfile::tempdir().expect("create owned fixture");
    let v1 = temp.path().join("v1.tar.zst");
    let v2 = temp.path().join("v2.tar.zst");
    write_archive_with(&v1, b"archive v1");
    write_archive_with(&v2, b"archive v2");

    // Symlink collision: both `install_at` and `reinstall_existing` fail
    // closed without following or overwriting the target directory.
    let sym_cache = temp.path().join("sym-cache");
    let slug_path = install_at(Some(v1.clone()), exocrate::Location::Custom(sym_cache.clone()))
        .expect("install v1 to discover slug path");
    fs::remove_dir_all(&slug_path).expect("remove v1 dir");
    let target_dir = temp.path().join("outside-target");
    fs::create_dir(&target_dir).expect("create target dir");
    fs::write(target_dir.join("keep.txt"), b"outside").expect("write target file");
    symlink(&target_dir, &slug_path).expect("replace slug with symlink");

    let err = install_at(Some(v2.clone()), exocrate::Location::Custom(sym_cache))
        .expect_err("install_at must reject symlinked install root");
    assert!(err.contains("symlink"), "{err}");
    let direct_err = reinstall_existing(&slug_path, exocrate::Source::Local(v2.clone()), false)
        .expect_err("reinstall_existing must reject symlinked install root");
    assert_eq!(direct_err.kind(), io::ErrorKind::AlreadyExists);
    assert!(
        fs::symlink_metadata(&slug_path)
            .unwrap()
            .file_type()
            .is_symlink()
    );
    assert_eq!(fs::read(target_dir.join("keep.txt")).unwrap(), b"outside");

    // Regular file collision: both `install_at` and `reinstall_existing`
    // fail closed while preserving the file.
    let file_cache = temp.path().join("file-cache");
    let file_slug = install_at(Some(v1), exocrate::Location::Custom(file_cache.clone()))
        .expect("install v1 to discover slug path");
    fs::remove_dir_all(&file_slug).expect("remove v1 dir");
    fs::write(&file_slug, b"not a directory").expect("replace slug with file");

    let file_err = install_at(Some(v2.clone()), exocrate::Location::Custom(file_cache))
        .expect_err("install_at must reject non-directory install root");
    assert!(file_err.contains("failed to install Anneal toolchain:"), "{file_err}");
    let direct_file_err = reinstall_existing(&file_slug, exocrate::Source::Local(v2), false)
        .expect_err("reinstall_existing must reject non-directory install root");
    assert_eq!(direct_file_err.kind(), io::ErrorKind::AlreadyExists);
    assert_eq!(fs::read(&file_slug).unwrap(), b"not a directory");
}

#[test]
fn installed_bundle_at_validates_real_dir_and_stays_read_only_when_absent() {
    let temp = tempfile::tempdir().expect("create owned fixture");
    let empty = temp.path().join("empty");
    fs::create_dir(&empty).expect("create empty cache dir");
    assert!(
        installed_bundle_at(exocrate::Location::Custom(empty.clone()))
            .expect("absent bundle resolves to Ok(None)")
            .is_none()
    );
    assert_eq!(fs::read_dir(&empty).unwrap().count(), 0);

    let v1 = temp.path().join("v1.tar.zst");
    write_archive(&v1);
    let cache = temp.path().join("cache");
    let slug_dir = install_at(Some(v1), exocrate::Location::Custom(cache.clone()))
        .expect("install v1 bundle");

    let bundle = installed_bundle_at(exocrate::Location::Custom(cache.clone()))
        .expect("resolve installed bundle")
        .expect("bundle present");
    assert_eq!(bundle.root, slug_dir);
    drop(bundle);

    let lock_path = sibling_lock_path(&slug_dir, ".lock").unwrap();
    fs::remove_file(&lock_path).expect("remove sibling lock file");
    assert!(
        installed_bundle_at(exocrate::Location::Custom(cache.clone())).is_err(),
        "missing sibling .lock file must fail closed"
    );
    fs::write(&lock_path, b"").expect("restore placeholder lock file");

    fs::remove_dir_all(&slug_dir).expect("remove bundle dir");
    fs::write(&slug_dir, b"file").expect("replace slug with regular file");
    assert!(
        installed_bundle_at(exocrate::Location::Custom(cache.clone())).is_err(),
        "regular file at slug path must fail closed"
    );

    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        fs::remove_file(&slug_dir).expect("remove placeholder file");
        let real = temp.path().join("real");
        fs::create_dir(&real).expect("create target dir");
        symlink(&real, &slug_dir).expect("symlink slug");
        let err = installed_bundle_at(exocrate::Location::Custom(cache))
            .expect_err("symlinked slug path must fail closed");
        assert!(err.contains("symlink"), "{err}");
    }
}

#[test]
fn reinstall_keeps_dir_present_and_coordinates_with_shared_bundle_lease() {
    use std::{sync::mpsc, thread, time::Duration};

    let temp = tempfile::tempdir().expect("create owned fixture");
    let v1 = temp.path().join("v1.tar.zst");
    let v2 = temp.path().join("v2.tar.zst");
    write_archive_with(&v1, b"archive v1");
    write_archive_with(&v2, b"archive v2");

    let cache = temp.path().join("cache");
    let root_v1 = install_at(Some(v1), exocrate::Location::Custom(cache.clone()))
        .expect("install v1 bundle");

    let lease = installed_bundle_at(exocrate::Location::Custom(cache.clone()))
        .expect("acquire v1 lease")
        .expect("v1 bundle present");

    let (started_tx, started_rx) = mpsc::channel();
    let (done_tx, done_rx) = mpsc::channel();
    let cache_for_writer = cache.clone();
    let writer = thread::spawn(move || {
        started_tx.send(()).unwrap();
        let result = install_at(Some(v2), exocrate::Location::Custom(cache_for_writer));
        done_tx.send(result).unwrap();
    });

    started_rx.recv().unwrap();
    let reinstall_lock = sibling_lock_path(&root_v1, ".reinstall.lock").unwrap();
    let deadline = std::time::Instant::now() + Duration::from_secs(5);
    loop {
        if let Ok(file) = fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(&reinstall_lock)
            && matches!(file.try_lock(), Err(fs::TryLockError::WouldBlock))
        {
            break;
        }
        assert!(
            std::time::Instant::now() < deadline,
            "writer thread never entered reinstall_existing"
        );
        thread::sleep(Duration::from_millis(10));
    }
    // Let the writer finish staging `v2` and block at `<slug>.lock`, then
    // confirm the shared lease keeps `v1` completely intact until dropped.
    thread::sleep(Duration::from_millis(100));
    assert!(
        matches!(done_rx.try_recv(), Err(mpsc::TryRecvError::Empty)),
        "reinstall must wait for shared reader lease on <slug>.lock"
    );
    assert!(root_v1.is_dir(), "installed directory must remain a dir");
    assert_eq!(fs::read(lease.root.join("marker.txt")).unwrap(), b"archive v1");

    drop(lease);
    let root_v2 = done_rx
        .recv_timeout(Duration::from_secs(10))
        .expect("writer finishes once lease drops")
        .expect("reinstall succeeds");
    writer.join().unwrap();
    assert_eq!(root_v2, root_v1);

    let lease_v2 = installed_bundle_at(exocrate::Location::Custom(cache))
        .expect("acquire v2 lease")
        .expect("v2 bundle present");
    assert_eq!(
        fs::read(lease_v2.root.join("marker.txt")).unwrap(),
        b"archive v2"
    );
}

#[test]
fn remove_temp_dir_best_effort_retains_directory_on_cleanup_error() {
    let container = tempfile::tempdir().expect("create owned container");
    let victim = tempfile::Builder::new()
        .prefix(".backup-")
        .tempdir_in(container.path())
        .expect("create victim tempdir");
    let victim_path = victim.path().to_path_buf();

    remove_temp_dir_best_effort_with(victim, "backup", |_| {
        Err(io::Error::from(io::ErrorKind::PermissionDenied))
    });

    assert!(
        victim_path.exists(),
        "best-effort cleanup failure must preserve dir path instead of panicking"
    );
}

#[test]
fn seed_archive_contains_only_incomplete_marker() {
    let decoder = zstd::Decoder::new(SEED_TAR_ZST).expect("decode SEED_TAR_ZST");
    let mut archive = tar::Archive::new(decoder);
    let mut names = Vec::new();
    for entry in archive.entries().expect("read tar entries") {
        let entry = entry.expect("valid tar entry");
        assert_eq!(entry.header().entry_type(), tar::EntryType::Regular);
        assert_eq!(entry.header().size().unwrap(), 0);
        names.push(entry.path().unwrap().to_path_buf());
    }
    assert_eq!(names, vec![PathBuf::from(".incomplete")]);
}
