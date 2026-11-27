// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::ffi::OsString;

use super::*;

#[test]
fn stages_locks_and_writes_hashed_inputs() {
    let checkout = tempfile::tempdir().unwrap();
    for rel in [
        "trusted/lean/lean-toolchain",
        "trusted/lean/foundation-lock.json",
        "trusted/audit/TrustedBoundary.lean",
        "trusted/audit/library-lock.json",
    ] {
        let p = checkout.path().join(rel);
        fs::create_dir_all(p.parent().unwrap()).unwrap();
        fs::write(p, rel.as_bytes()).unwrap();
    }

    let without_lib = LeanAuditFixture::new(checkout.path(), "test-nolib-", None, false).unwrap();
    assert!(without_lib.root().join("trusted/lean/Trusted.lean").is_file());
    assert!(!without_lib.root().join("trusted/audit/library-lock.json").exists());
    assert_eq!(without_lib.cache_policy(), OleanCachePolicy::Isolated);
    assert!(!without_lib.olean_cache().is_persistent());

    let shared_dir = tempfile::tempdir().unwrap();
    let persistent =
        SharedOleanCache::in_persistent_dir(shared_dir.path().join("target-cache")).unwrap();
    let with_lib = LeanAuditFixture::with_cache(
        checkout.path(),
        "test-lib-",
        Some("prelude\n"),
        true,
        OleanCachePolicy::Shared,
        persistent,
    )
    .unwrap();
    assert!(with_lib.root().join("trusted/audit/library-lock.json").is_file());
    assert_eq!(with_lib.cache_policy(), OleanCachePolicy::Shared);
    assert!(with_lib.olean_cache().is_persistent());
    assert_ne!(with_lib.olean_cache().home_dir(), without_lib.olean_cache().home_dir());
    let (path, hash) = with_lib.write_input_lean("Spec", "def x := 1\n").unwrap();
    assert_eq!(fs::read_to_string(path).unwrap(), "def x := 1\n");
    assert_eq!(hash, sha256_hex(b"def x := 1\n"));
}

#[test]
fn write_rel_and_write_input_lean_reject_escape_and_non_normal_paths() {
    let checkout = tempfile::tempdir().unwrap();
    for rel in [
        "trusted/lean/lean-toolchain",
        "trusted/lean/foundation-lock.json",
        "trusted/audit/TrustedBoundary.lean",
    ] {
        let p = checkout.path().join(rel);
        fs::create_dir_all(p.parent().unwrap()).unwrap();
        fs::write(p, rel.as_bytes()).unwrap();
    }
    let outside = tempfile::tempdir().unwrap();
    let outside_file = outside.path().join("escaped.txt");
    let fix = LeanAuditFixture::new(checkout.path(), "test-escape-", None, false).unwrap();

    for bad in [
        "",
        ".",
        "..",
        "../escaped.txt",
        "sub/../escaped.txt",
        "./nested.txt",
        outside_file.to_str().unwrap(),
    ] {
        assert!(fix.write_rel(bad, b"boom").is_err(), "write_rel must reject {bad:?}");
    }
    for bad_name in
        ["", ".", "..", "../Escape", "Sub/../Escape", "./Spec", outside_file.to_str().unwrap()]
    {
        assert!(
            fix.write_input_lean(bad_name, "def x := 0\n").is_err(),
            "write_input_lean must reject {bad_name:?}"
        );
    }
    assert!(!outside_file.exists());
}

#[cfg(unix)]
#[test]
fn fixture_succeeds_under_symlinked_temp_parent() {
    let checkout = tempfile::tempdir().unwrap();
    for rel in [
        "trusted/lean/lean-toolchain",
        "trusted/lean/foundation-lock.json",
        "trusted/audit/TrustedBoundary.lean",
    ] {
        let p = checkout.path().join(rel);
        fs::create_dir_all(p.parent().unwrap()).unwrap();
        fs::write(p, rel.as_bytes()).unwrap();
    }
    let outer = tempfile::tempdir().unwrap();
    let real_tmp = outer.path().join("real-tmp");
    let sym_tmp = outer.path().join("sym-tmp");
    fs::create_dir_all(&real_tmp).unwrap();
    std::os::unix::fs::symlink(&real_tmp, &sym_tmp).unwrap();

    let cache = SharedOleanCache::isolated().unwrap();
    let fix = LeanAuditFixture::with_cache_in_temp(
        &sym_tmp,
        checkout.path(),
        "test-sym-tmp-",
        None,
        false,
        OleanCachePolicy::Isolated,
        cache,
    )
    .unwrap();
    assert_eq!(fix.root(), fs::canonicalize(fix.root()).unwrap());
    let written = fix.write_rel("nested/Extra.lean", b"def y := 2\n").unwrap();
    assert_eq!(fs::read(&written).unwrap(), b"def y := 2\n");
    let (inp, _) = fix.write_input_lean("Spec", "def z := 3\n").unwrap();
    assert!(inp.is_file());
}

#[test]
fn persistent_cache_root_prefers_override_then_cargo_target_dir() {
    let explicit = resolve_persistent_cache_root(|k| match k {
        "ANNEAL_TEST_OLEAN_CACHE_DIR" => Some(OsString::from("/custom/cache-root")),
        "CARGO_TARGET_DIR" => Some(OsString::from("/ignored/target")),
        _ => None,
    })
    .unwrap();
    assert_eq!(explicit, PathBuf::from("/custom/cache-root"));

    let from_target = resolve_persistent_cache_root(|k| match k {
        "CARGO_TARGET_DIR" => Some(OsString::from("/build/target")),
        _ => None,
    })
    .unwrap();
    assert_eq!(from_target, PathBuf::from("/build/target/anneal-test-olean-cache"));

    let fallback = resolve_persistent_cache_root(|_| None).unwrap();
    assert!(fallback.ends_with("target/anneal-test-olean-cache"));
}

#[test]
fn persistent_cache_survives_drop_and_ephemeral_cache_cleans_up() {
    let parent = tempfile::tempdir().unwrap();
    let persistent_root = parent.path().join("shared-cache");
    let persisted_v2 = {
        let cache = SharedOleanCache::in_persistent_dir(persistent_root.clone()).unwrap();
        assert!(cache.is_persistent());
        let marker = cache.olean_cache_dir().join("v2/marker");
        fs::write(&marker, b"ok").unwrap();
        marker
    };
    assert_eq!(fs::read(&persisted_v2).unwrap(), b"ok");

    let ephemeral_home = {
        let cache = SharedOleanCache::isolated().unwrap();
        assert!(!cache.is_persistent());
        cache.home_dir().to_path_buf()
    };
    assert!(!ephemeral_home.exists());
}

#[test]
fn seeded_olean_cache_freezes_v2_entries_readonly_skips_junk_and_drops_cleanly() {
    let seed_root = tempfile::tempdir().unwrap();
    let key = "a".repeat(64);
    let valid_entry = seed_root.path().join("v2").join(&key);
    fs::create_dir_all(&valid_entry).unwrap();
    fs::write(valid_entry.join("metadata.json"), b"{}").unwrap();
    fs::write(valid_entry.join("module.olean"), b"olean-bytes").unwrap();
    // Temp dir, lockfile, and incomplete entry must be skipped.
    fs::create_dir_all(seed_root.path().join("v2/.tmp-inflight")).unwrap();
    fs::write(seed_root.path().join(format!("v2/{key}.lock")), b"").unwrap();
    let incomplete = seed_root.path().join("v2").join("b".repeat(64));
    fs::create_dir_all(&incomplete).unwrap();
    fs::write(incomplete.join("module.olean"), b"no-meta").unwrap();

    let home_path = {
        let cache = SharedOleanCache::from_seed_dir(Some(seed_root.path()), true).unwrap();
        assert_eq!(cache.seeded_entries(), 1);
        assert!(cache.is_readonly_root());
        let dst_entry = cache.olean_cache_dir().join("v2").join(&key);
        assert_eq!(fs::read(dst_entry.join("module.olean")).unwrap(), b"olean-bytes");
        assert!(!cache.olean_cache_dir().join("v2/.tmp-inflight").exists());
        assert!(!cache.olean_cache_dir().join("v2").join("b".repeat(64)).exists());

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(fs::metadata(&dst_entry).unwrap().permissions().mode() & 0o777, 0o500);
            assert_eq!(
                fs::metadata(dst_entry.join("module.olean")).unwrap().permissions().mode() & 0o777,
                0o444
            );
            assert_eq!(
                fs::metadata(cache.olean_cache_dir()).unwrap().permissions().mode() & 0o777,
                0o500
            );
        }

        let env = cache.checker_env().unwrap();
        assert!(env.iter().any(|(k, v)| k == "HOME" && Path::new(v) == cache.home_dir()));
        assert!(
            env.iter()
                .any(|(k, v)| k == "XDG_CACHE_HOME" && Path::new(v) == cache.xdg_cache_home())
        );
        cache.home_dir().to_path_buf()
    };
    // Drop must restore permissions on the frozen tree and remove it.
    assert!(!home_path.exists());
}

#[test]
fn from_seed_dir_skips_symlinked_and_regular_file_seed_roots() {
    let outer = tempfile::tempdir().unwrap();
    let real_seed = outer.path().join("real-seed");
    let key = "c".repeat(64);
    let valid_entry = real_seed.join("v2").join(&key);
    fs::create_dir_all(&valid_entry).unwrap();
    fs::write(valid_entry.join("metadata.json"), b"{}").unwrap();
    fs::write(valid_entry.join("module.olean"), b"olean-bytes").unwrap();

    // Regular file at `seed_olean_cache_dir` must return `Ok` with 0
    // entries rather than failing with `ENOTDIR` on `<file>/v2`.
    let regular_file = outer.path().join("not-a-dir");
    fs::write(&regular_file, b"regular file").unwrap();
    let from_file = SharedOleanCache::from_seed_dir(Some(&regular_file), false).unwrap();
    assert_eq!(from_file.seeded_entries(), 0);
    assert!(!from_file.olean_cache_dir().join("v2").join(&key).exists());

    #[cfg(unix)]
    {
        // Symlinked `seed_olean_cache_dir` (both bare and with trailing
        // `/`) must not be traversed to copy `real_seed/v2/*`.
        let sym_seed = outer.path().join("sym-seed");
        std::os::unix::fs::symlink(&real_seed, &sym_seed).unwrap();
        let from_sym = SharedOleanCache::from_seed_dir(Some(&sym_seed), false).unwrap();
        assert_eq!(from_sym.seeded_entries(), 0);
        assert!(!from_sym.olean_cache_dir().join("v2").join(&key).exists());

        let sym_trailing = PathBuf::from(format!("{}/", sym_seed.display()));
        let from_sym_slash = SharedOleanCache::from_seed_dir(Some(&sym_trailing), false).unwrap();
        assert_eq!(from_sym_slash.seeded_entries(), 0);
        assert!(!from_sym_slash.olean_cache_dir().join("v2").join(&key).exists());
    }
}
