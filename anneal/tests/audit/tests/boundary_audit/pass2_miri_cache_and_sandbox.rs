// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The Miri `.olean` cache and sandboxing of cold Miri and Pass 2
//! compilation.

use super::*;

/// Verifies the vendored `.olean` cache and compilation pipeline in
/// [`Checker::verify_and_stage_miri_entries`]:
/// 1. Staged source digest mismatch fails closed before consulting the cache or
///    invoking Lean.
/// 2. Compiled `.olean` digest mismatch fails closed and writes zero files to
///    the cache directory (write-after-verify).
/// 3. Cold compilation populates the cache with verified digests.
/// 4. Digest-gated cache restore succeeds without recompiling.
/// 5. Tampered cached `.olean` bytes are rejected (never blindly accepted),
///    forcing recompilation and healing the cache when valid source exists.
/// 6. Missing, mismatched, and unexpected compiled `.olean.server` /
///    `.olean.private` sidecars all fail closed with policy exit code `1`.
#[test]
fn verifies_miri_cache_and_rejects_unverified_oleans() {
    let fix = TempFixture::new(None);
    let cache_root = tempfile::Builder::new().prefix("anneal-miri-cache-test-").tempdir().unwrap();
    let vendor_dir = fix.root.join("fake-vendor");
    let src_path = vendor_dir.join("Miri/Tiny.lean");
    fs::create_dir_all(src_path.parent().unwrap()).unwrap();
    let valid_src =
        "prelude\nimport Init.Core\nnamespace Miri.Tiny\ndef x : Nat := 1\nend Miri.Tiny\n";
    let valid_src_sha = sha256_bytes(valid_src.as_bytes());
    let valid_sources = BTreeMap::from([("Miri/Tiny.lean".to_string(), valid_src_sha)]);
    fs::write(&src_path, valid_src).unwrap();

    // Compile once in a probe checker to obtain the deterministic `.olean`
    // companion digests for `Miri.Tiny`.
    let mut probe = fix.checker();
    probe.set_require_mir_wp(false);
    probe.run().unwrap();
    let probe_out = probe.stage().join("probe-lib/Miri/Tiny.olean");
    fs::create_dir_all(probe_out.parent().unwrap()).unwrap();
    probe
        .process(
            "probe-miri-tiny",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                probe_out.to_string_lossy().into_owned(),
                src_path.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let expected_olean = sha256_file(&probe_out, "test").unwrap();
    let probe_server = probe.stage().join("probe-lib/Miri/Tiny.olean.server");
    let expected_server =
        probe_server.exists().then(|| sha256_file(&probe_server, "test").unwrap());
    let probe_private = probe.stage().join("probe-lib/Miri/Tiny.olean.private");
    let expected_private =
        probe_private.exists().then(|| sha256_file(&probe_private, "test").unwrap());

    let good_entry = MiriClosureEntry {
        module: "Miri.Tiny".to_string(),
        path: "Miri/Tiny.lean".to_string(),
        olean_sha256: expected_olean.clone(),
        olean_server_sha256: expected_server.clone(),
        olean_private_sha256: expected_private.clone(),
    };

    // Case 0: Staged source SHA-256 mismatch fails closed with exit code `1`.
    let wrong_sources = BTreeMap::from([("Miri/Tiny.lean".to_string(), "1".repeat(64))]);
    let mut c0 = fix.checker();
    c0.set_require_mir_wp(false);
    c0.run().unwrap();
    let err_src_sha = c0
        .verify_and_stage_miri_entries(
            &vendor_dir,
            std::slice::from_ref(&good_entry),
            &wrong_sources,
        )
        .unwrap_err();
    assert_eq!(err_src_sha.code, 1, "expected policy error: {err_src_sha}");
    assert!(
        err_src_sha.message.contains("staged Miri source SHA-256 mismatch for Miri/Tiny.lean"),
        "unexpected source-mismatch error: {err_src_sha}"
    );

    // Case 1: Compiled `.olean` digest mismatch fails closed AND writes
    // nothing into the empty cache directory (write-after-verify invariant).
    let cache_mismatch = cache_root.path().join("cache-mismatch");
    fs::create_dir_all(&cache_mismatch).unwrap();
    let mut bad_entry = good_entry.clone();
    bad_entry.olean_sha256 = "0".repeat(64);
    let mut c1 = fix.checker();
    c1.set_require_mir_wp(false);
    c1.set_miri_cache_dir(Some(cache_mismatch.clone()));
    c1.run().unwrap();
    let err =
        c1.verify_and_stage_miri_entries(&vendor_dir, &[bad_entry], &valid_sources).unwrap_err();
    assert_eq!(err.code, 1, "expected policy error: {err}");
    assert!(
        err.message.contains("compiled Miri .olean SHA-256 mismatch for Miri.Tiny"),
        "unexpected mismatch error: {err}"
    );
    assert!(
        !cache_mismatch.join("Miri/Tiny.olean").exists(),
        "unverified .olean must never be written to cache"
    );

    // Case 2: Cold compile verifies digests and populates the cache.
    let cache_dir = cache_root.path().join("cache-live");
    fs::create_dir_all(&cache_dir).unwrap();
    let mut c2 = fix.checker();
    c2.set_require_mir_wp(false);
    c2.set_miri_cache_dir(Some(cache_dir.clone()));
    c2.run().unwrap();
    c2.verify_and_stage_miri_entries(
        &vendor_dir,
        std::slice::from_ref(&good_entry),
        &valid_sources,
    )
    .unwrap();
    let cached_olean = cache_dir.join("Miri/Tiny.olean");
    assert_eq!(
        sha256_file(&cached_olean, "test").unwrap(),
        expected_olean,
        "cached .olean digest must match verified output"
    );

    // Case 3: Digest-gated cache hit restores `.olean` without compiling
    // source (proven by temporarily replacing source with invalid Lean while
    // updating the expected source digest so staging succeeds).
    let invalid_src = "this is intentionally invalid lean syntax !!!\n";
    let invalid_sources =
        BTreeMap::from([("Miri/Tiny.lean".to_string(), sha256_bytes(invalid_src.as_bytes()))]);
    fs::write(&src_path, invalid_src).unwrap();
    let mut c3 = fix.checker();
    c3.set_require_mir_wp(false);
    c3.set_miri_cache_dir(Some(cache_dir.clone()));
    c3.run().unwrap();
    c3.verify_and_stage_miri_entries(
        &vendor_dir,
        std::slice::from_ref(&good_entry),
        &invalid_sources,
    )
    .unwrap();

    // Case 4a: Tampered cached `.olean` is rejected (cannot serve cache hit;
    // with invalid source present, fallback compilation fails closed).
    let mut bytes = fs::read(&cached_olean).unwrap();
    bytes[0] ^= 0xFF;
    fs::write(&cached_olean, &bytes).unwrap();
    let mut c4a = fix.checker();
    c4a.set_require_mir_wp(false);
    c4a.set_miri_cache_dir(Some(cache_dir.clone()));
    c4a.run().unwrap();
    let err_tampered = c4a
        .verify_and_stage_miri_entries(
            &vendor_dir,
            std::slice::from_ref(&good_entry),
            &invalid_sources,
        )
        .unwrap_err();
    assert!(
        err_tampered.phase.contains("compile-Miri.Tiny"),
        "tampered cached .olean must trigger recompile, got: {err_tampered}"
    );

    // Case 4b: With valid source restored, tampered cache entry is bypassed,
    // recompiled, re-verified, and healed on disk.
    fs::write(&src_path, valid_src).unwrap();
    let mut c4b = fix.checker();
    c4b.set_require_mir_wp(false);
    c4b.set_miri_cache_dir(Some(cache_dir.clone()));
    c4b.run().unwrap();
    c4b.verify_and_stage_miri_entries(
        &vendor_dir,
        std::slice::from_ref(&good_entry),
        &valid_sources,
    )
    .unwrap();
    assert_eq!(
        sha256_file(&cached_olean, "test").unwrap(),
        expected_olean,
        "healed cache entry must match pinned digest"
    );

    // Case 5: Missing expected `.olean.server` sidecar fails closed without
    // contaminating a fresh cache directory.
    let cache_sidecar = cache_root.path().join("cache-sidecar");
    fs::create_dir_all(&cache_sidecar).unwrap();
    let mut bad_sidecar = good_entry;
    bad_sidecar.olean_server_sha256 = Some("f".repeat(64));
    let mut c5 = fix.checker();
    c5.set_require_mir_wp(false);
    c5.set_miri_cache_dir(Some(cache_sidecar.clone()));
    c5.run().unwrap();
    let err_sidecar =
        c5.verify_and_stage_miri_entries(&vendor_dir, &[bad_sidecar], &valid_sources).unwrap_err();
    assert_eq!(err_sidecar.code, 1, "expected policy error: {err_sidecar}");
    assert!(
        err_sidecar.message.contains("missing compiled Miri .olean.server sidecar for Miri.Tiny"),
        "unexpected missing-sidecar error: {err_sidecar}"
    );
    assert!(
        !cache_sidecar.join("Miri/Tiny.olean").exists(),
        "sidecar mismatch must not write to cache"
    );

    // Case 6: Unexpected compiled `.olean.server` / `.olean.private` sidecar
    // (present on disk when `UPSTREAM_PIN.json` expects `None`) and sidecar
    // SHA-256 mismatch both fail closed with policy exit code `1`.
    let mod_path = vendor_dir.join("Miri/WithSidecar.lean");
    let mod_src = "module\nprelude\npublic import Init.Core\n\
                   namespace Miri.WithSidecar\npublic def x : Nat := 1\n\
                   end Miri.WithSidecar\n";
    let mod_sources =
        BTreeMap::from([("Miri/WithSidecar.lean".to_string(), sha256_bytes(mod_src.as_bytes()))]);
    fs::write(&mod_path, mod_src).unwrap();
    let probe_mod_out = probe.stage().join("probe-lib/Miri/WithSidecar.olean");
    probe
        .process(
            "probe-miri-sidecar",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                probe_mod_out.to_string_lossy().into_owned(),
                mod_path.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let mod_olean = sha256_file(&probe_mod_out, "test").unwrap();
    let mod_server = probe.stage().join("probe-lib/Miri/WithSidecar.olean.server");
    let mod_private = probe.stage().join("probe-lib/Miri/WithSidecar.olean.private");
    assert!(
        mod_server.exists(),
        "Lean `module` fixture must emit .olean.server to exercise sidecar checks"
    );
    let mod_server_sha = sha256_file(&mod_server, "test").unwrap();
    let mod_private_sha = mod_private.exists().then(|| sha256_file(&mod_private, "test").unwrap());

    // 6a. Unexpected `.olean.server` when entry expects `None`.
    let unexpected_server = MiriClosureEntry {
        module: "Miri.WithSidecar".to_string(),
        path: "Miri/WithSidecar.lean".to_string(),
        olean_sha256: mod_olean.clone(),
        olean_server_sha256: None,
        olean_private_sha256: mod_private_sha.clone(),
    };
    let mut c6a = fix.checker();
    c6a.set_require_mir_wp(false);
    c6a.run().unwrap();
    let err_unexpected_server = c6a
        .verify_and_stage_miri_entries(&vendor_dir, &[unexpected_server], &mod_sources)
        .unwrap_err();
    assert_eq!(err_unexpected_server.code, 1, "expected policy error: {err_unexpected_server}");
    assert!(
        err_unexpected_server
            .message
            .contains("unexpected Miri .olean.server sidecar for Miri.WithSidecar"),
        "unexpected sidecar error: {err_unexpected_server}"
    );

    // 6b. Mismatched `.olean.server` SHA-256 when entry expects `Some(...)`.
    let mismatched_server = MiriClosureEntry {
        module: "Miri.WithSidecar".to_string(),
        path: "Miri/WithSidecar.lean".to_string(),
        olean_sha256: mod_olean.clone(),
        olean_server_sha256: Some("e".repeat(64)),
        olean_private_sha256: mod_private_sha.clone(),
    };
    let mut c6b = fix.checker();
    c6b.set_require_mir_wp(false);
    c6b.run().unwrap();
    let err_mismatched_server = c6b
        .verify_and_stage_miri_entries(&vendor_dir, &[mismatched_server], &mod_sources)
        .unwrap_err();
    assert_eq!(err_mismatched_server.code, 1, "expected policy error: {err_mismatched_server}");
    assert!(
        err_mismatched_server
            .message
            .contains("compiled Miri .olean.server SHA-256 mismatch for Miri.WithSidecar"),
        "unexpected sidecar-mismatch error: {err_mismatched_server}"
    );

    // 6c. Unexpected `.olean.private` when emitted and entry expects `None`.
    if mod_private_sha.is_some() {
        let unexpected_private = MiriClosureEntry {
            module: "Miri.WithSidecar".to_string(),
            path: "Miri/WithSidecar.lean".to_string(),
            olean_sha256: mod_olean,
            olean_server_sha256: Some(mod_server_sha),
            olean_private_sha256: None,
        };
        let mut c6c = fix.checker();
        c6c.set_require_mir_wp(false);
        c6c.run().unwrap();
        let err_unexpected_private = c6c
            .verify_and_stage_miri_entries(&vendor_dir, &[unexpected_private], &mod_sources)
            .unwrap_err();
        assert_eq!(
            err_unexpected_private.code, 1,
            "expected policy error: {err_unexpected_private}"
        );
        assert!(
            err_unexpected_private
                .message
                .contains("unexpected Miri .olean.private sidecar for Miri.WithSidecar"),
            "unexpected private-sidecar error: {err_unexpected_private}"
        );
    }
}

/// Verifies that `--miri-cache-dir` / `Checker::set_miri_cache_dir` rejects
/// any cache directory located inside (or resolving inside) the repository
/// checkout as a policy error (exit code `1`), including non-existent paths,
/// parent traversals, and symlinks, while allowing sibling directories outside
/// the checkout.
#[test]
fn rejects_miri_cache_dir_inside_checkout() {
    let fix = TempFixture::new(None);
    let outside = tempfile::Builder::new().prefix("anneal-miri-outside-").tempdir().unwrap();

    let existing_inside = fix.root.join("existing-cache");
    fs::create_dir_all(&existing_inside).unwrap();
    let nonexistent_inside = fix.root.join(".evil-cache/nested");
    let traversed_inside = fix.root.join("sub/../.evil-cache");

    let link_into_checkout = outside.path().join("link-in");
    symlink(&existing_inside, &link_into_checkout).unwrap();
    let link_into_nested = link_into_checkout.join("deep");

    let dangling_into_checkout = outside.path().join("dangling-in");
    symlink(fix.root.join("does-not-exist"), &dangling_into_checkout).unwrap();

    let real_outside_cache = outside.path().join("real-cache");
    fs::create_dir_all(&real_outside_cache).unwrap();
    let link_out_of_checkout = fix.root.join("link-out");
    symlink(&real_outside_cache, &link_out_of_checkout).unwrap();

    let bad_paths = [
        fix.root.clone(),
        existing_inside,
        nonexistent_inside,
        traversed_inside,
        link_into_checkout,
        link_into_nested,
        dangling_into_checkout,
        link_out_of_checkout,
    ];
    for bad in &bad_paths {
        let mut checker = fix.checker();
        checker.set_require_mir_wp(false);
        checker.set_miri_cache_dir(Some(bad.clone()));
        let err = checker.run().unwrap_err();
        assert_eq!(err.code, 1, "expected policy error for {}: {err}", bad.display());
        assert_eq!(err.phase, "miri-pin", "unexpected phase for {}: {err}", bad.display());
        assert!(
            !checker.execution_began(),
            "Lean execution must not begin when cache dir is inside checkout: {}",
            bad.display()
        );
    }

    // Sibling path sharing a string prefix with `checkout` is outside the
    // checkout and must be accepted by containment validation.
    let sibling_parent = outside.path().join("parent");
    let fake_repo = sibling_parent.join("repo");
    let sibling_cache = sibling_parent.join("repo-cache");
    fs::create_dir_all(&fake_repo).unwrap();
    ensure_miri_cache_outside_checkout(&fake_repo, &sibling_cache).unwrap();

    // Verify end-to-end CLI rejection with exit code `1`.
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-audit-test-bin"))
        .env_clear()
        .arg("--anneal-root")
        .arg(&fix.root)
        .arg("--miri-cache-dir")
        .arg(fix.root.join(".evil-cache"))
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "expected exit code 1 from CLI: {output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Miri .olean cache directory must reside outside the repository checkout"),
        "unexpected CLI stderr: {stderr}"
    );
}

#[path = "pass2_miri_cache_and_sandbox/sandbox.rs"]
mod sandbox;
