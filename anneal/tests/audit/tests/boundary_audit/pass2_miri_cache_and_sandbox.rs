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

/// Verifies that cold `vendor/lean-miri/` compilation runs inside an OS-level
/// sandbox that prevents compile-time metaprograms (`run_cmd`) from writing to
/// the repository checkout, host directories, or auditor staging state
/// (including read-only `miri-lib`), and rejects unexpected extra files written
/// inside the isolated `/work/out` output directory before staging.
#[cfg(target_os = "linux")]
#[test]
fn sandboxes_cold_miri_compilation_against_host_and_stage_writes() {
    let fix = TempFixture::new(None);
    let vendor_dir = fix.root.join("fake-vendor");
    fs::create_dir_all(vendor_dir.join("Miri")).unwrap();

    // Case 1: A malicious `run_cmd` attempting to write to the repository
    // checkout fails inside the mount-isolated sandbox and leaves the checkout
    // untouched.
    let checkout_victim = fix.root.join("sandbox-escape-checkout.txt");
    let escape_checkout_src = format!(
        "import Lean.Elab.Command\n\
         namespace Miri.EscapeCheckout\n\
         run_cmd do\n\
           IO.FS.writeFile \"{}\" \"pwned\"\n\
         def x : Nat := 1\n\
         end Miri.EscapeCheckout\n",
        checkout_victim.display()
    );
    let escape_checkout_path = vendor_dir.join("Miri/EscapeCheckout.lean");
    fs::write(&escape_checkout_path, &escape_checkout_src).unwrap();
    let escape_checkout_entry = MiriClosureEntry {
        module: "Miri.EscapeCheckout".to_string(),
        path: "Miri/EscapeCheckout.lean".to_string(),
        olean_sha256: "0".repeat(64),
        olean_server_sha256: None,
        olean_private_sha256: None,
    };
    let escape_checkout_sources = BTreeMap::from([(
        "Miri/EscapeCheckout.lean".to_string(),
        sha256_bytes(escape_checkout_src.as_bytes()),
    )]);
    let mut c1 = fix.checker();
    c1.set_require_mir_wp(false);
    c1.run().unwrap();
    let err1 = c1
        .verify_and_stage_miri_entries(
            &vendor_dir,
            &[escape_checkout_entry],
            &escape_checkout_sources,
        )
        .unwrap_err();
    assert_eq!(err1.code, 2, "expected sandboxed compile error: {err1}");
    assert!(!checkout_victim.exists(), "sandboxed run_cmd must not be able to write to checkout");

    // Case 2: A malicious `run_cmd` attempting to write into the auditor's
    // read-only `/work/lp0` (`miri-lib` mount) or host `stage` fails with
    // `EROFS`/`ENOENT` and leaves both untouched.
    let mut c2 = fix.checker();
    c2.set_require_mir_wp(false);
    c2.run().unwrap();
    let stage_victim = c2.stage().join("sandbox-escape-stage.txt");
    let ro_lib_victim = c2.stage().join("miri-lib/sandbox-escape-ro.txt");
    let escape_stage_src = format!(
        "import Lean.Elab.Command\n\
         namespace Miri.EscapeStage\n\
         run_cmd do\n\
           try\n\
             IO.FS.writeFile \"{}\" \"pwned\"\n\
           catch _ =>\n\
             IO.FS.writeFile \"/work/lp0/sandbox-escape-ro.txt\" \"pwned\"\n\
         def x : Nat := 1\n\
         end Miri.EscapeStage\n",
        stage_victim.display()
    );
    let escape_stage_path = vendor_dir.join("Miri/EscapeStage.lean");
    fs::write(&escape_stage_path, &escape_stage_src).unwrap();
    let escape_stage_entry = MiriClosureEntry {
        module: "Miri.EscapeStage".to_string(),
        path: "Miri/EscapeStage.lean".to_string(),
        olean_sha256: "0".repeat(64),
        olean_server_sha256: None,
        olean_private_sha256: None,
    };
    let escape_stage_sources = BTreeMap::from([(
        "Miri/EscapeStage.lean".to_string(),
        sha256_bytes(escape_stage_src.as_bytes()),
    )]);
    let err2 = c2
        .verify_and_stage_miri_entries(&vendor_dir, &[escape_stage_entry], &escape_stage_sources)
        .unwrap_err();
    assert_eq!(err2.code, 2, "expected sandboxed compile error: {err2}");
    assert!(
        !stage_victim.exists() && !ro_lib_victim.exists(),
        "sandboxed run_cmd must not be able to write to stage or read-only miri-lib"
    );

    // Case 3: Even if a `run_cmd` drops an unexpected extra file inside the
    // sole writable sandbox output directory (`/work/out`) while producing a
    // digest-matching `.olean`, the outer auditor rejects the unexpected file
    // with policy exit code `1` and stages nothing into `miri-lib` or cache.
    let extra_out_src = "import Lean.Elab.Command\n\
        namespace Miri.ExtraOut\n\
        run_cmd do\n\
          IO.FS.writeFile \"out/unexpected-drop.txt\" \"junk\"\n\
        def x : Nat := 1\n\
        end Miri.ExtraOut\n";
    let extra_out_path = vendor_dir.join("Miri/ExtraOut.lean");
    fs::write(&extra_out_path, extra_out_src).unwrap();
    let mut probe = fix.checker();
    probe.set_require_mir_wp(false);
    probe.run().unwrap();
    let probe_out_dir = probe.stage().join("out");
    fs::create_dir_all(probe_out_dir.join("Miri")).unwrap();
    probe
        .process(
            "probe-extra-out",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                probe_out_dir.join("Miri/ExtraOut.olean").to_string_lossy().into_owned(),
                extra_out_path.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let extra_olean_sha = sha256_file(&probe_out_dir.join("Miri/ExtraOut.olean"), "test").unwrap();
    let extra_server_sha = probe_out_dir
        .join("Miri/ExtraOut.olean.server")
        .exists()
        .then(|| sha256_file(&probe_out_dir.join("Miri/ExtraOut.olean.server"), "test").unwrap());
    let extra_private_sha = probe_out_dir
        .join("Miri/ExtraOut.olean.private")
        .exists()
        .then(|| sha256_file(&probe_out_dir.join("Miri/ExtraOut.olean.private"), "test").unwrap());

    let cache_dir =
        tempfile::Builder::new().prefix("anneal-sandbox-extra-cache-").tempdir().unwrap();
    let extra_entry = MiriClosureEntry {
        module: "Miri.ExtraOut".to_string(),
        path: "Miri/ExtraOut.lean".to_string(),
        olean_sha256: extra_olean_sha,
        olean_server_sha256: extra_server_sha,
        olean_private_sha256: extra_private_sha,
    };
    let extra_sources = BTreeMap::from([(
        "Miri/ExtraOut.lean".to_string(),
        sha256_bytes(extra_out_src.as_bytes()),
    )]);
    let mut c3 = fix.checker();
    c3.set_require_mir_wp(false);
    c3.set_miri_cache_dir(Some(cache_dir.path().to_path_buf()));
    c3.run().unwrap();
    let err3 =
        c3.verify_and_stage_miri_entries(&vendor_dir, &[extra_entry], &extra_sources).unwrap_err();
    assert_eq!(err3.code, 2, "expected Door 1 error for extra sandbox output: {err3}");
    assert!(
        err3.message.contains("unexpected compiler output unexpected-drop.txt"),
        "unexpected error message: {err3}"
    );
    assert!(
        !c3.stage().join("miri-lib/Miri/ExtraOut.olean").exists()
            && !cache_dir.path().join("Miri/ExtraOut.olean").exists(),
        "rejected sandbox output must not be staged or cached"
    );

    // Case 4: A real Lean 4 `module`-system vendored file
    // (`Miri.Memory.QSortProof`, which emits `.olean.{server,private}` plus
    // ephemeral `.ir`/`.ir.sig` sidecars) compiles cold inside the sandbox,
    // stages and caches only the digest-verified `.olean*` artifacts, and
    // discards `.ir`/`.ir.sig`.
    let checkout = repo_root();
    let real_vendor = checkout.join("vendor/lean-miri");
    let real_pin = anneal_audit::verify_upstream_pin(&real_vendor).unwrap();
    let qsort_entry = real_pin
        .execution_machine_closure
        .iter()
        .find(|e| e.module == "Miri.Memory.QSortProof")
        .expect("Miri.Memory.QSortProof must exist in closure")
        .clone();
    let qsort_src_sha = real_pin
        .vendor_tree
        .files
        .iter()
        .find(|f| f.path == qsort_entry.path)
        .expect("QSortProof.lean must exist in vendor_tree")
        .sha256
        .clone();
    let qsort_sources = BTreeMap::from([(qsort_entry.path.clone(), qsort_src_sha)]);
    let qsort_cache =
        tempfile::Builder::new().prefix("anneal-sandbox-qsort-cache-").tempdir().unwrap();
    let mut c4 = fix.checker();
    c4.set_require_mir_wp(false);
    c4.set_miri_cache_dir(Some(qsort_cache.path().to_path_buf()));
    c4.run().unwrap();
    let miri_lib =
        c4.verify_and_stage_miri_entries(&real_vendor, &[qsort_entry], &qsort_sources).unwrap();
    for ext in ["olean", "olean.server", "olean.private"] {
        let rel = format!("Miri/Memory/QSortProof.{ext}");
        assert!(miri_lib.join(&rel).is_file(), "expected staged {rel} in miri-lib");
        assert!(qsort_cache.path().join(&rel).is_file(), "expected cached {rel} in miri cache");
    }
    for ext in ["ir", "ir.sig"] {
        let rel = format!("Miri/Memory/QSortProof.{ext}");
        assert!(!miri_lib.join(&rel).exists(), "ephemeral {rel} must not be staged into miri-lib");
        assert!(
            !qsort_cache.path().join(&rel).exists(),
            "ephemeral {rel} must not be written to miri cache"
        );
    }

    // Case 5: A non-module cold compile (`olean_server_sha256` and
    // `olean_private_sha256` both `None`) that emits `.ir` or `.ir.sig`
    // alongside a digest-matching `.olean` must still be rejected with Door 1
    // operational exit code `2`, staging and caching nothing.
    for (module, stem, leaf, ext) in [
        ("Miri.ExtraIr", "Miri/ExtraIr", "ExtraIr", "ir"),
        ("Miri.ExtraIrSig", "Miri/ExtraIrSig", "ExtraIrSig", "ir.sig"),
    ] {
        let sidecar_rel = format!("{stem}.{ext}");
        let sidecar_leaf = format!("{leaf}.{ext}");
        let src = format!(
            "import Lean.Elab.Command\n\
             namespace {module}\n\
             run_cmd do\n\
               IO.FS.writeFile \"out/{sidecar_leaf}\" \"fake-ir\"\n\
             def x : Nat := 1\n\
             end {module}\n"
        );
        let src_rel = format!("{stem}.lean");
        let src_path = vendor_dir.join(&src_rel);
        fs::write(&src_path, &src).unwrap();

        let mut ir_probe = fix.checker();
        ir_probe.set_require_mir_wp(false);
        ir_probe.run().unwrap();
        let ir_probe_out = ir_probe.stage().join("out");
        fs::create_dir_all(ir_probe_out.join("Miri")).unwrap();
        let olean_rel = format!("{stem}.olean");
        ir_probe
            .process(
                "probe-nonmodule-ir",
                &[
                    "-j1".to_string(),
                    "-M2048".to_string(),
                    "-t0".to_string(),
                    "-DElab.async=false".to_string(),
                    "-Ddebug.skipKernelTC=false".to_string(),
                    "-R".to_string(),
                    vendor_dir.to_string_lossy().into_owned(),
                    "-o".to_string(),
                    ir_probe_out.join(&olean_rel).to_string_lossy().into_owned(),
                    src_path.to_string_lossy().into_owned(),
                ],
            )
            .unwrap();
        assert!(
            !ir_probe_out.join(format!("{stem}.olean.server")).exists()
                && !ir_probe_out.join(format!("{stem}.olean.private")).exists(),
            "{module} must compile as a non-module entry"
        );
        let olean_sha = sha256_file(&ir_probe_out.join(&olean_rel), "test").unwrap();

        let ir_cache = tempfile::Builder::new()
            .prefix("anneal-sandbox-nonmodule-ir-cache-")
            .tempdir()
            .unwrap();
        let ir_entry = MiriClosureEntry {
            module: module.to_string(),
            path: src_rel.clone(),
            olean_sha256: olean_sha,
            olean_server_sha256: None,
            olean_private_sha256: None,
        };
        let ir_sources = BTreeMap::from([(src_rel, sha256_bytes(src.as_bytes()))]);
        let mut c5 = fix.checker();
        c5.set_require_mir_wp(false);
        c5.set_miri_cache_dir(Some(ir_cache.path().to_path_buf()));
        c5.run().unwrap();
        let err5 =
            c5.verify_and_stage_miri_entries(&vendor_dir, &[ir_entry], &ir_sources).unwrap_err();
        assert_eq!(err5.code, 2, "expected Door 1 error for non-module {ext} sidecar: {err5}");
        assert_eq!(err5.phase, "door1");
        let expected_diag = format!("unexpected compiler output {sidecar_leaf}");
        assert!(err5.message.contains(&expected_diag), "expected `{expected_diag}`, got: {err5}");
        assert!(
            !c5.stage().join("miri-lib").join(&olean_rel).exists()
                && !c5.stage().join("miri-lib").join(&sidecar_rel).exists()
                && !ir_cache.path().join(&olean_rel).exists()
                && !ir_cache.path().join(&sidecar_rel).exists(),
            "rejected non-module {ext} output must not be staged or cached"
        );
    }
}

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

/// Verifies that Pass 2 `"correspondence-preflight"` and Pass 2 module
/// compilation run inside the isolated Linux `bwrap` sandbox: a vendored
/// `Miri.*` `[init]` initializer cannot write to the host checkout or stage
/// during `"correspondence-preflight"` or during Pass 2 elaboration, and any
/// extra file dropped into `/work/out` is rejected with policy exit code `1`.
#[cfg(target_os = "linux")]
#[test]
fn sandboxes_pass2_preflight_and_compilation_against_host_and_stage_writes() {
    let fix = TempFixture::new(None);
    let vendor_dir = fix.root.join("fake-vendor");
    fs::create_dir_all(vendor_dir.join("Miri")).unwrap();

    // Build a vendored `Miri.InitWriter` module whose `initialize` hook runs
    // whenever `importModules` loads extensions (both during
    // `"correspondence-preflight"` and during Pass 2 compilation) and attempts
    // to write to a host checkout path, plus a second module that drops an
    // unexpected file into `/work/out/sneaky-drop.txt`.
    let host_victim = fix.root.join("pass2-escape-host.txt");
    let init_host_src = format!(
        "prelude\n\
         import Init.System.IO\n\
         namespace Miri.InitHost\n\
         initialize _ : Unit ← do\n\
           IO.FS.writeFile \"{}\" \"pwned\"\n\
           pure ()\n\
         def ok : Nat := 1\n\
         end Miri.InitHost\n",
        host_victim.display()
    );
    fs::write(vendor_dir.join("Miri/InitHost.lean"), &init_host_src).unwrap();

    let mut prebuild = fix.checker();
    prebuild.set_require_mir_wp(false);
    prebuild.run().unwrap();
    prebuild.ensure_sysroot_foundation().unwrap();
    let probe_lib = prebuild.stage().join("probe-miri-lib");
    fs::create_dir_all(probe_lib.join("Miri")).unwrap();
    // Compile `Miri.InitHost` into a temporary `.olean` for digest capture
    // (the `initialize` hook does not execute while compiling its own module,
    // only when an importing process loads the `.olean` with `loadExts`).
    prebuild
        .process(
            "probe-init-host",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                probe_lib.join("Miri/InitHost.olean").to_string_lossy().into_owned(),
                vendor_dir.join("Miri/InitHost.lean").to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    assert!(!host_victim.exists(), "compiling Miri.InitHost must not execute its initialize hook");

    // 1. `"correspondence-preflight"` runs inside `bwrap`: importing
    // `Miri.InitHost` with `loadExts := true` fails when the `[init]` hook
    // tries to write outside `/work/out`, leaving `host_victim` untouched.
    fs::create_dir_all(prebuild.stage().join("theory-lib")).unwrap();
    let src_dir = prebuild.stage().join("src/p2-sandbox-test");
    fs::create_dir_all(src_dir.join("Trusted")).unwrap();
    let sample_src = src_dir.join("Trusted/Correspondence.lean");
    fs::write(
        &sample_src,
        "-- anneal-trust-tier: candidate:mir_semantics\n\
         prelude\nimport Init.Core\nimport Miri.InitHost\n\
         def c : Nat := Miri.InitHost.ok\n",
    )
    .unwrap();
    let trusted_base_src = prebuild.modules()["Trusted"].clone();
    let err_pf = prebuild
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: vec![
                prebuild.stage().join("lib"),
                prebuild.stage().join("theory-lib"),
                probe_lib.clone(),
            ],
            trusted: vec!["Trusted".to_string()],
            theory: vec![],
            vendor_miri: vec!["Miri.InitHost".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src.clone())],
            sources: vec![("Trusted.Correspondence".to_string(), sample_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf.code, 2, "expected sandboxed correspondence-preflight failure: {err_pf}");
    assert!(
        !err_pf.message.contains("bwrap:"),
        "bwrap itself must launch Lean rather than failing on mount setup: {err_pf}"
    );
    assert!(
        err_pf.message.contains("pass2-escape-host.txt"),
        "expected failure from the malicious [init] host write attempt: {err_pf}"
    );
    assert!(
        !host_victim.exists(),
        "sandboxed correspondence-preflight must not write to host checkout"
    );

    // 2. Even if a vendored `[init]` drops an extra file inside the sole
    // writable `/work/out` directory during `"correspondence-preflight"`,
    // `anneal-audit` rejects it with policy exit code `1` before trusting
    // `result.json`.
    let init_drop_src = "prelude\n\
        import Init.System.IO\n\
        namespace Miri.InitDrop\n\
        initialize _ : Unit ← do\n\
          IO.FS.writeFile \"/work/out/sneaky-drop.txt\" \"junk\"\n\
          pure ()\n\
        def ok : Nat := 1\n\
        end Miri.InitDrop\n";
    fs::write(vendor_dir.join("Miri/InitDrop.lean"), init_drop_src).unwrap();
    prebuild
        .process(
            "probe-init-drop",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                probe_lib.join("Miri/InitDrop.olean").to_string_lossy().into_owned(),
                vendor_dir.join("Miri/InitDrop.lean").to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let sample_drop_src = src_dir.join("Trusted/DropTest.lean");
    fs::write(
        &sample_drop_src,
        "-- anneal-trust-tier: candidate:mir_semantics\n\
         prelude\nimport Init.Core\nimport Miri.InitDrop\n\
         def c : Nat := Miri.InitDrop.ok\n",
    )
    .unwrap();
    let err_drop = prebuild
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: vec![
                prebuild.stage().join("lib"),
                prebuild.stage().join("theory-lib"),
                probe_lib.clone(),
            ],
            trusted: vec!["Trusted".to_string()],
            theory: vec![],
            vendor_miri: vec!["Miri.InitDrop".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src)],
            sources: vec![("Trusted.DropTest".to_string(), sample_drop_src)],
        })
        .unwrap_err();
    assert_eq!(
        err_drop.code, 2,
        "expected Door 1 rejection for unexpected file in /work/out: {err_drop}"
    );
    assert!(
        err_drop.message.contains("unexpected inspector outputs"),
        "unexpected error message: {err_drop}"
    );

    // 3. Pass 2 module compilation (`run_correspondence_with_closure`) runs
    // inside `bwrap`: a vendored `[init]` that stays silent during
    // `"correspondence-preflight"` (where `/work/src/corr-trusted` is absent)
    // and attempts to write to the host checkout during Pass 2 compilation
    // fails inside the sandbox, leaving `compile_host_victim` untouched.
    let compile_host_victim = fix.root.join("pass2-compile-escape-host.txt");
    let init_compile_host_src = format!(
        "prelude\n\
         import Init.System.IO\n\
         namespace Miri.InitCompileHost\n\
         initialize _ : Unit ← do\n\
           if ← System.FilePath.pathExists \"/work/src/corr-trusted\" then\n\
             IO.FS.writeFile \"{}\" \"pwned\"\n\
           pure ()\n\
         def ok : Nat := 1\n\
         end Miri.InitCompileHost\n",
        compile_host_victim.display()
    );
    fs::write(vendor_dir.join("Miri/InitCompileHost.lean"), &init_compile_host_src).unwrap();
    let compile_host_olean = probe_lib.join("Miri/InitCompileHost.olean");
    prebuild
        .process(
            "probe-init-compile-host",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                compile_host_olean.to_string_lossy().into_owned(),
                vendor_dir.join("Miri/InitCompileHost.lean").to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let compile_host_entry = MiriClosureEntry {
        module: "Miri.InitCompileHost".to_string(),
        path: "Miri/InitCompileHost.lean".to_string(),
        olean_sha256: sha256_file(&compile_host_olean, "test").unwrap(),
        olean_server_sha256: None,
        olean_private_sha256: None,
    };
    let compile_host_sources = BTreeMap::from([(
        "Miri/InitCompileHost.lean".to_string(),
        sha256_bytes(init_compile_host_src.as_bytes()),
    )]);
    // Run Pass 1 on fresh checkers before creating `trusted/correspondence/`
    // and `correspondence/` so `Checker::run()` completes Pass 1 without
    // demanding `vendor/lean-miri/upstream-pin.json`.
    let mut c3 = fix.checker();
    c3.set_require_mir_wp(false);
    c3.run().unwrap();
    let mut c4 = fix.checker();
    c4.set_require_mir_wp(false);
    c4.run().unwrap();
    fs::create_dir_all(fix.root.join("trusted/correspondence/Trusted")).unwrap();
    fs::create_dir_all(fix.root.join("correspondence/Anneal")).unwrap();
    fs::write(
        fix.root.join("trusted/correspondence/Trusted/Correspondence.lean"),
        "-- anneal-trust-tier: candidate:mir_semantics\n\
         prelude\nimport Init.Core\nimport Miri.InitCompileHost\n\
         def c : Nat := Miri.InitCompileHost.ok\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean"),
        "prelude\nimport Trusted.Correspondence\n\
         def p : Nat := c\n",
    )
    .unwrap();
    let err_compile_host = c3
        .run_correspondence_with_closure(
            &BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            &vendor_dir,
            "0000000000000000000000000000000000000000",
            &[compile_host_entry],
            &compile_host_sources,
        )
        .unwrap_err();
    assert_eq!(
        err_compile_host.code, 2,
        "expected sandboxed Pass 2 compile failure: {err_compile_host}"
    );
    assert_eq!(err_compile_host.phase, "compile-Trusted.Correspondence");
    assert!(
        !err_compile_host.message.contains("bwrap:"),
        "bwrap itself must launch Lean rather than failing on mount setup: {err_compile_host}"
    );
    assert!(
        err_compile_host.message.contains("pass2-compile-escape-host.txt"),
        "expected failure from the malicious [init] host write attempt: {err_compile_host}"
    );
    assert!(
        !compile_host_victim.exists(),
        "sandboxed Pass 2 compilation must not write to host checkout"
    );

    // 4. Even if a vendored `[init]` drops an extra file into `/work/out`
    // during Pass 2 compilation, `anneal-audit` Door 1 rejects it and stages
    // nothing into `lib/`.
    let init_compile_drop_src = "prelude\n\
        import Init.System.IO\n\
        namespace Miri.InitCompileDrop\n\
        initialize _ : Unit ← do\n\
          if ← System.FilePath.pathExists \"/work/src/corr-trusted\" then\n\
            IO.FS.writeFile \"/work/out/sneaky-pass2.txt\" \"junk\"\n\
          pure ()\n\
        def ok : Nat := 1\n\
        end Miri.InitCompileDrop\n";
    fs::write(vendor_dir.join("Miri/InitCompileDrop.lean"), init_compile_drop_src).unwrap();
    let compile_drop_olean = probe_lib.join("Miri/InitCompileDrop.olean");
    prebuild
        .process(
            "probe-init-compile-drop",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                compile_drop_olean.to_string_lossy().into_owned(),
                vendor_dir.join("Miri/InitCompileDrop.lean").to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let compile_drop_entry = MiriClosureEntry {
        module: "Miri.InitCompileDrop".to_string(),
        path: "Miri/InitCompileDrop.lean".to_string(),
        olean_sha256: sha256_file(&compile_drop_olean, "test").unwrap(),
        olean_server_sha256: None,
        olean_private_sha256: None,
    };
    let compile_drop_sources = BTreeMap::from([(
        "Miri/InitCompileDrop.lean".to_string(),
        sha256_bytes(init_compile_drop_src.as_bytes()),
    )]);
    fs::write(
        fix.root.join("trusted/correspondence/Trusted/Correspondence.lean"),
        "-- anneal-trust-tier: candidate:mir_semantics\n\
         prelude\nimport Init.Core\nimport Miri.InitCompileDrop\n\
         def c : Nat := Miri.InitCompileDrop.ok\n",
    )
    .unwrap();
    let err_compile_drop = c4
        .run_correspondence_with_closure(
            &BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            &vendor_dir,
            "0000000000000000000000000000000000000000",
            &[compile_drop_entry],
            &compile_drop_sources,
        )
        .unwrap_err();
    assert_eq!(
        err_compile_drop.code, 2,
        "expected Door 1 rejection for unexpected file in Pass 2 /work/out: {err_compile_drop}"
    );
    assert!(
        err_compile_drop.message.contains("unexpected compiler outputs"),
        "unexpected error message: {err_compile_drop}"
    );
    assert!(
        !c4.stage().join("lib/Trusted/Correspondence.olean").exists(),
        "rejected Pass 2 output must not be staged into lib/"
    );
}
