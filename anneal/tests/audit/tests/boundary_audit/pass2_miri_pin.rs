// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The pinned `lean-miri` upstream and source lock, vendor constant
//! namespaces, and kernel checking of vendored modules.

use super::*;

/// Verifies that `verify_upstream_pin` and `Checker::run()` enforce
/// `vendor/lean-miri/UPSTREAM_PIN.json` and reject whole-directory deletion,
/// missing manifests, modified or unlisted `.lean` files, symlinks,
/// unauthorized `patched_files`, and invalid `execution_machine_closure`
/// entries with policy exit code `1`.
#[test]
fn verifies_upstream_pin_and_rejects_tampering() {
    let checkout = repo_root();
    let pin = anneal_audit::verify_upstream_pin(&checkout.join("vendor/lean-miri")).unwrap();
    assert_eq!(pin.schema_version, 2);
    assert_eq!(pin.vendor_tree.file_count, 608);
    assert_eq!(pin.patched_files.len(), 13);
    assert_eq!(pin.execution_machine_closure.len(), 160);

    // 1. Deleting `vendor/` in a repository checkout fails `Checker::run()`
    // with policy exit code `1` (`miri-pin`).
    let mut fix_missing_dir = TempFixture::new(None);
    copy_cargo_workspace(&fix_missing_dir.root);
    let err_no_vendor =
        fix_missing_dir.check_expected(Some(1), Some("miri-pin"), Some(false)).unwrap_err();
    assert!(
        err_no_vendor.message.contains("expected regular vendor directory"),
        "unexpected error: {err_no_vendor}"
    );

    // Prepare a mutable copy of `vendor/lean-miri` for tampering tests.
    let tmp = tempfile::tempdir().unwrap();
    let vendor_copy = tmp.path().join("vendor/lean-miri");
    copy_dir_all(&checkout.join("vendor/lean-miri"), &vendor_copy).unwrap();
    let pin = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap();

    // 2. Modified `.lean` file digest mismatch is rejected.
    let target_lean = vendor_copy.join("Miri.lean");
    let orig_lean = fs::read(&target_lean).unwrap();
    fs::write(&target_lean, b"-- tampered\n").unwrap();
    let err_tamper = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_tamper.code, 1);
    assert!(
        err_tamper.message.contains("vendor file SHA-256 mismatch for Miri.lean"),
        "unexpected error: {err_tamper}"
    );
    fs::write(&target_lean, &orig_lean).unwrap();

    // 2b. Patched `.lean` files are verified against `patched_sha256`, never
    // exempted from on-disk digest checking.
    for patched_rel in ["Miri/Interpreter/Call.lean", "Miri/Memory/Allocation.lean"] {
        let patched_lean = vendor_copy.join(patched_rel);
        let orig_patched = fs::read(&patched_lean).unwrap();
        let expected_patched_sha = &pin
            .patched_files
            .iter()
            .find(|p| p.path == patched_rel)
            .unwrap_or_else(|| panic!("{patched_rel} must be listed in patched_files"))
            .patched_sha256;
        fs::write(&patched_lean, b"-- tampered patched file\n").unwrap();
        let err_patched_tamper = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
        assert_eq!(err_patched_tamper.code, 1);
        assert!(
            err_patched_tamper.message.contains(&format!(
                "vendor file SHA-256 mismatch for {patched_rel}: expected {expected_patched_sha}"
            )),
            "unexpected error: {err_patched_tamper}"
        );
        fs::write(&patched_lean, &orig_patched).unwrap();
    }

    // 3. Unlisted `.lean` file is rejected.
    let rogue_lean = vendor_copy.join("Miri/Rogue.lean");
    fs::write(&rogue_lean, b"def x := 1\n").unwrap();
    let err_unlisted = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_unlisted.code, 1);
    assert!(
        err_unlisted.message.contains("unlisted Lean file in vendor/lean-miri: Miri/Rogue.lean"),
        "unexpected error: {err_unlisted}"
    );
    fs::remove_file(&rogue_lean).unwrap();

    // 3b. Unlisted non-`.lean` file (e.g. a pre-compiled `.olean`) is rejected.
    let rogue_olean = vendor_copy.join("Miri/Rogue.olean");
    fs::write(&rogue_olean, b"fake-olean-bytes").unwrap();
    let err_rogue_olean = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_rogue_olean.code, 1);
    assert!(
        err_rogue_olean.message.contains("unlisted file in vendor/lean-miri: Miri/Rogue.olean"),
        "unexpected error: {err_rogue_olean}"
    );
    fs::remove_file(&rogue_olean).unwrap();

    // 3c. Deleted pinned `.lean` file is rejected.
    fs::remove_file(&target_lean).unwrap();
    let err_deleted_lean = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_deleted_lean.code, 1);
    assert!(
        err_deleted_lean.message.contains("missing pinned .lean file in vendor/lean-miri"),
        "unexpected error: {err_deleted_lean}"
    );
    fs::write(&target_lean, &orig_lean).unwrap();

    // 3d. Deleted pinned auxiliary file is rejected.
    let target_aux = vendor_copy.join("LICENSE-MIT");
    let orig_aux = fs::read(&target_aux).unwrap();
    fs::remove_file(&target_aux).unwrap();
    let err_deleted_aux = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_deleted_aux.code, 1);
    assert!(
        err_deleted_aux.message.contains("missing pinned auxiliary file in vendor/lean-miri"),
        "unexpected error: {err_deleted_aux}"
    );
    fs::write(&target_aux, &orig_aux).unwrap();

    // 4. Symlink inside `vendor/lean-miri` is rejected.
    #[cfg(unix)]
    {
        let link_path = vendor_copy.join("Miri/Symlink.lean");
        std::os::unix::fs::symlink(&target_lean, &link_path).unwrap();
        let err_symlink = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
        assert_eq!(err_symlink.code, 1);
        assert!(
            err_symlink.message.contains("symlink forbidden in vendor/lean-miri"),
            "unexpected error: {err_symlink}"
        );
        fs::remove_file(&link_path).unwrap();
    }

    // 5. Modifying `UPSTREAM_PIN.json` without updating
    // `LOCKED_UPSTREAM_PIN_SHA256` is rejected before JSON parsing (both for
    // structured edits and malformed JSON). Structural pin-bytes checks
    // (`patched_files`, `vendor_tree`, `execution_machine_closure`) are
    // covered directly via `verify_upstream_pin_bytes` in `miri_pin.rs`.
    let pin_path = vendor_copy.join("UPSTREAM_PIN.json");
    let orig_pin_bytes = fs::read(&pin_path).unwrap();
    let mut pin_notes_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
    pin_notes_json["notes"].as_array_mut().unwrap().push(json!("extra note"));
    fs::write(&pin_path, serde_json::to_vec(&pin_notes_json).unwrap()).unwrap();
    let err_pin_sha = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_pin_sha.code, 1);
    assert!(
        err_pin_sha.message.contains("UPSTREAM_PIN.json SHA-256 differs from locked digest"),
        "unexpected error: {err_pin_sha}"
    );

    fs::write(&pin_path, b"{not valid json").unwrap();
    let err_bad_json_sha = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_bad_json_sha.code, 1);
    assert!(
        err_bad_json_sha.message.contains("UPSTREAM_PIN.json SHA-256 differs from locked digest"),
        "unexpected error: {err_bad_json_sha}"
    );

    // 6. Missing `UPSTREAM_PIN.json` is rejected with policy exit code `1`.
    fs::remove_file(&pin_path).unwrap();
    let err_missing_pin = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_missing_pin.code, 1);
    assert!(
        err_missing_pin.message.contains("missing UPSTREAM_PIN.json"),
        "unexpected error: {err_missing_pin}"
    );
}

/// Verifies that `upstream/source-lock.json` conforms to `SourceLock`'s closed
/// schema (admitting only the upstream `c92d1d97` `null` `**HASH**` on
/// `upstream/rustc-source/Cargo.lock`) and rejects unknown top-level or nested
/// fields, stray `**HASH**` elsewhere, malformed digests, blank/padded
/// components, non-canonical paths, bad `schema_version`, and duplicate paths.
#[test]
fn verifies_source_lock_schema_and_rejects_malformed_records() {
    let checkout = repo_root();
    let source_lock_bytes =
        fs::read(checkout.join("vendor/lean-miri/upstream/source-lock.json")).unwrap();
    let parsed = anneal_audit::verify_source_lock_bytes(&source_lock_bytes).unwrap();
    assert_eq!(parsed.schema_version, 1);
    assert_eq!(parsed.files.len(), 707);
    assert_eq!(parsed.supporting_files.len(), 12);

    // Future upstream lockfiles that remove the legacy `"**HASH**": null` on
    // `upstream/rustc-source/Cargo.lock` must still validate cleanly.
    let mut cleaned_lock: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    cleaned_lock["supporting_files"][11].as_object_mut().unwrap().remove("**HASH**");
    anneal_audit::verify_source_lock_bytes(&serde_json::to_vec(&cleaned_lock).unwrap()).unwrap();

    let expect_policy = |val: &serde_json::Value, needle: &str| {
        let err =
            anneal_audit::verify_source_lock_bytes(&serde_json::to_vec(val).unwrap()).unwrap_err();
        assert_eq!(err.code, 1, "expected policy error for {needle}, got {err}");
        assert!(err.message.contains(needle), "expected {needle:?} in: {err}");
    };

    // On-disk modification of `upstream/source-lock.json` is rejected by
    // `verify_upstream_pin`.
    let tmp = tempfile::tempdir().unwrap();
    let vendor_copy = tmp.path().join("vendor/lean-miri");
    copy_dir_all(&checkout.join("vendor/lean-miri"), &vendor_copy).unwrap();
    let mut disk_lock: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    disk_lock["supporting_files"][0]
        .as_object_mut()
        .unwrap()
        .insert("**HASH**".to_string(), serde_json::Value::Null);
    fs::write(
        vendor_copy.join("upstream/source-lock.json"),
        serde_json::to_vec(&disk_lock).unwrap(),
    )
    .unwrap();
    let err_disk = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_disk.code, 1);
    assert!(
        err_disk.message.contains("vendor aux file SHA-256 mismatch for upstream/source-lock.json"),
        "unexpected error: {err_disk}"
    );

    // Stray `**HASH**` is rejected on any other record, when non-null on the
    // legacy record, or anywhere in `files`.
    expect_policy(&disk_lock, "unexpected `**HASH**` field in `supporting_files`");

    let mut non_null_legacy: serde_json::Value =
        serde_json::from_slice(&source_lock_bytes).unwrap();
    non_null_legacy["supporting_files"][11]["**HASH**"] = serde_json::json!("override");
    expect_policy(&non_null_legacy, "unexpected `**HASH**` field in `supporting_files`");

    let mut file_stray: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    file_stray["files"][0]
        .as_object_mut()
        .unwrap()
        .insert("**HASH**".to_string(), serde_json::Value::Null);
    expect_policy(&file_stray, "unexpected `**HASH**` field in `files`");

    let mut moved_legacy: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    let legacy_record = moved_legacy["supporting_files"].as_array_mut().unwrap().pop().unwrap();
    assert_eq!(legacy_record["path"].as_str(), Some("upstream/rustc-source/Cargo.lock"));
    moved_legacy["files"].as_array_mut().unwrap().push(legacy_record);
    expect_policy(
        &moved_legacy,
        "unexpected `**HASH**` field in `files` record for upstream/rustc-source/Cargo.lock",
    );

    // Unknown fields at top level and across nested `deny_unknown_fields`
    // structs must fail closed.
    let mut top_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    top_extra.as_object_mut().unwrap().insert("unexpected".to_string(), serde_json::json!(true));
    expect_policy(&top_extra, "unknown field `unexpected`");

    let mut file_rec_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    file_rec_extra["files"][0]
        .as_object_mut()
        .unwrap()
        .insert("extra_file_key".to_string(), serde_json::json!(1));
    expect_policy(&file_rec_extra, "unknown field `extra_file_key`");

    let mut pins_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    pins_extra["pins"]
        .as_object_mut()
        .unwrap()
        .insert("extra_pins_key".to_string(), serde_json::json!(1));
    expect_policy(&pins_extra, "unknown field `extra_pins_key`");

    let mut pin_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    pin_extra["pins"]["rustc"]
        .as_object_mut()
        .unwrap()
        .insert("extra_pin_key".to_string(), serde_json::json!(1));
    expect_policy(&pin_extra, "unknown field `extra_pin_key`");

    let mut acq_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    acq_extra["acquisition"]
        .as_object_mut()
        .unwrap()
        .insert("extra_acq_key".to_string(), serde_json::json!(1));
    expect_policy(&acq_extra, "unknown field `extra_acq_key`");

    let mut sel_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    sel_extra["acquisition"]["rustc_selected_archive_paths"]
        .as_object_mut()
        .unwrap()
        .insert("extra_sel_key".to_string(), serde_json::json!(1));
    expect_policy(&sel_extra, "unknown field `extra_sel_key`");

    let mut ext_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    ext_extra["external_dependencies"]
        .as_object_mut()
        .unwrap()
        .insert("extra_ext_key".to_string(), serde_json::json!(1));
    expect_policy(&ext_extra, "unknown field `extra_ext_key`");

    let mut cargo_pkg_extra: serde_json::Value =
        serde_json::from_slice(&source_lock_bytes).unwrap();
    cargo_pkg_extra["external_dependencies"]["cargo_packages"][0]
        .as_object_mut()
        .unwrap()
        .insert("extra_pkg_key".to_string(), serde_json::json!(1));
    expect_policy(&cargo_pkg_extra, "unknown field `extra_pkg_key`");

    let mut rustc_crate_extra: serde_json::Value =
        serde_json::from_slice(&source_lock_bytes).unwrap();
    rustc_crate_extra["external_dependencies"]["rustc_private_crates"][0]
        .as_object_mut()
        .unwrap()
        .insert("extra_crate_key".to_string(), serde_json::json!(1));
    expect_policy(&rustc_crate_extra, "unknown field `extra_crate_key`");

    let mut res_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    res_extra["external_dependencies"]["resolution_file"]
        .as_object_mut()
        .unwrap()
        .insert("extra_res_key".to_string(), serde_json::json!(1));
    expect_policy(&res_extra, "unknown field `extra_res_key`");

    // Schema version, acquisition, resolution file, and pin field validations.
    let mut bad_ver: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_ver["schema_version"] = serde_json::json!(2);
    expect_policy(&bad_ver, "unsupported upstream/source-lock.json schema_version: 2");

    let mut bad_acq: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_acq["acquisition"]["rustc_selected_archive_paths"]["count"] = serde_json::json!(0);
    expect_policy(&bad_acq, "invalid `acquisition` metadata");

    let mut bad_res: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_res["external_dependencies"]["resolution_file"]["sha256"] = serde_json::json!("bad");
    expect_policy(&bad_res, "invalid `resolution_file` record");

    let mut bad_pin: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_pin["pins"]["rustc"]["commit"] = serde_json::json!("short");
    expect_policy(&bad_pin, "invalid `rustc` pin record");

    // Malformed `files` and `supporting_files` records, non-canonical paths,
    // padded components, and intra/cross-section duplicate paths.
    let mut empty_files: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    empty_files["files"] = serde_json::json!([]);
    expect_policy(&empty_files, "upstream/source-lock.json `files` must not be empty");

    let mut bad_file_blob: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_file_blob["files"][0]["git_blob"] = serde_json::json!("bad-blob");
    expect_policy(&bad_file_blob, "invalid `files` git_blob");

    let mut bad_blob: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_blob["supporting_files"][0]["git_blob"] = serde_json::json!("not-a-40-hex-oid");
    expect_policy(&bad_blob, "invalid `supporting_files` git_blob");

    let mut bad_sha: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_sha["supporting_files"][0]["sha256"] = serde_json::json!("deadbeef");
    expect_policy(&bad_sha, "invalid `supporting_files` sha256");

    for bad_component in ["   ", " aes", "aes "] {
        let mut bad_comp: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
        bad_comp["supporting_files"][0]["component"] = serde_json::json!(bad_component);
        expect_policy(&bad_comp, "invalid `supporting_files` component name");
    }

    for non_canon in
        ["../escape", "upstream//a", "upstream/./a", "upstream/a/", "/abs/path", "upstream\\a"]
    {
        let mut dirty_path: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
        dirty_path["supporting_files"][0]["path"] = serde_json::json!(non_canon);
        expect_policy(&dirty_path, "invalid `supporting_files` path");
    }

    let mut dup_path: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    let dup_entry = dup_path["supporting_files"][0].clone();
    dup_path["supporting_files"].as_array_mut().unwrap().push(dup_entry);
    expect_policy(&dup_path, "duplicate `supporting_files` path");

    let mut cross_dup: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    let file_entry = cross_dup["files"][0].clone();
    cross_dup["supporting_files"].as_array_mut().unwrap().push(file_entry);
    expect_policy(&cross_dup, "duplicate `supporting_files` path");

    // Unknown component, unpaired manifest fields, non-canonical
    // `extracted_root`, malformed `pin_markers`, and blank metadata.
    let mut bad_component: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_component["files"][0]["component"] = serde_json::json!("unknown_dep");
    expect_policy(&bad_component, "invalid `files` component name");

    let mut unpaired_manifest: serde_json::Value =
        serde_json::from_slice(&source_lock_bytes).unwrap();
    unpaired_manifest["pins"]["rustc"]
        .as_object_mut()
        .unwrap()
        .remove("extracted_paths_manifest_sha256");
    expect_policy(&unpaired_manifest, "invalid `rustc` pin record");

    let mut bad_extracted_root: serde_json::Value =
        serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_extracted_root["pins"]["aes"]["extracted_root"] = serde_json::json!("../aes");
    expect_policy(&bad_extracted_root, "invalid `aes` pin record");

    let mut bad_marker: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_marker["acquisition"]["pin_markers"]["miri"] = serde_json::json!("/abs/miri.commit");
    expect_policy(&bad_marker, "invalid `acquisition` metadata");

    let mut empty_notes: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    empty_notes["scope_notes"] = serde_json::json!([]);
    expect_policy(&empty_notes, "invalid coverage or feature metadata");

    let mut empty_cargo_pkgs: serde_json::Value =
        serde_json::from_slice(&source_lock_bytes).unwrap();
    empty_cargo_pkgs["external_dependencies"]["cargo_packages"] = serde_json::json!([]);
    expect_policy(&empty_cargo_pkgs, "invalid `external_dependencies` metadata");

    let mut blank_cargo_name: serde_json::Value =
        serde_json::from_slice(&source_lock_bytes).unwrap();
    blank_cargo_name["external_dependencies"]["cargo_packages"][0]["name"] =
        serde_json::json!(" ");
    expect_policy(&blank_cargo_name, "invalid `external_dependencies` metadata");

    let mut bad_rustc_sha: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_rustc_sha["external_dependencies"]["rustc_private_crates"][0]["checksum"] =
        serde_json::json!("not-a-sha256");
    expect_policy(&bad_rustc_sha, "invalid `external_dependencies` metadata");

    let mut bad_cov_root: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_cov_root["external_dependencies"]["rustc_private_crates"][0]["coverage_roots"] =
        serde_json::json!(["../escape"]);
    expect_policy(&bad_cov_root, "invalid `external_dependencies` metadata");

    let mut blank_native: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    blank_native["external_dependencies"]["toolchain_and_native"] = serde_json::json!([""]);
    expect_policy(&blank_native, "invalid `external_dependencies` metadata");

    // Each case violates exactly one admission predicate of an otherwise valid
    // lock, so deleting that predicate lets the case pass validation or fail
    // with a different message.
    const ACQ: &str = "invalid `acquisition` metadata";
    const EXT: &str = "invalid `external_dependencies` metadata";
    const COV: &str = "invalid coverage or feature metadata";
    const FILE_COMPONENT: &str = "invalid `files` component name";
    type Mutation = fn(&mut serde_json::Value);
    let cases: &[(&str, Mutation)] = &[
        (ACQ, |v| v["acquisition"]["note"] = serde_json::json!(" ")),
        (ACQ, |v| v["acquisition"]["note"] = serde_json::json!("note ")),
        (ACQ, |v| {
            v["acquisition"]["pin_markers"]["extra"] =
                serde_json::json!("upstream/.pins/extra.commit");
        }),
        (ACQ, |v| {
            let markers = v["acquisition"]["pin_markers"].as_object_mut().unwrap();
            let aes = markers.remove("aes").unwrap();
            markers.insert("aes2".to_owned(), aes);
        }),
        ("invalid `resolution_file` record", |v| {
            v["external_dependencies"]["resolution_file"]["note"] = serde_json::json!("");
        }),
        ("invalid `rustc_upstream_resolution_file` record", |v| {
            v["external_dependencies"]["rustc_upstream_resolution_file"]["note"] =
                serde_json::json!(" padded");
        }),
        (EXT, |v| v["external_dependencies"]["cargo_packages"][0]["scope"] = serde_json::json!("")),
        (EXT, |v| {
            v["external_dependencies"]["cargo_packages"][0]["version"] = serde_json::json!(" ");
        }),
        (EXT, |v| {
            v["external_dependencies"]["cargo_packages"][1]["requirement"] = serde_json::json!("");
        }),
        (EXT, |v| {
            let pkg = &mut v["external_dependencies"]["cargo_packages"][20];
            assert!(pkg.get("path").is_some(), "fixture package 20 must set `path`");
            pkg["path"] = serde_json::json!(" ");
        }),
        (EXT, |v| {
            v["external_dependencies"]["cargo_packages"][0]["features"] =
                serde_json::json!(["hazmat", " "]);
        }),
        (EXT, |v| v["external_dependencies"]["rustc_private_crates"] = serde_json::json!([])),
        (EXT, |v| {
            v["external_dependencies"]["rustc_private_crates"][0]["name"] = serde_json::json!("");
        }),
        (EXT, |v| {
            v["external_dependencies"]["rustc_private_crates"][0]["status"] =
                serde_json::json!(" ");
        }),
        (EXT, |v| {
            v["external_dependencies"]["rustc_private_crates"][0]["evidence"] =
                serde_json::json!("");
        }),
        (EXT, |v| {
            v["external_dependencies"]["rustc_private_crates"][1]["version"] =
                serde_json::json!(" ");
        }),
        (EXT, |v| {
            v["external_dependencies"]["rustc_private_crates"][1]["git_commit"] =
                serde_json::json!("short");
        }),
        (EXT, |v| v["external_dependencies"]["toolchain_and_native"] = serde_json::json!([])),
        (COV, |v| v["coverage_roots"] = serde_json::json!([])),
        (COV, |v| v["coverage_roots"][0] = serde_json::json!("upstream//escape")),
        (COV, |v| v["coverage_expected_rust_modules"] = serde_json::json!({})),
        (COV, |v| v["coverage_expected_rust_modules"]["upstream/./src"] = serde_json::json!(1)),
        (COV, |v| {
            let modules = v["coverage_expected_rust_modules"].as_object_mut().unwrap();
            *modules.values_mut().next().unwrap() = serde_json::json!(0);
        }),
        (COV, |v| v["features"] = serde_json::json!({})),
        (COV, |v| v["features"][" "] = serde_json::json!(["stack-cache"])),
        (COV, |v| v["features"]["default"] = serde_json::json!(["stack-cache", ""])),
        (COV, |v| v["scope_notes"] = serde_json::json!([" "])),
        ("invalid `rustc` pin record", |v| {
            v["pins"]["rustc"]["extracted_paths_manifest"] = serde_json::json!("../paths.txt");
        }),
        ("invalid `rustc` pin record", |v| {
            v["pins"]["rustc"].as_object_mut().unwrap().remove("extracted_paths_manifest");
        }),
        ("invalid `aes` pin record", |v| {
            v["pins"]["aes"]["checksum_source"] = serde_json::json!(" ");
        }),
        ("invalid `aes` pin record", |v| {
            v["pins"]["aes"]["package_version"] = serde_json::json!("");
        }),
        ("invalid `miri` pin record", |v| {
            v["pins"]["miri"]["commit_date_utc"] = serde_json::json!("");
        }),
        ("invalid `miri` pin record", |v| v["pins"]["miri"]["commit_url"] = serde_json::json!(" ")),
        ("invalid `miri` pin record", |v| v["pins"]["miri"]["pinned_via"] = serde_json::json!("")),
        ("invalid `miri` pin record", |v| {
            v["pins"]["miri"]["archive_url"] = serde_json::json!(" padded");
        }),
        ("invalid `miri` pin record", |v| {
            v["pins"]["miri"]["repository"] = serde_json::json!("padded ");
        }),
        ("invalid `rustc_apfloat` pin record", |v| {
            v["pins"]["rustc_apfloat"]["registry"] = serde_json::json!(" ");
        }),
        (FILE_COMPONENT, |v| v["files"][0]["component"] = serde_json::json!("rustc_")),
        (FILE_COMPONENT, |v| v["files"][0]["component"] = serde_json::json!("rustc_Abi")),
    ];
    for (needle, mutate) in cases {
        let mut lock: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
        mutate(&mut lock);
        expect_policy(&lock, needle);
    }
}

/// Verifies that `"correspondence-audit"` rejects a `.vendorMiri` module that
/// declares a constant in the reserved `Trusted` or `Anneal` root namespace
/// (including a `private` declaration), declares an `axiom` or `unsafe`
/// constant, or directly references `sorryAx`, `Lean.ofReduceBool`, or
/// `Lean.trustCompiler`, while a benign vendor constant passes those checks
/// and standalone kernel replay and fails only later at unconditional
/// `closureCorr` (`unknown declaration origin:
/// Miri.Interpreter.ExecutionMachine.step`).
#[test]
fn rejects_vendor_constants_in_reserved_namespaces() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    let trusted_lib = checker.stage().join("lib");
    let vendor_src = checker.stage().join("src/fake-miri");
    let vendor_lib = checker.stage().join("fake-miri-lib");
    let cases: [(&str, &str, Option<&str>); 12] = [
        (
            "Miri.SpoofTrusted",
            "namespace Trusted\ndef Spoof : Nat := 0\nend Trusted\n",
            Some(
                "external module Miri.SpoofTrusted cannot declare constant \
                 Trusted.Spoof in reserved Trusted namespace",
            ),
        ),
        (
            "Miri.SpoofAnneal",
            "namespace Anneal\ndef Spoof : Nat := 0\nend Anneal\n",
            Some(
                "external module Miri.SpoofAnneal cannot declare constant \
                 Anneal.Spoof in reserved Anneal namespace",
            ),
        ),
        (
            "Miri.SpoofPrivate",
            "namespace Trusted\nprivate def hidden : Nat := 0\nend Trusted\n",
            Some("in reserved Trusted namespace"),
        ),
        (
            "Miri.SpoofAxiom",
            "namespace Miri.SpoofAxiom\naxiom spoofAx : False\nend Miri.SpoofAxiom\n",
            Some("vendor Miri module Miri.SpoofAxiom cannot declare axiom Miri.SpoofAxiom.spoofAx"),
        ),
        (
            "Miri.SpoofUnsafe",
            "namespace Miri.SpoofUnsafe\nunsafe def evil : Nat := 0\nend Miri.SpoofUnsafe\n",
            Some(
                "vendor Miri module Miri.SpoofUnsafe cannot declare unsafe \
                 constant Miri.SpoofUnsafe.evil",
            ),
        ),
        (
            "Miri.SpoofSorry",
            "namespace Miri.SpoofSorry\ntheorem spoofSorry : False := sorry\nend Miri.SpoofSorry\n",
            Some(
                "vendor Miri module Miri.SpoofSorry constant Miri.SpoofSorry.spoofSorry \
                 references sorryAx",
            ),
        ),
        (
            "Miri.SpoofOfReduceBool",
            "namespace Miri.SpoofOfReduceBool\n\
             theorem spoof (h : Lean.reduceBool true = true) : true = true := \
             Lean.ofReduceBool true true h\n\
             end Miri.SpoofOfReduceBool\n",
            Some(
                "vendor Miri module Miri.SpoofOfReduceBool constant \
                 Miri.SpoofOfReduceBool.spoof references forbidden compiler primitive",
            ),
        ),
        (
            "Miri.SpoofTrustCompiler",
            "namespace Miri.SpoofTrustCompiler\n\
             theorem spoof : True := Lean.trustCompiler\n\
             end Miri.SpoofTrustCompiler\n",
            Some(
                "vendor Miri module Miri.SpoofTrustCompiler constant \
                 Miri.SpoofTrustCompiler.spoof references forbidden compiler primitive \
                 Lean.trustCompiler",
            ),
        ),
        (
            "Miri.Interpreter.ExecutionMachine",
            "namespace Miri.Interpreter.ExecutionMachine\nunsafe def step : Nat := 0\nend Miri.Interpreter.ExecutionMachine\n",
            Some(
                "vendor Miri module Miri.Interpreter.ExecutionMachine cannot declare \
                 unsafe constant Miri.Interpreter.ExecutionMachine.step",
            ),
        ),
        (
            "Miri.Interpreter.ExecutionMachine",
            "namespace Miri.Interpreter.ExecutionMachine\npartial def step (n : Nat) : Nat := step n\nend Miri.Interpreter.ExecutionMachine\n",
            Some(
                "opaque/partial vendor Miri constant Miri.Interpreter.ExecutionMachine.step \
                 from Miri.Interpreter.ExecutionMachine in correspondence dependency cone",
            ),
        ),
        (
            "Miri.Interpreter.ExecutionMachine",
            "namespace Miri.Interpreter.ExecutionMachine\nopaque step : Nat := 0\nend Miri.Interpreter.ExecutionMachine\n",
            Some(
                "opaque/partial vendor Miri constant Miri.Interpreter.ExecutionMachine.step \
                 from Miri.Interpreter.ExecutionMachine in correspondence dependency cone",
            ),
        ),
        ("Miri.Benign", "namespace Miri.Benign\ndef ok : Nat := 0\nend Miri.Benign\n", None),
    ];
    for (module, body, expected) in cases {
        let rel = module.replace('.', "/");
        let src = vendor_src.join(format!("{rel}.lean"));
        fs::create_dir_all(src.parent().unwrap()).unwrap();
        fs::write(&src, format!("prelude\nimport Init.Core\n{body}")).unwrap();
        let out = vendor_lib.join(format!("{rel}.olean"));
        fs::create_dir_all(out.parent().unwrap()).unwrap();
        checker
            .process(
                &format!("compile-{module}"),
                &[
                    "-j1".to_string(),
                    "-M2048".to_string(),
                    "-t0".to_string(),
                    "-R".to_string(),
                    vendor_src.to_string_lossy().into_owned(),
                    "-o".to_string(),
                    out.to_string_lossy().into_owned(),
                    src.to_string_lossy().into_owned(),
                ],
            )
            .unwrap();
        let err = checker
            .inspect(InspectorRequest::CorrespondenceAudit {
                search_path: vec![trusted_lib.clone(), vendor_lib.clone()],
                trusted: vec!["Trusted".to_string()],
                corr_trusted: Vec::new(),
                theory: Vec::new(),
                corr_theory: Vec::new(),
                vendor_miri: vec![module.to_string()],
                module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            })
            .unwrap_err();
        assert_eq!(err.code, 1, "unexpected error code for {module}: {err}");
        assert_eq!(err.phase, "correspondence-audit", "unexpected phase: {err}");
        match expected {
            Some(message) => {
                assert!(err.message.contains(message), "unexpected error for {module}: {err}")
            }
            None => {
                assert!(
                    !err.message.contains("reserved"),
                    "benign vendor module {module} was rejected: {err}"
                );
                assert!(
                    err.message.contains(
                        "unknown declaration origin: Miri.Interpreter.ExecutionMachine.step"
                    ),
                    "unexpected error for {module}: {err}"
                );
            }
        }
    }
}

/// Verifies end-to-end that standalone kernel replay in Pass 2
/// (`"correspondence-audit"`) rejects an ill-typed `.vendorMiri` `.olean`
/// compiled with a scoped `set_option debug.skipKernelTC true` override (even
/// when compiled with CLI `-Ddebug.skipKernelTC=false`), and that a valid
/// minimal vendor closure passes replay and reports `miriReplay: true` with a
/// positive `miriReplayedDeclarations` count.
#[test]
fn rejects_vendor_miri_skip_kernel_tc_during_replay() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    checker.ensure_sysroot_foundation().unwrap();
    let trusted_lib = checker.stage().join("lib");
    let vendor_src = checker.stage().join("src/skip-tc-miri");
    let vendor_lib = checker.stage().join("skip-tc-miri-lib");

    // 1. Compile a vendor module whose scoped `set_option debug.skipKernelTC
    // true` overrides CLI `-Ddebug.skipKernelTC=false` to emit an ill-typed
    // theorem (`Miri.SkipKernelTC.bogus : False := True.intro`) into the
    // `.olean` without using `axiom`, `sorryAx`, `unsafe`, or compiler
    // reflection primitives.
    let bogus_src = vendor_src.join("Miri/SkipKernelTC.lean");
    let bogus_out = vendor_lib.join("Miri/SkipKernelTC.olean");
    fs::create_dir_all(bogus_src.parent().unwrap()).unwrap();
    fs::create_dir_all(bogus_out.parent().unwrap()).unwrap();
    fs::write(
        &bogus_src,
        "import Lean.Elab.Command\n\
         namespace Miri.SkipKernelTC\n\
         set_option debug.skipKernelTC true in\n\
         run_cmd\n\
           Lean.Elab.Command.liftCoreM <| Lean.addDecl <| .thmDecl {\n\
             name := `Miri.SkipKernelTC.bogus\n\
             levelParams := []\n\
             type := Lean.mkConst `False\n\
             value := Lean.mkConst `True.intro\n\
           }\n\
         end Miri.SkipKernelTC\n",
    )
    .unwrap();
    checker
        .process(
            "compile-Miri.SkipKernelTC",
            &[
                "-j1".to_string(),
                "-M4096".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_src.to_string_lossy().into_owned(),
                "-o".to_string(),
                bogus_out.to_string_lossy().into_owned(),
                bogus_src.to_string_lossy().into_owned(),
            ],
        )
        .expect(
            "Lean must accept scoped `set_option debug.skipKernelTC true` \
             at compile time to prove CLI `-Ddebug.skipKernelTC=false` alone \
             is insufficient",
        );

    let err_replay = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![trusted_lib.clone(), vendor_lib.clone()],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.SkipKernelTC".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    // Kernel replay exceptions are operational errors (exit code `2`) so no
    // stringified `Kernel.Exception` can spoof `"policy:"`.
    assert_eq!(
        err_replay.code, 2,
        "expected operational exit code 2 on kernel replay failure: {err_replay}"
    );
    assert_eq!(err_replay.phase, "correspondence-audit", "unexpected phase: {err_replay}");
    assert!(
        err_replay.message.contains("vendor Miri kernel replay failed")
            && err_replay.message.contains("Miri.SkipKernelTC.bogus")
            && err_replay.message.contains("declaration type mismatch"),
        "expected kernel replay type-mismatch rejection, got: {err_replay}"
    );

    // 2. Verify the positive path: a valid minimal `.vendorMiri` module
    // defining the 21 `ExecutionMachine` cone roots passes standalone kernel
    // replay and returns `miriReplay: true` with `miriReplayedDeclarations`
    // positive, while vendor-only mode (no correspondence modules) reports
    // `correspondenceReplay: false` with zero correspondence declarations
    // replayed.
    let valid_src = vendor_src.join("Miri/Interpreter/ExecutionMachine.lean");
    let valid_out = vendor_lib.join("Miri/Interpreter/ExecutionMachine.olean");
    fs::create_dir_all(valid_src.parent().unwrap()).unwrap();
    fs::create_dir_all(valid_out.parent().unwrap()).unwrap();
    fs::write(
        &valid_src,
        "prelude\n\
         import Init.Core\n\
         namespace Miri.Interpreter.ExecutionMachine\n\
         def step : Nat := 0\n\
         def AllowedStep : Nat := 0\n\
         def withValidation : Nat := 0\n\
         def stepHooks : Nat := 0\n\
         def rvalueHooks : Nat := 0\n\
         def operandHooks : Nat := 0\n\
         def projectionHooks : Nat := 0\n\
         def discriminantHooks : Nat := 0\n\
         def scalarHooks : Nat := 0\n\
         end Miri.Interpreter.ExecutionMachine\n\
         namespace Miri.Interpreter.Step\n\
         def step : Nat := 0\n\
         def evalStatement : Nat := 0\n\
         end Miri.Interpreter.Step\n\
         namespace Miri.Interpreter.ControlFlow\n\
         def goToBlock : Nat := 0\n\
         def evalTerminator : Nat := 0\n\
         def returnFromCurrentFrame : Nat := 0\n\
         end Miri.Interpreter.ControlFlow\n\
         namespace Miri.Interpreter.ExecutionControl\n\
         def hooks : Nat := 0\n\
         end Miri.Interpreter.ExecutionControl\n\
         namespace Miri.Interpreter.MachineHooks\n\
         def storageLiveDyn : Nat := 0\n\
         def storageDead : Nat := 0\n\
         end Miri.Interpreter.MachineHooks\n\
         namespace Miri.Interpreter.OperandMachine\n\
         def evalOperand : Nat := 0\n\
         def evalPlaceToOp : Nat := 0\n\
         end Miri.Interpreter.OperandMachine\n\
         namespace Miri.Interpreter.PlaceMachine\n\
         def readImmediate : Nat := 0\n\
         def writeMemory : Nat := 0\n\
         end Miri.Interpreter.PlaceMachine\n\
         namespace Miri.Interpreter.ValidityVisitor\n\
         def validatePlace : Nat := 0\n\
         end Miri.Interpreter.ValidityVisitor\n\
         namespace Miri.Interpreter.ValidityMemory\n\
         def bind : Nat := 0\n\
         end Miri.Interpreter.ValidityMemory\n\
         namespace Miri.Interpreter\n\
         def evalRvalueIntoPlace : Nat := 0\n\
         def evalOperand : Nat := 0\n\
         end Miri.Interpreter\n\
         namespace Miri.Interpreter.TerminatorMachine\n\
         def beforeTerminatorWithChoice : Nat := 0\n\
         end Miri.Interpreter.TerminatorMachine\n\
         namespace Miri.Interpreter.ScalarOps\n\
         def binary : Nat := 0\n\
         def unary : Nat := 0\n\
         end Miri.Interpreter.ScalarOps\n\
         namespace Miri.Interpreter.IntegerOps\n\
         def binary : Nat := 0\n\
         def binaryBool : Nat := 0\n\
         def unary : Nat := 0\n\
         end Miri.Interpreter.IntegerOps\n\
         namespace Miri.Interpreter.Discriminant\n\
         def readDiscriminant : Nat := 0\n\
         def discriminantForVariant : Nat := 0\n\
         end Miri.Interpreter.Discriminant\n\
         namespace Miri.Memory.ScalarInt\n\
         def truncateFromUInt : Nat := 0\n\
         def tryFromUInt : Nat := 0\n\
         def tryToBool : Nat := 0\n\
         end Miri.Memory.ScalarInt\n",
    )
    .unwrap();
    checker
        .process(
            "compile-Miri.Interpreter.ExecutionMachine",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_src.to_string_lossy().into_owned(),
                "-o".to_string(),
                valid_out.to_string_lossy().into_owned(),
                valid_src.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();

    let ok_rep = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![trusted_lib, vendor_lib],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Interpreter.ExecutionMachine".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap();
    assert_eq!(ok_rep.get("miriReplay"), Some(&json!(true)));
    assert_eq!(ok_rep.get("miriReplayedDeclarations").and_then(Json::as_u64), Some(36));
    assert_eq!(ok_rep.get("correspondenceReplay"), Some(&json!(false)));
    for zero_field in ["correspondenceDeclarations", "correspondenceReplayedDeclarations"] {
        assert_eq!(
            ok_rep.get(zero_field).and_then(Json::as_u64),
            Some(0),
            "unexpected {zero_field}: {ok_rep}"
        );
    }
    assert!(
        ok_rep
            .get("miriClosureReachableDeclarations")
            .and_then(Json::as_u64)
            .is_some_and(|n| n >= 36),
        "unexpected reachable declarations: {ok_rep}"
    );
    assert_eq!(ok_rep.get("miriClosureAxioms"), Some(&json!([])));
}
