// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `--artifacts` destinations, early failure receipts, and
//! `--overwrite-artifacts`.

use super::*;

#[cfg(unix)]
#[test]
fn rejects_non_utf8_artifact_paths_before_staging_or_retention() {
    use std::{ffi::OsString, fs, os::unix::ffi::OsStringExt};

    let project = tempfile::tempdir().expect("create artifact-path fixture");
    let request = project.path().join("request.json");
    let request_bytes = b"not JSON\n";
    fs::write(&request, request_bytes).unwrap();
    for route in [Route::Direct, Route::Cargo] {
        let absent = project.path().join(OsString::from_vec(
            format!("{route:?}-new-").into_bytes().into_iter().chain([0xff]).collect(),
        ));
        let existing = project.path().join(OsString::from_vec(
            format!("{route:?}-existing-").into_bytes().into_iter().chain([0xff]).collect(),
        ));
        fs::create_dir(&existing).unwrap();
        fs::write(existing.join("keep"), b"caller evidence").unwrap();
        for destination in [&absent, &existing] {
            let mut cmd = command(route, project.path());
            cmd.args(["verify", "--format", "json"])
                .arg("--request")
                .arg(&request)
                .arg("--artifacts")
                .arg(destination);
            #[cfg(not(feature = "setup"))]
            cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
            let output = cmd.output().unwrap();
            assert_result(&output, 2, "", "");
            assert!(output.stderr.is_empty(), "{output:?}");
            let receipt: serde_json::Value = serde_json::from_slice(&output.stdout)
                .expect("invalid artifact path returns a JSON receipt");
            assert_eq!(receipt["schema_version"], 3);
            assert_eq!(receipt["taint_reasons"], serde_json::json!([]));
            assert!(receipt.get("tainted").is_none(), "{receipt}");
            assert_eq!(receipt["status"], "tool_failed");
            assert_eq!(receipt["phase"], "retention");
            assert_eq!(receipt["detail"], "artifact destination path must be UTF-8");
            assert!(receipt.get("artifacts").is_none(), "{receipt}");
            assert!(!absent.exists());
            assert_eq!(fs::read(existing.join("keep")).unwrap(), b"caller evidence");
            assert_eq!(fs::read_dir(&existing).unwrap().count(), 1);
            assert_eq!(fs::read(&request).unwrap(), request_bytes);
        }
        // A missing temp parent would fail stage creation. The encoding check
        // must run first, without reading a request or creating either path.
        let missing_tmp = project.path().join(format!("{route:?}-missing-temp"));
        let mut cmd = command(route, project.path());
        cmd.env("TMPDIR", &missing_tmp)
            .args(["verify", "--format", "json"])
            .arg("--request")
            .arg(project.path().join("missing-request"))
            .arg("--artifacts")
            .arg(&absent);
        #[cfg(not(feature = "setup"))]
        cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let output = cmd.output().unwrap();
        assert_result(&output, 2, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["schema_version"], 3);
        assert_eq!(receipt["taint_reasons"], serde_json::json!([]));
        assert_eq!(receipt["phase"], "retention");
        assert_eq!(receipt["detail"], "artifact destination path must be UTF-8");
        assert!(!missing_tmp.exists());
        assert!(!absent.exists());

        // UTF-8 paths retain the normal rejected-request evidence and receipt.
        // This control needs no compiler or Lean process.
        let ordinary = project.path().join(format!("{route:?}-ordinary-evidence"));
        let mut cmd = command(route, project.path());
        cmd.args(["verify", "--format", "json"])
            .arg("--request")
            .arg(&request)
            .arg("--artifacts")
            .arg(&ordinary);
        #[cfg(not(feature = "setup"))]
        cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let output = cmd.output().unwrap();
        assert_result(&output, 1, "", "");
        assert!(output.stderr.is_empty(), "{output:?}");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["schema_version"], 3);
        assert_eq!(receipt["taint_reasons"], serde_json::json!([]));
        assert_eq!(receipt["status"], "unsupported");
        assert_eq!(receipt["phase"], "request");
        assert_eq!(receipt["artifacts"].as_str(), ordinary.to_str());
        assert!(ordinary.is_dir());
        assert_eq!(fs::read(&request).unwrap(), request_bytes);
    }
}

#[test]
fn early_verification_failures_have_versioned_receipts() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let existing = project.path().join("existing");
    fs::create_dir(&existing).unwrap();
    fs::write(existing.join("keep"), b"caller evidence").unwrap();
    for route in [Route::Direct, Route::Cargo] {
        for phase in ["staging", "retention"] {
            let mut child = command(route, project.path());
            child.args(["verify", "--format", "json"]).arg("--request").arg(&request);
            #[cfg(not(feature = "setup"))]
            child.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
            if phase == "staging" {
                child.env("TMPDIR", project.path().join("missing-temp"));
            } else {
                child.arg("--artifacts").arg(&existing);
            }
            let output = child.output().unwrap();
            assert_result(&output, 2, "", "");
            assert!(output.stderr.is_empty(), "{output:?}");
            let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
            assert_eq!(receipt["schema_version"], 3, "{receipt}");
            assert_eq!(receipt["taint_reasons"], serde_json::json!([]));
            assert!(receipt.get("tainted").is_none(), "{receipt}");
            assert_eq!(receipt["status"], "tool_failed");
            assert_eq!(receipt["phase"], phase);
            assert_eq!(fs::read(existing.join("keep")).unwrap(), b"caller evidence");
            assert_eq!(fs::read_dir(&existing).unwrap().count(), 1);
        }
    }
}

#[test]
fn overwrite_artifacts_replaces_only_earlier_artifacts() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let destination = project.path().join("evidence");
    let run = |route: Route, overwrite: bool| {
        let mut child = command(route, project.path());
        child
            .args(["verify", "--format", "json"])
            .arg("--request")
            .arg(&request)
            .arg("--artifacts")
            .arg(&destination);
        if overwrite {
            child.arg("--overwrite-artifacts");
        }
        #[cfg(not(feature = "setup"))]
        child.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let output = child.output().unwrap();
        let receipt: serde_json::Value =
            serde_json::from_slice(&output.stdout).unwrap_or_else(|e| panic!("{e}: {output:?}"));
        (output, receipt)
    };
    // The rejected request needs no compiler or Lean process, yet retains
    // its (empty) evidence directory each time.
    for route in [Route::Direct, Route::Cargo] {
        let (output, receipt) = run(route, true);
        assert_result(&output, 1, "", "");
        assert_eq!(receipt["phase"], "request", "{receipt}");
        assert_eq!(receipt["artifacts"].as_str(), destination.to_str());
        assert!(destination.is_dir());
        // Without the flag, the existing destination is still refused.
        let (output, receipt) = run(route, false);
        assert_result(&output, 2, "", "");
        assert_eq!(receipt["phase"], "retention", "{receipt}");
        assert!(receipt["detail"].as_str().unwrap().contains("--overwrite-artifacts"), "{receipt}");
    }
    // An earlier artifact entry is replaced; no staging siblings remain.
    fs::write(destination.join("request.json"), b"earlier").unwrap();
    let (output, _) = run(Route::Direct, true);
    assert_result(&output, 1, "", "");
    assert!(!destination.join("request.json").exists());
    let names: Vec<_> = fs::read_dir(project.path())
        .unwrap()
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .filter(|n| n.contains("anneal-"))
        .collect();
    assert!(names.is_empty(), "{names:?}");
    // A foreign entry blocks replacement before staging.
    fs::write(destination.join("notes.txt"), b"caller notes").unwrap();
    let (output, receipt) = run(Route::Direct, true);
    assert_result(&output, 2, "", "");
    assert_eq!(receipt["phase"], "retention", "{receipt}");
    assert!(receipt["detail"].as_str().unwrap().contains("notes.txt"), "{receipt}");
    assert_eq!(fs::read(destination.join("notes.txt")).unwrap(), b"caller notes");
    #[cfg(unix)]
    {
        let link = project.path().join("evidence-link");
        let target = project.path().join("link-target");
        fs::create_dir(&target).unwrap();
        std::os::unix::fs::symlink(&target, &link).unwrap();
        let mut child = command(Route::Direct, project.path());
        child
            .args(["verify", "--format", "json"])
            .arg("--request")
            .arg(&request)
            .arg("--artifacts")
            .arg(&link)
            .arg("--overwrite-artifacts");
        #[cfg(not(feature = "setup"))]
        child.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let output = child.output().unwrap();
        assert_result(&output, 2, "symlink", "");
        assert!(fs::symlink_metadata(&link).unwrap().is_symlink());
        assert_eq!(fs::read_dir(&target).unwrap().count(), 0);
    }
}

/// `--overwrite-artifacts` never deletes the caller's inputs: a destination
/// holding the `--request` file, or a source root that a readable request
/// declares, is refused before staging and left untouched.
#[test]
fn overwrite_artifacts_refuses_destinations_holding_inputs() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let destination = project.path().join("ev");
    fs::create_dir_all(destination.join("rust")).unwrap();
    fs::write(destination.join(".cargo-anneal-artifacts"), "cargo-anneal verification artifacts\n")
        .unwrap();
    let lib = include_str!("../../../../trusted/cargo-anneal/assets/scalar/lib.rs");
    fs::write(destination.join("rust/lib.rs"), lib).unwrap();
    let inner_request = destination.join("request.json");
    fs::write(&inner_request, b"not JSON\n").unwrap();
    let outer_request = project.path().join("outer.json");
    fs::write(
        &outer_request,
        serde_json::json!({
            "schema_version": 1,
            "compilation": {
                "source_root": "ev/rust",
                "crate_root": "lib.rs",
                "crate_name": "scalar",
                "source_files": ["lib.rs"],
            },
            "scope": {"kind": "selected_unit", "roots": ["zero"]},
            "proof": {"source_root": ".", "sources": []},
        })
        .to_string(),
    )
    .unwrap();
    for request in [&inner_request, &outer_request] {
        let mut child = command(Route::Direct, project.path());
        child
            .args(["verify", "--format", "json", "--request"])
            .arg(request)
            .arg("--artifacts")
            .arg(&destination)
            .arg("--overwrite-artifacts")
            .args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let output = child.output().unwrap();
        assert_result(&output, 2, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["phase"], "retention", "{receipt}");
        assert!(receipt["detail"].as_str().unwrap().contains("verification input"), "{receipt}");
        assert_eq!(fs::read(&inner_request).unwrap(), b"not JSON\n");
        assert_eq!(fs::read_to_string(destination.join("rust/lib.rs")).unwrap(), lib);
    }
}

/// An earlier run's success evidence (`result.json`, `lean-lib/`) never
/// survives a later failing `--overwrite-artifacts` run.
#[test]
fn overwrite_artifacts_drops_earlier_success_evidence_on_failure() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let destination = project.path().join("evidence");
    fs::create_dir_all(destination.join("lean-lib/Proof")).unwrap();
    fs::write(destination.join(".cargo-anneal-artifacts"), "cargo-anneal verification artifacts\n")
        .unwrap();
    fs::write(destination.join("result.json"), b"{\"status\":\"crate_verified\"}").unwrap();
    fs::write(destination.join("lean-lib/Proof/Proof.olean"), b"olean").unwrap();
    let mut child = command(Route::Direct, project.path());
    child
        .args(["verify", "--format", "json", "--request"])
        .arg(&request)
        .arg("--artifacts")
        .arg(&destination)
        .arg("--overwrite-artifacts");
    #[cfg(not(feature = "setup"))]
    child.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let output = child.output().unwrap();
    assert_result(&output, 1, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["phase"], "request", "{receipt}");
    assert_eq!(receipt["artifacts"].as_str(), destination.to_str(), "{receipt}");
    assert!(!destination.join("result.json").exists());
    assert!(!destination.join("lean-lib").exists());
    assert!(destination.join(".cargo-anneal-artifacts").is_file());
}

/// A run that stages every early entry, including a `--verify-shard-plan`
/// snapshot (`expected-shard-plan.json`), leaves a retained directory that a
/// rerun with `--overwrite-artifacts` must still recognize and replace.
#[test]
fn overwrite_artifacts_replaces_retained_shard_plan_snapshot() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    for (name, contents) in [
        ("lib.rs", include_str!("../../../../trusted/cargo-anneal/assets/scalar/lib.rs")),
        (
            "request.json",
            include_str!("../../../../trusted/cargo-anneal/assets/scalar/request.json"),
        ),
        ("Spec.lean", include_str!("../../../../trusted/cargo-anneal/assets/scalar/Spec.lean")),
        ("Proof.lean", include_str!("../../../../trusted/cargo-anneal/assets/scalar/Proof.lean")),
    ] {
        fs::write(project.path().join(name), contents).unwrap();
    }
    let plan = project.path().join("anneal-shards.json");
    fs::write(
        &plan,
        serde_json::json!({
            "schema_version": 1,
            "sharded": false,
            "scope": "crate",
            "shard_min_bodies": 0,
            "shard_max_bodies": 0,
            "shard_max_ast_nodes": 0,
            "total_bodies": 0,
            "total_shards": 0,
            "id_tree_sha256": null,
            "shards": [],
        })
        .to_string(),
    )
    .unwrap();
    let destination = project.path().join("evidence");
    // Nonexistent tool paths stop the run at `capture-tool`, after the
    // request and shard plan are staged, without any compiler or Lean.
    let run = |overwrite: bool| {
        let mut child = command(Route::Direct, project.path());
        child
            .args(["verify", "--format", "json", "--request"])
            .arg(project.path().join("request.json"))
            .arg("--verify-shard-plan")
            .arg(&plan)
            .arg("--artifacts")
            .arg(&destination)
            .args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        if overwrite {
            child.arg("--overwrite-artifacts");
        }
        let output = child.output().unwrap();
        let receipt: serde_json::Value =
            serde_json::from_slice(&output.stdout).unwrap_or_else(|e| panic!("{e}: {output:?}"));
        (output, receipt)
    };
    let (output, receipt) = run(false);
    assert_result(&output, 2, "", "");
    assert_eq!(receipt["phase"], "capture-tool", "{receipt}");
    assert_eq!(receipt["artifacts"].as_str(), destination.to_str(), "{receipt}");
    assert!(destination.join("expected-shard-plan.json").is_file());
    assert!(destination.join("request.json").is_file());
    fs::write(destination.join("expected-shard-plan.json"), b"earlier").unwrap();

    let (output, receipt) = run(true);
    assert_result(&output, 2, "", "");
    assert_eq!(receipt["phase"], "capture-tool", "{receipt}");
    assert_eq!(receipt["artifacts"].as_str(), destination.to_str(), "{receipt}");
    assert_eq!(
        fs::read(destination.join("expected-shard-plan.json")).unwrap(),
        fs::read(&plan).unwrap()
    );
}

#[test]
fn unclaimable_artifact_destinations_fail_before_staging_or_request_reading() {
    use std::{fs, path::PathBuf};
    let project = tempfile::tempdir().unwrap();
    let directory = project.path().join("existing-directory");
    fs::create_dir(&directory).unwrap();
    fs::write(directory.join("keep"), b"caller evidence").unwrap();
    let file = project.path().join("existing-file");
    fs::write(&file, b"caller file").unwrap();
    // Relative destinations resolve against the working directory, which
    // `command` sets to `project`.
    let base_destinations = [
        (directory.clone(), "already exists"),
        (PathBuf::from("existing-directory"), "already exists"),
        (file.clone(), "already exists"),
        (project.path().join("missing-parent/out"), "artifact destination parent"),
        (file.join("out"), "artifact destination parent"),
        (project.path().join("missing-parent/."), "must end in a new directory name"),
    ];
    #[cfg(unix)]
    let unix_destinations = {
        let dangling = project.path().join("dangling-link");
        std::os::unix::fs::symlink(project.path().join("absent-target"), &dangling).unwrap();
        // With a trailing separator, `lstat` follows the link but `mkdir`
        // still refuses it.
        vec![(PathBuf::from("dangling-link/"), "already exists"), (dangling, "already exists")]
    };
    #[cfg(not(unix))]
    let unix_destinations: [(PathBuf, &str); 0] = [];
    let destinations: Vec<_> = base_destinations.into_iter().chain(unix_destinations).collect();
    // A missing request and a missing temp parent would each fail later
    // phases. The receipt must still name retention, showing the destination
    // was rejected before staging, request parsing, capture, or Lean.
    let missing_tmp = project.path().join("missing-temp");
    for route in [Route::Direct, Route::Cargo] {
        for (destination, detail) in &destinations {
            let mut child = command(route, project.path());
            child
                .env("TMPDIR", &missing_tmp)
                .arg("verify")
                .args(["--format", "json"])
                .arg("--request")
                .arg(project.path().join("missing-request"))
                .arg("--artifacts")
                .arg(destination);
            #[cfg(not(feature = "setup"))]
            child.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
            let output = child.output().unwrap();
            assert_result(&output, 2, "", "");
            assert!(output.stderr.is_empty(), "{output:?}");
            let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
            assert_eq!(receipt["schema_version"], 3, "{receipt}");
            assert_eq!(receipt["status"], "tool_failed", "{receipt}");
            assert_eq!(receipt["phase"], "retention", "{receipt}");
            assert!(receipt["detail"].as_str().unwrap().contains(detail), "{receipt}");
            assert!(receipt.get("artifacts").is_none(), "{receipt}");
            assert!(!missing_tmp.exists());
        }
    }
    // Default human verdict card + `--receipt-out` also honor `--artifacts`
    // preflight rejection before staging.
    let receipt_file = project.path().join("preflight-receipt.json");
    let mut human_child = command(Route::Direct, project.path());
    human_child
        .env_remove("CARGO_TERM_COLOR")
        .env_remove("CLICOLOR_FORCE")
        .env_remove("FORCE_COLOR")
        .env("TMPDIR", &missing_tmp)
        .arg("verify")
        .arg("--request")
        .arg(project.path().join("missing-request"))
        .arg("--artifacts")
        .arg(&directory)
        .arg("--receipt-out")
        .arg(&receipt_file);
    #[cfg(not(feature = "setup"))]
    human_child.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let human_out = human_child.output().unwrap();
    assert_result(
        &human_out,
        2,
        "[FAIL] VERIFICATION FAILED (tool_failed in phase `retention`, exit 2)",
        "",
    );
    let written_receipt: serde_json::Value =
        serde_json::from_slice(&fs::read(&receipt_file).unwrap()).unwrap();
    assert_eq!(written_receipt["status"], "tool_failed", "{written_receipt}");
    assert_eq!(written_receipt["phase"], "retention", "{written_receipt}");
    assert!(written_receipt.get("artifacts").is_none(), "{written_receipt}");
    assert!(!missing_tmp.exists());

    assert_eq!(fs::read(directory.join("keep")).unwrap(), b"caller evidence");
    assert_eq!(fs::read_dir(&directory).unwrap().count(), 1);
    assert_eq!(fs::read(&file).unwrap(), b"caller file");
    assert!(!project.path().join("missing-parent").exists());
    assert!(!project.path().join("absent-target").exists());

    // New paths inside an existing directory, including a relative single
    // component, pass preflight and still retain rejected-request evidence.
    // This control needs no compiler or Lean process.
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    for (spelling, created) in [
        (directory.join("fresh-evidence"), directory.join("fresh-evidence")),
        (PathBuf::from("relative-evidence"), project.path().join("relative-evidence")),
    ] {
        let mut child = command(Route::Direct, project.path());
        child
            .arg("verify")
            .args(["--format", "json"])
            .arg("--request")
            .arg(&request)
            .arg("--artifacts")
            .arg(&spelling);
        #[cfg(not(feature = "setup"))]
        child.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let output = child.output().unwrap();
        assert_result(&output, 1, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["status"], "unsupported", "{receipt}");
        assert_eq!(receipt["phase"], "request", "{receipt}");
        assert_eq!(receipt["artifacts"].as_str(), spelling.to_str());
        assert!(created.is_dir());
    }

    // Late retention failure: an unwritable parent passes preflight (which does
    // not check parent write permission), runs staging and request parsing, and
    // fails in `retain_stage` (`phase: "retention"`, exit 2).
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        let readonly_parent = project.path().join("readonly-parent");
        fs::create_dir(&readonly_parent).unwrap();
        fs::set_permissions(&readonly_parent, fs::Permissions::from_mode(0o555)).unwrap();
        let probe = readonly_parent.join("probe-perm");
        match fs::create_dir(&probe) {
            Ok(()) => {
                let _ = fs::remove_dir(&probe);
            }
            Err(probe_err) => {
                let late_dest = readonly_parent.join("late-retention-fail");
                // Missing `TMPDIR` must fail in `staging` rather than
                // `retention`, proving preflight admitted `late_dest`.
                let missing_late_tmp = project.path().join("missing-late-temp");
                let mut preflight_ok_cmd = command(Route::Direct, project.path());
                preflight_ok_cmd
                    .env("TMPDIR", &missing_late_tmp)
                    .arg("verify")
                    .args(["--format", "json"])
                    .arg("--request")
                    .arg(&request)
                    .arg("--artifacts")
                    .arg(&late_dest);
                #[cfg(not(feature = "setup"))]
                preflight_ok_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
                let preflight_ok_out = preflight_ok_cmd.output().unwrap();
                assert_result(&preflight_ok_out, 2, "", "");
                let preflight_ok_rec: serde_json::Value =
                    serde_json::from_slice(&preflight_ok_out.stdout).unwrap();
                assert_eq!(preflight_ok_rec["phase"], "staging", "{preflight_ok_rec}");

                let mut late_cmd = command(Route::Direct, project.path());
                late_cmd
                    .arg("verify")
                    .args(["--format", "json"])
                    .arg("--request")
                    .arg(&request)
                    .arg("--artifacts")
                    .arg(&late_dest);
                #[cfg(not(feature = "setup"))]
                late_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
                let late_out = late_cmd.output().unwrap();
                assert_result(&late_out, 2, "", "");
                let late_rec: serde_json::Value = serde_json::from_slice(&late_out.stdout).unwrap();
                assert_eq!(late_rec["schema_version"], 3, "{late_rec}");
                assert_eq!(late_rec["status"], "tool_failed", "{late_rec}");
                assert_eq!(late_rec["phase"], "retention", "{late_rec}");
                let late_detail = late_rec["detail"].as_str().unwrap();
                assert!(!late_detail.starts_with("artifact destination"), "{late_rec}");
                assert!(late_detail.contains(&probe_err.to_string()), "{late_rec}");
                assert!(late_rec.get("artifacts").is_none(), "{late_rec}");
                assert!(!late_dest.exists());
            }
        }
        let _ = fs::set_permissions(&readonly_parent, fs::Permissions::from_mode(0o700));
    }
}
