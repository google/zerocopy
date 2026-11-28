// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Host policy conflicts, taint reporting, explicit tool paths without
//! `setup`, and `--allow-unstable-feature`.

use super::*;

#[cfg(not(feature = "setup"))]
#[test]
fn verify_without_setup_feature_requires_explicit_tool_paths() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let rust = project.path().join("rust");
    fs::create_dir(&rust).unwrap();
    fs::write(rust.join("lib.rs"), b"pub fn zero() -> u64 { 0 }\n").unwrap();
    let request = project.path().join("request.json");
    fs::write(
        &request,
        serde_json::to_vec(&serde_json::json!({
            "schema_version": 1,
            "compilation": {
                "source_root": rust,
                "crate_root": "lib.rs",
                "crate_name": "fixture",
                "edition": "2024",
                "target": "x86_64-unknown-linux-gnu",
                "source_files": ["lib.rs"]
            },
            "scope": {"kind": "crate"},
            "proof": {"source_root": "unused", "sources": []}
        }))
        .unwrap(),
    )
    .unwrap();

    for route in [Route::Direct, Route::Cargo] {
        for extra in [&[][..], &["--capture", "cap", "--sysroot", "sys"], &["--lean", "lean"]] {
            let mut cmd = command(route, project.path());
            cmd.arg("verify").arg("--request").arg(&request).args(extra);
            let output = cmd.output().unwrap();
            assert_result(&output, 2, "", "error:");
            assert!(output.stdout.is_empty(), "{output:?}");
        }
    }
}

#[test]
fn host_policy_conflicts_exit_2_on_stderr_with_empty_stdout() {
    let project = tempfile::tempdir().unwrap();
    let base_rustc = [
        "verify",
        "rustc",
        "lib.rs",
        "--crate-name",
        "fixture",
        "--spec-file",
        "Spec=Spec.lean",
        "--proof-file",
        "Proof=Proof.lean",
    ];

    let bad_cases: Vec<Vec<&str>> = vec![
        vec!["verify", "--request", "r.json", "--export-lean-lib"],
        vec!["verify", "--request", "r.json", "--capture", "cap", "--lean", "lean"],
        vec!["verify", "--request", "r.json", "--sysroot", "sys", "--lean", "lean"],
        vec![
            "verify",
            "--request",
            "r.json",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
            "--allow-unpinned-lean",
        ],
        vec![
            "verify",
            "--request",
            "r.json",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
            "--lean",
            "lean",
            "--lean-memory-mb",
            "0",
        ],
        vec![
            "verify",
            "--request",
            "r.json",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
            "--lean",
            "lean",
            "--select",
            "foo",
        ],
        [
            &[
                "verify",
                "--request",
                "r.json",
                "--capture",
                "cap",
                "--sysroot",
                "sys",
                "--lean",
                "lean",
            ][..],
            &base_rustc[1..],
        ]
        .concat(),
        [
            &[
                "verify",
                "--manifest-path",
                "Cargo.toml",
                "--proof-dir",
                "proof",
                "--capture",
                "cap",
                "--sysroot",
                "sys",
                "--lean",
                "lean",
            ][..],
            &base_rustc[1..],
        ]
        .concat(),
        [
            &base_rustc[..],
            &[
                "--capture",
                "cap",
                "--sysroot",
                "sys",
                "--lean",
                "lean",
                "--spec-file",
                "Spec=Other.lean",
            ],
        ]
        .concat(),
        [
            &base_rustc[..],
            &["--capture", "cap", "--sysroot", "sys", "--lean", "lean", "--export-lean-lib"],
        ]
        .concat(),
        vec![
            "verify",
            "--request",
            "r.json",
            "--panic",
            "abort",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
            "--lean",
            "lean",
        ],
        [
            &[
                "verify",
                "--panic",
                "abort",
                "--capture",
                "cap",
                "--sysroot",
                "sys",
                "--lean",
                "lean",
            ][..],
            &base_rustc[1..],
        ]
        .concat(),
        vec![
            "verify",
            "--manifest-path",
            "Cargo.toml",
            "--proof-dir",
            "proof",
            "--panic",
            "bogus",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
            "--lean",
            "lean",
        ],
    ];

    for args in bad_cases {
        let output = command(Route::Direct, project.path()).args(&args).output().unwrap();
        assert_result(&output, 2, "", "error:");
        assert!(output.stdout.is_empty(), "{args:?}: {output:?}");
    }
}

#[test]
fn unpinned_policy_taint_emits_stderr_banner_and_v3_failure_receipt() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let missing_tmp = project.path().join("missing-tmp");

    let mut cmd = command(Route::Direct, project.path());
    cmd.env("TMPDIR", &missing_tmp)
        .args(["verify", "--format", "json", "--request"])
        .arg(&request)
        .args([
            "--allow-unpinned-lean",
            "--lean",
            "custom-lean",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
        ]);
    let output = cmd.output().unwrap();
    assert_result(&output, 2, "", "TAINTED");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["schema_version"], 3, "{receipt}");
    assert_eq!(receipt["taint_reasons"], serde_json::json!(["unpinned_lean"]), "{receipt}");
    assert!(receipt.get("tainted").is_none(), "{receipt}");
    assert!(receipt.get("unpinned_lean").is_none(), "{receipt}");
    assert_eq!(receipt["phase"], "staging");
}

#[test]
fn unsandboxed_elaboration_flag_marks_early_failure_receipt_tainted() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let mut cmd = command(Route::Direct, project.path());
    cmd.args(["verify", "--format", "json", "--allow-unsandboxed-elaboration", "--request"])
        .arg(&request);
    #[cfg(not(feature = "setup"))]
    cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let output = cmd.output().unwrap();
    assert_result(&output, 1, "", "TAINTED");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["schema_version"], 3, "{receipt}");
    assert_eq!(
        receipt["taint_reasons"],
        serde_json::json!(["unsandboxed_elaboration"]),
        "{receipt}"
    );
    assert_eq!(receipt["status"], "unsupported", "{receipt}");
    assert_eq!(receipt["phase"], "request", "{receipt}");
    assert!(
        receipt.get("elaboration_sandbox").is_none(),
        "pre-sandbox failure must omit elaboration_sandbox: {receipt}"
    );
}

#[test]
fn taint_monoid_combines_all_three_allow_flags_in_canonical_order() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let mut cmd = command(Route::Direct, project.path());
    // Pass relaxation flags in reverse lexicographical order to confirm the
    // receipt projects a canonical sorted `BTreeSet<VerificationTaint>`.
    cmd.args([
        "verify",
        "--format",
        "json",
        "--allow-unsandboxed-elaboration",
        "--allow-unpinned-lean",
        "--allow-sorry-in-proof",
        "--lean",
        "fake-lean",
        "--request",
    ])
    .arg(&request);
    #[cfg(not(feature = "setup"))]
    cmd.args(["--capture", "cap", "--sysroot", "sys"]);
    let output = cmd.output().unwrap();
    assert_result(&output, 1, "", "TAINTED");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("--allow-sorry-in-proof"), "{stderr}");
    assert!(stderr.contains("--allow-unpinned-lean"), "{stderr}");
    assert!(stderr.contains("--allow-unsandboxed-elaboration"), "{stderr}");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["schema_version"], 3, "{receipt}");
    assert_eq!(
        receipt["taint_reasons"],
        serde_json::json!(["sorry_in_proof", "unpinned_lean", "unsandboxed_elaboration"]),
        "{receipt}"
    );
    assert_eq!(receipt["status"], "unsupported", "{receipt}");
    assert_eq!(receipt["phase"], "request", "{receipt}");
    assert!(
        receipt.get("elaboration_sandbox").is_none(),
        "pre-sandbox failure must omit elaboration_sandbox: {receipt}"
    );
}

#[test]
fn allow_unstable_feature_flag_validates_names_and_conflicts() {
    let project = tempfile::tempdir().unwrap();
    std::fs::write(project.path().join("lib.rs"), b"pub fn id(x: u8) -> u8 { x }\n").unwrap();
    for bad in [
        &["verify", "--request", "r.json", "--allow-unstable-feature", "*"][..],
        &["verify", "--request", "r.json", "--allow-unstable-feature", "Doc_cfg"][..],
        &["verify", "--request", "r.json", "--allow-unstable-feature", "doc_cfg,"][..],
        &["verify", "--request", "r.json", "--allow-unstable-feature=doc-cfg"][..],
        &[
            "verify",
            "--allow-unstable-feature",
            "doc_cfg",
            "rustc",
            "lib.rs",
            "--crate-name",
            "core",
            "--stdlib-crate",
            "core",
            "--select",
            "id",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ][..],
    ] {
        let output = command(Route::Direct, project.path()).args(bad).output().unwrap();
        assert_result(&output, 2, "", "error:");
        assert!(output.stdout.is_empty(), "{bad:?}: {output:?}");
    }
}

#[test]
fn allow_unstable_feature_flag_marks_early_failure_receipt_tainted() {
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    std::fs::write(&request, b"not JSON\n").unwrap();
    let mut cmd = command(Route::Direct, project.path());
    cmd.args([
        "verify",
        "--format",
        "json",
        "--allow-unstable-feature",
        "doc_cfg",
        "--allow-sorry-in-proof",
        "--request",
    ])
    .arg(&request);
    #[cfg(not(feature = "setup"))]
    cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let output = cmd.output().unwrap();
    assert_result(&output, 1, "", "--allow-unstable-feature");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(
        receipt["taint_reasons"],
        serde_json::json!(["sorry_in_proof", "unmodeled_unstable_features"]),
        "{receipt}"
    );
    assert_eq!(receipt["status"], "unsupported", "{receipt}");
}

/// Run `verify rustc` against a fake capture that records its arguments and
/// publishes `configuration_extra` merged into a matching configuration.
fn verify_with_fake_capture(
    project: &std::path::Path,
    configuration_extra: &str,
    extra_args: &[&str],
) -> (std::process::Output, String) {
    use std::{fs, os::unix::fs::PermissionsExt};

    fs::write(project.join("lib.rs"), b"pub fn id(x: u8) -> u8 { x }\n").unwrap();
    fs::write(project.join("Spec.lean"), b"-- spec\n").unwrap();
    fs::write(project.join("Proof.lean"), b"-- proof\n").unwrap();
    let sysroot = project.join("sysroot");
    fs::create_dir_all(&sysroot).unwrap();
    let fake_lean = project.join("fake-lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();
    let recorded_args = project.join("capture.args");
    let fake_capture = project.join("fake-capture");
    let script = format!(
        "#!/bin/sh\n\
         set -eu\n\
         printf '%s\\n' \"$@\" > {args_file:?}\n\
         out_dir=''\n\
         while [ \"$#\" -gt 0 ]; do\n\
           if [ \"$1\" = '--out-dir' ]; then\n\
             shift\n\
             out_dir=\"$1\"\n\
           fi\n\
           shift\n\
         done\n\
         mkdir -p \"$out_dir\"\n\
         cat > \"$out_dir/capture.json\" <<'JSON'\n\
         {{\n\
           \"schema_version\": 5,\n\
           \"compiler\": {{\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"}},\n\
           \"configuration\": {{\n\
             \"crate_root\": \"lib.rs\",\n\
             \"crate_name\": \"demo\",\n\
             \"crate_type\": \"lib\",\n\
             \"panic\": \"unwind\",\n\
             \"overflow_checks\": false,\n\
             \"target\": \"x86_64-unknown-linux-gnu\",\n\
             \"edition\": \"2024\",\n\
             \"cfg\": [],\n\
             \"env\": {{}}{configuration_extra}\n\
           }},\n\
           \"source_files\": [],\n\
           \"census\": [],\n\
           \"selected\": [],\n\
           \"program\": {{\"scope\": {{\"kind\": \"selected_unit\", \"roots\": [\"id\"]}}, \"bodies\": []}}\n\
         }}\n\
         JSON\n\
         printf '{{\"status\":\"captured\"}}\\n'\n",
        args_file = recorded_args.display(),
    );
    fs::write(&fake_capture, script).unwrap();
    fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

    let mut cmd = command(Route::Direct, project);
    cmd.args([
        "verify",
        "--format",
        "json",
        "--capture",
        fake_capture.to_str().unwrap(),
        "--sysroot",
        sysroot.to_str().unwrap(),
        "--lean",
        fake_lean.to_str().unwrap(),
    ])
    .args(extra_args)
    .args([
        "rustc",
        "lib.rs",
        "--crate-name",
        "demo",
        "--select",
        "id",
        "--spec-file",
        "Spec=Spec.lean",
        "--proof-file",
        "Proof=Proof.lean",
    ]);
    let output = cmd.output().unwrap();
    let args = fs::read_to_string(&recorded_args).unwrap_or_default();
    (output, args)
}

#[test]
fn verify_forwards_allowed_unstable_features_and_authenticates_capture() {
    let flags = [
        "--allow-unstable-feature",
        "doc_cfg,allocator_api",
        "--allow-unstable-feature",
        "doc_cfg",
    ];
    let detail = |output: &std::process::Output| -> serde_json::Value {
        serde_json::from_slice(&output.stdout).unwrap()
    };

    // Capture must record exactly the sorted, deduplicated operator list.
    for (label, extra) in [
        ("omitted allowlist", ""),
        ("narrowed allowlist", r#", "allowed_unstable_features": ["doc_cfg"]"#),
        (
            "observed outside allowlist",
            r#", "allowed_unstable_features": ["allocator_api", "doc_cfg"],
              "observed_unstable_features": ["specialization"]"#,
        ),
    ] {
        let project = tempfile::tempdir().unwrap();
        let (output, args) = verify_with_fake_capture(project.path(), extra, &flags);
        let receipt = detail(&output);
        assert_eq!(receipt["status"], "tool_failed", "{label}: {receipt}");
        assert_eq!(receipt["phase"], "capture", "{label}: {receipt}");
        assert!(receipt["detail"].as_str().unwrap().contains("unstable"), "{label}: {receipt}");
        assert_eq!(
            receipt["taint_reasons"],
            serde_json::json!(["unmodeled_unstable_features"]),
            "{label}: {receipt}"
        );
        let forwarded: Vec<&str> =
            args.lines().filter(|line| line.starts_with("--allow-unstable-feature")).collect();
        assert_eq!(
            forwarded,
            ["--allow-unstable-feature=allocator_api", "--allow-unstable-feature=doc_cfg"],
            "{label}: {args}"
        );
    }

    // A capture that reports features without the flag is refused too.
    let project = tempfile::tempdir().unwrap();
    let (output, args) = verify_with_fake_capture(
        project.path(),
        r#", "allowed_unstable_features": ["doc_cfg"]"#,
        &[],
    );
    let receipt = detail(&output);
    assert_eq!(receipt["phase"], "capture", "{receipt}");
    assert!(receipt["detail"].as_str().unwrap().contains("unstable"), "{receipt}");
    assert!(!args.contains("--allow-unstable-feature"), "{args}");

    // A matching capture passes the feature checks (verification then fails
    // later for unrelated reasons in this fake setup).
    let project = tempfile::tempdir().unwrap();
    let (output, _) = verify_with_fake_capture(
        project.path(),
        r#", "allowed_unstable_features": ["allocator_api", "doc_cfg"],
          "observed_unstable_features": ["doc_cfg"]"#,
        &flags,
    );
    let receipt = detail(&output);
    assert!(
        !receipt["detail"].as_str().unwrap_or("").contains("unstable"),
        "matching capture rejected: {receipt}"
    );
}

#[test]
fn allow_unstable_feature_conflicts_with_stdlib_crate_request() {
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    std::fs::write(
        &request,
        br#"{
            "schema_version": 1,
            "compilation": {
                "source_root": ".",
                "crate_root": "lib.rs",
                "crate_name": "core",
                "source_files": ["lib.rs"],
                "stdlib_crate": "core"
            },
            "scope": {"kind": "selected_unit", "roots": ["id"]},
            "proof": {"source_root": ".", "sources": []}
        }"#,
    )
    .unwrap();
    std::fs::write(project.path().join("lib.rs"), b"pub fn id(x: u8) -> u8 { x }\n").unwrap();
    let mut cmd = command(Route::Direct, project.path());
    cmd.args(["verify", "--format", "json", "--allow-unstable-feature", "doc_cfg", "--request"])
        .arg(&request);
    #[cfg(not(feature = "setup"))]
    cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let output = cmd.output().unwrap();
    assert_result(&output, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["status"], "tool_failed", "{receipt}");
    assert_eq!(receipt["phase"], "request", "{receipt}");
    assert!(receipt["detail"].as_str().unwrap().contains("stdlib_crate"), "{receipt}");
}

#[test]
fn fast_check_refuses_receipt_outputs_and_never_emits_receipt_v3() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let lib_rs = project.path().join("lib.rs");
    let spec_lean = project.path().join("Spec.lean");
    let proof_lean = project.path().join("Proof.lean");
    fs::write(&lib_rs, b"pub fn id(x: u32) -> u32 { x }\n").unwrap();
    fs::write(&spec_lean, b"-- spec\n").unwrap();
    fs::write(&proof_lean, b"-- proof\n").unwrap();

    // Pre-populate an existing artifact directory so an `--overwrite-artifacts`
    // bypass would delete `result.json` or `lean-lib/Captured.olean`.
    let existing_art = project.path().join("existing-art");
    fs::create_dir_all(existing_art.join("lean-lib")).unwrap();
    fs::write(existing_art.join(".cargo-anneal-artifacts"), b"").unwrap();
    fs::write(existing_art.join("result.json"), b"{\"status\":\"crate_verified\"}\n").unwrap();
    fs::write(existing_art.join("lean-lib/Captured.olean"), b"olean").unwrap();

    let conflict_cases: &[(&[&str], &str)] = &[
        (&["--receipt-out", "receipt.json"], "--receipt-out"),
        (&["--artifacts", "art"], "--artifacts"),
        (&["--artifacts", "art", "--export-lean-lib"], "--artifacts"),
        (&["--export-lean-lib"], "--export-lean-lib"),
        (&["--overwrite-artifacts"], "--overwrite-artifacts"),
        (&["--artifacts", "existing-art", "--overwrite-artifacts"], "--artifacts"),
        (
            &["--artifacts", "existing-art", "--overwrite-artifacts", "--export-lean-lib"],
            "--artifacts",
        ),
        (&["--paranoid-quorum"], "--paranoid-quorum"),
        (&["--format", "json"], "--format json"),
    ];

    for &(conflicting, expected_flag) in conflict_cases {
        // (a) Single-level `--request` invocation: must reject specifically on
        //     `--fast-check` (never vacuously on `requires --artifacts`).
        let mut cmd = command(Route::Direct, project.path());
        cmd.args(["verify", "--fast-check", "--request"]).arg(&request).args(conflicting);
        #[cfg(not(feature = "setup"))]
        cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let output = cmd.output().unwrap();
        assert_result(&output, 2, "", "--fast-check");
        assert_result(&output, 2, "", expected_flag);
        assert!(output.stdout.is_empty(), "{conflicting:?}: {output:?}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!stderr.contains("requires `--artifacts"), "{stderr}");

        // (b) Split across `verify --fast-check rustc ... <conflicting>`.
        let spec_arg = format!("Spec={}", spec_lean.display());
        let proof_arg = format!("Proof={}", proof_lean.display());
        let mut split_before = command(Route::Direct, project.path());
        split_before
            .args(["verify", "--fast-check", "rustc"])
            .arg(&lib_rs)
            .args([
                "--crate-name",
                "c",
                "--edition",
                "2024",
                "--spec-file",
                &spec_arg,
                "--proof-file",
                &proof_arg,
                "--spec-decl",
                "Spec.specs",
                "--theorem",
                "Proof.verify",
            ])
            .args(conflicting);
        #[cfg(not(feature = "setup"))]
        split_before.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let out_before = split_before.output().unwrap();
        assert_result(&out_before, 2, "", "--fast-check");
        assert_result(&out_before, 2, "", expected_flag);
        assert!(out_before.stdout.is_empty(), "split_before {conflicting:?}: {out_before:?}");

        // (c) Split across `verify <conflicting> rustc ... --fast-check`.
        let mut split_after = command(Route::Direct, project.path());
        split_after.arg("verify").args(conflicting).arg("rustc").arg(&lib_rs).args([
            "--crate-name",
            "c",
            "--edition",
            "2024",
            "--spec-file",
            &spec_arg,
            "--proof-file",
            &proof_arg,
            "--spec-decl",
            "Spec.specs",
            "--theorem",
            "Proof.verify",
            "--fast-check",
        ]);
        #[cfg(not(feature = "setup"))]
        split_after.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let out_after = split_after.output().unwrap();
        assert_result(&out_after, 2, "", "--fast-check");
        assert_result(&out_after, 2, "", expected_flag);
        assert!(out_after.stdout.is_empty(), "split_after {conflicting:?}: {out_after:?}");
    }

    assert!(!project.path().join("receipt.json").exists());
    assert!(!project.path().join("art").exists());
    assert!(existing_art.join("result.json").is_file());
    assert!(existing_art.join("lean-lib/Captured.olean").is_file());

    // Even when `--format auto` runs over a non-TTY pipe, `--fast-check`
    // emits human output with explicit tainting rather than Receipt v3 JSON.
    let mut cmd = command(Route::Direct, project.path());
    cmd.args(["verify", "--fast-check", "--format", "auto", "--request"]).arg(&request);
    #[cfg(not(feature = "setup"))]
    cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let output = cmd.output().unwrap();
    assert_result(&output, 1, "fast_check_dev_mode", "UNVERIFIED_DEV_ONLY");
    assert_result(&output, 1, "[FAIL]", "TAINTED");
    assert!(
        serde_json::from_slice::<serde_json::Value>(&output.stdout).is_err(),
        "fast-check must never emit JSON receipt: {}",
        String::from_utf8_lossy(&output.stdout)
    );
}
