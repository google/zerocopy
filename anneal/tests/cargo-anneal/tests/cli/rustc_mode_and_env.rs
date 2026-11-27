// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `rustc`-mode staging and proof modules, and request `--env` binding.

use super::*;

#[cfg(unix)]
#[test]
fn rustc_mode_stages_symlinks_strict_roles_and_rejects_fifos() {
    use std::{fs, os::unix::fs::symlink};

    let project = tempfile::tempdir().unwrap();
    let cas = project.path().join("cas");
    fs::create_dir(&cas).unwrap();
    fs::write(cas.join("a.rs"), b"pub mod sub;\n").unwrap();
    fs::write(cas.join("b.rs"), b"pub fn zero() -> u64 { 0 }\n").unwrap();
    fs::write(cas.join("spec.lean"), b"-- spec\n").unwrap();
    fs::write(cas.join("proof.lean"), b"-- proof\n").unwrap();

    let runfiles = project.path().join("runfiles/crate/src");
    fs::create_dir_all(&runfiles).unwrap();
    symlink(cas.join("a.rs"), runfiles.join("lib.rs")).unwrap();
    symlink(cas.join("b.rs"), runfiles.join("sub.rs")).unwrap();
    symlink(cas.join("spec.lean"), runfiles.join("Contract.lean")).unwrap();
    symlink(cas.join("proof.lean"), runfiles.join("Spec.Helper.lean")).unwrap();

    let evidence = project.path().join("evidence");
    // Host flags passed both BEFORE and AFTER `rustc` must work.
    let output = command(Route::Direct, project.path())
        .args(["verify", "--format", "json"])
        .arg("--capture")
        .arg(project.path().join("missing-capture"))
        .arg("--sysroot")
        .arg(project.path())
        .arg("rustc")
        .arg(runfiles.join("lib.rs"))
        .args(["--crate-name", "sample", "--source-file"])
        .arg(runfiles.join("sub.rs"))
        .arg("--spec-file")
        .arg(format!("Contract={}", runfiles.join("Contract.lean").display()))
        .arg("--proof-file")
        .arg(format!("Spec.Helper={}", runfiles.join("Spec.Helper.lean").display()))
        .args([
            "--spec-decl",
            "Contract:StarnixEbpf.Contract.specs",
            "--theorem",
            "Spec.Helper:Proof.custom",
            "--lean",
        ])
        .arg(project.path().join("missing-lean"))
        .arg("--artifacts")
        .arg(&evidence)
        .output()
        .unwrap();
    assert_result(&output, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["schema_version"], 3, "{receipt}");
    assert_eq!(receipt["phase"], "capture-tool", "{receipt}");
    let req: serde_json::Value =
        serde_json::from_slice(&fs::read(evidence.join("request.json")).unwrap()).unwrap();
    assert_eq!(req["compilation"]["source_root"], "rust");
    assert_eq!(req["compilation"]["crate_root"], "lib.rs");
    assert_eq!(req["compilation"]["source_files"], serde_json::json!(["lib.rs", "sub.rs"]));
    assert_eq!(req["proof"]["source_root"], "authored");
    assert_eq!(req["proof"]["specification_module"], "Contract");
    assert_eq!(req["proof"]["specification"], "StarnixEbpf.Contract.specs");
    assert_eq!(req["proof"]["theorem_module"], "Spec.Helper");
    assert_eq!(req["proof"]["theorem"], "Proof.custom");
    assert_eq!(
        req["proof"]["sources"],
        serde_json::json!([
            {"module": "Contract", "path": "Contract.lean", "role": "specification"},
            {"module": "Spec.Helper", "path": "Spec/Helper.lean", "role": "proof"},
        ])
    );

    // FIFO symlink target must fail immediately without hanging.
    let fifo = project.path().join("pipe.rs");
    assert!(Command::new("mkfifo").arg(&fifo).status().unwrap().success());
    let fifo_link = runfiles.join("fifo.rs");
    symlink(&fifo, &fifo_link).unwrap();
    let fifo_out = command(Route::Direct, project.path())
        .args(["verify", "--format", "json"])
        .arg("--capture")
        .arg(project.path().join("missing-capture"))
        .arg("--sysroot")
        .arg(project.path())
        .arg("--lean")
        .arg(project.path().join("missing-lean"))
        .arg("rustc")
        .arg(&fifo_link)
        .args(["--crate-name", "sample", "--spec-file"])
        .arg(format!("Spec={}", runfiles.join("Contract.lean").display()))
        .arg("--proof-file")
        .arg(format!("Proof={}", runfiles.join("Spec.Helper.lean").display()))
        .output()
        .unwrap();
    assert_result(&fifo_out, 1, "", "");
    let fifo_receipt: serde_json::Value = serde_json::from_slice(&fifo_out.stdout).unwrap();
    assert_eq!(fifo_receipt["status"], "unsupported");
    assert_eq!(fifo_receipt["phase"], "inputs");
}

#[test]
fn rustc_mode_rejects_reserved_or_mismatched_proof_modules_before_capture() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let lib = project.path().join("lib.rs");
    let spec = project.path().join("Spec.lean");
    let proof = project.path().join("Proof.lean");
    fs::write(&lib, b"pub fn zero() -> u64 { 0 }\n").unwrap();
    fs::write(&spec, b"-- spec\n").unwrap();
    fs::write(&proof, b"-- proof\n").unwrap();

    // Reserved module name (`Trusted`) must be rejected before capture.
    let reserved_out = command(Route::Direct, project.path())
        .args(["verify", "--format", "json", "rustc"])
        .arg(&lib)
        .args(["--crate-name", "sample", "--spec-file"])
        .arg(format!("Trusted={}", spec.display()))
        .arg("--proof-file")
        .arg(format!("Proof={}", proof.display()))
        .args([
            "--spec-decl",
            "Trusted:Trusted.specs",
            "--capture",
            "missing-capture",
            "--sysroot",
            "missing-sysroot",
            "--lean",
            "missing-lean",
        ])
        .output()
        .unwrap();
    assert_result(&reserved_out, 1, "", "");
    let reserved_receipt: serde_json::Value = serde_json::from_slice(&reserved_out.stdout).unwrap();
    assert_eq!(reserved_receipt["status"], "unsupported");
    assert_eq!(reserved_receipt["phase"], "proof");

    // Unknown `--spec-decl` module or role mismatch must be rejected early
    // before capture runs.
    for extra in [
        &["--spec-decl", "Missing:Missing.specs"][..],
        &["--theorem", "Missing:Missing.verify"][..],
        &["--spec-decl", "Proof:Proof.specs"][..],
        &["--theorem", "Spec:Spec.verify"][..],
    ] {
        let out = command(Route::Direct, project.path())
            .args(["verify", "--format", "json", "rustc"])
            .arg(&lib)
            .args(["--crate-name", "sample", "--spec-file"])
            .arg(format!("Spec={}", spec.display()))
            .arg("--proof-file")
            .arg(format!("Proof={}", proof.display()))
            .args(extra)
            .args([
                "--capture",
                "missing-capture",
                "--sysroot",
                "missing-sysroot",
                "--lean",
                "missing-lean",
            ])
            .output()
            .unwrap();
        assert_result(&out, 1, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(receipt["status"], "unsupported", "{extra:?}: {receipt}");
        assert_eq!(receipt["phase"], "proof", "{extra:?}: {receipt}");
    }
}

#[test]
fn verify_rejects_smuggled_env_key_in_request_json() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(
        &request,
        serde_json::to_vec(&serde_json::json!({
            "schema_version": 1,
            "compilation": {
                "source_root": ".",
                "crate_root": "lib.rs",
                "crate_name": "demo",
                "env": { "A=B": "C" },
                "source_files": ["lib.rs"]
            },
            "scope": { "kind": "selected_unit", "roots": ["f"] },
            "proof": {
                "source_root": ".",
                "sources": []
            }
        }))
        .unwrap(),
    )
    .unwrap();
    let mut cmd = command(Route::Direct, project.path());
    cmd.args(["verify", "--format", "json", "--request"]).arg(&request);
    #[cfg(not(feature = "setup"))]
    cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let output = cmd.output().unwrap();
    assert_result(&output, 1, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["status"], "unsupported", "{receipt}");
    assert_eq!(receipt["phase"], "request", "{receipt}");
    assert!(receipt["detail"].as_str().unwrap_or("").contains("must not contain '='"), "{receipt}");
}

#[cfg(unix)]
#[test]
fn verify_passes_env_flags_and_rejects_mismatched_capture_env() {
    use std::{fs, os::unix::fs::PermissionsExt};

    let project = tempfile::tempdir().unwrap();
    fs::write(project.path().join("lib.rs"), b"pub fn f() -> u64 { 0 }\n").unwrap();
    fs::write(project.path().join("Spec.lean"), b"").unwrap();
    fs::write(project.path().join("Proof.lean"), b"").unwrap();
    let sysroot = project.path().join("sysroot");
    fs::create_dir_all(&sysroot).unwrap();
    let fake_lean = project.path().join("lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

    let recorded_args = project.path().join("capture_args.txt");
    let fake_capture = project.path().join("fake-capture");
    // Emit a syntactically valid schema-5 capture manifest whose
    // `configuration.env` disagrees with the requested `--env` binding.
    let script = format!(
        "#!/bin/sh\n\
         out_dir=\"\"\n\
         : > \"{args_file}\"\n\
         while [ \"$#\" -gt 0 ]; do\n\
           printf '%s\\n' \"$1\" >> \"{args_file}\"\n\
           if [ \"$1\" = \"--out-dir\" ]; then\n\
             shift\n\
             out_dir=\"$1\"\n\
             printf '%s\\n' \"$1\" >> \"{args_file}\"\n\
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
             \"env\": {{\"CARGO_PKG_VERSION\": \"0.0.0-mismatch\"}}\n\
           }},\n\
           \"source_files\": [],\n\
           \"census\": [],\n\
           \"selected\": [],\n\
           \"program\": {{\"scope\": {{\"kind\": \"selected_unit\", \"roots\": [\"f\"]}}, \"bodies\": []}}\n\
         }}\n\
         JSON\n\
         printf '{{\"status\":\"captured\"}}\\n'\n",
        args_file = recorded_args.display(),
    );
    fs::write(&fake_capture, script).unwrap();
    fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

    let output = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--lean",
            fake_lean.to_str().unwrap(),
            "rustc",
            "lib.rs",
            "--crate-name",
            "demo",
            "--env",
            "CARGO_PKG_VERSION=0.8.64",
            "--select",
            "f",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ])
        .output()
        .unwrap();
    assert_result(&output, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["status"], "tool_failed", "{receipt}");
    assert_eq!(receipt["phase"], "capture", "{receipt}");
    assert!(
        receipt["detail"]
            .as_str()
            .unwrap_or("")
            .contains("capture differs from the requested compilation or scope"),
        "{receipt}"
    );
    let args_text = fs::read_to_string(&recorded_args).unwrap();
    let recorded_lines: Vec<&str> = args_text.lines().collect();
    assert!(
        recorded_lines.contains(&"--env=CARGO_PKG_VERSION=0.8.64"),
        "expected --env=CARGO_PKG_VERSION=0.8.64 in capture args:\n{args_text}"
    );
    assert!(
        recorded_lines.windows(2).any(|w| w == ["--crate-type", "lib"]),
        "expected --crate-type lib in capture args:\n{args_text}"
    );
    assert!(
        recorded_lines.windows(2).any(|w| w == ["--panic", "unwind"]),
        "expected --panic unwind in capture args:\n{args_text}"
    );

    // Also confirm `cargo-anneal` rejects capture manifests whose reported
    // `crate_type`, `panic` strategy, or `overflow_checks` setting disagrees
    // with the request.
    for (bad_crate_type, bad_panic, bad_overflow, req_crate_type, req_panic, req_overflow) in [
        ("lib", "unwind", false, "bin", "unwind", false),
        ("bin", "unwind", false, "bin", "abort", false),
        ("bin", "unwind", true, "bin", "unwind", false),
        ("bin", "unwind", false, "bin", "unwind", true),
    ] {
        let mismatch_script = format!(
            "#!/bin/sh\n\
             out_dir=\"\"\n\
             while [ \"$#\" -gt 0 ]; do\n\
               if [ \"$1\" = \"--out-dir\" ]; then shift; out_dir=\"$1\"; fi\n\
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
                 \"crate_type\": \"{bad_crate_type}\",\n\
                 \"panic\": \"{bad_panic}\",\n\
                 \"overflow_checks\": {bad_overflow},\n\
                 \"target\": \"x86_64-unknown-linux-gnu\",\n\
                 \"edition\": \"2024\",\n\
                 \"cfg\": [],\n\
                 \"env\": {{}}\n\
               }},\n\
               \"source_files\": [],\n\
               \"census\": [],\n\
               \"selected\": [],\n\
               \"program\": {{\"scope\": {{\"kind\": \"selected_unit\", \"roots\": [\"f\"]}}, \"bodies\": []}}\n\
             }}\n\
             JSON\n\
             printf '{{\"status\":\"captured\"}}\\n'\n"
        );
        fs::write(&fake_capture, mismatch_script).unwrap();
        fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();
        let mut mismatch_args = vec![
            "verify",
            "--format",
            "json",
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--lean",
            fake_lean.to_str().unwrap(),
            "rustc",
            "lib.rs",
            "--crate-name",
            "demo",
            "--crate-type",
            req_crate_type,
            "--panic",
            req_panic,
            "--select",
            "f",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ];
        if req_overflow {
            mismatch_args.push("--overflow-checks");
        }
        let mismatch_out =
            command(Route::Direct, project.path()).args(&mismatch_args).output().unwrap();
        assert_result(&mismatch_out, 2, "", "");
        let mismatch_receipt: serde_json::Value =
            serde_json::from_slice(&mismatch_out.stdout).unwrap();
        assert_eq!(mismatch_receipt["status"], "tool_failed", "{mismatch_receipt}");
        assert_eq!(mismatch_receipt["phase"], "capture", "{mismatch_receipt}");
        assert!(
            mismatch_receipt["detail"]
                .as_str()
                .unwrap_or("")
                .contains("capture differs from the requested compilation or scope"),
            "{mismatch_receipt}"
        );
    }
}
