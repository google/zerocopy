// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `init` scaffolding, failure-receipt hints, output formats, and broken
//! pipes.

use super::*;

#[test]
fn testkit_parses_cli_failure_receipt_cleanly() {
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    std::fs::write(&request, b"not JSON\n").unwrap();
    let mut cmd = command(Route::Direct, project.path());
    cmd.args(["verify", "--format", "json"]).arg("--request").arg(&request);
    #[cfg(not(feature = "setup"))]
    cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let output = cmd.output().unwrap();
    assert_result(&output, 1, "", "");
    let parsed = anneal_testkit::VerifyReceipt::from_json_slice(&output.stdout).unwrap();
    anneal_testkit::assert_rejected(&parsed, "unsupported", Some("request"), "").unwrap();
}

#[test]
fn init_scaffolds_cargo_and_standalone_without_overwriting() {
    use std::fs;

    for route in [Route::Direct, Route::Cargo] {
        let project = tempfile::tempdir().unwrap();
        let no_manifest = command(route, project.path()).arg("init").output().unwrap();
        assert_result(&no_manifest, 1, "", "no Cargo.toml found");

        fs::write(project.path().join("Cargo.toml"), "[workspace]\nmembers = [\"a\"]\n").unwrap();
        let workspace = command(route, project.path()).arg("init").output().unwrap();
        assert_result(&workspace, 1, "", "virtual workspace");

        fs::write(
            project.path().join("Cargo.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        let ok = command(route, project.path()).arg("init").output().unwrap();
        assert_result(&ok, 0, "Initialized Anneal proof files:", "");
        assert!(project.path().join("proof/Spec.lean").is_file());
        assert!(project.path().join("proof/Proof.lean").is_file());
        let spec_text = fs::read_to_string(project.path().join("proof/Spec.lean")).unwrap();
        let proof_text = fs::read_to_string(project.path().join("proof/Proof.lean")).unwrap();
        assert!(spec_text.starts_with("module\nprelude\npublic import Trusted.MirSemantics"));
        assert!(spec_text.contains("@[expose] public section"));
        assert!(!spec_text.contains("sorry"));
        assert!(proof_text.starts_with("module\nprelude\npublic import Expected"));
        assert!(proof_text.contains("public theorem verify : Expected.claim"));

        let second = command(route, project.path()).arg("init").output().unwrap();
        assert_result(&second, 1, "", "refusing to overwrite existing file");

        let standalone_dir = project.path().join("hello");
        let standalone = command(route, project.path())
            .args(["init", "--standalone", "--proof-dir"])
            .arg(&standalone_dir)
            .output()
            .unwrap();
        assert_result(&standalone, 0, "cargo anneal verify --request", "");
        for name in ["lib.rs", "request.json", "Spec.lean", "Proof.lean"] {
            assert!(standalone_dir.join(name).is_file(), "missing {name}");
        }
        let sa_spec = fs::read_to_string(standalone_dir.join("Spec.lean")).unwrap();
        let sa_proof = fs::read_to_string(standalone_dir.join("Proof.lean")).unwrap();
        assert!(sa_spec.starts_with("module\nprelude\npublic import Trusted.MirSemantics"));
        assert!(sa_proof.contains("public theorem verify : Expected.claim"));
    }
}

#[test]
fn init_profile_v2_scaffolds_specs_v2_and_conflicts_with_standalone() {
    use std::fs;

    for route in [Route::Direct, Route::Cargo] {
        let project = tempfile::tempdir().unwrap();
        fs::write(
            project.path().join("Cargo.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        let ok = command(route, project.path()).args(["init", "--profile", "v2"]).output().unwrap();
        assert_result(&ok, 0, "mir_profile_version = 2", "");
        let spec_text = fs::read_to_string(project.path().join("proof/Spec.lean")).unwrap();
        let proof_text = fs::read_to_string(project.path().join("proof/Proof.lean")).unwrap();
        assert!(spec_text.contains("def specs : SpecsV2 where"), "{spec_text}");
        assert!(proof_text.contains("public theorem verify : Expected.claim"), "{proof_text}");

        let conflict = command(route, project.path())
            .args(["init", "--standalone", "--profile", "v2", "--proof-dir"])
            .arg(project.path().join("standalone"))
            .output()
            .unwrap();
        assert_result(&conflict, 2, "", "cannot be used with");
        assert!(!project.path().join("standalone").exists());
    }
}

#[test]
fn failure_receipts_emit_actionable_hints_while_preserving_detail() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    fs::create_dir_all(project.path().join("crate_proc_macro/src")).unwrap();
    fs::create_dir_all(project.path().join("crate_proc_macro/proof")).unwrap();
    fs::write(
        project.path().join("crate_proc_macro/Cargo.toml"),
        "[package]\nname = \"pm_demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\nproc-macro = true\n",
    )
    .unwrap();
    fs::write(project.path().join("crate_proc_macro/src/lib.rs"), b"pub fn f() -> u64 { 0 }\n")
        .unwrap();

    // 1. Missing Cargo manifest names the path and sets a clear hint.
    let missing_manifest = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--manifest-path",
            "absent/Cargo.toml",
            "--proof-dir",
            "crate_proc_macro/proof",
        ])
        .args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"])
        .output()
        .unwrap();
    assert_result(&missing_manifest, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&missing_manifest.stdout).unwrap();
    assert_eq!(receipt["phase"], "cargo");
    assert!(receipt["detail"].as_str().unwrap().contains("Cargo.toml"), "{receipt}");
    assert!(receipt["hint"].as_str().unwrap().contains("--manifest-path"), "{receipt}");

    // 2. Cargo shortcut refusal preserves detail and suggests `--request` /
    //    `skill --example`.
    let feat_out = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--manifest-path",
            "crate_proc_macro/Cargo.toml",
            "--proof-dir",
            "crate_proc_macro/proof",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
            "--lean",
            "lean",
        ])
        .output()
        .unwrap();
    assert_result(&feat_out, 1, "", "");
    let feat_receipt: serde_json::Value = serde_json::from_slice(&feat_out.stdout).unwrap();
    assert_eq!(feat_receipt["phase"], "cargo");
    assert_eq!(
        feat_receipt["detail"],
        "build scripts and procedural macros need an explicit configured compilation"
    );
    assert!(feat_receipt["hint"].as_str().unwrap().contains("--request"), "{feat_receipt}");

    // 3. Missing `--proof-dir` names the path and suggests `cargo anneal init`.
    fs::create_dir_all(project.path().join("crate_ok/src")).unwrap();
    fs::create_dir_all(project.path().join("crate_ok/proof")).unwrap();
    fs::write(
        project.path().join("crate_ok/Cargo.toml"),
        "[package]\nname = \"ok_demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(project.path().join("crate_ok/src/lib.rs"), b"pub fn f() -> u64 { 0 }\n").unwrap();
    let dummy_sysroot = project.path().join("dummy-sysroot");
    fs::create_dir(&dummy_sysroot).unwrap();
    let dummy_capture = project.path().join("dummy-capture");
    let dummy_lean = project.path().join("dummy-lean");
    fs::write(&dummy_capture, b"stub\n").unwrap();
    fs::write(&dummy_lean, b"stub\n").unwrap();
    let missing_proof_dir = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--manifest-path",
            "crate_ok/Cargo.toml",
            "--proof-dir",
            "crate_ok/missing-proof",
            "--capture",
        ])
        .arg(&dummy_capture)
        .arg("--sysroot")
        .arg(&dummy_sysroot)
        .arg("--lean")
        .arg(&dummy_lean)
        .output()
        .unwrap();
    assert_result(&missing_proof_dir, 2, "", "");
    let proof_receipt: serde_json::Value =
        serde_json::from_slice(&missing_proof_dir.stdout).unwrap();
    assert_eq!(proof_receipt["phase"], "proof");
    assert!(
        proof_receipt["detail"].as_str().unwrap().contains("cannot inspect proof directory"),
        "{proof_receipt}"
    );
    assert!(
        proof_receipt["hint"].as_str().unwrap().contains("cargo anneal init"),
        "{proof_receipt}"
    );

    // 4. Missing capture tool emits setup/explicit-tool guidance.
    let missing_explicit = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--manifest-path",
            "crate_ok/Cargo.toml",
            "--proof-dir",
            "crate_ok/proof",
            "--capture",
            "absent-capture",
            "--sysroot",
        ])
        .arg(&dummy_sysroot)
        .arg("--lean")
        .arg(&dummy_lean)
        .output()
        .unwrap();
    assert_result(&missing_explicit, 2, "", "");
    let explicit_receipt: serde_json::Value =
        serde_json::from_slice(&missing_explicit.stdout).unwrap();
    assert_eq!(explicit_receipt["phase"], "capture-tool");
    assert!(
        explicit_receipt["hint"].as_str().unwrap().contains("`--capture`"),
        "{explicit_receipt}"
    );
    #[cfg(feature = "setup")]
    {
        // Under `cargo test --workspace`, Cargo builds `anneal-rustc-capture`
        // beside `CARGO_BIN_EXE_cargo-anneal`; stage an isolated `cargo-anneal`
        // binary in an empty directory so sibling fallback cannot find it.
        let isolated_dir = project.path().join("isolated-bin");
        fs::create_dir(&isolated_dir).unwrap();
        let exe_name = Path::new(env!("CARGO_BIN_EXE_cargo-anneal-test-bin")).file_name().unwrap();
        let isolated_cli = isolated_dir.join(exe_name);
        if fs::hard_link(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"), &isolated_cli).is_err() {
            #[cfg(unix)]
            {
                let stage = Command::new("/bin/sh")
                    .arg("-ceu")
                    .arg("cp \"$1\" \"$2\"")
                    .arg("sh")
                    .arg(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"))
                    .arg(&isolated_cli)
                    .output()
                    .unwrap();
                assert_result(&stage, 0, "", "");
            }
            #[cfg(not(unix))]
            fs::copy(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"), &isolated_cli).unwrap();
        }
        let empty_cache = project.path().join("empty-cache");
        let missing_tools = Command::new(&isolated_cli)
            .current_dir(project.path())
            .env("XDG_CACHE_HOME", &empty_cache)
            .env("HOME", &empty_cache)
            .env_remove("ANNEAL_CAPTURE")
            .env_remove("ANNEAL_SYSROOT")
            .env_remove("ANNEAL_LEAN")
            .args([
                "verify",
                "--format",
                "json",
                "--manifest-path",
                "crate_ok/Cargo.toml",
                "--proof-dir",
                "crate_ok/proof",
            ])
            .output()
            .unwrap();
        assert_result(&missing_tools, 2, "", "");
        let tool_receipt: serde_json::Value =
            serde_json::from_slice(&missing_tools.stdout).unwrap();
        assert_eq!(tool_receipt["phase"], "capture-tool");
        assert!(tool_receipt["hint"].as_str().unwrap().contains("setup"), "{tool_receipt}");
    }

    // 5. Capture JSON envelope remains valid JSON in `detail` while `hint`
    //    explains Rust MIR bounds.
    #[cfg(unix)]
    {
        let fake_capture = project.path().join("fake-capture");
        let body = "#!/bin/sh\n\
            printf '%s\\n' '{\"status\":\"unsupported\",\"diagnostics\":[\"1 required obligations are unsupported\"],\"unsupported\":[{\"def_id\":3,\"path\":\"take_ref\",\"reason\":\"unsupported type: &\\u0027{erased} u64\"}]}'\n\
            exit 1\n";
        let stage = Command::new("/bin/sh")
            .arg("-ceu")
            .arg("printf '%s' \"$1\" > \"$2\" && chmod 0755 \"$2\"")
            .arg("sh")
            .arg(body)
            .arg(&fake_capture)
            .output()
            .unwrap();
        assert_result(&stage, 0, "", "");

        fs::write(project.path().join("crate_ok/proof/Spec.lean"), b"prelude\n").unwrap();
        fs::write(project.path().join("crate_ok/proof/Proof.lean"), b"prelude\n").unwrap();
        let sysroot = project.path().join("sysroot");
        fs::create_dir(&sysroot).unwrap();
        let fake_lean = project.path().join("fake-lean");
        fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();

        let cap_out = command(Route::Direct, project.path())
            .args([
                "verify",
                "--format",
                "json",
                "--manifest-path",
                "crate_ok/Cargo.toml",
                "--proof-dir",
                "crate_ok/proof",
                "--capture",
            ])
            .arg(&fake_capture)
            .arg("--sysroot")
            .arg(&sysroot)
            .arg("--lean")
            .arg(&fake_lean)
            .output()
            .unwrap();
        assert_result(&cap_out, 1, "", "");
        let cap_receipt: serde_json::Value = serde_json::from_slice(&cap_out.stdout).unwrap();
        assert_eq!(cap_receipt["phase"], "capture");
        let parsed_detail: serde_json::Value =
            serde_json::from_str(cap_receipt["detail"].as_str().unwrap()).unwrap();
        assert_eq!(parsed_detail["unsupported"][0]["path"], "take_ref");
        let hint = cap_receipt["hint"].as_str().unwrap();
        assert!(hint.contains("`take_ref`") && hint.contains("references"), "{cap_receipt}");
    }
}

#[test]
fn default_verify_format_is_human_and_format_json_never_emits_ansi() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();

    // 1. Default invocation (`--format` omitted) emits human `[FAIL]` card with
    //    zero ANSI on non-TTY pipes even when `CI=true`.
    let mut default_cmd = command(Route::Direct, project.path());
    default_cmd
        .env_remove("CARGO_TERM_COLOR")
        .env_remove("CLICOLOR_FORCE")
        .env_remove("FORCE_COLOR")
        .env("CI", "true")
        .args(["verify", "--request"])
        .arg(&request);
    #[cfg(not(feature = "setup"))]
    default_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let default_out = default_cmd.output().unwrap();
    assert_result(
        &default_out,
        1,
        "[FAIL] VERIFICATION FAILED (unsupported in phase `request`, exit 1)",
        "",
    );
    let default_stdout = String::from_utf8(default_out.stdout).unwrap();
    assert!(
        !default_stdout.contains('\x1b'),
        "non-TTY pipe must omit ANSI even when CI=true:\n{default_stdout}"
    );
    assert!(!default_stdout.contains("[OK]"), "{default_stdout}");

    // 2. `--color always` styles human cards with SGR, while
    //    `--format json --color always` remains pure RFC 8259 JSON with zero
    //    ANSI escapes.
    let mut colored_human = command(Route::Direct, project.path());
    colored_human.args(["--color", "always", "verify", "--request"]).arg(&request);
    #[cfg(not(feature = "setup"))]
    colored_human.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let colored_out = colored_human.output().unwrap();
    let colored_stdout = String::from_utf8(colored_out.stdout).unwrap();
    assert!(colored_stdout.contains("\x1b[1;31m[FAIL]\x1b[0m"), "{colored_stdout}");

    let mut colored_json = command(Route::Direct, project.path());
    colored_json
        .args(["--color", "always", "verify", "--format", "json", "--request"])
        .arg(&request);
    #[cfg(not(feature = "setup"))]
    colored_json.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let json_out = colored_json.output().unwrap();
    assert_eq!(json_out.status.code(), Some(1));
    assert!(!json_out.stdout.contains(&0x1b), "JSON stdout must never contain ESC");
    let parsed: serde_json::Value = serde_json::from_slice(&json_out.stdout).unwrap();
    assert_eq!(parsed["schema_version"], 3);
    assert_eq!(parsed["status"], "unsupported");

    // 3. `--format auto` resolves to JSON when stdout is piped.
    let mut auto_cmd = command(Route::Direct, project.path());
    auto_cmd.args(["verify", "--format", "auto", "--request"]).arg(&request);
    #[cfg(not(feature = "setup"))]
    auto_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let auto_out = auto_cmd.output().unwrap();
    assert_eq!(auto_out.status.code(), Some(1));
    let auto_parsed: serde_json::Value = serde_json::from_slice(&auto_out.stdout).unwrap();
    assert_eq!(auto_parsed["schema_version"], 3);
}

#[cfg(unix)]
#[test]
fn broken_pipe_exits_cleanly_and_preserves_nonzero_verify_exit_codes() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let binary = Path::new(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"));
    let request = project.path().join("bad-request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let missing_tmp = project.path().join("missing-tmp");

    // 1. `cargo-anneal skill | true`: closed read end triggers `EPIPE`;
    //    `computed_exit == 0` -> exits `0` with zero panic diagnostics on
    //    stderr.
    let skill_rc = project.path().join("skill.rc");
    let skill_pipe = Command::new("/bin/sh")
        .arg("-c")
        .arg("(\"$1\" skill 2>\"$2\"; printf '%d' \"$?\" > \"$3\") | true")
        .arg("sh")
        .arg(binary)
        .arg(project.path().join("skill.stderr"))
        .arg(&skill_rc)
        .output()
        .unwrap();
    assert!(skill_pipe.status.success(), "{skill_pipe:?}");
    assert_eq!(fs::read_to_string(&skill_rc).unwrap(), "0");
    assert!(fs::read(project.path().join("skill.stderr")).unwrap().is_empty());

    // 2. Failing `verify` (`exit 1` and `exit 2`) with an immediately closed
    //    stdout pipe preserves its exact non-zero exit code (`1` or `2`, never
    //    `0` or `101`) and still writes `--receipt-out` atomically before exit.
    let receipt_one = project.path().join("pipe-exit1.json");
    #[cfg(feature = "setup")]
    let extra = "";
    #[cfg(not(feature = "setup"))]
    let extra = "--capture cap --sysroot sys --lean lean";

    let verify_exit1 = Command::new("/bin/sh")
        .arg("-c")
        .arg(format!(
            "(\"$1\" verify --request \"$2\" --receipt-out \"$3\" {extra}; printf '%d' \"$?\" > \"$4\") | true"
        ))
        .arg("sh")
        .arg(binary)
        .arg(&request)
        .arg(&receipt_one)
        .arg(project.path().join("rc1.txt"))
        .output()
        .unwrap();
    assert!(verify_exit1.status.success());
    assert_eq!(fs::read_to_string(project.path().join("rc1.txt")).unwrap(), "1");
    let rec1: serde_json::Value = serde_json::from_slice(&fs::read(&receipt_one).unwrap()).unwrap();
    assert_eq!(rec1["status"], "unsupported");

    let verify_exit2 = Command::new("/bin/sh")
        .arg("-c")
        .arg(format!(
            "(TMPDIR=\"$3\" \"$1\" verify --request \"$2\" {extra}; printf '%d' \"$?\" > \"$4\") | true"
        ))
        .arg("sh")
        .arg(binary)
        .arg(&request)
        .arg(&missing_tmp)
        .arg(project.path().join("rc2.txt"))
        .output()
        .unwrap();
    assert!(verify_exit2.status.success());
    assert_eq!(fs::read_to_string(project.path().join("rc2.txt")).unwrap(), "2");
}
