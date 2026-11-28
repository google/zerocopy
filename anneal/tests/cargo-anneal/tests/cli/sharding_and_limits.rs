// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Sharding guards, the inspector output bound, and heartbeat limits.

use super::*;

#[cfg(unix)]
#[test]
fn sharding_cli_guards_reserved_modules_missing_shards_and_shard_plan() {
    use std::fs;
    use std::os::unix::fs::PermissionsExt;

    let project = tempfile::tempdir().unwrap();
    fs::write(project.path().join("lib.rs"), b"pub fn f() -> u64 { 0 }\n").unwrap();
    fs::write(project.path().join("Spec.lean"), b"").unwrap();
    fs::write(project.path().join("Proof.lean"), b"").unwrap();
    fs::write(project.path().join("Bad.lean"), b"").unwrap();
    let sysroot = project.path().join("sysroot");
    fs::create_dir_all(&sysroot).unwrap();
    let fake_lean = project.path().join("lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

    let fake_capture = project.path().join("fake-capture");
    let script = "#!/bin/sh\n\
        set -eu\n\
        out_dir=''\n\
        while [ \"$#\" -gt 0 ]; do\n\
          if [ \"$1\" = '--out-dir' ]; then shift; out_dir=\"$1\"; fi\n\
          shift\n\
        done\n\
        mkdir -p \"$out_dir\"\n\
        cat > \"$out_dir/capture.json\" <<'JSON'\n\
        {\n\
          \"schema_version\": 5,\n\
          \"compiler\": {\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"},\n\
          \"configuration\": {\n\
            \"crate_root\": \"lib.rs\",\n\
            \"crate_name\": \"demo\",\n\
            \"crate_type\": \"lib\",\n\
            \"panic\": \"unwind\",\n\
            \"overflow_checks\": false,\n\
            \"target\": \"x86_64-unknown-linux-gnu\",\n\
            \"edition\": \"2024\",\n\
            \"cfg\": [],\n\
            \"env\": {}\n\
          },\n\
          \"source_files\": [],\n\
          \"census\": [],\n\
          \"selected\": [],\n\
          \"program\": {\"scope\": {\"kind\": \"crate\"}, \"bodies\": [{}, {}]}\n\
        }\n\
        JSON\n\
        printf '{\"status\":\"captured\"}\\n'\n";
    fs::write(&fake_capture, script).unwrap();
    fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

    // 1. `--shard-max-bodies 0` fails argument parsing with exit code 2.
    let zero_max = command(Route::Direct, project.path())
        .args([
            "verify",
            "--shard-max-bodies",
            "0",
            "--request",
            "request.json",
        ])
        .output()
        .unwrap();
    assert_result(&zero_max, 2, "", "value must be at least 1");

    // 2. Authored `Captured.*` and `Expected.*` submodules are reserved.
    for (flag, arg) in [
        ("--proof-file", "Captured.Shard_000=Bad.lean"),
        ("--proof-file", "Expected.Claim=Bad.lean"),
        ("--spec-file", "Captured.Spec=Bad.lean"),
    ] {
        let out = command(Route::Direct, project.path())
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
                "--spec-file",
                "Spec=Spec.lean",
                "--proof-file",
                "Proof=Proof.lean",
                flag,
                arg,
            ])
            .output()
            .unwrap();
        assert_result(&out, 1, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(receipt["status"], "unsupported", "{receipt}");
        assert_eq!(receipt["phase"], "proof", "{receipt}");
        assert!(
            receipt["detail"].as_str().unwrap_or("").contains("reserved proof module"),
            "{receipt}"
        );
    }

    // 3. Emitting > `--shard-min-bodies` bodies without shards fails closed.
    let missing_shards = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--shard-min-bodies",
            "1",
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
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ])
        .output()
        .unwrap();
    assert_result(&missing_shards, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&missing_shards.stdout).unwrap();
    assert_eq!(receipt["status"], "tool_failed", "{receipt}");
    assert_eq!(receipt["phase"], "capture", "{receipt}");
    assert!(
        receipt["detail"].as_str().unwrap_or("").contains("without capture_shards.json"),
        "{receipt}"
    );

    // 4. `shard-plan --write` / `--check` and `--verify-shard-plan` checks.
    let req_path = project.path().join("request.json");
    fs::write(
        &req_path,
        serde_json::to_vec(&serde_json::json!({
            "schema_version": 1,
            "compilation": {
                "source_root": ".",
                "crate_root": "lib.rs",
                "crate_name": "demo",
                "source_files": ["lib.rs"]
            },
            "scope": { "kind": "crate" },
            "proof": {
                "source_root": ".",
                "sources": [
                    { "module": "Spec", "path": "Spec.lean", "role": "specification" },
                    { "module": "Proof", "path": "Proof.lean", "role": "proof" }
                ]
            }
        }))
        .unwrap(),
    )
    .unwrap();
    let plan_path = project.path().join("anneal-shards.json");
    let write_plan = command(Route::Direct, project.path())
        .args([
            "shard-plan",
            "--request",
            req_path.to_str().unwrap(),
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--shard-min-bodies",
            "10",
            "--write",
            plan_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_result(&write_plan, 0, "\"sharded\": false", "wrote shard plan");

    let check_ok = command(Route::Cargo, project.path())
        .args([
            "shard-plan",
            "--request",
            req_path.to_str().unwrap(),
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--shard-min-bodies",
            "10",
            "--check",
            plan_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_result(&check_ok, 0, "\"total_bodies\": 2", "");

    let check_drift = command(Route::Direct, project.path())
        .args([
            "shard-plan",
            "--request",
            req_path.to_str().unwrap(),
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--shard-min-bodies",
            "5",
            "--check",
            plan_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_result(&check_drift, 1, "", "shard-plan mismatch");

    let verify_drift = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--request",
            req_path.to_str().unwrap(),
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--lean",
            fake_lean.to_str().unwrap(),
            "--shard-min-bodies",
            "5",
            "--verify-shard-plan",
            plan_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_result(&verify_drift, 2, "", "");
    let drift_receipt: serde_json::Value = serde_json::from_slice(&verify_drift.stdout).unwrap();
    assert!(
        drift_receipt["detail"].as_str().unwrap_or("").contains("shard-plan mismatch"),
        "{drift_receipt}"
    );

    // 5. `--receipt-out` aliasing `--verify-shard-plan` fails closed (exit 2)
    //    without modifying the shard plan on disk.
    let plan_before = fs::read(&plan_path).unwrap();
    let alias_out = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--request",
            req_path.to_str().unwrap(),
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--lean",
            fake_lean.to_str().unwrap(),
            "--verify-shard-plan",
            plan_path.to_str().unwrap(),
            "--receipt-out",
            plan_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_result(&alias_out, 2, "", "");
    let alias_receipt: serde_json::Value = serde_json::from_slice(&alias_out.stdout).unwrap();
    assert_eq!(alias_receipt["phase"], "receipt-out", "{alias_receipt}");
    assert!(
        alias_receipt["detail"].as_str().unwrap_or("").contains("aliases verification input"),
        "{alias_receipt}"
    );
    assert_eq!(fs::read(&plan_path).unwrap(), plan_before);
}

/// Write a fake unpinned Lean toolchain, Rust capture tool, and sysroot under
/// `root` for the `rustc`-mode crate `demo` (`lib.rs`, `Spec.lean`,
/// `Proof.lean`). Lean answers admission queries, writes stub `.olean`s, and
/// writes a 256-byte inspector `result.json`; `before_run` is shell run first
/// on every other Lean invocation. Returns `(lean, capture, sysroot)`.
#[cfg(unix)]
fn write_fake_unpinned_toolchain(
    root: &Path,
    before_run: &str,
) -> (std::path::PathBuf, std::path::PathBuf, std::path::PathBuf) {
    use std::{fs, os::unix::fs::PermissionsExt};

    fs::write(root.join("lib.rs"), b"pub fn id(x: u8) -> u8 { x }\n").unwrap();
    fs::write(root.join("Spec.lean"), b"-- spec\n").unwrap();
    fs::write(root.join("Proof.lean"), b"-- proof\n").unwrap();
    let sysroot = root.join("rust-sysroot");
    fs::create_dir_all(&sysroot).unwrap();

    let lean_prefix = root.join("lean-prefix");
    fs::create_dir_all(lean_prefix.join("bin")).unwrap();
    fs::create_dir_all(lean_prefix.join("lib/lean")).unwrap();
    fs::write(lean_prefix.join("lib/lean/Init.olean"), b"olean\x02init").unwrap();
    let fake_lean = lean_prefix.join("bin/lean");
    let lean_script = format!(
        "#!/bin/sh\n\
         set -eu\n\
         if [ \"${{1:-}}\" = '--version' ]; then\n\
           printf 'Lean (version 4.35.0)\\n'\n\
           exit 0\n\
         fi\n\
         if [ \"${{1:-}}\" = '--print-prefix' ]; then\n\
           printf '%s\\n' {prefix:?}\n\
           exit 0\n\
         fi\n\
         {before_run}\n\
         out_olean=''\n\
         run_mode=0\n\
         last=''\n\
         while [ \"$#\" -gt 0 ]; do\n\
           case \"$1\" in\n\
             -o)\n\
               shift\n\
               out_olean=\"$1\"\n\
               ;;\n\
             --run)\n\
               run_mode=1\n\
               ;;\n\
           esac\n\
           last=\"$1\"\n\
           shift\n\
         done\n\
         if [ -n \"$out_olean\" ]; then\n\
           printf 'olean\\002inspector' > \"$out_olean\"\n\
           exit 0\n\
         fi\n\
         if [ \"$run_mode\" -eq 1 ]; then\n\
           dd if=/dev/zero bs=256 count=1 of=\"$last\" status=none\n\
           exit 0\n\
         fi\n\
         exit 0\n",
        prefix = lean_prefix.display(),
    );
    fs::write(&fake_lean, lean_script).unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

    let fake_capture = root.join("fake-capture");
    let cap_script = "#!/bin/sh\n\
        set -eu\n\
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
        {\n\
          \"schema_version\": 5,\n\
          \"compiler\": {\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"},\n\
          \"configuration\": {\n\
            \"crate_root\": \"lib.rs\",\n\
            \"crate_name\": \"demo\",\n\
            \"crate_type\": \"lib\",\n\
            \"panic\": \"unwind\",\n\
            \"overflow_checks\": false,\n\
            \"target\": \"x86_64-unknown-linux-gnu\",\n\
            \"edition\": \"2024\",\n\
            \"cfg\": [],\n\
            \"env\": {}\n\
          },\n\
          \"source_files\": [],\n\
          \"census\": [],\n\
          \"selected\": [],\n\
          \"program\": {\"scope\": {\"kind\": \"selected_unit\", \"roots\": [\"id\"]}, \"bodies\": []}\n\
        }\n\
        JSON\n\
        printf -- '-- captured\\n' > \"$out_dir/Captured.lean\"\n\
        printf '{\"status\":\"captured\"}\\n'\n";
    fs::write(&fake_capture, cap_script).unwrap();
    fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();
    (fake_lean, fake_capture, sysroot)
}

#[test]
fn max_inspector_output_bytes_validates_bounds_and_propagates_to_verify() {
    let project = tempfile::tempdir().unwrap();
    for route in [Route::Direct, Route::Cargo] {
        for subargs in [&["verify", "--help"][..], &["verify", "rustc", "--help"][..]] {
            let mut cmd = command(route, project.path());
            cmd.args(subargs);
            let output = cmd.output().unwrap();
            assert_eq!(output.status.code(), Some(0), "{route:?} {subargs:?}: {output:?}");
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert!(stdout.contains("--max-inspector-output-bytes"), "{route:?} {subargs:?}");
        }

        for bad in ["0", "1073741825", "-1", "not-a-number"] {
            let flag = format!("--max-inspector-output-bytes={bad}");
            let mut cmd = command(route, project.path());
            cmd.args(["verify", "--request", "request.json", &flag]);
            let output = cmd.output().unwrap();
            assert_result(&output, 2, "", "");
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains("max-inspector-output-bytes"), "{route:?} bad={bad}: {stderr}");
        }
    }

    // End-to-end propagation through `verify`: configure a fake unpinned Lean
    // toolchain whose inspector run writes a 256-byte `result.json`. Under
    // `--max-inspector-output-bytes 64`, Door 1 rejects `result.json` with the
    // size-cap error and `audit` hint; raising `--max-inspector-output-bytes`
    // to `4096` admits the 256-byte file past Door 1 into protocol parsing.
    #[cfg(unix)]
    {
        let project = tempfile::tempdir().unwrap();
        let root = project.path();
        let (fake_lean, fake_capture, sysroot) = write_fake_unpinned_toolchain(root, ":");

        let run_verify_with_cap = |cap_bytes: &str| -> serde_json::Value {
            let mut cmd = command(Route::Direct, root);
            cmd.args([
                "verify",
                "--format",
                "json",
                "--no-cache",
                "--allow-unpinned-lean",
                "--allow-unsandboxed-elaboration",
                "--capture",
                fake_capture.to_str().unwrap(),
                "--sysroot",
                sysroot.to_str().unwrap(),
                "--lean",
                fake_lean.to_str().unwrap(),
                "--max-inspector-output-bytes",
                cap_bytes,
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
            assert_eq!(output.status.code(), Some(2), "cap={cap_bytes}: {output:?}");
            serde_json::from_slice(&output.stdout).unwrap()
        };

        let small_receipt = run_verify_with_cap("64");
        assert_eq!(small_receipt["status"], "tool_failed", "{small_receipt}");
        assert_eq!(small_receipt["phase"], "audit", "{small_receipt}");
        let small_detail = small_receipt["detail"].as_str().unwrap();
        assert!(small_detail.contains("exceeds size cap (256 > 64 bytes)"), "{small_receipt}");
        let small_hint = small_receipt["hint"].as_str().unwrap();
        assert!(small_hint.contains("--max-inspector-output-bytes"), "{small_receipt}");

        let raised_receipt = run_verify_with_cap("4096");
        assert_eq!(raised_receipt["status"], "tool_failed", "{raised_receipt}");
        assert_eq!(raised_receipt["phase"], "audit", "{raised_receipt}");
        let raised_detail = raised_receipt["detail"].as_str().unwrap();
        assert!(!raised_detail.contains("exceeds size cap"), "{raised_receipt}");
        assert!(
            raised_detail.contains("unexpected inspector protocol response"),
            "{raised_receipt}"
        );
        assert!(raised_receipt["hint"].is_null(), "{raised_receipt}");
    }
}

/// `--child-timeout-secs` bounds each Lean child: a fake Lean whose first
/// non-admission invocation sleeps for 3 seconds is killed under a 1-second
/// limit, with a hint naming the flag, but runs to the same later failure
/// under the default or a raised limit.
#[cfg(unix)]
#[test]
fn child_timeout_secs_bounds_lean_children() {
    let project = tempfile::tempdir().unwrap();
    let root = project.path();
    let marker = root.join("slept");
    for query_arg in ["--version", "--print-prefix"] {
        let (adm_lean, adm_capture, adm_sysroot) = write_fake_unpinned_toolchain(root, ":");
        let query_sleep_script = format!(
            "#!/bin/sh\n\
             set -eu\n\
             if [ \"${{1:-}}\" = {query_arg:?} ]; then\n\
               : > {m:?}\n\
               sleep 4\n\
             fi\n\
             if [ \"${{1:-}}\" = '--version' ]; then\n\
               printf 'Lean (version 4.35.0)\\n'\n\
               exit 0\n\
             fi\n\
             if [ \"${{1:-}}\" = '--print-prefix' ]; then\n\
               printf '%s\\n' {prefix:?}\n\
               exit 0\n\
             fi\n\
             exit 0\n",
            m = marker.display(),
            prefix = root.join("lean-prefix").display(),
        );
        std::fs::write(&adm_lean, query_sleep_script).unwrap();
        let _ = std::fs::remove_file(&marker);
        let mut cmd = command(Route::Direct, root);
        cmd.args(["verify", "--format", "json", "--no-cache", "--allow-unpinned-lean"])
            .args(["--allow-unsandboxed-elaboration", "--child-timeout-secs", "1", "--capture"])
            .arg(&adm_capture)
            .arg("--sysroot")
            .arg(&adm_sysroot)
            .arg("--lean")
            .arg(&adm_lean)
            .args(["rustc", "lib.rs", "--crate-name", "demo", "--select", "id"])
            .args(["--spec-file", "Spec=Spec.lean", "--proof-file", "Proof=Proof.lean"]);
        let output = cmd.output().unwrap();
        assert_eq!(output.status.code(), Some(2), "{query_arg}: {output:?}");
        assert!(marker.exists(), "{query_arg}: fake Lean never ran");
        let adm_timed_out: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(adm_timed_out["status"], "tool_failed", "{query_arg}: {adm_timed_out}");
        let adm_detail = adm_timed_out["detail"].as_str().unwrap();
        assert!(
            adm_detail.contains("exceeded wall-clock timeout of 1s"),
            "{query_arg}: {adm_timed_out}"
        );
        assert!(
            adm_timed_out["hint"].as_str().unwrap().contains("--child-timeout-secs"),
            "{query_arg}: {adm_timed_out}"
        );
    }

    let (fake_lean, fake_capture, sysroot) = write_fake_unpinned_toolchain(
        root,
        &format!("if [ ! -e {m:?} ]; then : > {m:?}; sleep 3; fi", m = marker.display()),
    );
    let run_verify = |timeout: Option<&str>| -> serde_json::Value {
        let _ = std::fs::remove_file(&marker);
        let mut cmd = command(Route::Direct, root);
        cmd.args(["verify", "--format", "json", "--no-cache", "--allow-unpinned-lean"])
            .args(["--allow-unsandboxed-elaboration", "--capture"])
            .arg(&fake_capture)
            .arg("--sysroot")
            .arg(&sysroot)
            .arg("--lean")
            .arg(&fake_lean);
        if let Some(timeout) = timeout {
            cmd.args(["--child-timeout-secs", timeout]);
        }
        cmd.args(["rustc", "lib.rs", "--crate-name", "demo", "--select", "id"]);
        cmd.args(["--spec-file", "Spec=Spec.lean", "--proof-file", "Proof=Proof.lean"]);
        let output = cmd.output().unwrap();
        assert_eq!(output.status.code(), Some(2), "timeout={timeout:?}: {output:?}");
        assert!(marker.exists(), "timeout={timeout:?}: fake Lean never ran");
        serde_json::from_slice(&output.stdout).unwrap()
    };

    let timed_out = run_verify(Some("1"));
    assert_eq!(timed_out["status"], "tool_failed", "{timed_out}");
    let detail = timed_out["detail"].as_str().unwrap();
    assert!(detail.contains("exceeded wall-clock timeout of 1s"), "{timed_out}");
    assert!(timed_out["hint"].as_str().unwrap().contains("--child-timeout-secs"), "{timed_out}");

    // The limit only bounds run time: every run carries the same taints.
    let default = run_verify(None);
    for (timeout, receipt) in [(None, &default), (Some("30"), &run_verify(Some("30")))] {
        let detail = receipt["detail"].as_str().unwrap();
        assert!(!detail.contains("wall-clock timeout"), "timeout={timeout:?}: {receipt}");
        assert!(
            detail.contains("unexpected inspector protocol response"),
            "timeout={timeout:?}: {receipt}"
        );
        assert_eq!(receipt["taint_reasons"], timed_out["taint_reasons"], "{receipt}");
    }
    assert_eq!(
        default["taint_reasons"],
        serde_json::json!(["unpinned_lean", "unsandboxed_elaboration"]),
        "{default}"
    );
}

#[cfg(unix)]
#[test]
fn verify_emits_structured_reason_on_authored_proof_heartbeat_limit() {
    use std::{fs, os::unix::fs::PermissionsExt};

    let project = tempfile::tempdir().unwrap();
    let root = project.path();
    fs::write(root.join("lib.rs"), b"pub fn id(x: u8) -> u8 { x }\n").unwrap();
    fs::write(root.join("Spec.lean"), b"-- spec\n").unwrap();
    fs::write(root.join("Proof.lean"), b"-- proof\n").unwrap();
    let sysroot = root.join("rust-sysroot");
    fs::create_dir_all(&sysroot).unwrap();

    let lean_prefix = root.join("lean-prefix");
    fs::create_dir_all(lean_prefix.join("bin")).unwrap();
    fs::create_dir_all(lean_prefix.join("lib/lean/Init")).unwrap();
    fs::write(lean_prefix.join("lib/lean/Init.olean"), b"olean\x02init").unwrap();
    for m in ["Coe", "Core", "Notation", "Prelude", "SizeOf", "Tactics"] {
        fs::write(lean_prefix.join(format!("lib/lean/Init/{m}.olean")), b"olean\x02fnd").unwrap();
    }
    let fake_lean = lean_prefix.join("bin/lean");
    let lean_script = format!(
        "#!/bin/sh\n\
         set -eu\n\
         if [ \"${{1:-}}\" = '--version' ]; then\n\
           printf 'Lean (version 4.35.0)\\n'\n\
           exit 0\n\
         fi\n\
         if [ \"${{1:-}}\" = '--print-prefix' ]; then\n\
           printf '%s\\n' {prefix:?}\n\
           exit 0\n\
         fi\n\
         out_olean=''\n\
         run_mode=0\n\
         prev=''\n\
         last=''\n\
         while [ \"$#\" -gt 0 ]; do\n\
           case \"$1\" in\n\
             -o)\n\
               shift\n\
               out_olean=\"$1\"\n\
               ;;\n\
             --run)\n\
               run_mode=1\n\
               ;;\n\
           esac\n\
           prev=\"$last\"\n\
           last=\"$1\"\n\
           shift\n\
         done\n\
         if [ \"$run_mode\" -eq 1 ]; then\n\
           /usr/bin/python3 -c 'import json, sys; req = json.load(open(sys.argv[1])); m = req[\"mode\"]; fnd = [\"Init.Coe\", \"Init.Core\", \"Init.Notation\", \"Init.Prelude\", \"Init.SizeOf\", \"Init.Tactics\"]; res = {{\"headers\": [{{\"module\": n, \"imports\": [], \"isModule\": False}} for n, _ in req[\"sources\"]]}} if m == \"headers\" else ({{\"checked\": [n for n, _ in req[\"sources\"]]}} if m == \"spec-preflight\" else ({{\"graph\": {{k: ([{{\"module\": d, \"importAll\": False, \"isExported\": True, \"isMeta\": False}} for d in fnd if d != k] if k == \"Init.Core\" else []) for k in fnd}}}} if m == \"resolve-imports\" else {{}})); json.dump({{\"ok\": True, \"result\": res}}, open(sys.argv[2], \"w\"))' \"$prev\" \"$last\"\n\
           exit 0\n\
         fi\n\
         case \"$out_olean\" in\n\
           */Proof.olean|Proof.olean)\n\
             printf '{{\"severity\":\"error\",\"kind\":\"runtime.maxHeartbeats\",\"data\":\"(deterministic) timeout\"}}\\n'\n\
             exit 1\n\
             ;;\n\
         esac\n\
         if [ -n \"$out_olean\" ]; then\n\
           printf 'olean\\002stub' > \"$out_olean\"\n\
           exit 0\n\
         fi\n\
         exit 0\n",
        prefix = lean_prefix.display(),
    );
    fs::write(&fake_lean, lean_script).unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

    let fake_capture = root.join("fake-capture");
    let cap_script = "#!/bin/sh\n\
        set -eu\n\
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
        {\n\
          \"schema_version\": 5,\n\
          \"compiler\": {\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"},\n\
          \"configuration\": {\n\
            \"crate_root\": \"lib.rs\",\n\
            \"crate_name\": \"demo\",\n\
            \"crate_type\": \"lib\",\n\
            \"panic\": \"unwind\",\n\
            \"overflow_checks\": false,\n\
            \"target\": \"x86_64-unknown-linux-gnu\",\n\
            \"edition\": \"2024\",\n\
            \"cfg\": [],\n\
            \"env\": {}\n\
          },\n\
          \"source_files\": [],\n\
          \"census\": [],\n\
          \"selected\": [],\n\
          \"program\": {\"scope\": {\"kind\": \"selected_unit\", \"roots\": [\"id\"]}, \"bodies\": []}\n\
        }\n\
        JSON\n\
        printf -- '-- captured\\n' > \"$out_dir/Captured.lean\"\n\
        printf '{\"status\":\"captured\"}\\n'\n";
    fs::write(&fake_capture, cap_script).unwrap();
    fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

    let receipt_out = root.join("emitted-receipt.json");
    let output = command(Route::Direct, root)
        .args([
            "verify",
            "--format",
            "json",
            "--no-cache",
            "--allow-unpinned-lean",
            "--allow-unsandboxed-elaboration",
            "--receipt-out",
            receipt_out.to_str().unwrap(),
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
            "--select",
            "id",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");

    let stdout_receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let file_receipt: serde_json::Value =
        serde_json::from_slice(&fs::read(&receipt_out).unwrap()).unwrap();
    for (label, receipt) in [("stdout", &stdout_receipt), ("receipt-out", &file_receipt)] {
        assert_eq!(receipt["status"], "proof_failed", "{label}: {receipt}");
        assert_eq!(receipt["phase"], "audit", "{label}: {receipt}");
        assert_eq!(receipt["reason"], "heartbeat_limit_exceeded", "{label}: {receipt}");
    }
}
