// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Binding of the request's crate root, standard-library crate, and
//! instantiation scope to the capture.

use super::*;

#[cfg(unix)]
#[test]
fn verify_rejects_mismatched_capture_crate_root() {
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
    let fake_capture = project.path().join("fake-capture");
    let script = "#!/bin/sh\n\
         out_dir=\"\"\n\
         while [ \"$#\" -gt 0 ]; do\n\
           if [ \"$1\" = \"--out-dir\" ]; then shift; out_dir=\"$1\"; fi\n\
           shift\n\
         done\n\
         mkdir -p \"$out_dir\"\n\
         cat > \"$out_dir/capture.json\" <<'JSON'\n\
         {\n\
           \"schema_version\": 5,\n\
           \"compiler\": {\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"},\n\
           \"configuration\": {\n\
             \"crate_root\": \"other.rs\",\n\
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
           \"program\": {\"scope\": {\"kind\": \"selected_unit\", \"roots\": [\"f\"]}, \"bodies\": []}\n\
         }\n\
         JSON\n\
         printf '{\"status\":\"captured\"}\\n'\n";
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
}

#[cfg(unix)]
#[test]
fn verify_accepts_equivalent_request_crate_root_spellings() {
    use std::{fs, os::unix::fs::PermissionsExt};

    let project = tempfile::tempdir().unwrap();
    fs::create_dir_all(project.path().join("src")).unwrap();
    fs::write(project.path().join("src/lib.rs"), b"pub fn f() -> u64 { 0 }\n").unwrap();
    fs::write(project.path().join("Spec.lean"), b"").unwrap();
    fs::write(project.path().join("Proof.lean"), b"").unwrap();
    let sysroot = project.path().join("sysroot");
    fs::create_dir_all(&sysroot).unwrap();
    let fake_lean = project.path().join("lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

    let write_fake_capture = |name: &str, crate_root_field: &str| {
        let path = project.path().join(name);
        let script = format!(
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
                 {crate_root_field}\
                 \"crate_name\": \"demo\",\n\
                 \"crate_type\": \"lib\",\n\
                 \"panic\": \"unwind\",\n\
                 \"overflow_checks\": false,\n\
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
             printf -- '-- captured\\n' > \"$out_dir/Captured.lean\"\n\
             printf '{{\"status\":\"captured\"}}\\n'\n"
        );
        fs::write(&path, script).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
        path
    };

    let run_req = |capture_bin: &std::path::Path, crate_root: &str| -> serde_json::Value {
        let req_path = project.path().join("request.json");
        let req = serde_json::json!({
            "schema_version": 1,
            "compilation": {
                "source_root": ".",
                "crate_root": crate_root,
                "crate_name": "demo",
                "crate_type": "lib",
                "panic": "unwind",
                "overflow_checks": false,
                "target": "x86_64-unknown-linux-gnu",
                "edition": "2024",
                "cfg": [],
                "env": {},
                "source_files": [crate_root]
            },
            "scope": { "kind": "selected_unit", "roots": ["f"] },
            "proof": {
                "source_root": ".",
                "sources": [
                    { "module": "Spec", "path": "Spec.lean", "role": "specification" },
                    { "module": "Proof", "path": "Proof.lean", "role": "proof" }
                ],
                "specification": "Spec.specs",
                "theorem": "Proof.verify"
            }
        });
        fs::write(&req_path, serde_json::to_vec(&req).unwrap()).unwrap();
        let output = command(Route::Direct, project.path())
            .args([
                "verify",
                "--format",
                "json",
                "--capture",
                capture_bin.to_str().unwrap(),
                "--sysroot",
                sysroot.to_str().unwrap(),
                "--lean",
                fake_lean.to_str().unwrap(),
                "--request",
                req_path.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        assert_result(&output, 2, "", "");
        serde_json::from_slice(&output.stdout).unwrap()
    };

    // Component-equivalent spellings admitted by `declared_file` must pass
    // capture authentication against normalized `src/lib.rs` and reach audit.
    let norm_cap = write_fake_capture("fake-capture-norm", "\"crate_root\": \"src/lib.rs\",\n");
    for spelling in ["src//lib.rs", "src/./lib.rs"] {
        let receipt = run_req(&norm_cap, spelling);
        assert_eq!(receipt["phase"], "audit", "spelling={spelling}: {receipt}");
    }

    // Missing or non-string `crate_root` in `capture.json` still fails closed.
    let missing_cap = write_fake_capture("fake-capture-missing", "");
    let nonstr_cap = write_fake_capture("fake-capture-nonstr", "\"crate_root\": 123,\n");
    for bad_cap in [&missing_cap, &nonstr_cap] {
        let receipt = run_req(bad_cap, "src/lib.rs");
        assert_eq!(receipt["phase"], "capture", "{receipt}");
        assert!(
            receipt["detail"]
                .as_str()
                .unwrap_or("")
                .contains("capture differs from the requested compilation or scope"),
            "{receipt}"
        );
    }
}

#[cfg(unix)]
#[test]
fn verify_passes_stdlib_crate_flag_and_rejects_mismatched_capture_capability() {
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

    // A capture with relaxed language-item admission must never satisfy a
    // request that did not ask for it, and vice versa.
    for (request_capability, manifest_capability) in [(true, ""), (false, "\"core\"")] {
        let stdlib_field = if manifest_capability.is_empty() {
            String::new()
        } else {
            format!(",\\n\"stdlib_crate\": {manifest_capability}")
        };
        let script = format!(
            "#!/bin/sh\n\
             out_dir=\"\"\n\
             : > \"{args_file}\"\n\
             while [ \"$#\" -gt 0 ]; do\n\
               printf '%s\\n' \"$1\" >> \"{args_file}\"\n\
               if [ \"$1\" = \"--out-dir\" ]; then shift; out_dir=\"$1\"; fi\n\
               shift\n\
             done\n\
             mkdir -p \"$out_dir\"\n\
             printf '{{\\n\
               \"schema_version\": 5,\\n\
               \"compiler\": {{\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"}},\\n\
               \"configuration\": {{\\n\
                 \"crate_root\": \"lib.rs\",\\n\
                 \"crate_name\": \"core\",\\n\
                 \"crate_type\": \"lib\",\\n\
                 \"panic\": \"unwind\",\\n\
                 \"overflow_checks\": false,\\n\
                 \"target\": \"x86_64-unknown-linux-gnu\",\\n\
                 \"edition\": \"2024\",\\n\
                 \"cfg\": [],\\n\
                 \"env\": {{}}{stdlib_field}\\n\
               }},\\n\
               \"source_files\": [],\\n\
               \"census\": [],\\n\
               \"selected\": [],\\n\
               \"program\": {{\"scope\": {{\"kind\": \"selected_unit\", \"roots\": [\"f\"]}}, \"bodies\": []}}\\n\
             }}\\n' > \"$out_dir/capture.json\"\n\
             printf '{{\"status\":\"captured\"}}\\n'\n",
            args_file = recorded_args.display(),
        );
        fs::write(&fake_capture, script).unwrap();
        fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();
        let mut args = vec![
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
            "core",
            "--select",
            "f",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ];
        if request_capability {
            args.extend(["--stdlib-crate", "core"]);
        }
        let output = command(Route::Direct, project.path()).args(&args).output().unwrap();
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
        let recorded: Vec<&str> = args_text.lines().collect();
        assert_eq!(
            recorded.windows(2).any(|w| w == ["--stdlib-crate", "core"]),
            request_capability,
            "capture args:\n{args_text}"
        );
    }
}

#[cfg(unix)]
#[test]
fn verify_rejects_whole_crate_stdlib_crate_as_unsupported() {
    use std::{fs, os::unix::fs::PermissionsExt};

    let project = tempfile::tempdir().unwrap();
    fs::write(project.path().join("lib.rs"), b"pub fn f() -> u64 { 0 }\n").unwrap();
    fs::write(project.path().join("Spec.lean"), b"").unwrap();
    fs::write(project.path().join("Proof.lean"), b"").unwrap();
    let sysroot = project.path().join("sysroot");
    fs::create_dir_all(&sysroot).unwrap();
    let fake_lean = project.path().join("fake-lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();
    let capture_invoked = project.path().join("capture_invoked");
    let fake_capture = project.path().join("fake-capture");
    let capture_script = format!("#!/bin/sh\n: > {:?}\nexit 99\n", capture_invoked.display());
    fs::write(&fake_capture, capture_script).unwrap();
    fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

    let request_path = project.path().join("request.json");
    fs::write(
        &request_path,
        r#"{
  "schema_version": 1,
  "compilation": {
    "source_root": ".",
    "crate_root": "lib.rs",
    "crate_name": "core",
    "source_files": ["lib.rs"],
    "stdlib_crate": "core"
  },
  "scope": {"kind": "crate"},
  "proof": {
    "source_root": ".",
    "specification": "Spec.specs",
    "theorem": "Proof.verify",
    "sources": [
      {"module": "Spec", "path": "Spec.lean", "role": "specification"},
      {"module": "Proof", "path": "Proof.lean", "role": "proof"}
    ]
  }
}
"#,
    )
    .unwrap();

    let request_args = [
        "verify",
        "--format",
        "json",
        "--capture",
        fake_capture.to_str().unwrap(),
        "--sysroot",
        sysroot.to_str().unwrap(),
        "--lean",
        fake_lean.to_str().unwrap(),
        "--request",
        request_path.to_str().unwrap(),
    ];
    let rustc_args = [
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
        "core",
        "--stdlib-crate",
        "core",
        "--spec-file",
        "Spec=Spec.lean",
        "--proof-file",
        "Proof=Proof.lean",
    ];
    for args in [&request_args[..], &rustc_args[..]] {
        let output = command(Route::Direct, project.path()).args(args).output().unwrap();
        assert_result(&output, 1, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["status"], "unsupported", "{receipt}");
        assert_eq!(receipt["phase"], "request", "{receipt}");
        assert!(
            receipt["detail"]
                .as_str()
                .unwrap_or("")
                .contains("--stdlib-crate requires selected scope"),
            "{receipt}"
        );
        assert!(!capture_invoked.exists(), "capture should not be invoked for {args:?}");
    }
}

#[test]
fn verify_passes_instantiate_flags_and_rejects_mismatched_capture_scope() {
    use std::{fs, os::unix::fs::PermissionsExt};

    let project = tempfile::tempdir().unwrap();
    fs::write(project.path().join("lib.rs"), b"pub fn id<T>(x: T) -> T { x }\n").unwrap();
    fs::write(project.path().join("Spec.lean"), b"-- spec\n").unwrap();
    fs::write(project.path().join("Proof.lean"), b"-- proof\n").unwrap();

    // Malformed `--instantiate` JSON and `--request` + `--instantiate` conflict
    // must fail CLI validation with exit 2 and empty stdout.
    for bad in [
        &["verify", "--request", "r.json", "--instantiate", r#"{"path":"id","args":["usize"]}"#][..],
        &[
            "verify",
            "rustc",
            "lib.rs",
            "--crate-name",
            "demo",
            "--instantiate",
            "not-json",
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

    let sysroot = project.path().join("sysroot");
    fs::create_dir(&sysroot).unwrap();
    let fake_lean = project.path().join("fake-lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

    let recorded_args = project.path().join("capture.args");
    let fake_capture = project.path().join("fake-capture");
    // Emit a capture manifest whose scope omits the requested instantiation so
    // cargo-anneal rejects the mismatched scope before invoking Lean.
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
             \"target\": \"x86_64-unknown-linux-gnu\",\n\
             \"edition\": \"2024\",\n\
             \"cfg\": [],\n\
             \"env\": {{}}\n\
           }},\n\
           \"source_files\": [],\n\
           \"census\": [],\n\
           \"selected\": [],\n\
           \"program\": {{\"scope\": {{\"kind\": \"selected_unit\", \"roots\": []}}, \"bodies\": []}}\n\
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
            "--instantiate",
            r#"{"path":"id","args":["usize"]}"#,
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
    assert!(
        args_text.lines().any(|line| line == r#"{"path":"id","args":["usize"]}"#),
        "expected serialized --instantiate JSON in capture args:\n{args_text}"
    );
}
