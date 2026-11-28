// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `--exclude-trait` validation and capture forwarding.

use super::*;

#[test]
fn exclude_trait_cli_validation_and_capture_forwarding() {
    let project = tempfile::tempdir().expect("create external working directory");

    // 1. Reject non-allowlisted traits and incompatible scope flags via clap.
    for args in [
        &[
            "verify",
            "--manifest-path",
            "Cargo.toml",
            "--proof-dir",
            "proof",
            "--exclude-trait",
            "core::ops::Drop",
        ][..],
        &[
            "verify",
            "--manifest-path",
            "Cargo.toml",
            "--proof-dir",
            "proof",
            "--select",
            "f",
            "--exclude-trait",
            "core::fmt::Debug",
        ],
        &[
            "verify",
            "--request",
            "request.json",
            "--exclude-trait",
            "core::fmt::Debug",
        ],
        &[
            "verify",
            "rustc",
            "lib.rs",
            "--crate-name",
            "demo",
            "--select",
            "f",
            "--exclude-trait",
            "core::fmt::Debug",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ],
        &[
            "verify",
            "rustc",
            "lib.rs",
            "--crate-name",
            "demo",
            "--exclude-trait",
            "core::clone::Clone",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ],
    ] {
        let output = command(Route::Direct, project.path())
            .args(args)
            .output()
            .expect("run invalid --exclude-trait args");
        assert_result(&output, 2, "", "error:");
    }

    // 2. Verify canonical forwarding of `--exclude-trait` to the capture tool
    //    across `--manifest-path`, `verify rustc`, and `--request`.
    #[cfg(unix)]
    {
        use std::fs;
        fs::create_dir_all(project.path().join("pkg/src")).unwrap();
        fs::create_dir_all(project.path().join("pkg/proof")).unwrap();
        fs::write(
            project.path().join("pkg/Cargo.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        fs::write(project.path().join("pkg/src/lib.rs"), b"pub fn zero() -> u64 { 0 }\n").unwrap();
        fs::write(project.path().join("pkg/proof/Spec.lean"), b"prelude\n").unwrap();
        fs::write(project.path().join("pkg/proof/Proof.lean"), b"prelude\n").unwrap();
        let args_log = project.path().join("captured-args.txt");
        let fake_capture = project.path().join("fake-capture");
        let body = format!(
            "#!/bin/sh\nprintf '%s\\n' \"$@\" > {}\n\
             printf '%s\\n' '{{\"status\":\"unsupported\",\"diagnostics\":[\"probe stop\"],\"unsupported\":[]}}'\n\
             exit 1\n",
            args_log.display()
        );
        let stage = Command::new("/bin/sh")
            .arg("-ceu")
            .arg("printf '%s' \"$1\" > \"$2\" && chmod 0755 \"$2\"")
            .arg("sh")
            .arg(&body)
            .arg(&fake_capture)
            .output()
            .unwrap();
        assert_result(&stage, 0, "", "");
        let sysroot = project.path().join("sysroot");
        fs::create_dir(&sysroot).unwrap();
        let fake_lean = project.path().join("fake-lean");
        fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();

        let assert_forwarded = |label: &str, out: &Output| {
            assert_result(out, 1, "", "");
            let logged = fs::read_to_string(&args_log).unwrap();
            let lines: Vec<&str> = logged.lines().collect();
            let mut forwarded = Vec::new();
            let mut idx = 0;
            while idx < lines.len() {
                if lines[idx] == "--exclude-trait" {
                    forwarded.push(lines[idx + 1]);
                    idx += 2;
                } else {
                    idx += 1;
                }
            }
            assert_eq!(
                forwarded,
                vec!["core::fmt::Debug", "core::fmt::Display"],
                "{label}: logged args:\n{logged}"
            );
            let _ = fs::remove_file(&args_log);
        };

        let cargo_out = command(Route::Direct, project.path())
            .args([
                "verify",
                "--manifest-path",
                "pkg/Cargo.toml",
                "--proof-dir",
                "pkg/proof",
                "--exclude-trait",
                "core::fmt::Display",
                "--exclude-trait",
                "core::fmt::Debug",
                "--capture",
            ])
            .arg(&fake_capture)
            .arg("--sysroot")
            .arg(&sysroot)
            .arg("--lean")
            .arg(&fake_lean)
            .output()
            .unwrap();
        assert_forwarded("cargo shortcut", &cargo_out);

        let rustc_out = command(Route::Direct, project.path())
            .args([
                "verify",
                "rustc",
                "pkg/src/lib.rs",
                "--crate-name",
                "demo",
                "--exclude-trait",
                "core::fmt::Display",
                "--exclude-trait",
                "core::fmt::Debug",
                "--spec-file",
                "Spec=pkg/proof/Spec.lean",
                "--proof-file",
                "Proof=pkg/proof/Proof.lean",
                "--capture",
            ])
            .arg(&fake_capture)
            .arg("--sysroot")
            .arg(&sysroot)
            .arg("--lean")
            .arg(&fake_lean)
            .output()
            .unwrap();
        assert_forwarded("verify rustc", &rustc_out);

        let req_path = project.path().join("request.json");
        fs::write(
            &req_path,
            serde_json::json!({
                "schema_version": 1,
                "compilation": {
                    "source_root": "pkg/src",
                    "crate_root": "lib.rs",
                    "crate_name": "demo",
                    "edition": "2024",
                    "target": "x86_64-unknown-linux-gnu",
                    "cfg": [],
                    "source_files": ["lib.rs"]
                },
                "scope": {
                    "kind": "crate",
                    "excluded_traits": ["core::fmt::Display", "core::fmt::Debug"]
                },
                "proof": {
                    "source_root": "pkg/proof",
                    "sources": [
                        {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                        {"module": "Proof", "path": "Proof.lean", "role": "proof"}
                    ]
                }
            })
            .to_string(),
        )
        .unwrap();
        let req_out = command(Route::Direct, project.path())
            .args(["verify", "--request"])
            .arg(&req_path)
            .arg("--capture")
            .arg(&fake_capture)
            .arg("--sysroot")
            .arg(&sysroot)
            .arg("--lean")
            .arg(&fake_lean)
            .output()
            .unwrap();
        assert_forwarded("request json", &req_out);
    }
}
