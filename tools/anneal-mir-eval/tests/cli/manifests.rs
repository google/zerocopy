// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Manifest v5 body selection, the unsafe-probe opt-in, and a real
//! `zerocopy` capture manifest.

use super::*;

#[test]
fn cli_manifest_v5_body_selection_and_unsafe_probe_opt_in() {
    struct TempDir(std::path::PathBuf);
    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    let dir = TempDir(
        std::env::temp_dir().join(format!("anneal-mir-eval-manifest-{}", std::process::id())),
    );
    fs::create_dir_all(&dir.0).unwrap();
    let json_path = dir.0.join("manifest.json");
    let h = "b".repeat(64);
    fs::write(
        &json_path,
        format!(
            r#"{{
                "schema_version": 5,
                "compiler": {{
                    "commit": "0123456789abcdef",
                    "version": "1.100.0",
                    "sysroot": "/sysroot",
                    "rustc_sha256": "{h}",
                    "driver": {{
                        "linkage": "dynamic_dso",
                        "driver_sha256": "{h}",
                        "dso_digests": {{}}
                    }}
                }},
                "configuration": {{
                    "crate_root": "src/lib.rs",
                    "crate_name": "demo",
                    "crate_type": "lib",
                    "panic": "unwind",
                    "edition": "2024",
                    "target": "powerpc64-unknown-linux-gnu",
                    "cfg": [],
                    "env": {{}},
                    "opt_level": 0,
                    "debug_assertions": false,
                    "overflow_checks": false,
                    "mir_preserve_ub": true,
                    "pointer_bits": 64,
                    "endian": "big",
                    "declared_source_files": ["src/lib.rs"]
                }},
                "source_files": [],
                "census": [],
                "selected": [],
                "unsupported": [],
                "program": {{
                    "scope": {{ "kind": "crate" }},
                    "mir_profile_version": 1,
                    "bodies": [
                        {{
                            "arg_count": 0,
                            "is_unsafe": false,
                            "identity": "rust-path-v1::demo::unit",
                            "local_tys": [{{ "kind": "unit" }}],
                            "blocks": [{{
                                "statements": [],
                                "terminator": {{ "kind": "ret" }}
                            }}]
                        }},
                        {{
                            "arg_count": 1,
                            "is_unsafe": true,
                            "identity": "rust-path-v1::demo::unsafe_nz",
                            "local_tys": [{{ "kind": "unit" }}, {{ "kind": "bool" }}],
                            "blocks": [
                                {{
                                    "statements": [],
                                    "terminator": {{
                                        "kind": "switch_int",
                                        "operand": {{ "kind": "copy", "local": 1 }},
                                        "targets": [[1, 1]],
                                        "otherwise": 2
                                    }}
                                }},
                                {{
                                    "statements": [],
                                    "terminator": {{ "kind": "ret" }}
                                }},
                                {{
                                    "statements": [],
                                    "terminator": {{ "kind": "unreachable" }}
                                }}
                            ]
                        }}
                    ]
                }}
            }}"#
        ),
    )
    .unwrap();
    let p = json_path.to_str().unwrap();

    // Multi-body manifest requires explicit `--body` for `eval`.
    let no_body = Command::new(bin_path()).args(["eval", p]).output().unwrap();
    assert_eq!(no_body.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&no_body.stderr).contains("pass --body"));

    let with_body =
        Command::new(bin_path()).args(["eval", p, "--body", "demo::unit"]).output().unwrap();
    assert!(with_body.status.success(), "{}", String::from_utf8_lossy(&with_body.stderr));

    // `probe --all` skips `unsafe fn` by default (`exit 0`) in both text and
    // JSON modes; `--include-unsafe` probes it (`exit 2`).
    let skip_unsafe = Command::new(bin_path()).args(["probe", p, "--all"]).output().unwrap();
    assert!(skip_unsafe.status.success());
    let skip_out = String::from_utf8_lossy(&skip_unsafe.stdout);
    assert!(skip_out.contains("skipped_unsafe=true"), "{skip_out}");

    let skip_json =
        Command::new(bin_path()).args(["probe", p, "--all", "--json"]).output().unwrap();
    assert!(skip_json.status.success());
    let skip_json_out = String::from_utf8_lossy(&skip_json.stdout);
    assert!(skip_json_out.contains("\"skipped_unsafe\": true"), "{skip_json_out}");

    let inc_unsafe =
        Command::new(bin_path()).args(["probe", p, "--all", "--include-unsafe"]).output().unwrap();
    assert_eq!(inc_unsafe.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&inc_unsafe.stdout).contains("COUNTEREXAMPLE"));
}

#[test]
fn cli_evaluates_and_probes_real_zerocopy_capture_manifest() {
    let fixture = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/zerocopy_01_usize_pointer_metadata_capture.json"
    );

    let list_out = Command::new(bin_path()).args(["list", fixture]).output().unwrap();
    assert!(list_out.status.success(), "{}", String::from_utf8_lossy(&list_out.stderr));
    let list_stdout = String::from_utf8_lossy(&list_out.stdout);
    assert!(list_stdout.contains("<usize as PointerMetadata>::from_elem_count"), "{list_stdout}");
    assert!(list_stdout.contains("<usize as PointerMetadata>::to_elem_count"), "{list_stdout}");

    let eval_out = Command::new(bin_path())
        .args([
            "eval",
            fixture,
            "--body",
            "<usize as PointerMetadata>::from_elem_count",
            "--arg",
            "42",
        ])
        .output()
        .unwrap();
    assert!(eval_out.status.success(), "{}", String::from_utf8_lossy(&eval_out.stderr));
    assert!(String::from_utf8_lossy(&eval_out.stdout).contains("RETURNED 42usize"));

    let probe_out = Command::new(bin_path())
        .args(["probe", fixture, "--all", "--cases", "32"])
        .output()
        .unwrap();
    assert!(probe_out.status.success(), "{}", String::from_utf8_lossy(&probe_out.stderr));
    let probe_stdout = String::from_utf8_lossy(&probe_out.stdout);
    assert!(
        probe_stdout
            .contains("ub=0 (replayable=0, model_only_unreplayed=0) unsupported=0 oom_fuel=0"),
        "{probe_stdout}"
    );
}
