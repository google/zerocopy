// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end CLI tests for the `anneal-mir-eval` binary across `list`, `eval`,
//! and `probe` subcommands and exit codes (`0`, `1`, `2`, `3`).

#![forbid(unsafe_code)]

use std::{fs, process::Command};

fn bin_path() -> &'static str {
    env!("CARGO_BIN_EXE_anneal-mir-eval")
}

fn fixture_program_json() -> &'static str {
    r#"{
        "scope": { "kind": "selected_unit", "roots": ["demo::add", "demo::div"] },
        "pointer_width_bits": 64,
        "mir_profile_version": 1,
        "bodies": [
            {
                "arg_count": 2,
                "is_unsafe": false,
                "identity": "rust-path-v1::demo::add",
                "local_tys": [
                    { "kind": "int", "width": "i32", "signed": false },
                    { "kind": "int", "width": "i32", "signed": false },
                    { "kind": "int", "width": "i32", "signed": false }
                ],
                "blocks": [{
                    "statements": [{
                        "kind": "assign",
                        "local": 0,
                        "value": {
                            "kind": "binary",
                            "op": "add",
                            "left": { "kind": "copy", "local": 1 },
                            "right": { "kind": "copy", "local": 2 }
                        }
                    }],
                    "terminator": { "kind": "ret" }
                }]
            },
            {
                "arg_count": 2,
                "is_unsafe": false,
                "identity": "rust-path-v1::demo::div",
                "local_tys": [
                    { "kind": "int", "width": "i32", "signed": false },
                    { "kind": "int", "width": "i32", "signed": false },
                    { "kind": "int", "width": "i32", "signed": false }
                ],
                "blocks": [{
                    "statements": [{
                        "kind": "assign",
                        "local": 0,
                        "value": {
                            "kind": "binary",
                            "op": "div",
                            "left": { "kind": "copy", "local": 1 },
                            "right": { "kind": "copy", "local": 2 }
                        }
                    }],
                    "terminator": { "kind": "ret" }
                }]
            },
            {
                "arg_count": 0,
                "is_unsafe": false,
                "identity": "rust-path-v1::demo::unmodeled",
                "local_tys": [{ "kind": "unit" }],
                "blocks": [{
                    "statements": [{ "kind": "unsupported" }],
                    "terminator": { "kind": "ret" }
                }]
            }
        ]
    }"#
}

#[test]
fn cli_list_eval_probe_and_exit_codes() {
    struct TempDir(std::path::PathBuf);
    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    let dir =
        TempDir(std::env::temp_dir().join(format!("anneal-mir-eval-cli-{}", std::process::id())));
    fs::create_dir_all(&dir.0).unwrap();
    let json_path = dir.0.join("program.json");
    fs::write(&json_path, fixture_program_json()).unwrap();
    let path_str = json_path.to_str().unwrap();

    // `list`
    let list_out = Command::new(bin_path()).args(["list", path_str]).output().unwrap();
    assert!(list_out.status.success());
    let list_stdout = String::from_utf8_lossy(&list_out.stdout);
    assert!(list_stdout.contains("demo::add(u32, u32) -> u32"));
    assert!(list_stdout.contains("demo::div(u32, u32) -> u32"));

    // `eval` success -> exit 0 (using suffix body name without rust-path-v1::)
    let eval_ok = Command::new(bin_path())
        .args(["eval", path_str, "--body", "demo::add", "--arg", "30", "--arg", "12", "--trace"])
        .output()
        .unwrap();
    assert!(eval_ok.status.success());
    let ok_stdout = String::from_utf8_lossy(&eval_ok.stdout);
    assert!(ok_stdout.contains("RETURNED 42u32"));
    assert!(ok_stdout.contains("assign(_0)"));

    // `eval` JSON encodes scalar bits as canonical decimal string
    let eval_json = Command::new(bin_path())
        .args([
            "eval",
            path_str,
            "--body",
            "rust-path-v1::demo::add",
            "--arg",
            "30",
            "--arg",
            "12",
            "--json",
        ])
        .output()
        .unwrap();
    assert!(eval_json.status.success());
    let json_stdout = String::from_utf8_lossy(&eval_json.stdout);
    assert!(json_stdout.contains("\"bits\": \"42\""));

    // `eval` UB -> exit 2
    let eval_ub = Command::new(bin_path())
        .args(["eval", path_str, "--body", "demo::div", "--arg", "10", "--arg", "0", "--json"])
        .output()
        .unwrap();
    assert_eq!(eval_ub.status.code(), Some(2));
    let ub_stdout = String::from_utf8_lossy(&eval_ub.stdout);
    assert!(ub_stdout.contains("\"kind\": \"undefined\""));

    // `eval` Unsupported -> exit 3
    let eval_unsup =
        Command::new(bin_path()).args(["eval", path_str, "--body", "2"]).output().unwrap();
    assert_eq!(eval_unsup.status.code(), Some(3));

    // `probe` clean body -> exit 0 and text line reports `unsupported_param_shape=false`
    let probe_ok = Command::new(bin_path())
        .args(["probe", path_str, "--body", "demo::add", "--cases", "32"])
        .output()
        .unwrap();
    assert!(probe_ok.status.success());
    let probe_ok_stdout = String::from_utf8_lossy(&probe_ok.stdout);
    assert!(
        probe_ok_stdout.contains("unsupported_param_shape=false"),
        "expected unsupported_param_shape=false in stdout: {probe_ok_stdout}"
    );

    // `probe` div body -> exit 2 with counterexample
    let probe_ub = Command::new(bin_path())
        .args(["probe", path_str, "--body", "demo::div", "--cases", "32"])
        .output()
        .unwrap();
    assert_eq!(probe_ub.status.code(), Some(2));
    let probe_stdout = String::from_utf8_lossy(&probe_ub.stdout);
    assert!(probe_stdout.contains("COUNTEREXAMPLE"));

    // `probe` unsupported body -> exit 3
    let probe_unsup = Command::new(bin_path())
        .args(["probe", path_str, "--body", "demo::unmodeled", "--cases", "4"])
        .output()
        .unwrap();
    assert_eq!(probe_unsup.status.code(), Some(3));

    // `probe` rejects conflicting `--all` and `--body` flags -> exit 1
    let probe_conflict = Command::new(bin_path())
        .args(["probe", path_str, "--all", "--body", "demo::add"])
        .output()
        .unwrap();
    assert_eq!(probe_conflict.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&probe_conflict.stderr).contains("cannot combine --all"));

    // Unknown subcommand -> exit 1
    let bad_cmd = Command::new(bin_path()).args(["bogus"]).output().unwrap();
    assert_eq!(bad_cmd.status.code(), Some(1));
}

#[test]
fn cli_signed_hex_range_and_unit_arg_type_checks() {
    struct TempDir(std::path::PathBuf);
    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    let dir =
        TempDir(std::env::temp_dir().join(format!("anneal-mir-eval-edge-{}", std::process::id())));
    fs::create_dir_all(&dir.0).unwrap();
    let json_path = dir.0.join("edge.json");
    fs::write(
        &json_path,
        r#"{
            "scope": { "kind": "selected_unit", "roots": ["demo::id_i8", "demo::id_unit"] },
            "pointer_width_bits": 64,
            "mir_profile_version": 1,
            "bodies": [
                {
                    "arg_count": 1,
                    "is_unsafe": false,
                    "identity": "rust-path-v1::demo::id_i8",
                    "local_tys": [
                        { "kind": "int", "width": "i8", "signed": true },
                        { "kind": "int", "width": "i8", "signed": true }
                    ],
                    "blocks": [{
                        "statements": [{
                            "kind": "assign",
                            "local": 0,
                            "value": {
                                "kind": "use",
                                "operand": { "kind": "copy", "local": 1 }
                            }
                        }],
                        "terminator": { "kind": "ret" }
                    }]
                },
                {
                    "arg_count": 1,
                    "is_unsafe": false,
                    "identity": "rust-path-v1::demo::id_unit",
                    "local_tys": [{ "kind": "unit" }, { "kind": "unit" }],
                    "blocks": [{
                        "statements": [{
                            "kind": "assign",
                            "local": 0,
                            "value": {
                                "kind": "use",
                                "operand": { "kind": "copy", "local": 1 }
                            }
                        }],
                        "terminator": { "kind": "ret" }
                    }]
                }
            ]
        }"#,
    )
    .unwrap();
    let path_str = json_path.to_str().unwrap();

    // Valid two's-complement 8-bit hex passes (`0xff` -> `-1i8`).
    let ok_hex = Command::new(bin_path())
        .args(["eval", path_str, "--body", "demo::id_i8", "--arg", "0xff"])
        .output()
        .unwrap();
    assert!(ok_hex.status.success(), "{}", String::from_utf8_lossy(&ok_hex.stderr));
    assert!(String::from_utf8_lossy(&ok_hex.stdout).contains("RETURNED -1i8"));

    // Out-of-range signed hex (`0x1ff` for `i8`) exits 1.
    let bad_hex = Command::new(bin_path())
        .args(["eval", path_str, "--body", "demo::id_i8", "--arg", "0x1ff"])
        .output()
        .unwrap();
    assert_eq!(bad_hex.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&bad_hex.stderr).contains("out of range"));

    // Passing `()` to an `i8` parameter fails argument parsing with exit 1 (not 3).
    let bad_unit = Command::new(bin_path())
        .args(["eval", path_str, "--body", "demo::id_i8", "--arg", "()"])
        .output()
        .unwrap();
    assert_eq!(bad_unit.status.code(), Some(1));

    // Passing `()` to a unit parameter succeeds.
    let ok_unit = Command::new(bin_path())
        .args(["eval", path_str, "--body", "demo::id_unit", "--arg", "()"])
        .output()
        .unwrap();
    assert!(ok_unit.status.success(), "{}", String::from_utf8_lossy(&ok_unit.stderr));
}

#[test]
fn cli_profile_v2_auto_dispatch_strict_v1_and_raw_ptr_probe() {
    struct TempDir(std::path::PathBuf);
    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    let dir = TempDir(
        std::env::temp_dir().join(format!("anneal-mir-eval-probe-shape-{}", std::process::id())),
    );
    fs::create_dir_all(&dir.0).unwrap();
    let json_path = dir.0.join("probe_shape.json");
    fs::write(
        &json_path,
        r#"{
            "scope": { "kind": "selected_unit", "roots": ["demo::raw_ptr"] },
            "pointer_width_bits": 64,
            "mir_profile_version": 2,
            "bodies": [
                {
                    "arg_count": 1,
                    "is_unsafe": false,
                    "identity": "rust-path-v1::demo::raw_ptr",
                    "local_tys": [
                        { "kind": "unit" },
                        {
                            "kind": "raw_ptr",
                            "mutability": "shared",
                            "pointee": { "kind": "int", "width": "i32", "signed": false }
                        }
                    ],
                    "blocks": [{
                        "statements": [],
                        "terminator": { "kind": "ret" }
                    }]
                }
            ]
        }"#,
    )
    .unwrap();
    let p = json_path.to_str().unwrap();

    // `--strict-v1` explicitly rejects `mir_profile_version == 2` (`exit 3`).
    let strict_probe = Command::new(bin_path())
        .args(["probe", p, "--body", "demo::raw_ptr", "--cases", "8", "--strict-v1"])
        .output()
        .unwrap();
    assert_eq!(strict_probe.status.code(), Some(3));
    let strict_probe_err = String::from_utf8_lossy(&strict_probe.stderr);
    assert!(strict_probe_err.contains("strict Profile v1"), "{strict_probe_err}");

    // Auto-selection (and `--profile-v2`) probes Profile v2 `RawPtr` inputs
    // cleanly.
    for extra in [&[][..], &["--profile-v2"][..]] {
        let mut cmd = Command::new(bin_path());
        cmd.args(["probe", p, "--body", "demo::raw_ptr", "--cases", "8"]).args(extra);
        let out = cmd.output().unwrap();
        assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains("unsupported_param_shape=false"),
            "expected unsupported_param_shape=false in stdout: {stdout}"
        );
    }
}

#[test]
fn cli_profile_v2_assert_ub_vs_unsupported_and_strict_v1_rejection() {
    struct TempDir(std::path::PathBuf);
    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    let dir =
        TempDir(std::env::temp_dir().join(format!("anneal-mir-eval-term-{}", std::process::id())));
    fs::create_dir_all(&dir.0).unwrap();
    let json_path = dir.0.join("v2_assert.json");
    fs::write(
        &json_path,
        r#"{
            "scope": { "kind": "selected_unit", "roots": ["demo::bounds", "demo::null_chk"] },
            "pointer_width_bits": 64,
            "mir_profile_version": 2,
            "bodies": [
                {
                    "arg_count": 0,
                    "is_unsafe": false,
                    "identity": "rust-path-v1::demo::bounds",
                    "local_tys": [{ "kind": "unit" }],
                    "blocks": [{
                        "statements": [],
                        "terminator": {
                            "kind": "assert",
                            "cond": {
                                "kind": "constant",
                                "ty": { "kind": "bool" },
                                "lit": { "kind": "scalar", "bits": "0" }
                            },
                            "expected": true,
                            "msg": { "kind": "bounds_check" },
                            "target": 0,
                            "unwind": "terminate"
                        }
                    }]
                },
                {
                    "arg_count": 0,
                    "is_unsafe": false,
                    "identity": "rust-path-v1::demo::null_chk",
                    "local_tys": [{ "kind": "unit" }],
                    "blocks": [{
                        "statements": [],
                        "terminator": {
                            "kind": "assert",
                            "cond": {
                                "kind": "constant",
                                "ty": { "kind": "bool" },
                                "lit": { "kind": "scalar", "bits": "0" }
                            },
                            "expected": true,
                            "msg": { "kind": "null_ptr_deref" },
                            "target": 0,
                            "unwind": "continue"
                        }
                    }]
                }
            ]
        }"#,
    )
    .unwrap();
    let p = json_path.to_str().unwrap();

    // `--strict-v1` fails closed (`exit 3`).
    let strict_flag = Command::new(bin_path())
        .args(["eval", p, "--body", "demo::bounds", "--strict-v1"])
        .output()
        .unwrap();
    assert_eq!(
        strict_flag.status.code(),
        Some(3),
        "{}",
        String::from_utf8_lossy(&strict_flag.stderr)
    );

    // Profile v2 panicking `Assert(BoundsCheck)` fails closed with `exit 3`
    // (`Unsupported`).
    let bounds =
        Command::new(bin_path()).args(["eval", p, "--body", "demo::bounds"]).output().unwrap();
    assert_eq!(bounds.status.code(), Some(3), "{}", String::from_utf8_lossy(&bounds.stdout));

    // Profile v2 `Assert(NullPtrDeref)` faults `exit 2` (`Undefined`) with
    // `model_only_unreplayed` witness class.
    let null_chk =
        Command::new(bin_path()).args(["eval", p, "--body", "demo::null_chk"]).output().unwrap();
    assert_eq!(null_chk.status.code(), Some(2), "{}", String::from_utf8_lossy(&null_chk.stdout));
    let null_out = String::from_utf8_lossy(&null_chk.stdout);
    assert!(null_out.contains("model_only_unreplayed"), "{null_out}");

    let probe_null =
        Command::new(bin_path()).args(["probe", p, "--body", "demo::null_chk"]).output().unwrap();
    assert_eq!(probe_null.status.code(), Some(2));
    let probe_out = String::from_utf8_lossy(&probe_null.stdout);
    assert!(probe_out.contains("(replayable=0, model_only_unreplayed=1)"), "{probe_out}");
    assert!(probe_out.contains("class=model_only_unreplayed"), "{probe_out}");
}

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

#[test]
fn cli_probe_exits_3_on_unsupported_program_even_with_empty_skipped_uninhabited_or_zero_cases() {
    struct TempDir(std::path::PathBuf);
    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let dir = TempDir(
        std::env::temp_dir().join(format!("anneal-mir-eval-probe-val-{}", std::process::id())),
    );
    fs::create_dir_all(&dir.0).unwrap();

    // 1. Empty `bodies` with `pointer_width_bits: 32` must exit 3 (not 0).
    let empty_32 = dir.0.join("empty_32.json");
    fs::write(
        &empty_32,
        r#"{
            "scope": { "kind": "crate" },
            "pointer_width_bits": 32,
            "mir_profile_version": 1,
            "bodies": []
        }"#,
    )
    .unwrap();
    let out1 = Command::new(bin_path())
        .args(["probe", empty_32.to_str().unwrap(), "--all"])
        .output()
        .unwrap();
    assert_eq!(out1.status.code(), Some(3), "{}", String::from_utf8_lossy(&out1.stderr));

    // 2. All-skipped `unsafe` body with `mir_profile_version: 99` must exit 3.
    let skipped_v99 = dir.0.join("skipped_v99.json");
    fs::write(
        &skipped_v99,
        r#"{
            "scope": { "kind": "selected_unit", "roots": ["demo::u"] },
            "pointer_width_bits": 64,
            "mir_profile_version": 99,
            "bodies": [{
                "arg_count": 0,
                "is_unsafe": true,
                "identity": "rust-path-v1::demo::u",
                "local_tys": [{ "kind": "unit" }],
                "blocks": [{ "statements": [], "terminator": { "kind": "ret" } }]
            }]
        }"#,
    )
    .unwrap();
    let out2 = Command::new(bin_path())
        .args(["probe", skipped_v99.to_str().unwrap(), "--all"])
        .output()
        .unwrap();
    assert_eq!(out2.status.code(), Some(3), "{}", String::from_utf8_lossy(&out2.stderr));

    // 3. `--cases 0` with `blocks: []` body must exit 3.
    let bad_blocks = dir.0.join("bad_blocks.json");
    fs::write(
        &bad_blocks,
        r#"{
            "scope": { "kind": "selected_unit", "roots": ["demo::empty_bb"] },
            "pointer_width_bits": 64,
            "mir_profile_version": 1,
            "bodies": [{
                "arg_count": 0,
                "is_unsafe": false,
                "identity": "rust-path-v1::demo::empty_bb",
                "local_tys": [{ "kind": "unit" }],
                "blocks": []
            }]
        }"#,
    )
    .unwrap();
    let out3 = Command::new(bin_path())
        .args(["probe", bad_blocks.to_str().unwrap(), "--all", "--cases", "0"])
        .output()
        .unwrap();
    assert_eq!(out3.status.code(), Some(3), "{}", String::from_utf8_lossy(&out3.stderr));

    // 4. Uninhabited `!` param with `mir_profile_version: 2` under
    //    `--strict-v1` must exit 3, while auto-dispatch cleanly reports
    //    uninhabited (`exit 0`).
    let never_v2 = dir.0.join("never_v2.json");
    fs::write(
        &never_v2,
        r#"{
            "scope": { "kind": "selected_unit", "roots": ["demo::never"] },
            "pointer_width_bits": 64,
            "mir_profile_version": 2,
            "bodies": [{
                "arg_count": 1,
                "is_unsafe": false,
                "identity": "rust-path-v1::demo::never",
                "local_tys": [{ "kind": "unit" }, { "kind": "never" }],
                "blocks": [{ "statements": [], "terminator": { "kind": "ret" } }]
            }]
        }"#,
    )
    .unwrap();
    let out4 = Command::new(bin_path())
        .args(["probe", never_v2.to_str().unwrap(), "--all", "--strict-v1"])
        .output()
        .unwrap();
    assert_eq!(out4.status.code(), Some(3), "{}", String::from_utf8_lossy(&out4.stderr));
    let out4_auto = Command::new(bin_path())
        .args(["probe", never_v2.to_str().unwrap(), "--all"])
        .output()
        .unwrap();
    assert!(out4_auto.status.success(), "{}", String::from_utf8_lossy(&out4_auto.stderr));
    assert!(String::from_utf8_lossy(&out4_auto.stdout).contains("uninhabited=true"));
}

#[test]
fn cli_probe_exits_3_on_empty_64_invalid_skipped_unsafe_and_empty_identity() {
    struct TempDir(std::path::PathBuf);
    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let dir = TempDir(
        std::env::temp_dir().join(format!("anneal-mir-eval-probe-edge-{}", std::process::id())),
    );
    fs::create_dir_all(&dir.0).unwrap();

    // 1. Empty `bodies` with 64-bit v1 must exit 3 (not 0).
    let empty_64 = dir.0.join("empty_64.json");
    fs::write(
        &empty_64,
        r#"{
            "scope": { "kind": "crate" },
            "pointer_width_bits": 64,
            "mir_profile_version": 1,
            "bodies": []
        }"#,
    )
    .unwrap();
    for args in [
        vec!["probe", empty_64.to_str().unwrap(), "--all"],
        vec!["probe", empty_64.to_str().unwrap(), "--all", "--json"],
    ] {
        let out = Command::new(bin_path()).args(&args).output().unwrap();
        assert_eq!(out.status.code(), Some(3), "{}", String::from_utf8_lossy(&out.stderr));
    }

    // 2. Statically invalid `is_unsafe: true` bodies (`blocks: []` or
    // `Ty::Unsupported`) must fail with exit 3 even without `--include-unsafe`.
    let invalid_unsafe_cases = [
        (
            "unsafe_empty_blocks.json",
            r#"{
                "scope": { "kind": "selected_unit", "roots": ["demo::u"] },
                "pointer_width_bits": 64,
                "mir_profile_version": 1,
                "bodies": [{
                    "arg_count": 0,
                    "is_unsafe": true,
                    "identity": "rust-path-v1::demo::u",
                    "local_tys": [{ "kind": "unit" }],
                    "blocks": []
                }]
            }"#,
        ),
        (
            "unsafe_unsup_ty.json",
            r#"{
                "scope": { "kind": "selected_unit", "roots": ["demo::u"] },
                "pointer_width_bits": 64,
                "mir_profile_version": 1,
                "bodies": [{
                    "arg_count": 0,
                    "is_unsafe": true,
                    "identity": "rust-path-v1::demo::u",
                    "local_tys": [{ "kind": "unsupported" }],
                    "blocks": [{ "statements": [], "terminator": { "kind": "ret" } }]
                }]
            }"#,
        ),
    ];
    for (name, body_json) in invalid_unsafe_cases {
        let p = dir.0.join(name);
        fs::write(&p, body_json).unwrap();
        let out = Command::new(bin_path())
            .args(["probe", p.to_str().unwrap(), "--all"])
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(3), "{name}: {}", String::from_utf8_lossy(&out.stderr));
        let json_out = Command::new(bin_path())
            .args(["probe", p.to_str().unwrap(), "--all", "--json"])
            .output()
            .unwrap();
        assert_eq!(json_out.status.code(), Some(3));
        let json_str = String::from_utf8_lossy(&json_out.stdout);
        assert!(json_str.contains("\"skipped_unsafe\": false"), "{name}: {json_str}");
        assert!(json_str.contains("\"unsupported_count\": 1"), "{name}: {json_str}");
    }

    // 3. Empty `body.identity` (safe or unsafe) must fail with exit 3 on
    // `probe` and `eval`.
    for (name, is_unsafe) in [("empty_id_safe.json", false), ("empty_id_unsafe.json", true)] {
        let p = dir.0.join(name);
        fs::write(
            &p,
            format!(
                r#"{{
                    "scope": {{ "kind": "selected_unit", "roots": [""] }},
                    "pointer_width_bits": 64,
                    "mir_profile_version": 1,
                    "bodies": [{{
                        "arg_count": 0,
                        "is_unsafe": {is_unsafe},
                        "identity": "",
                        "local_tys": [{{ "kind": "unit" }}],
                        "blocks": [{{ "statements": [], "terminator": {{ "kind": "ret" }} }}]
                    }}]
                }}"#
            ),
        )
        .unwrap();
        let p_str = p.to_str().unwrap();
        let probe_out = Command::new(bin_path()).args(["probe", p_str, "--all"]).output().unwrap();
        assert_eq!(probe_out.status.code(), Some(3), "{name}");
        let eval_out =
            Command::new(bin_path()).args(["eval", p_str, "--body", "0"]).output().unwrap();
        assert_eq!(eval_out.status.code(), Some(3), "{name}");
    }

    // 4. Positive control: statically valid `is_unsafe: true` body still skips
    // with exit 0 unless `--include-unsafe` is passed.
    let valid_unsafe = dir.0.join("valid_unsafe.json");
    fs::write(
        &valid_unsafe,
        r#"{
            "scope": { "kind": "selected_unit", "roots": ["demo::u"] },
            "pointer_width_bits": 64,
            "mir_profile_version": 1,
            "bodies": [{
                "arg_count": 0,
                "is_unsafe": true,
                "identity": "rust-path-v1::demo::u",
                "local_tys": [{ "kind": "unit" }],
                "blocks": [{ "statements": [], "terminator": { "kind": "ret" } }]
            }]
        }"#,
    )
    .unwrap();
    let ok_out = Command::new(bin_path())
        .args(["probe", valid_unsafe.to_str().unwrap(), "--all", "--json"])
        .output()
        .unwrap();
    assert!(ok_out.status.success(), "{}", String::from_utf8_lossy(&ok_out.stderr));
    let ok_str = String::from_utf8_lossy(&ok_out.stdout);
    assert!(ok_str.contains("\"skipped_unsafe\": true"), "{ok_str}");

    // 5. Duplicate `body.identity` across `bodies` must fail with exit 3 on
    // `probe --all` and `eval`.
    let dup_ids = dir.0.join("dup_identities.json");
    fs::write(
        &dup_ids,
        r#"{
            "scope": { "kind": "selected_unit", "roots": ["demo::f"] },
            "pointer_width_bits": 64,
            "mir_profile_version": 1,
            "bodies": [
                {
                    "arg_count": 0,
                    "is_unsafe": false,
                    "identity": "rust-path-v1::demo::f",
                    "local_tys": [{ "kind": "unit" }],
                    "blocks": [{ "statements": [], "terminator": { "kind": "ret" } }]
                },
                {
                    "arg_count": 0,
                    "is_unsafe": false,
                    "identity": "rust-path-v1::demo::f",
                    "local_tys": [{ "kind": "unit" }],
                    "blocks": [{ "statements": [], "terminator": { "kind": "ret" } }]
                }
            ]
        }"#,
    )
    .unwrap();
    let dup_str = dup_ids.to_str().unwrap();
    assert_eq!(
        Command::new(bin_path()).args(["probe", dup_str, "--all"]).output().unwrap().status.code(),
        Some(3)
    );
    assert_eq!(
        Command::new(bin_path())
            .args(["eval", dup_str, "--body", "rust-path-v1::demo::f"])
            .output()
            .unwrap()
            .status
            .code(),
        Some(3)
    );
}

#[test]
fn cli_evaluates_and_probes_real_zerocopy_profile_v2_manifests() {
    struct TempDir(std::path::PathBuf);
    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    let fixture_06 = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/zerocopy_06_byte_slice_into_byte_slice_capture.json"
    );
    let list_06 = Command::new(bin_path()).args(["list", fixture_06]).output().unwrap();
    assert!(list_06.status.success(), "{}", String::from_utf8_lossy(&list_06.stderr));
    let list_06_out = String::from_utf8_lossy(&list_06.stdout);
    assert!(list_06_out.contains("mir_profile_version=2"), "{list_06_out}");
    assert!(list_06_out.contains("into_byte_slice"), "{list_06_out}");

    let probe_06 = Command::new(bin_path())
        .args(["probe", fixture_06, "--all", "--cases", "16"])
        .output()
        .unwrap();
    assert!(probe_06.status.success(), "{}", String::from_utf8_lossy(&probe_06.stderr));
    let probe_06_out = String::from_utf8_lossy(&probe_06.stdout);
    assert!(
        probe_06_out.contains("ub=0 (replayable=0, model_only_unreplayed=0)"),
        "{probe_06_out}"
    );
    assert!(probe_06_out.contains("unsupported=0"), "{probe_06_out}");

    let fixture_08 = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/zerocopy_08_byte_slice_split_at_unchecked_capture.json"
    );
    let list_08 = Command::new(bin_path()).args(["list", fixture_08]).output().unwrap();
    assert!(list_08.status.success(), "{}", String::from_utf8_lossy(&list_08.stderr));
    let list_08_out = String::from_utf8_lossy(&list_08.stdout);
    assert!(list_08_out.contains("split_at_unchecked"), "{list_08_out}");
    assert!(list_08_out.contains("overflow_checks="), "{list_08_out}");

    // Valid split via `--arg "[10,20,30,40]" --arg 2` -> exit 0.
    let eval_ok = Command::new(bin_path())
        .args(["eval", fixture_08, "--arg", "[10,20,30,40]", "--arg", "2"])
        .output()
        .unwrap();
    assert!(eval_ok.status.success(), "{}", String::from_utf8_lossy(&eval_ok.stderr));
    let eval_ok_out = String::from_utf8_lossy(&eval_ok.stdout);
    assert!(eval_ok_out.contains("RETURNED"), "{eval_ok_out}");

    // Out-of-bounds split via `--arg "[10,20]" --arg 5` -> exit 2
    // (replayable UB).
    let eval_oob = Command::new(bin_path())
        .args(["eval", fixture_08, "--arg", "[10,20]", "--arg", "5"])
        .output()
        .unwrap();
    assert_eq!(eval_oob.status.code(), Some(2), "{}", String::from_utf8_lossy(&eval_oob.stdout));
    let eval_oob_out = String::from_utf8_lossy(&eval_oob.stdout);
    assert!(eval_oob_out.contains("replayable_miri_ub"), "{eval_oob_out}");

    // Explicit `--query <query.json>` with CallerMemory -> exit 0.
    let dir =
        TempDir(std::env::temp_dir().join(format!("anneal-mir-eval-query-{}", std::process::id())));
    fs::create_dir_all(&dir.0).unwrap();
    let query_path = dir.0.join("query.json");
    fs::write(
        &query_path,
        r#"{
            "args": [
                {
                    "kind": "slice_ptr",
                    "value": {
                        "ptr": { "alloc_id": 2, "offset_bytes": 0, "width": "isize" },
                        "len": 3
                    }
                },
                {
                    "kind": "scalar",
                    "value": { "width": "isize", "signed": false, "bits": "1" }
                }
            ],
            "caller_mem": {
                "allocations": [{
                    "alloc_id": 2,
                    "align_log2": 0,
                    "mutability": "shared",
                    "bytes": [
                        { "kind": "init", "byte": 1, "prov": null },
                        { "kind": "init", "byte": 2, "prov": null },
                        { "kind": "init", "byte": 3, "prov": null }
                    ],
                    "live": true
                }]
            }
        }"#,
    )
    .unwrap();
    let eval_query = Command::new(bin_path())
        .args(["eval", fixture_08, "--query", query_path.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(eval_query.status.success(), "{}", String::from_utf8_lossy(&eval_query.stderr));
    assert!(String::from_utf8_lossy(&eval_query.stdout).contains("RETURNED"));

    // `probe --all` skips unsafe by default (`exit 0`); `--include-unsafe`
    // surfaces a `replayable_miri_ub` counterexample (`exit 2`).
    let probe_skip =
        Command::new(bin_path()).args(["probe", fixture_08, "--all"]).output().unwrap();
    assert!(probe_skip.status.success());
    assert!(String::from_utf8_lossy(&probe_skip.stdout).contains("skipped_unsafe=true"));

    let probe_ub = Command::new(bin_path())
        .args(["probe", fixture_08, "--all", "--include-unsafe", "--cases", "32"])
        .output()
        .unwrap();
    assert_eq!(probe_ub.status.code(), Some(2));
    let probe_ub_out = String::from_utf8_lossy(&probe_ub.stdout);
    assert!(probe_ub_out.contains("class=replayable_miri_ub"), "{probe_ub_out}");
    assert!(probe_ub_out.contains("model_only_unreplayed=0"), "{probe_ub_out}");

    let probe_ub_json = Command::new(bin_path())
        .args(["probe", fixture_08, "--all", "--include-unsafe", "--cases", "32", "--json"])
        .output()
        .unwrap();
    assert_eq!(probe_ub_json.status.code(), Some(2));
    let probe_ub_json_out = String::from_utf8_lossy(&probe_ub_json.stdout);
    assert!(
        probe_ub_json_out.contains("\"witness_class\": \"replayable_miri_ub\""),
        "{probe_ub_json_out}"
    );
}
