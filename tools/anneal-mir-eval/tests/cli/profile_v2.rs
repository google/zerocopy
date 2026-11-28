// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Profile v2 auto-dispatch and raw-pointer probes, `assert` UB versus
//! unsupported features, strict Profile v1 rejection, and real `zerocopy`
//! Profile v2 captures.

use super::*;

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
    assert!(probe_ub_json_out.contains("\"fault_location\""), "{probe_ub_json_out}");
    assert!(probe_ub_out.contains("ub_class=") && probe_ub_out.contains(" @ bb"), "{probe_ub_out}");
    assert!(eval_oob_out.contains(" @ bb"), "{eval_oob_out}");
}
