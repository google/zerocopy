// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `probe` exiting `3` on unsupported programs and on empty, invalid,
//! skipped, unsafe, or uninhabited cases.

use super::*;

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
