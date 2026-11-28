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

use anneal_mir_eval::{
    Counterexample, EvalConfig, Outcome, Program, TerminalOut, eval_body_with_config,
    trace_location,
};

#[path = "cli/manifests.rs"]
mod manifests;
#[path = "cli/profile_v2.rs"]
mod profile_v2;
#[path = "cli/unsupported_probes.rs"]
mod unsupported_probes;

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
fn cli_eval_and_probe_emit_structured_fault_locations() {
    let jp = std::env::temp_dir().join(format!("anneal-mir-triage-{}.json", std::process::id()));
    fs::write(&jp, r#"{"scope":{"kind":"selected_unit","roots":["d::a","d::b","d::c"]},"pointer_width_bits":64,"mir_profile_version":2,"bodies":[{"arg_count":1,"is_unsafe":false,"identity":"d::a","local_tys":[{"kind":"int","width":"i32","signed":false},{"kind":"int","width":"i32","signed":false}],"blocks":[{"statements":[{"kind":"assign","local":0,"projection":[],"value":{"kind":"binary","op":"div","left":{"kind":"copy","local":1,"projection":[]},"right":{"kind":"copy","local":1,"projection":[]}}}],"terminator":{"kind":"ret"}}]},{"arg_count":0,"is_unsafe":false,"identity":"d::b","local_tys":[{"kind":"unit"}],"blocks":[{"statements":[],"terminator":{"kind":"goto","block":1}},{"statements":[],"terminator":{"kind":"unreachable"}}]},{"arg_count":1,"is_unsafe":false,"identity":"d::c","local_tys":[{"kind":"unit"},{"kind":"int","width":"i32","signed":false}],"blocks":[{"statements":[],"terminator":{"kind":"unsupported"}}]}]}"#).unwrap();
    let p = jp.to_str().unwrap();
    let run = |a: &[&str]| Command::new(bin_path()).args(a).output().unwrap();
    let chk = |a: &[&str], code: i32, sub: &str| {
        let o = run(a);
        assert!(o.status.code() == Some(code) && String::from_utf8_lossy(&o.stdout).contains(sub));
    };
    chk(&["eval", p, "--body", "d::a", "--arg", "0"], 2, "@ bb0:stmt0");
    chk(&["eval", p, "--body", "d::a", "--arg", "1", "--fuel", "0"], 3, "OUT OF FUEL @ bb0:stmt0");
    chk(&["eval", p, "--body", "d::b"], 2, "@ bb1:term");
    let po = String::from_utf8(run(&["probe", p, "--all", "--cases", "4"]).stdout).unwrap();
    assert!(po.contains("ub_class=div_by_zero") && po.contains("@ bb0:stmt0"), "{po}");
    assert!(po.contains("ub_class=unreachable_executed") && po.contains("@ bb1:term"), "{po}");
    assert!(po.contains("UNSUPPORTED args=(") && po.contains("@ bb0:term"), "{po}");
    let out = run(&["probe", p, "--body", "d::a", "--cases", "1", "--fuel", "0", "--json"]);
    let j: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    let _ = fs::remove_file(&jp);
    let fl = &j[0]["first_out_of_fuel"]["fault_location"];
    assert!(fl["kind"] == "out_of_fuel" && fl["is_terminator"] == false, "{fl}");

    let v1: Program = serde_json::from_str(r#"{"scope":{"kind":"crate"},"pointer_width_bits":64,"mir_profile_version":1,"bodies":[{"arg_count":0,"is_unsafe":false,"identity":"caller","local_tys":[{"kind":"int","width":"i8","signed":false}],"blocks":[{"statements":[],"terminator":{"kind":"sysroot_call","op":{"kind":"unchecked_add","ty":{"width":"i8","signed":false}},"args":[{"kind":"constant","ty":{"kind":"int","width":"i8","signed":false},"lit":{"kind":"scalar","bits":"255"}},{"kind":"constant","ty":{"kind":"int","width":"i8","signed":false},"lit":{"kind":"scalar","bits":"1"}}],"dst":0,"target":0,"unwind":"continue"}}]},{"arg_count":0,"is_unsafe":false,"identity":"callee","local_tys":[{"kind":"unit"}],"blocks":[{"statements":[],"terminator":{"kind":"unreachable"}}]},{"arg_count":0,"is_unsafe":false,"identity":"wrap","local_tys":[{"kind":"unit"}],"blocks":[{"statements":[],"terminator":{"kind":"call","callee":1,"args":[],"dst":0,"target":0,"unwind":"continue"}}]}]}"#).unwrap();
    let cfg = EvalConfig { record_events: false, ..EvalConfig::profile_v1() };
    let ev = |id, c: &EvalConfig| eval_body_with_config(&v1, id, &[], 8, c);
    let loc = |id| trace_location(&v1, &ev(id, &cfg)).unwrap();
    let s = |id, e| loc(id).format_site(Some(e));
    assert_eq!((s(0, 0), s(0, 2)), ("core::num::sysroot bb0:stmt0".into(), s(0, 0)));
    assert_eq!((s(2, 2), s(99, 99)), ("body[1] (callee) bb0:term".into(), "entry".into()));
    let mut tr = ev(1, &EvalConfig::profile_v1());
    let cm = Default::default;
    assert!(Counterexample::from_trace(vec![], cm(), tr.clone()).fault_location.is_none());
    let ce = Counterexample::from_trace_in_program(&v1, vec![], cm(), tr.clone());
    assert!(ce.fault_location.is_some_and(|l| l.is_terminator));
    tr.final_state = None;
    let unwound = Outcome::Returned(TerminalOut::Unwound { caller_mem: cm() });
    for o in [unwound, Outcome::Aborted { caller_mem: cm() }] {
        tr.outcome = o;
        assert_eq!(trace_location(&v1, &tr).unwrap().format_site(Some(0)), s(2, 2));
    }
}
