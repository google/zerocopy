// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Capture confinement, response-file rejection, and binary Cargo shortcuts.

use std::{ffi::OsStr, fs};

use serde_json::json;

use crate::helpers::{
    SCALAR_PROOF, SCALAR_SOURCE, SCALAR_SPEC, corpus_path, expect_failed, expect_verified,
    lean_source, new_workspace, run_verify_inv, run_verify_strs, stage_work_files,
    verify_invocation, with_host_cargo_env, write_json_file, write_scalar_baseline,
};

#[test]
fn rejects_external_file_inclusion_via_path_attribute() {
    let staged = stage_work_files(
        "anneal-path-escape-",
        &[
            ("outside/secret.rs", b"pub fn helper(x: usize) -> usize { x }\n"),
            ("lean/Spec.lean", SCALAR_SPEC.as_bytes()),
            ("lean/Proof.lean", SCALAR_PROOF.as_bytes()),
        ],
    );
    let work = staged.work_dir();
    let ext_file = work.join("outside/secret.rs");
    fs::create_dir_all(work.join("rust")).unwrap();
    fs::write(
        work.join("rust/lib.rs"),
        format!(
            "#[path = {:?}]\npub mod outside;\n\
             pub fn id(x: usize) -> usize {{ outside::helper(x) }}\n",
            ext_file.display().to_string()
        ),
    )
    .unwrap();

    let req = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": work.join("rust"),
            "crate_root": "lib.rs",
            "crate_name": "escape_test",
            "edition": "2024",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": { "kind": "crate" },
        "proof": {
            "source_root": work.join("lean"),
            "sources": [
                { "module": "Spec", "path": "Spec.lean", "role": "specification" },
                { "module": "Proof", "path": "Proof.lean", "role": "proof" }
            ]
        }
    });
    let req_path = write_json_file(&work.join("req.json"), &req);
    let res = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    expect_failed(&res, 1, "unsupported", Some("capture"), "undeclared compiler read");
}

#[test]
fn declared_cfg_cannot_expand_compiler_response_files() {
    let staged = new_workspace("anneal-rsp-cfg-").stage().unwrap();
    let work = staged.work_dir();
    let base_req = write_scalar_baseline(work);
    fs::write(
        work.join("rust/lib.rs"),
        format!(
            "{SCALAR_SOURCE}\n#[cfg(not(injected))]\ncompile_error!(\"missing declared cfg\");\n"
        ),
    )
    .unwrap();

    // Existing response file would make compilation succeed if rustc treated
    // `--cfg=@file` as response-file expansion rather than a literal cfg value.
    let response = work.join("compiler-flags.rsp");
    fs::write(&response, b"dummy\n--cfg\ninjected\n").unwrap();
    for (name, path) in
        [("cfg-existing-response", response), ("cfg-missing-response", work.join("missing.rsp"))]
    {
        let mut req = base_req.clone();
        req["compilation"]["cfg"] = json!([format!("@{}", path.display())]);
        let req_path = write_json_file(&work.join(format!("{name}.json")), &req);
        let art = work.join(name);
        let res = run_verify_strs(
            &staged,
            &["--request", req_path.to_str().unwrap(), "--artifacts", art.to_str().unwrap()],
        );
        expect_failed(&res, 2, "compiler_failed", Some("capture"), "rustc rejected");
        let stderr = String::from_utf8_lossy(&res.process.stderr);
        assert!(stderr.contains("invalid `--cfg` argument"), "missing stderr diag: {stderr}");
        let diagnostic = fs::read_to_string(art.join("capture.stderr")).unwrap();
        assert!(diagnostic.contains("invalid `--cfg` argument"));
        assert!(!diagnostic.contains("failed to load argument file"));
        assert!(!art.join("capture/capture.json").exists());
    }

    // Normal cfg flags and quoted `@` strings preserve round-trip parity.
    let mut ok_req = base_req;
    let cfg = json!([r#"feature="@literal""#, "injected"]);
    ok_req["compilation"]["cfg"] = cfg.clone();
    let ok_path = write_json_file(&work.join("cfg-literal-values.json"), &ok_req);
    let ok_res = run_verify_strs(&staged, &["--request", ok_path.to_str().unwrap()]);
    let ok = expect_verified(&ok_res, "crate_verified", true);
    assert_eq!(ok.configuration["cfg"], cfg);
}

#[test]
fn verify_runs_real_capture_before_spec_or_proof_audit_error() {
    let staged = new_workspace("anneal-capture-order-").stage().unwrap();
    let work = staged.work_dir();

    let good_rs = fs::read(corpus_path("scalar_specs/annotated_id/lib.rs")).unwrap();
    let bad_spec = fs::read(corpus_path("scalar_specs/spec_unknown_ident_rejected/Spec.lean")).unwrap();
    let bad_mir_rs = b"pub fn unsupported_float(s: f64) -> usize { let _ = s; 0 }\n";
    let proof_lean = fs::read(corpus_path("scalar_specs/annotated_id/Proof.lean")).unwrap();

    // 1. Valid crate + bad `Spec.lean` runs capture first.
    let rust_good = work.join("rust-good");
    let lean_bad = work.join("lean-bad");
    fs::create_dir_all(&rust_good).unwrap();
    fs::create_dir_all(&lean_bad).unwrap();
    fs::write(rust_good.join("lib.rs"), &good_rs).unwrap();
    fs::write(lean_bad.join("Spec.lean"), &bad_spec).unwrap();
    fs::write(lean_bad.join("Proof.lean"), &proof_lean).unwrap();
    let r1_json = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_good,
            "crate_root": "lib.rs",
            "crate_name": "cap_first",
            "edition": "2024",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": { "kind": "crate" },
        "proof": {
            "source_root": lean_bad,
            "sources": [
                { "module": "Spec", "path": "Spec.lean", "role": "specification" },
                { "module": "Proof", "path": "Proof.lean", "role": "proof" }
            ]
        }
    });
    let r1_path = write_json_file(&work.join("r1.json"), &r1_json);
    let art1 = work.join("art-bad-spec");
    let run1 = run_verify_strs(
        &staged,
        &["--request", r1_path.to_str().unwrap(), "--artifacts", art1.to_str().unwrap()],
    );
    expect_failed(&run1, 1, "proof_failed", Some("audit"), "Unknown identifier");
    let captured_lean = fs::read_to_string(art1.join("capture/Captured.lean"))
        .expect("capture must emit Captured.lean before Lean audit");
    assert!(
        captured_lean.contains("def program : Trusted.MirAst.Program")
            && captured_lean.contains("Trusted.MirAst.TerminatorKind.return_"),
        "expected real MIR body in Captured.lean:\n{captured_lean}"
    );

    // 2. Unsupported MIR + bad `Spec.lean` fails at `capture`, never `audit`.
    let rust_bad = work.join("rust-bad");
    fs::create_dir_all(&rust_bad).unwrap();
    fs::write(rust_bad.join("lib.rs"), bad_mir_rs).unwrap();
    let mut r2_json = r1_json;
    r2_json["compilation"]["source_root"] = json!(rust_bad);
    let r2_path = write_json_file(&work.join("r2.json"), &r2_json);
    let art2 = work.join("art-bad-mir-and-spec");
    let run2 = run_verify_strs(
        &staged,
        &["--request", r2_path.to_str().unwrap(), "--artifacts", art2.to_str().unwrap()],
    );
    expect_failed(&run2, 1, "unsupported", Some("capture"), "unsupported type: f64");
    assert!(!art2.join("capture/Captured.lean").exists());
}

#[test]
fn cargo_shortcut_verifies_std_and_nostd_nomain_binaries() {
    let staged = new_workspace("anneal-cargo-bins-").stage().unwrap();
    let work = staged.work_dir();

    // 1. Standard library binary (`fn main() {}`) verified whole-crate.
    let unit_lean = work.join("unit-lean");
    fs::create_dir_all(&unit_lean).unwrap();
    fs::write(
        unit_lean.join("Spec.lean"),
        lean_source(
            "import Trusted.MirSemantics",
            "open Trusted.MirSemantics\nnamespace Spec\n\
             def specs : Specs := { safety := fun _ _ => True, property := fun _ => True }\n\
             end Spec",
        ),
    )
    .unwrap();
    fs::write(
        unit_lean.join("Proof.lean"),
        lean_source(
            "import Expected\nimport Anneal.MirWp.Execution",
            "open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp\nnamespace Proof\n\
             theorem verify : Expected.claim := by\n  \
               refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, trivial⟩\n  \
               intro id body found\n  \
               cases id with\n  \
               | zero =>\n    \
                 injection found with hEq\n    \
                 subst hEq\n    \
                 refine bodyVerified_of_safe rfl rfl (fun args valid _ => ?_)\n    \
                 cases args with\n    \
                 | nil =>\n      \
                   have hRun : Runs Captured.body_0 4 [] .unit := rfl\n      \
                   exact (run_initial_success hRun).1\n    \
                 | cons _ _ => cases valid\n  \
               | succ _ => cases found\n\
             end Proof",
        ),
    )
    .unwrap();

    let std_pkg = work.join("std-bin");
    fs::create_dir_all(std_pkg.join("src")).unwrap();
    fs::write(
        std_pkg.join("Cargo.toml"),
        "[package]\nname = \"std-bin\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(std_pkg.join("src/main.rs"), "fn main() {}\n").unwrap();
    let std_manifest = std_pkg.join("Cargo.toml");
    let std_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            std_manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            unit_lean.as_os_str(),
        ]),
    );
    let std_res = run_verify_inv(&staged, &std_inv);
    let std_ok = expect_verified(&std_res, "crate_verified", true);
    assert_eq!(std_ok.configuration["crate_type"], "bin");
    assert_eq!(std_ok.configuration["panic"], "unwind");

    // 2. `#![no_std] #![no_main]` binary with `_start -> !` and
    //    `zx_process_exit(1) -> !`.
    let nostd_src = br#"#![no_std]
#![no_main]

use core::panic::PanicInfo;

unsafe extern "C" {
    fn zx_process_exit(code: i32) -> !;
}

#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! {
    unsafe { zx_process_exit(2) }
}

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    unsafe { zx_process_exit(0) }
}

/// # Safety
/// `ok` must be `true`; otherwise `zx_process_exit(1)` diverges.
pub unsafe fn guarded_exit(ok: bool) -> bool {
    if ok {
        true
    } else {
        unsafe { zx_process_exit(1) }
    }
}
"#;
    let nostd_pkg = work.join("nostd-bin");
    fs::create_dir_all(nostd_pkg.join("src")).unwrap();
    fs::write(
        nostd_pkg.join("Cargo.toml"),
        "[package]\nname = \"nostd-bin\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(nostd_pkg.join("src/main.rs"), nostd_src).unwrap();

    let nostd_lean = work.join("nostd-lean");
    fs::create_dir_all(&nostd_lean).unwrap();
    fs::write(
        nostd_lean.join("Spec.lean"),
        lean_source(
            "import Trusted.MirSemantics",
            "open Trusted.MirAst Trusted.MirSemantics\nnamespace Spec\n\
             def specs : Specs := { safety := fun _ args => args = [.bool true], property := fun _ => True }\n\
             end Spec",
        ),
    )
    .unwrap();
    fs::write(
        nostd_lean.join("Proof.lean"),
        lean_source(
            "import Expected\nimport Anneal.MirWp.Execution",
            "open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp\nnamespace Proof\n\
             theorem verify : Expected.claim := by\n  \
               refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, trivial⟩\n  \
               intro id body found\n  \
               cases id with\n  \
               | zero =>\n    \
                 injection found with hEq\n    \
                 subst hEq\n    \
                 refine bodyVerified_of_safe rfl rfl (fun args _ req => ?_)\n    \
                 have hArg : args = [.bool true] := req rfl\n    \
                 subst hArg\n    \
                 have hRun : Runs Captured.body_0 8 [.bool true] (.bool true) := rfl\n    \
                 exact (run_initial_success hRun).1\n  \
               | succ _ => cases found\n\
             end Proof",
        ),
    )
    .unwrap();

    let nostd_manifest = nostd_pkg.join("Cargo.toml");

    // 2a. Passing run (`--panic abort --select guarded_exit`).
    let ok_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            nostd_manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            nostd_lean.as_os_str(),
            OsStr::new("--panic"),
            OsStr::new("abort"),
            OsStr::new("--select"),
            OsStr::new("guarded_exit"),
        ]),
    );
    let ok_res = run_verify_inv(&staged, &ok_inv);
    let ok_rec = expect_verified(&ok_res, "selected_unit_verified", true);
    assert_eq!(ok_rec.configuration["crate_name"], "nostd_bin");
    assert_eq!(ok_rec.configuration["crate_type"], "bin");
    assert_eq!(ok_rec.configuration["panic"], "abort");
    assert!(ok_rec.taint_reasons.is_empty());
    assert!(
        !ok_rec.assumptions.iter().any(|a| a.contains("as .aborted")),
        "local #[panic_handler] receipt must not claim .aborted modeling: {:?}",
        ok_rec.assumptions
    );

    // 2b. Default `--panic unwind` fails compilation on `#![no_std]` binary.
    let no_panic_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            nostd_manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            nostd_lean.as_os_str(),
            OsStr::new("--select"),
            OsStr::new("guarded_exit"),
        ]),
    );
    let no_panic_res = run_verify_inv(&staged, &no_panic_inv);
    expect_failed(&no_panic_res, 2, "compiler_failed", Some("capture"), "rustc rejected");
    let no_panic_stderr = String::from_utf8_lossy(&no_panic_res.process.stderr);
    assert!(
        no_panic_stderr.contains("unwinding panics are not supported without std"),
        "expected missing std unwind diagnostic on stderr:\n{no_panic_stderr}"
    );

    // 2c. Whole-crate scope without `--select` fails closed at capture.
    let whole_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            nostd_manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            nostd_lean.as_os_str(),
            OsStr::new("--panic"),
            OsStr::new("abort"),
        ]),
    );
    let whole_res = run_verify_inv(&staged, &whole_inv);
    expect_failed(&whole_res, 1, "unsupported", Some("capture"), "unsupported");

    // 2d. Weakening Spec to permit `guarded_exit(false)` reaches
    //     `zx_process_exit(1)` (`.unsupported` -> fault) and fails audit.
    fs::write(
        nostd_lean.join("Spec.lean"),
        lean_source(
            "import Trusted.MirSemantics",
            "open Trusted.MirAst Trusted.MirSemantics\nnamespace Spec\n\
             def specs : Specs := { safety := fun _ _ => True, property := fun _ => True }\n\
             end Spec",
        ),
    )
    .unwrap();
    fs::write(
        nostd_lean.join("Proof.lean"),
        lean_source(
            "import Expected\nimport Anneal.MirWp.Execution",
            "open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp\nnamespace Proof\n\
             theorem verify : Expected.claim := by\n  \
               refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, trivial⟩\n  \
               intro id body found\n  \
               cases id with\n  \
               | zero =>\n    \
                 injection found with hEq\n    \
                 subst hEq\n    \
                 refine bodyVerified_of_safe rfl rfl (fun args _ _ => ?_)\n    \
                 have hRun : Runs Captured.body_0 8 [.bool false] (.bool false) := rfl\n    \
                 exact (run_initial_success hRun).1\n  \
               | succ _ => cases found\n\
             end Proof",
        ),
    )
    .unwrap();
    let weak_res = run_verify_inv(&staged, &ok_inv);
    expect_failed(&weak_res, 1, "proof_failed", Some("audit"), "Proof.lean");
}
