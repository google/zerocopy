// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Large-capture Lean elaboration balancing and anti-vacuity lint regressions.

use std::{fmt::Write as _, fs, process::Command};

use cargo_anneal::{Checker, TargetAuditRequest, TargetBindings, TargetModule, TargetRole};
use serde_json::{Value, json};

use crate::helpers::{
    anneal_root, corpus_path, expect_verified, lean_source, new_workspace, run_verify_strs,
    sha256_hex, workspace_tools, write_json_file, write_scalar_baseline,
};

#[test]
fn balances_large_captured_lists_through_lean_and_target_audit() {
    let tools = workspace_tools();
    let capture_bin = tools.capture.as_deref().expect("capture binary");
    let staged = new_workspace("anneal-large-lists-").stage().unwrap();
    let work = staged.work_dir();
    let repo_root = anneal_root();
    let bundle_root = work.join("bundle");

    for rel in [
        "trusted/audit/TrustedBoundary.lean",
        "trusted/audit/library-lock.json",
        "trusted/lean/foundation-lock.json",
        "trusted/lean/lean-toolchain",
        "trusted/lean/Trusted.lean",
    ] {
        let dest = bundle_root.join(rel);
        fs::create_dir_all(dest.parent().unwrap()).unwrap();
        fs::copy(repo_root.join(rel), dest).unwrap();
    }

    let mut base_modules = Vec::new();
    for (module, rel) in [
        ("Trusted.MirAst.Types", "trusted/lean/Trusted/MirAst/Types.lean"),
        ("Trusted.MirAst.Places", "trusted/lean/Trusted/MirAst/Places.lean"),
        ("Trusted.MirAst.Rvalues", "trusted/lean/Trusted/MirAst/Rvalues.lean"),
        ("Trusted.MirAst.Statements", "trusted/lean/Trusted/MirAst/Statements.lean"),
        ("Trusted.MirAst.Terminators", "trusted/lean/Trusted/MirAst/Terminators.lean"),
        ("Trusted.MirAst.Body", "trusted/lean/Trusted/MirAst/Body.lean"),
        ("Trusted.MirAst", "trusted/lean/Trusted/MirAst.lean"),
    ] {
        let src = repo_root.join(rel);
        let bytes = fs::read(&src).unwrap();
        base_modules.push(TargetModule {
            module: module.to_owned(),
            source: src,
            expected_sha256: sha256_hex(&bytes),
            role: TargetRole::Model,
        });
    }

    let run_capture_and_audit = |tag: &str, rust_src: &str, expected_bodies: usize| {
        let crate_root = work.join(format!("{tag}/lib.rs"));
        fs::create_dir_all(crate_root.parent().unwrap()).unwrap();
        fs::write(&crate_root, rust_src).unwrap();

        let capture_out = work.join(format!("{tag}-capture"));
        let status = Command::new(capture_bin)
            .arg("capture")
            .arg("--crate-root")
            .arg(&crate_root)
            .arg(format!("--crate-name=large_{tag}"))
            .arg("--target=x86_64-unknown-linux-gnu")
            .arg("--out-dir")
            .arg(&capture_out)
            .arg("--source-file")
            .arg(&crate_root)
            .arg("--scope=crate")
            .arg("--sysroot")
            .arg(&tools.sysroot)
            .env("LD_LIBRARY_PATH", tools.sysroot.join("lib"))
            .output()
            .expect("run anneal-rustc-capture on large crate");
        assert!(
            status.status.success(),
            "capture ({tag}) failed: {}\n{}",
            String::from_utf8_lossy(&status.stdout),
            String::from_utf8_lossy(&status.stderr)
        );

        let manifest: Value =
            serde_json::from_slice(&fs::read(capture_out.join("capture.json")).unwrap()).unwrap();
        let captured_path = capture_out.join("Captured.lean");
        let captured_lean = fs::read_to_string(&captured_path).unwrap();
        assert!(
            captured_lean.contains("(_root_.List.append "),
            "expected balanced _root_.List.append chunks in {tag} Captured.lean"
        );

        let target_dir = work.join(format!("{tag}-lean"));
        fs::create_dir_all(&target_dir).unwrap();
        let make_lean = |name: &str, role: TargetRole, imports: &str, body: &str| {
            let path = target_dir.join(format!("{name}.lean"));
            let contents = lean_source(imports, body);
            fs::write(&path, contents.as_bytes()).unwrap();
            TargetModule {
                module: name.to_owned(),
                source: path,
                expected_sha256: sha256_hex(contents.as_bytes()),
                role,
            }
        };

        let mut modules = base_modules.clone();
        modules.push(make_lean(
            "Trusted.MirSemantics",
            TargetRole::Model,
            "import Trusted.MirAst",
            &format!(
                "namespace Trusted.MirSemantics\n\n\
                 structure Crate where\n  \
                   program : Trusted.MirAst.Program\n  \
                   specs : Trusted.MirAst.Program → Prop\n\n\
                 def UnitTheorem (c : Crate) : Prop :=\n  \
                   c.program.bodies.length = {expected_bodies} ∧ c.specs c.program\n\n\
                 end Trusted.MirSemantics"
            ),
        ));
        modules.push(TargetModule {
            module: "Captured".to_owned(),
            expected_sha256: sha256_hex(captured_lean.as_bytes()),
            source: captured_path,
            role: TargetRole::Capture,
        });
        modules.push(make_lean(
            "Spec",
            TargetRole::Specification,
            "import Trusted.MirAst",
            &format!(
                "namespace Spec\n\
                 def specs (p : Trusted.MirAst.Program) : Prop :=\n  \
                   p.bodies.length = {expected_bodies}\n\
                 end Spec"
            ),
        ));
        modules.push(make_lean(
            "Expected",
            TargetRole::Expected,
            "import Trusted.MirSemantics\nimport Captured\nimport Spec",
            "namespace Expected\n\
             def claim : Prop := Trusted.MirSemantics.UnitTheorem \
               (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n\
             end Expected",
        ));
        modules.push(make_lean(
            "Proof",
            TargetRole::Proof,
            "import Expected",
            &format!(
                "namespace Proof\n\
                 theorem bodies_len : Captured.program.bodies.length = {expected_bodies} := rfl\n\
                 theorem verify : Expected.claim := ⟨bodies_len, bodies_len⟩\n\
                 end Proof"
            ),
        ));

        let h = sha256_hex(format!("large-capture-binding-{tag}").as_bytes());
        let request = TargetAuditRequest {
            modules,
            theorem_module: "Proof".to_owned(),
            theorem_name: "Proof.verify".to_owned(),
            expected_module: "Expected".to_owned(),
            expected_declaration: "Expected.claim".to_owned(),
            canonical_root: "Trusted.MirSemantics.UnitTheorem".to_owned(),
            subject_declaration: "Captured.program".to_owned(),
            specification_declaration: "Spec.specs".to_owned(),
            bindings: TargetBindings {
                request_sha256: h.clone(),
                capture_sha256: h.clone(),
                model_manifest_sha256: h.clone(),
                specification_manifest_sha256: h,
            },
            allow_sorry_in_proof: false,
        };

        let mut checker = Checker::new(&bundle_root, Some(&tools.lean)).unwrap();
        let report = checker.run_target(&request).expect("target audit failed");
        assert_eq!(report["replay"], json!(true), "{report}");
        assert_eq!(report["exactType"], json!(true), "{report}");
        assert_eq!(report["theorem"], json!("Proof.verify"), "{report}");
        (manifest, captured_lean)
    };

    // 1. Multi-body crate exercising chunking across bodies, locals,
    //    statements, switch targets, enum discriminants, and >= 100-char names.
    let mut rust_src = String::new();
    for i in 0..69 {
        let _ = writeln!(&mut rust_src, "pub fn fn_{i:02}() -> u64 {{ 0 }}");
    }
    rust_src.push_str("pub enum LargeEnum {\n");
    for i in 0..70 {
        let _ = writeln!(&mut rust_src, "    V{i},");
    }
    rust_src.push_str("}\n");
    let long_mod = format!("m_{}", "x".repeat(75));
    let _ = writeln!(&mut rust_src, "pub mod {long_mod} {{");
    rust_src.push_str("    pub fn long_fn(e: crate::LargeEnum) -> u64 {\n");
    for i in 0..85 {
        let _ = writeln!(&mut rust_src, "        let _v_{i}: u64 = 0;");
    }
    rust_src.push_str("        match e {\n");
    for i in 0..70 {
        let _ = writeln!(&mut rust_src, "            crate::LargeEnum::V{i} => {},", i + 1);
    }
    rust_src.push_str("        }\n    }\n}\n");

    let (capture_manifest, _) = run_capture_and_audit("bodies", &rust_src, 70);
    let bodies = capture_manifest["program"]["bodies"].as_array().unwrap();
    assert_eq!(bodies.len(), 70);
    assert!(bodies.iter().any(|b| b["identity"].as_str().unwrap().len() >= 100));
    assert!(bodies.iter().any(|b| {
        b["blocks"]
            .as_array()
            .unwrap()
            .iter()
            .map(|blk| blk["statements"].as_array().unwrap().len())
            .sum::<usize>()
            >= 250
    }));

    // 2. 1970-variant enum (`discriminants : List Nat`): balanced chunking
    //    avoids Lean 4.34.1 `maxRecDepth` during elaboration.
    let mut wide_enum = String::from("pub enum WideEnum {\n");
    for i in 0..1970 {
        let _ = writeln!(&mut wide_enum, "    V{i},");
    }
    wide_enum.push_str("}\npub fn use_wide(_: WideEnum) -> u64 { 0 }\n");
    run_capture_and_audit("wide_enum", &wide_enum, 1);
}

#[test]
fn anti_vacuity_lint_clean_spin_and_unsafe_identity() {
    let staged = new_workspace("anneal-antivacuity-").stage().unwrap();
    let work = staged.work_dir();
    let req = write_scalar_baseline(work);
    let req_path = write_json_file(&work.join("req.json"), &req);

    // 1. Clean `scalar` proof emits empty `spec_warnings` and clean stderr.
    let clean_res = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    let clean_ok = expect_verified(&clean_res, "crate_verified", true);
    assert!(clean_ok.spec_warnings.is_empty(), "{clean_ok:?}");
    assert!(clean_res.process.stderr.is_empty());

    // 2. Global `Specs.safety := fun _ _ => False` emits
    //    `unsatisfiable_safety`.
    let spin_dir = corpus_path("spin");
    fs::write(work.join("rust/lib.rs"), fs::read(spin_dir.join("lib.rs")).unwrap()).unwrap();
    fs::write(work.join("lean/Spec.lean"), fs::read(spin_dir.join("Spec.lean")).unwrap()).unwrap();
    fs::write(work.join("lean/Proof.lean"), fs::read(spin_dir.join("Proof.lean")).unwrap())
        .unwrap();
    let spin_res = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    let spin_ok = expect_verified(&spin_res, "crate_verified", true);
    assert!(spin_ok.spec_warnings.iter().any(|w| w["code"] == "unsatisfiable_safety"));
    let spin_stderr = String::from_utf8_lossy(&spin_res.process.stderr);
    assert!(spin_stderr.contains("WARNING [anti-vacuity: unsatisfiable_safety]"), "{spin_stderr}");

    // 3. Per-body `False` safety + `trivial_property` on `unsafe_identity`.
    let uid_dir = corpus_path("unsafe_identity");
    fs::write(work.join("rust/lib.rs"), fs::read(uid_dir.join("lib.rs")).unwrap()).unwrap();
    fs::write(work.join("lean/Spec.lean"), fs::read(uid_dir.join("Spec.lean")).unwrap()).unwrap();
    fs::write(work.join("lean/Proof.lean"), fs::read(uid_dir.join("Proof.lean")).unwrap()).unwrap();
    let uid_res = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    let uid_ok = expect_verified(&uid_res, "crate_verified", true);
    assert!(
        uid_ok.spec_warnings.iter().any(|w| {
            w["code"] == "unsatisfiable_safety" && w["body"] == "rust-path-v1::locked"
        })
    );
    assert!(!uid_ok.spec_warnings.iter().any(|w| w["body"] == "rust-path-v1::open"));
    assert!(uid_ok.spec_warnings.iter().any(|w| w["code"] == "trivial_property"));
}

#[test]
fn anti_vacuity_lint_unused_bindings_and_wrong_arity() {
    let staged = new_workspace("anneal-lint-unused-").stage().unwrap();
    let work = staged.work_dir();
    let req = write_scalar_baseline(work);
    let req_path = write_json_file(&work.join("req.json"), &req);

    // 4. Unused named bindings and non-trivial `property` ignoring `Program`.
    fs::write(
        work.join("lean/Spec.lean"),
        lean_source(
            "import Trusted.MirSemantics",
            "namespace Spec\n\
             open Trusted.MirAst Trusted.MirSemantics\n\
             noncomputable def helper (unusedArg : Nat) (_ : Nat) : Prop := True\n\
             noncomputable def ignoredProp (_ : Program) : Prop := ∃ n : Nat, n = 0\n\
             noncomputable def specs : Specs := ⟨fun unusedSafety _ => helper 0 0, ignoredProp⟩\n\
             end Spec",
        ),
    )
    .unwrap();
    fs::write(
        work.join("lean/Proof.lean"),
        lean_source(
            "import Expected\nimport Anneal.MirWp",
            "namespace Proof\n\
             open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp\n\
             theorem execution : execProg (entryProgForBody Captured.program 0) 2 { args := [] } (fun _ => True) := trivial\n\
             theorem safeBody : WellFormed (entryProgForBody Captured.program 0) { args := [] } :=\n  \
               (wellFormed_and_spec_of_wp (entryProgForBody Captured.program 0) { args := [] } 2 (fun _ => True) (wpProg_of_execProg execution)).1.1\n\
             theorem verify : Expected.claim := by\n  \
               refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ⟨0, rfl⟩⟩\n  \
               intro id body found\n  \
               cases id with\n  \
               | zero =>\n    \
                 have same : Captured.program.bodies[0] = body := Option.some.inj found\n    \
                 subst body\n    \
                 refine ⟨found, rfl, ?_⟩\n    \
                 intro args valid _\n    \
                 cases args with\n    \
                 | nil => exact safeBody\n    \
                 | cons _ _ => cases valid\n  \
               | succ id => cases found\n\
             end Proof",
        ),
    )
    .unwrap();
    let unused_res = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    let unused_ok = expect_verified(&unused_res, "crate_verified", true);
    assert!(unused_ok.spec_warnings.iter().any(|w| {
        w["code"] == "unused_spec_binding"
            && w["declaration"] == "Spec.helper"
            && w["message"].as_str().is_some_and(|m| m.contains("unusedArg"))
    }));
    assert!(unused_ok.spec_warnings.iter().any(|w| {
        w["code"] == "unused_spec_binding"
            && w["declaration"] == "Spec.specs"
            && w["message"].as_str().is_some_and(|m| m.contains("unusedSafety"))
    }));
    assert!(unused_ok.spec_warnings.iter().any(|w| {
        w["code"] == "unused_spec_binding"
            && w["declaration"] == "Spec.specs"
            && w["message"].as_str().is_some_and(|m| m.contains("ignores its `Program` argument"))
    }));
    assert!(!unused_ok.spec_warnings.iter().any(|w| w["code"] == "trivial_property"));

    // 5. Wrong-arity safety match on `unsafe fn` flags `unsatisfiable_safety`.
    fs::write(work.join("rust/lib.rs"), "pub unsafe fn bad_arity() -> u64 { 0 }\n").unwrap();
    fs::write(
        work.join("lean/Spec.lean"),
        lean_source(
            "import Trusted.MirSemantics",
            "namespace Spec\n\
             open Trusted.MirAst Trusted.MirSemantics\n\
             noncomputable def specs : Specs :=\n  \
               ⟨fun fn args => match args with | [_] => fn = \"rust-path-v1::bad_arity\" | _ => False, fun _ => True⟩\n\
             end Spec",
        ),
    )
    .unwrap();
    fs::write(
        work.join("lean/Proof.lean"),
        lean_source(
            "import Expected",
            "namespace Proof\n\
             open Trusted.MirAst Trusted.MirSemantics\n\
             theorem verify : Expected.claim := by\n  \
               refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, trivial⟩\n  \
               intro id body found\n  \
               cases id with\n  \
               | zero =>\n    \
                 have same : Captured.program.bodies[0] = body := Option.some.inj found\n    \
                 subst body\n    \
                 refine ⟨found, rfl, ?_⟩\n    \
                 intro args valid safety\n    \
                 have bad : False := by cases args with | nil => exact safety rfl | cons _ _ => cases valid\n    \
                 exact False.elim bad\n  \
               | succ id => cases found\n\
             end Proof",
        ),
    )
    .unwrap();
    let arity_res = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    let arity_ok = expect_verified(&arity_res, "crate_verified", true);
    assert!(arity_ok.spec_warnings.iter().any(|w| {
        w["code"] == "unsatisfiable_safety" && w["body"] == "rust-path-v1::bad_arity"
    }));
}

#[test]
fn explicit_instantiation_and_required_consts_verify_end_to_end() {
    let staged = new_workspace("anneal-mono-consts-").stage().unwrap();
    let work = staged.work_dir();
    let mut req = write_scalar_baseline(work);

    fs::write(
        work.join("rust/lib.rs"),
        "pub trait LayoutVal: Sized {\n\
             const VAL: usize = {\n\
                 assert!(core::mem::size_of::<Self>() > 0);\n\
                 core::mem::size_of::<Self>()\n\
             };\n\
         }\n\
         impl LayoutVal for u64 {}\n\
         impl LayoutVal for () {}\n\
         pub fn layout_val<T: LayoutVal>() -> usize {\n\
             const { assert!(core::mem::size_of::<T>() > 0); }\n\
             T::VAL\n\
         }\n",
    )
    .unwrap();
    fs::write(
        work.join("lean/Spec.lean"),
        lean_source(
            "import Trusted.MirSemantics",
            "namespace Spec\n\
             open Trusted.MirAst Trusted.MirSemantics\n\
             def expectedReturn : TerminalOut :=\n  \
               .returned ⟨.scalar ⟨.isize, false, BitVec.ofNat 128 8⟩, ⟨[]⟩⟩\n\
             noncomputable def returnsEight (program : Program) : Prop :=\n  \
               let entry := entryProgForBody program 0\n  \
               let call : Query := { args := [] }\n  \
               SatisfiesPost entry call (fun outcome => outcome = expectedReturn) ∧\n    \
                 (¬ Diverges entry call) ∧ Behavior entry call expectedReturn\n\
             noncomputable def specs : Specs := ⟨fun _ _ => True, returnsEight⟩\n\
             end Spec",
        ),
    )
    .unwrap();
    fs::write(
        work.join("lean/Proof.lean"),
        lean_source(
            "import Expected\nimport Anneal.MirWp",
            "namespace Proof\n\
             open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp\n\
             theorem execution :\n    \
               execProg (entryProgForBody Captured.program 0) 10 { args := [] }\n      \
                 (fun outcome => outcome = Spec.expectedReturn) := rfl\n\
             theorem totalCorrectness : Spec.returnsEight Captured.program := by\n  \
               have ⟨post, terminates, out, returned, result⟩ :=\n    \
                 wellFormed_and_spec_of_wp (entryProgForBody Captured.program 0)\n      \
                   { args := [] } 10 (fun outcome => outcome = Spec.expectedReturn)\n      \
                   (wpProg_of_execProg execution)\n  \
               exact ⟨post, terminates, result ▸ returned⟩\n\
             theorem verify : Expected.claim := by\n  \
               refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, totalCorrectness⟩\n  \
               intro id body found\n  \
               cases id with\n  \
               | zero =>\n      \
                 have same : Captured.program.bodies[0] = body := Option.some.inj found\n      \
                 subst body\n      \
                 refine ⟨found, rfl, ?_⟩\n      \
                 intro args valid _\n      \
                 cases args with\n      \
                 | nil => exact totalCorrectness.1.1\n      \
                 | cons _ _ => cases valid\n  \
               | succ id => cases found\n\
             end Proof",
        ),
    )
    .unwrap();

    req["scope"] = json!({
        "kind": "selected_unit",
        "roots": [],
        "instantiations": [{"path": "layout_val", "args": ["u64"]}]
    });
    let ok_path = write_json_file(&work.join("ok_req.json"), &req);
    let ok_res = run_verify_strs(&staged, &["--request", ok_path.to_str().unwrap()]);
    let ok_receipt = expect_verified(&ok_res, "selected_unit_verified", true);
    assert!(ok_receipt.taint_reasons.is_empty(), "{ok_receipt:?}");

    // Post-monomorphization `const { assert!(size_of::<()>() > 0) }` must fail
    // closed during capture.
    req["scope"] = json!({
        "kind": "selected_unit",
        "roots": [],
        "instantiations": [{"path": "layout_val", "args": ["()"]}]
    });
    let bad_path = write_json_file(&work.join("bad_req.json"), &req);
    let bad_res = run_verify_strs(&staged, &["--request", bad_path.to_str().unwrap()]);
    crate::helpers::expect_failed(&bad_res, 2, "compiler_failed", Some("capture"), "");
}

#[test]
fn onboarding_init_and_diagnostic_hints_e2e() {
    use std::ffi::OsStr;

    use anneal_testkit::assertions::assert_outcome_exit;

    use crate::helpers::{verify_invocation, with_host_cargo_env};

    let cli = workspace_tools().cli.as_deref().expect("workspace cli binary");
    let staged = new_workspace("anneal-ux-e2e-").stage().unwrap();
    let dir = staged.work_dir();

    // 1. `cargo anneal init --standalone` produces a directly verifiable example.
    let standalone = dir.join("hello");
    let init_out = Command::new(cli)
        .args(["init", "--standalone", "--proof-dir"])
        .arg(&standalone)
        .output()
        .unwrap();
    assert!(
        init_out.status.success(),
        "init --standalone failed:\n{}",
        String::from_utf8_lossy(&init_out.stderr)
    );
    let pass_inv =
        verify_invocation(&[OsStr::new("--request"), standalone.join("request.json").as_os_str()]);
    let pass_raw = staged.exec(&pass_inv).unwrap();
    assert_outcome_exit(&pass_raw.process, 0).unwrap();
    let pass_stdout = String::from_utf8_lossy(&pass_raw.process.stdout);
    let pass_receipt: Value = serde_json::from_str(&pass_stdout).unwrap();
    assert_eq!(pass_receipt["status"], "selected_unit_verified", "{pass_receipt}");
    assert_eq!(pass_receipt["taint_reasons"], json!([]), "{pass_receipt}");

    // 2. Cargo `init` + unmodified starter proof emits a concise Lean placeholder hint,
    //    `example` in `Spec.lean` emits a spec-preflight hint, and `take_ref` capture
    //    emits a Profile v1 reference hint while preserving existing `detail` contracts.
    let krate = dir.join("crate_demo");
    fs::create_dir_all(krate.join("src")).unwrap();
    fs::create_dir_all(krate.join("empty_proof")).unwrap();
    fs::write(
        krate.join("Cargo.toml"),
        "[package]\nname = \"ux_demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(krate.join("src/lib.rs"), "pub fn zero() -> u64 { 0 }\n").unwrap();

    let manifest = krate.join("Cargo.toml");
    let empty_proof_inv = with_host_cargo_env(verify_invocation(&[
        OsStr::new("--manifest-path"),
        manifest.as_os_str(),
        OsStr::new("--proof-dir"),
        krate.join("empty_proof").as_os_str(),
    ]));
    let empty_proof_out = staged.exec(&empty_proof_inv).unwrap().process;
    assert_outcome_exit(&empty_proof_out, 1).unwrap();
    let empty_proof_receipt: Value = serde_json::from_slice(&empty_proof_out.stdout).unwrap();
    assert_eq!(empty_proof_receipt["phase"], "proof", "{empty_proof_receipt}");
    assert_eq!(
        empty_proof_receipt["detail"],
        "specification and theorem must have their declared source roles"
    );
    assert!(
        empty_proof_receipt["hint"].as_str().is_some_and(|h| h.contains("cargo anneal init")),
        "{empty_proof_receipt}"
    );

    let cargo_init = Command::new(cli).current_dir(&krate).arg("init").output().unwrap();
    assert!(cargo_init.status.success());

    let proof_dir = krate.join("proof");
    let hole_inv = with_host_cargo_env(verify_invocation(&[
        OsStr::new("--manifest-path"),
        manifest.as_os_str(),
        OsStr::new("--proof-dir"),
        proof_dir.as_os_str(),
    ]));
    let hole_out = staged.exec(&hole_inv).unwrap().process;
    assert_outcome_exit(&hole_out, 1).unwrap();
    let hole_receipt: Value = serde_json::from_slice(&hole_out.stdout).unwrap();
    assert_eq!(hole_receipt["status"], "proof_failed", "{hole_receipt}");
    assert!(
        hole_receipt["hint"]
            .as_str()
            .is_some_and(|h| h.contains("Proof.lean:") && h.contains("Complete the remaining proof")),
        "{hole_receipt}"
    );

    let spec_path = krate.join("proof/Spec.lean");
    let orig_spec = fs::read_to_string(&spec_path).unwrap();
    fs::write(&spec_path, format!("{orig_spec}\nexample : True := trivial\n")).unwrap();
    let spec_out = staged.exec(&hole_inv).unwrap().process;
    assert_outcome_exit(&spec_out, 1).unwrap();
    let spec_receipt: Value = serde_json::from_slice(&spec_out.stdout).unwrap();
    assert!(
        spec_receipt["detail"].as_str().unwrap().contains("Lean.Parser.Command.example"),
        "{spec_receipt}"
    );
    assert!(
        spec_receipt["hint"].as_str().is_some_and(|h| h.contains("`example`")),
        "{spec_receipt}"
    );

    fs::write(krate.join("src/lib.rs"), "pub fn take_ref(x: &u64) -> u64 { *x }\n").unwrap();
    let ref_out = staged.exec(&hole_inv).unwrap().process;
    assert_outcome_exit(&ref_out, 1).unwrap();
    let ref_receipt: Value = serde_json::from_slice(&ref_out.stdout).unwrap();
    assert_eq!(ref_receipt["phase"], "capture", "{ref_receipt}");
    assert!(
        ref_receipt["hint"]
            .as_str()
            .is_some_and(|h| h.contains("`take_ref`") && h.contains("references")),
        "{ref_receipt}"
    );
}
