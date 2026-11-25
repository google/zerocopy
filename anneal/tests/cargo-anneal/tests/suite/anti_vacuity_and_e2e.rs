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
        let capture_shards_path = capture_out.join("capture_shards.json");
        if capture_shards_path.is_file() {
            let shards_json: Value =
                serde_json::from_slice(&fs::read(&capture_shards_path).unwrap()).unwrap();
            for shard in shards_json["shards"].as_array().unwrap() {
                let idx = shard["shard_idx"].as_u64().unwrap();
                let mod_name = shard["capture_module"].as_str().unwrap().to_owned();
                let expected_sha = shard["capture_sha256"].as_str().unwrap().to_owned();
                let shard_path = capture_out.join(format!("Captured/Shard_{idx:03}.lean"));
                modules.push(TargetModule {
                    module: mod_name,
                    expected_sha256: expected_sha,
                    source: shard_path,
                    role: TargetRole::Capture,
                });
            }
        }
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
    //    emits a nested-reference hint while preserving existing `detail`
    //    contracts.
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
    let empty_proof_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            krate.join("empty_proof").as_os_str(),
        ]),
    );
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
    let hole_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            proof_dir.as_os_str(),
        ]),
    );
    let hole_out = staged.exec(&hole_inv).unwrap().process;
    assert_outcome_exit(&hole_out, 1).unwrap();
    let hole_receipt: Value = serde_json::from_slice(&hole_out.stdout).unwrap();
    assert_eq!(hole_receipt["status"], "proof_failed", "{hole_receipt}");
    assert!(hole_receipt.get("reason").is_none(), "{hole_receipt}");
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

    fs::write(krate.join("src/lib.rs"), "pub fn take_ref(x: &&u64) -> u64 { **x }\n").unwrap();
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

#[test]
fn verifies_crate_with_over_100_long_identity_bodies_at_default_max_rec_depth() {
    let staged = new_workspace("anneal-long-id-").stage().unwrap();
    let work = staged.work_dir();
    let req = write_scalar_baseline(work);

    // Generate 105 free functions inside long nested modules so every captured
    // identity exceeds 100 characters and shares a 120-character prefix. This
    // exercises the O(N log N) `bodiesHaveUniqueIdentities` balanced tree on
    // worst-case shared-prefix comparisons and the balanced-append
    // `BodyStaticAdmitted` path end-to-end at default `maxRecDepth = 512`.
    // Whole-crate scope refuses traits, so long trait-impl paths are covered
    // by the selected-unit proofs under `zerocopy/proofs/`.
    let outer = "long_identity_scaling_outer_module_for_balanced_tree";
    let inner = "long_identity_scaling_inner_module_for_balanced_tree";
    let mut rust_src = format!("pub mod {outer} {{\n    pub mod {inner} {{\n");
    for i in 0..105 {
        let _ = writeln!(&mut rust_src, "        pub fn fn_{i:03}() -> u64 {{ 0 }}");
    }
    rust_src.push_str("    }\n}\n");
    fs::write(work.join("rust/lib.rs"), rust_src).unwrap();

    let proof = lean_source(
        "import Expected\nimport Anneal.MirWp",
        r#"namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

private def expectedBlocks : List BasicBlock :=
  [{ statements :=
       [.assign { localId := 0, projection := [] }
         (.use (.constant { ty := .int .i64 false, lit := .scalar (BitVec.ofNat 128 0) }))]
   , terminator := .return_
   , cleanup := false }]

private def isZeroBody (b : Body) : Bool :=
  match b with
  | { argumentCount := 0
    , locals := [.int .i64 false]
    , basicBlocks := [{
        statements := [.assign { localId := 0, projection := [] }
          (.use (.constant { ty := .int .i64 false, lit := .scalar k }))]
        terminator := .return_
        cleanup := false }]
    , isUnsafe := false
    , identity := _ } => k == BitVec.ofNat 128 0
  | _ => false

private noncomputable def allZeroBodiesAdm (p : Program) (bs : List Body) : Bool :=
  bs.foldr (fun b acc => isZeroBody b && BodyStaticAdmitted p b && acc) true

private theorem and3 {a b c : Bool} (h : (a && b && c) = true) :
    a = true ∧ b = true ∧ c = true := by
  cases a <;> cases b <;> cases c <;> first | exact ⟨rfl, rfl, rfl⟩ | cases h

private theorem allZeroBodiesAdm_getElem {p : Program} :
    ∀ {bs : List Body} {k : Nat} {b : Body},
      allZeroBodiesAdm p bs = true →
      Trusted.MirSemantics.getElem? bs k = some b →
      isZeroBody b = true ∧ BodyStaticAdmitted p b = true
  | [], _, _, _, hGet => by cases hGet
  | b₀ :: rest, 0, b, hAll, hGet => by
    injection hGet with hEq
    subst hEq
    have h := and3 (a := isZeroBody b₀) (b := BodyStaticAdmitted p b₀)
      (c := allZeroBodiesAdm p rest) hAll
    exact ⟨h.1, h.2.1⟩
  | b₀ :: rest, k + 1, b, hAll, hGet =>
    allZeroBodiesAdm_getElem
      (and3 (a := isZeroBody b₀) (b := BodyStaticAdmitted p b₀)
        (c := allZeroBodiesAdm p rest) hAll).2.2
      hGet

private theorem all_bodies_adm :
    allZeroBodiesAdm Captured.program Captured.program.bodies = true := rfl

private theorem zeroBody_runs (ident : String) :
    Runs
      { argumentCount := 0
      , locals := [.int .i64 false]
      , basicBlocks := expectedBlocks
      , isUnsafe := false
      , identity := ident }
      2 [] (.scalar ⟨.i64, false, BitVec.ofNat 128 0⟩) := rfl

private theorem zeroBody_verified {defId : DefId} {body : Body}
    (hGet : Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hShape : isZeroBody body = true)
    (hAdm : BodyStaticAdmitted Captured.program body = true) :
    BodyVerified Captured.program defId body (Spec.specs.safety body.identity) := by
  unfold isZeroBody at hShape
  split at hShape
  · case h_1 k _ =>
    have hk : k = BitVec.ofNat 128 0 := beq_iff_eq.mp hShape
    subst hk
    refine bodyVerified_of_safe hGet hAdm (fun args valid _ => ?_)
    have hNil : args = [] := checkArgsMatch_nil_iff.mp valid
    subst hNil
    exact (run_initial_success (zeroBody_runs _)).1
  · cases hShape

private theorem execution :
    execProg (entryProgForBody Captured.program 0) 2 { args := [] }
      (fun outcome => outcome = Spec.expectedReturn) := rfl

private theorem totalCorrectness : Spec.returnsZero Captured.program := by
  have ⟨post, terminates, out, returned, result⟩ :=
    wellFormed_and_spec_of_wp (entryProgForBody Captured.program 0)
      { args := [] } 2 (fun outcome => outcome = Spec.expectedReturn)
      (wpProg_of_execProg execution)
  exact ⟨post, terminates, result ▸ returned⟩

-- Kernel-checked negative boundaries and shared-prefix long-identity checks
-- at default `maxRecDepth = 512`, assembled like captured identities from
-- balanced `<= 16`-character literal leaves.
private def longSharedPrefix : String :=
  Trusted.MirAst.stringAppend
    (Trusted.MirAst.stringAppend
      (Trusted.MirAst.stringAppend "rust-path-v1::lo" "ng_identity_scal")
      (Trusted.MirAst.stringAppend "ing_outer_module" "_for_balanced_tr"))
    (Trusted.MirAst.stringAppend
      (Trusted.MirAst.stringAppend "ee::long_identit" "y_scaling_inner_")
      (Trusted.MirAst.stringAppend "module_for_balan" "ced_tree::fn_"))

private theorem duplicate_identities_rejected :
    bodiesHaveUniqueIdentities [Captured.body_0, Captured.body_0] = false := rfl

-- A trailing duplicate must be caught by every arm of the four-way unrolled
-- pass (list lengths 3 through 7), and a duplicate of a body deep inside the
-- balanced tree of all 105 captured bodies must be found as well.
private theorem trailing_duplicate_rejected_len3 :
    bodiesHaveUniqueIdentities
      [Captured.body_0, Captured.body_1, Captured.body_0] = false := rfl

private theorem trailing_duplicate_rejected_len4 :
    bodiesHaveUniqueIdentities
      [Captured.body_0, Captured.body_1, Captured.body_2, Captured.body_0] =
      false := rfl

private theorem trailing_duplicate_rejected_len5 :
    bodiesHaveUniqueIdentities
      [Captured.body_0, Captured.body_1, Captured.body_2, Captured.body_3,
       Captured.body_0] = false := rfl

private theorem trailing_duplicate_rejected_len6 :
    bodiesHaveUniqueIdentities
      [Captured.body_0, Captured.body_1, Captured.body_2, Captured.body_3,
       Captured.body_4, Captured.body_2] = false := rfl

private theorem trailing_duplicate_rejected_len7 :
    bodiesHaveUniqueIdentities
      [Captured.body_0, Captured.body_1, Captured.body_2, Captured.body_3,
       Captured.body_4, Captured.body_5, Captured.body_3] = false := rfl

private theorem deep_duplicate_rejected :
    bodiesHaveUniqueIdentities
      (Captured.program.bodies ++ [Captured.body_57]) = false := rfl

private theorem long_shared_prefix_duplicate_rejected :
    bodiesHaveUniqueIdentities
      [{ Captured.body_0 with identity := Trusted.MirAst.stringAppend longSharedPrefix "a" },
       { Captured.body_0 with identity := Trusted.MirAst.stringAppend longSharedPrefix "a" }] =
      false := rfl

private theorem long_shared_prefix_distinct_accepted :
    bodiesHaveUniqueIdentities
      [{ Captured.body_0 with identity := Trusted.MirAst.stringAppend longSharedPrefix "a" },
       { Captured.body_0 with identity := Trusted.MirAst.stringAppend longSharedPrefix "b" }] =
      true := rfl

private theorem empty_identity_rejected :
    BodyStaticAdmitted Captured.program { Captured.body_0 with identity := "" } = false := rfl

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, totalCorrectness⟩
  intro defId body found
  have ⟨hShape, hAdm⟩ := allZeroBodiesAdm_getElem all_bodies_adm found
  exact zeroBody_verified found hShape hAdm

end Proof"#,
    );
    fs::write(work.join("lean/Proof.lean"), proof).unwrap();

    let req_path = write_json_file(&work.join("request.json"), &req);
    let artifacts = work.join("scaling_105_crate");
    let accepted = run_verify_strs(
        &staged,
        &["--request", req_path.to_str().unwrap(), "--artifacts", artifacts.to_str().unwrap()],
    );
    let receipt = expect_verified(&accepted, "crate_verified", true);
    assert_eq!(
        receipt.audit.get("exactType").and_then(Value::as_bool),
        Some(true),
        "{receipt:?}"
    );

    let shard_0_lean = artifacts.join("capture/Captured/Shard_000.lean");
    let string_append_source = if shard_0_lean.exists() {
        shard_0_lean
    } else {
        artifacts.join("capture/Captured.lean")
    };
    let captured_lean = fs::read_to_string(&string_append_source).unwrap();
    assert!(
        captured_lean.contains("Trusted.MirAst.stringAppend"),
        "expected long identities in {} to use balanced Trusted.MirAst.stringAppend",
        string_append_source.display()
    );

    let captured_json: Value =
        serde_json::from_slice(&fs::read(artifacts.join("capture/capture.json")).unwrap()).unwrap();
    let bodies = captured_json["program"]["bodies"].as_array().unwrap();
    assert_eq!(bodies.len(), 105, "expected 105 captured bodies");
    for body in bodies {
        let identity = body["identity"].as_str().unwrap();
        assert!(identity.len() > 100, "expected a > 100-char identity, got {identity:?}");
    }
}

#[test]
fn anti_vacuity_lint_profile_v2_specs_v2() {
    let staged = new_workspace("anneal-antivacuity-v2-").stage().unwrap();
    let work = staged.work_dir();
    let req = write_scalar_baseline(work);
    let req_path = write_json_file(&work.join("req.json"), &req);

    fs::write(
        work.join("rust/lib.rs"),
        "pub unsafe fn v2_zero() -> *const u8 {\n    0usize as *const u8\n}\n",
    )
    .unwrap();

    let false_proof = lean_source(
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
             exact ⟨found, rfl, fun _ _ hSafety => False.elim (hSafety rfl)⟩\n  \
           | succ _ => cases found\n\
         end Proof",
    );

    // 1. Global `SpecsV2.safety := fun _ _ => False` and trivial `property`.
    fs::write(
        work.join("lean/Spec.lean"),
        lean_source(
            "import Trusted.MirSemantics",
            "namespace Spec\n\
             open Trusted.MirAst Trusted.MirSemantics\n\
             noncomputable def specs : SpecsV2 := ⟨fun _ _ => False, fun _ => True⟩\n\
             end Spec",
        ),
    )
    .unwrap();
    fs::write(work.join("lean/Proof.lean"), &false_proof).unwrap();
    let global_res = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    let global_ok = expect_verified(&global_res, "crate_verified", true);
    assert!(
        global_ok.spec_warnings.iter().any(
            |w| w["code"] == "unsatisfiable_safety" && w.get("body").is_none_or(Value::is_null)
        ),
        "{global_ok:?}"
    );
    assert!(
        global_ok.spec_warnings.iter().any(|w| w["code"] == "trivial_property"),
        "{global_ok:?}"
    );

    // 2. Per-body wrong arity on `SpecsV2` + `Program`-ignoring `property`.
    fs::write(
        work.join("lean/Spec.lean"),
        lean_source(
            "import Trusted.MirSemantics",
            "namespace Spec\n\
             open Trusted.MirAst Trusted.MirSemantics\n\
             noncomputable def ignoredProp (_ : Program) : Prop := ∃ n : Nat, n = 0\n\
             noncomputable def specs : SpecsV2 :=\n  \
               ⟨fun fn q => match q.args with | [_] => fn = \"rust-path-v1::v2_zero\" | _ => False, ignoredProp⟩\n\
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
               refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ⟨0, rfl⟩⟩\n  \
               intro id body found\n  \
               cases id with\n  \
               | zero =>\n    \
                 have same : Captured.program.bodies[0] = body := Option.some.inj found\n    \
                 subst body\n    \
                 refine ⟨found, rfl, ?_⟩\n    \
                 intro q valid safety\n    \
                 have hS := safety rfl\n    \
                 dsimp only [Spec.specs] at hS\n    \
                 cases hArgs : q.args with\n    \
                 | nil =>\n      \
                   rw [hArgs] at hS\n      \
                   exact False.elim hS\n    \
                 | cons _ _ =>\n      \
                   have hMatch := valid.2.1\n      \
                   rw [hArgs] at hMatch\n      \
                   cases hMatch\n  \
               | succ _ => cases found\n\
             end Proof",
        ),
    )
    .unwrap();
    let arity_res = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    let arity_ok = expect_verified(&arity_res, "crate_verified", true);
    assert!(
        arity_ok.spec_warnings.iter().any(|w| {
            w["code"] == "unsatisfiable_safety" && w["body"] == "rust-path-v1::v2_zero"
        }),
        "{arity_ok:?}"
    );
    assert!(
        arity_ok.spec_warnings.iter().any(|w| {
            w["code"] == "unused_spec_binding"
                && w["declaration"] == "Spec.specs"
                && w["message"]
                    .as_str()
                    .is_some_and(|m| m.contains("ignores its `Program` argument"))
        }),
        "{arity_ok:?}"
    );
    assert!(
        !arity_ok.spec_warnings.iter().any(|w| w["code"] == "trivial_property"),
        "{arity_ok:?}"
    );
}
