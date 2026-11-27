// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end checks of explicit instantiation and required constants,
//! onboarding hints, long identity bodies, and the Profile v2 lint.

use super::*;

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

    // 1. `cargo anneal init --standalone` produces a directly verifiable
    //    example.
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

    // 2. Cargo `init` + unmodified starter proof emits a concise Lean
    //    placeholder hint, `example` in `Spec.lean` emits a spec-preflight
    //    hint, and `take_ref` capture emits a nested-reference hint while
    //    preserving existing `detail` contracts.
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
