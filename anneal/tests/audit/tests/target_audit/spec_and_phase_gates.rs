// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Specification acceptance, the phase 1 and phase 2 target audit, spec
//! warnings, and program arity.

use super::*;

/// Positive end-to-end check confirming rich pure specifications—including
/// `noncomputable section`, `@[local simp]`, `@[reducible, inline]`,
/// `deriving BEq, DecidableEq, Repr, Inhabited, Ord, Hashable`,
/// `set_option maxHeartbeats` / `linter.*`, `decide +kernel`, `decide +revert`,
/// `omega`, `open System.Platform (numBits)`, and well-founded recursion
/// (`termination_by`/`decreasing_by`, which generates paired
/// `wfRec._unsafe_rec`)—pass `"spec-preflight"` and `"target-audit"` cleanly.
#[test]
fn spec_preflight_and_target_audit_accept_rich_pure_specs_and_wf_recursion() {
    let mut f = Fixture::new(
        "import Expected\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f.set(
        "Spec",
        TargetRole::Specification,
        r#"import Model
set_option linter.unusedVariables false
open System.Platform (numBits)
noncomputable section SpecRich
structure Tag where
  val : Nat
deriving BEq, DecidableEq, Repr, Inhabited, Ord, Hashable
@[reducible, inline] def hostBits : Nat := numBits + System.Platform.numBits
@[local simp] theorem hostBits_pos : 0 < hostBits := by
  have h := System.Platform.numBits_eq
  rcases h with h32 | h64
  · simp [hostBits, h32]
  · simp [hostBits, h64]
set_option maxHeartbeats 200000 in
theorem dec_kernel_ok : 2 + 2 = 4 := by decide +kernel
theorem dec_revert_ok (b : Bool) : (b || !b) = true := by decide +revert
theorem omega_ok (n : Nat) : n + 1 > n := by omega
def wfHalf (n : Nat) : Nat :=
  if h : n = 0 then 0 else wfHalf (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
def optElem : Option Nat := [1, 2][0]?
def optHead : Option Nat := [1, 2].head?
def sumFor : Nat := Id.run do
  let mut acc := 0
  for x in [1, 2, 3] do
    acc := acc + x
  return acc
section
open BitVec
def bvLit (x : Nat) (h : x < 2^8) : BitVec 8 := x#'h
end
section
open BitVec hiding ofNat
def bvLitHide (x : Nat) (h : x < 2^8) : BitVec 8 := x#'h
end
section
open Int
def negSuccVal (n : Nat) : Int := -[n+1]
end
end SpecRich
def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p
"#,
    );
    let mut checker = f.cargo_checker();
    checker.set_allow_unpinned_lean(true);
    let report = checker.run_target(&f.request).unwrap();
    assert_eq!(report["replay"], true);
    assert_eq!(report["exactType"], true);
    assert_eq!(report["sorryDeclarations"], serde_json::json!([]));
}

/// Unified `"target-audit"` Phase 1 enforces whole-specification invariants
/// even on declarations unreferenced by `Spec.specs` (rejecting `opaque`,
/// `sorryAx` even when `allow_sorry_in_proof = true`, transitive `IO`,
/// `dbgTrace`, or `System.Platform.target`, forged unpaired `._unsafe_rec`, and
/// forged `Proof` references to a paired `._unsafe_rec`, plus companion
/// artifact parts).
#[test]
fn target_audit_phase1_enforces_whole_spec_opaque_effects_and_unsafe_rec_invariants() {
    use anneal_audit::ModuleArtifacts;
    use std::collections::BTreeMap;

    // Helper: compile ONE valid unpinned baseline via `run_target` (which
    // admits the full `Init` closure into `checker.admitted()`), then overwrite
    // and recompile `Spec` (and `Expected`/`Proof`) directly into `stage/lib`
    // to exercise `"target-audit"` Phase 1 directly without `"spec-preflight"`.
    let mut f = Fixture::new(
        "import Expected\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f.set(
        "Spec",
        TargetRole::Specification,
        "import Model\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    let mut checker = f.cargo_checker();
    checker.set_allow_unpinned_lean(true);
    checker.run_target(&f.request).unwrap();

    let mut audit_bypassing_preflight = |spec_src: &str,
                                         proof_src: &str,
                                         allow_sorry: bool,
                                         forge_companion: bool|
     -> Result<Json, Failure> {
        f.set("Spec", TargetRole::Specification, spec_src);
        f.set("Proof", TargetRole::Proof, proof_src);
        f.request.allow_sorry_in_proof = allow_sorry;
        for name in ["Spec", "Expected", "Proof"] {
            let m = f.request.modules.iter().find(|x| x.module == name).unwrap();
            let staged_src = checker.stage().join("ro").join(format!("{name}.lean"));
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let _ = fs::set_permissions(&staged_src, fs::Permissions::from_mode(0o600));
            }
            fs::copy(&m.source, &staged_src).unwrap();
            let hdr_json = checker
                .inspect_headers(&[(name.to_string(), staged_src.clone())])
                .unwrap();
            let hdrs: cargo_anneal::PreflightResult = serde_json::from_value(hdr_json).unwrap();
            let header = hdrs.headers.into_iter().next().unwrap();
            let dest_olean = checker.stage().join("lib").join(format!("{name}.olean"));
            if dest_olean.exists() {
                #[cfg(unix)]
                {
                    use std::os::unix::fs::PermissionsExt;
                    let _ = fs::set_permissions(&dest_olean, fs::Permissions::from_mode(0o600));
                }
            }
            checker
                .compile_lean_module(
                    name,
                    &staged_src,
                    header.imports,
                    header.is_module,
                    "lib",
                    false,
                    true,
                )
                .unwrap();
        }
        if forge_companion {
            let spec_olean = checker.stage().join("lib/Spec.olean");
            let fake_priv = checker.stage().join("lib/Spec.olean.private");
            fs::copy(&spec_olean, &fake_priv).unwrap();
            let mut avail = BTreeMap::new();
            avail.insert("olean", spec_olean.to_string_lossy().into_owned());
            avail.insert("olean.private", fake_priv.to_string_lossy().into_owned());
            let adm = checker.admitted_mut().unwrap();
            adm.artifacts.insert(
                "Spec".into(),
                ModuleArtifacts::from_available(&avail, "fixture", || "missing".into()).unwrap(),
            );
        }
        checker.inspect_target(&f.request)
    };

    let clean_proof = "import Expected\n\
        theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n";

    // 1. Unused `opaque` in `Spec` rejected in Phase 1.
    let err = audit_bypassing_preflight(
        "import Model\nopaque Spec.unusedOp : Nat := 0\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        clean_proof,
        false,
        false,
    )
    .unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(
        err.message.contains("opaque declaration Spec.unusedOp"),
        "{err}"
    );

    // 2. Unused `sorry` in `Spec` rejected in Phase 1 EVEN WITH
    //    `allow_sorry_in_proof = true`.
    let err = audit_bypassing_preflight(
        "import Model\ntheorem Spec.unusedSorry : True := sorry\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        clean_proof,
        true,
        false,
    )
    .unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(err.message.contains("unapproved axiom sorryAx"), "{err}");

    // 3. Unused `Spec` declaration transitively referencing `IO`, `dbgTrace`,
    //    or `System.Platform.target` rejected in Phase 1.
    for (label, decl, expected) in [
        (
            "io",
            "def Spec.unusedIo : IO Unit := pure ()\n",
            "disallowed constant IO",
        ),
        (
            "dbg-trace",
            "def Spec.unusedDbg : Nat := dbgTrace \"x\" (fun _ => 0)\n",
            "disallowed constant dbgTrace",
        ),
        (
            "platform-target",
            "def Spec.unusedTarget : String := System.Platform.target\n",
            "disallowed constant System.Platform.target",
        ),
        (
            "get-elem-bang",
            "def Spec.unusedGetElemBang : Nat := (#[] : Array Nat)[0]!\n",
            "cannot reference GetElem?.getElem!",
        ),
        (
            "list-head-bang",
            "def Spec.unusedHeadBang : Nat := ([] : List Nat).head!\n",
            "cannot reference List.head!",
        ),
        (
            "option-get-bang",
            "def Spec.unusedGetBang : Nat := (none : Option Nat).get!\n",
            "cannot reference Option.get!",
        ),
        (
            "do-while-loop",
            "def Spec.unusedWhile : Nat := Id.run do\n  let mut x := 5\n  while x > 0 do\n    x := x - 1\n  return x\n",
            "disallowed constant Lean.Loop",
        ),
        (
            "out-of-bounds",
            "def Spec.unusedOob : Nat := outOfBounds\n",
            "cannot reference outOfBounds",
        ),
        (
            "pos-slice-or-panic",
            "def Spec.unusedPosSliceOrPanic := @String.Pos.sliceOrPanic\n",
            "cannot reference String.Pos.sliceOrPanic",
        ),
        (
            "slice-pos-slice-or-panic",
            "def Spec.unusedSlicePosSliceOrPanic := @String.Slice.Pos.sliceOrPanic\n",
            "cannot reference String.Slice.Pos.sliceOrPanic",
        ),
        (
            "repeat-m",
            "def Spec.unusedRepeatM : Nat := Id.run (repeatM (fun _ => pure (Sum.inr 0)) ())\n",
            "disallowed constant repeatM",
        ),
    ] {
        let err = audit_bypassing_preflight(
            &format!(
                "import Model\n{decl}def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n"
            ),
            clean_proof,
            false,
            false,
        )
        .unwrap_err();
        assert_eq!(
            (err.code, err.phase.as_str()),
            (1, "target-audit"),
            "{label}: {err}"
        );
        assert!(err.message.contains(expected), "{label}: {err}");
    }

    // 4. Unpaired `partial def Spec.orphan._unsafe_rec` rejected in Phase 1.
    let err = audit_bypassing_preflight(
        "import Model\npartial def Spec.orphan._unsafe_rec (n : Nat) : Nat := \
         Spec.orphan._unsafe_rec n\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        clean_proof,
        false,
        false,
    )
    .unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(
        err.message
            .contains("opaque declaration Spec.orphan._unsafe_rec")
            || err.message.contains("unsafe/partial"),
        "{err}"
    );

    // 5a. Safe Proof referencing a legitimately paired
    //     `Spec.wfHalf._unsafe_rec` is already rejected by Lean's kernel during
    //     `compile-Proof`; an `unsafe def` in `Spec` referencing
    //     `Spec.wfHalf._unsafe_rec` (or an `unsafe def Spec.foo._unsafe_rec`
    //     paired by name with total `Spec.foo`) compiles cleanly and is
    //     rejected by `"target-audit"` Phase 1.
    let wf_spec = r#"import Model
def Spec.wfHalf (n : Nat) : Nat :=
  if h : n = 0 then 0 else Spec.wfHalf (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p
"#;
    let err = audit_bypassing_preflight(
        &format!("{wf_spec}unsafe def Spec.sneak (n : Nat) : Nat := Spec.wfHalf._unsafe_rec n\n"),
        clean_proof,
        false,
        false,
    )
    .unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(
        err.message.contains("unsafe/partial") || err.message.contains("paired _unsafe_rec"),
        "{err}"
    );

    // 5b. `unsafe def Spec.foo._unsafe_rec` next to total `def Spec.foo` fails
    //     the `!ci.isUnsafe` pairing guard and is rejected by `"target-audit"`.
    let err = audit_bypassing_preflight(
        "import Model\ndef Spec.foo (n : Nat) : Nat := n\n\
         unsafe def Spec.foo._unsafe_rec (n : Nat) : Nat := n\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        clean_proof,
        false,
        false,
    )
    .unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(
        err.message
            .contains("unsafe/partial logical dependency Spec.foo._unsafe_rec"),
        "{err}"
    );

    // 6. Companion artifact part (`.olean.private`) on a target source module
    //    rejected by `"target-audit"`.
    let err = audit_bypassing_preflight(
        "import Model\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        clean_proof,
        false,
        true,
    )
    .unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(
        err.message.contains("companion artifact parts unsupported"),
        "{err}"
    );

    // 7. Forged `isModule = true` `.olean` on a target source module rejected
    //    by `"target-audit"`.
    let clean_spec = "import Model\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n";
    let _ = audit_bypassing_preflight(clean_spec, clean_proof, false, false).unwrap();
    let spec_olean = checker.stage().join("lib/Spec.olean");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let _ = fs::set_permissions(&spec_olean, fs::Permissions::from_mode(0o600));
    }
    let forge_script = checker.stage().join("ForgeIsModule.lean");
    fs::write(
        &forge_script,
        format!(
            r#"import Lean
open Lean in
def main : IO Unit := do
  let p := System.FilePath.mk {:?}
  let (data, _) ← readModuleData p
  saveModuleData p `Spec {{ data with isModule := true }}
"#,
            spec_olean.to_string_lossy()
        ),
    )
    .unwrap();
    checker
        .process(
            "forge-is-module",
            &[
                "--run".to_string(),
                forge_script.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let mut avail_single = BTreeMap::new();
    avail_single.insert("olean", spec_olean.to_string_lossy().into_owned());
    checker.admitted_mut().unwrap().artifacts.insert(
        "Spec".into(),
        ModuleArtifacts::from_available(&avail_single, "fixture", || "missing".into()).unwrap(),
    );
    let err = checker.inspect_target(&f.request).unwrap_err();
    assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{err}");
    assert!(
        err.message.contains("module-system artifact unsupported in Spec"),
        "expected pre-import isModule mismatch rejection: {err}"
    );
}

/// Phase 2 `"target-audit"` with `allow_sorry_in_proof`:
/// - rejects proof `sorry` when `allow_sorry_in_proof = false`;
/// - admits proof-only `sorry` when `allow_sorry_in_proof = true` and records
///   ALL proof declarations that reference `sorryAx` (verifying per-edge
///   admission before `visited` short-circuiting);
/// - emits `"sorryDeclarations": []` without `"sorryAx"` in `"axioms"` when a
///   proof under `allow_sorry_in_proof = true` uses zero `sorry`s; and
/// - rejects `sorry` in `Model`, `Capture`, or `Expected` even when
///   `allow_sorry_in_proof = true`.
#[test]
fn target_audit_phase2_allow_sorry_in_proof_tracks_multiple_helpers_and_isolates_phase1() {
    let multi_sorry_proof = "prelude\nimport Expected\n\
        theorem Proof.helperA : Captured.program.toNat = 7 := sorry\n\
        theorem Proof.helperB : Spec.specs Captured.program := sorry\n\
        theorem Proof.verify : Expected.claim := And.intro Proof.helperA Proof.helperB\n";

    // 1. Default (`allow_sorry_in_proof = false`) rejects proof `sorry`.
    let f_strict = Fixture::new(multi_sorry_proof);
    f_strict.reject_audit("unapproved axiom sorryAx from Init.Prelude");

    // 2. `allow_sorry_in_proof = true` admits BOTH proof helpers and reports
    //    both in sorted `sorryDeclarations`.
    let mut f_allow = Fixture::new(multi_sorry_proof);
    f_allow.request.allow_sorry_in_proof = true;
    let report = f_allow.run().unwrap();
    assert_eq!(report["replay"], true);
    assert_eq!(report["exactType"], true);
    assert_eq!(
        report["sorryDeclarations"],
        serde_json::json!(["Proof.helperA", "Proof.helperB"])
    );
    assert!(
        report["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .any(|a| a == "sorryAx"),
        "expected sorryAx in axioms: {report}"
    );

    // 3. Clean proof under `allow_sorry_in_proof = true` has empty
    //    `sorryDeclarations` and omits `sorryAx` from `axioms`.
    let mut f_clean = Fixture::new(PROOF);
    f_clean.request.allow_sorry_in_proof = true;
    let clean_report = f_clean.run().unwrap();
    assert_eq!(clean_report["sorryDeclarations"], serde_json::json!([]));
    assert!(
        clean_report["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .all(|a| a != "sorryAx"),
        "unexpected sorryAx in clean axioms: {clean_report}"
    );

    // 4. `sorry` in `Capture`, `Model`, or `Expected` (Phase 1) is rejected
    //    EVEN WITH `allow_sorry_in_proof = true`.
    let mut f_bad_capture = Fixture::new(multi_sorry_proof);
    f_bad_capture.request.allow_sorry_in_proof = true;
    f_bad_capture.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\ndef Captured.program : BitVec 8 := sorry\n",
    );
    f_bad_capture.reject_audit("unapproved axiom sorryAx from Init.Prelude");

    let mut f_bad_model = Fixture::new(multi_sorry_proof);
    f_bad_model.request.allow_sorry_in_proof = true;
    f_bad_model.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Prelude\nimport Init.Core\nimport Init.Data.BitVec.Basic\n\
         namespace Trusted.MirSemantics\n\
         structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
         theorem modelHelper : True := sorry\n\
         def UnitTheorem (c : Crate) : Prop := (fun _ : True => c.program.toNat = 7 ∧ c.specs c.program) modelHelper\n\
         end Trusted.MirSemantics\n",
    );
    f_bad_model.reject_audit("unapproved axiom sorryAx from Init.Prelude");

    let mut f_bad_expected = Fixture::new(multi_sorry_proof);
    f_bad_expected.request.allow_sorry_in_proof = true;
    f_bad_expected.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Model\nimport Captured\nimport Spec\n\
         theorem Expected.helper : True := sorry\n\
         def Expected.claim : Prop := (fun _ : True => Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)) Expected.helper\n",
    );
    f_bad_expected.reject_audit("unapproved axiom sorryAx from Init.Prelude");
}

#[test]
fn target_audit_reports_empty_and_unused_binding_spec_warnings() {
    let f_clean = Fixture::new(PROOF);
    let clean_report = f_clean.run().unwrap();
    assert_eq!(clean_report["specWarnings"], serde_json::json!([]));

    let mut f_unused = Fixture::new(PROOF);
    f_unused.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         def Spec.helper (unusedParam : Nat) (p : BitVec 8) : Prop := p &&& p = p\n\
         def Spec.specs (p : BitVec 8) : Prop := Spec.helper 0 p\n",
    );
    let unused_report = f_unused.run().unwrap();
    assert_eq!(unused_report["replay"], true);
    assert_eq!(
        unused_report["specWarnings"],
        serde_json::json!([{
            "code": "unused_spec_binding",
            "declaration": "Spec.helper",
            "message": "unused argument binding(s) in `Spec.helper`: unusedParam"
        }])
    );
}

#[test]
fn target_audit_rejects_wrong_program_arity_fail_closed() {
    let make_fixture = |extra_field_decl: &str, extra_field_val: &str| {
        let mut f = Fixture::new(
            "prelude\nimport Expected\ntheorem Proof.verify : Expected.claim := And.intro True.intro rfl\n",
        );
        f.set(
            "Model",
            TargetRole::Model,
            &format!(
                "prelude\nimport Init.Prelude\nimport Init.Core\n\
                 namespace Trusted.MirAst\n\
                 structure Program where\n\
                   bodies : List Nat\n\
                   entryDefId : Nat\n\
                   pointerWidthBits : Nat\n\
                   mirProfileVersion : Nat\n\
                   scope : Nat\n\
                   overflowChecks : Bool\n\
                   panicStrategy : Nat\n\
                 {extra_field_decl}\
                 end Trusted.MirAst\n\
                 namespace Trusted.MirSemantics\n\
                 structure Specs where\n\
                   safety : String → List Nat → Prop\n\
                   property : Trusted.MirAst.Program → Prop\n\
                 structure Crate where\n\
                   program : Trusted.MirAst.Program\n\
                   specs : Specs\n\
                 def UnitTheorem (c : Crate) : Prop :=\n\
                   c.specs.safety \"\" List.nil ∧ c.specs.property c.program\n\
                 end Trusted.MirSemantics\n"
            ),
        );
        f.set(
            "Captured",
            TargetRole::Capture,
            &format!(
                "prelude\nimport Model\n\
                 def Captured.program : Trusted.MirAst.Program :=\n\
                   Trusted.MirAst.Program.mk List.nil 0 64 1 0 false 0{extra_field_val}\n"
            ),
        );
        f.set(
            "Spec",
            TargetRole::Specification,
            "prelude\nimport Model\n\
             def Spec.specs : Trusted.MirSemantics.Specs :=\n\
               Trusted.MirSemantics.Specs.mk (fun _ _ => True) (fun p => p.pointerWidthBits = 64)\n",
        );
        f.set(
            "Expected",
            TargetRole::Expected,
            "prelude\nimport Model\nimport Captured\nimport Spec\n\
             def Expected.claim : Prop :=\n\
               Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
        );
        f
    };

    // A 7-field `Program` (wrong arity) must fail closed, never silently skip
    // linting.
    let f_wrong_arity = make_fixture("", "");
    f_wrong_arity.reject_audit("unexpected Program arity");

    // Control: 8-field `Program` (expected arity) passes cleanly.
    let f_ok = make_fixture("hasLocalPanicHandler : Bool\n", " true");
    let ok_report = f_ok.run().unwrap();
    assert_eq!(ok_report["replay"], true);
}
