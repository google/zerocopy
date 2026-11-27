// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Specification vacuity inspection.

use super::*;

/// Verifies `inspectSpecVacuity` handles `BitVec`, `Option`, `Exists`, `Nat.le`
/// and `BitVec` inequalities/disjunctions while avoiding false positives on
/// uninhabited `Fin 0` and custom opaque orderings, and surfaces truncation on
/// opaque or over-long captured programs.
#[test]
fn inspect_spec_vacuity_handles_bitvec_option_exists_le_and_fin0() {
    let make_specs_fixture = |spec_expr: &str| {
        let mut f = Fixture::new(
            "prelude\nimport Expected\n\
             theorem Proof.verify : Expected.claim := ⟨rfl, .inr trivial, .inr trivial⟩\n",
        );
        f.set(
            "Model",
            TargetRole::Model,
            "prelude\nimport Init.Data.BitVec.Basic\n\
             namespace Trusted.MirAst\n\
             structure Program where\n  \
               bodies : List Nat\n  \
               pointerWidthBits : Nat\n  \
               mirProfileVersion : Nat\n  \
               entryDefId : Nat\n  \
               scope : Nat\n  \
               overflowChecks : Bool\n  \
               panicStrategy : Nat\n  \
               hasLocalPanicHandler : Bool\n\
             opaque customLe : Nat → Nat → Prop\n\
             end Trusted.MirAst\n\
             namespace Trusted.MirSemantics\n\
             structure Val where\n  raw : Nat\n\
             structure Specs where\n  \
               safety : String → List Val → Prop\n  \
               property : Trusted.MirAst.Program → Prop\n\
             structure Crate where\n  \
               program : Trusted.MirAst.Program\n  \
               specs : Specs\n\
             def UnitTheorem (c : Crate) : Prop :=\n  \
               c.program.bodies = [] ∧ (c.specs.safety \"\" [] ∨ True) ∧ \
                 (c.specs.property c.program ∨ True)\n\
             end Trusted.MirSemantics\n",
        );
        f.set(
            "Captured",
            TargetRole::Capture,
            "prelude\nimport Model\n\
             def Captured.program : Trusted.MirAst.Program := ⟨[], 64, 1, 0, 0, false, 0, false⟩\n",
        );
        f.set("Spec", TargetRole::Specification, spec_expr);
        f.set(
            "Expected",
            TargetRole::Expected,
            "prelude\nimport Model\nimport Captured\nimport Spec\n\
             def Expected.claim : Prop :=\n  \
               Trusted.MirSemantics.UnitTheorem\n    \
                 (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
        );
        f
    };

    let rep_bv = make_specs_fixture(
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
           ⟨fun _ _ => (∀ _x : BitVec 64, False) ∨ (∀ _o : Option Nat, 1 ≤ 0) ∨ \
             BitVec.ofNat 64 0 = BitVec.ofNat 64 1,\n   \
            fun _p => ∃ _b : BitVec 64, True⟩\n",
    )
    .run()
    .unwrap();
    assert!(
        rep_bv["specWarnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| w["code"] == "unsatisfiable_safety"),
        "expected BitVec/Option/Nat.le unsatisfiable_safety: {rep_bv}"
    );
    assert!(
        rep_bv["specWarnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| w["code"] == "trivial_property"),
        "expected Exists BitVec trivial_property: {rep_bv}"
    );

    // 2. Uninhabited `Fin 0`, modulo-wrapping `(256 : BitVec 8) = 0`, and
    //    custom opaque `LE Nat` must NOT emit `unsatisfiable_safety`.
    let rep_non_vacuous = make_specs_fixture(
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
           ⟨fun _ _ => (∀ _x : Fin 0, False) ∧\n      \
              (256 : BitVec 8) = (0 : BitVec 8) ∧\n      \
              (letI : LE Nat := ⟨Trusted.MirAst.customLe⟩; (1 : Nat) ≤ (0 : Nat)),\n   \
            fun p => p.bodies = []⟩\n",
    )
    .run()
    .unwrap();
    assert_eq!(
        rep_non_vacuous["specWarnings"],
        serde_json::json!([]),
        "unexpected vacuity warning on Fin 0 / wrapping BitVec / custom LE: {rep_non_vacuous}"
    );

    // 3. Inhabited `Fin 1` in `∀ _ : Fin 1, False` triggers
    //    `unsatisfiable_safety`, while `(256 : BitVec 8) = 0` in `property`
    //    triggers `trivial_property`.
    let rep_fin1 = make_specs_fixture(
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
           ⟨fun _ _ => ∀ _x : Fin 1, False,\n   \
            fun _p => (256 : BitVec 8) = (0 : BitVec 8)⟩\n",
    )
    .run()
    .unwrap();
    let fin1_warnings = rep_fin1["specWarnings"].as_array().unwrap();
    assert!(
        fin1_warnings.iter().any(|w| w["code"] == "unsatisfiable_safety"),
        "expected Fin 1 unsatisfiable_safety: {rep_fin1}"
    );
    assert!(
        fin1_warnings.iter().any(|w| w["code"] == "trivial_property"),
        "expected trivial_property on (256 : BitVec 8) = 0: {rep_fin1}"
    );

    // 4. `Trusted.MirSemantics.Val` is recognized as an inhabited domain.
    let rep_val = make_specs_fixture(
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
           ⟨fun _ _ => ∀ _v : Trusted.MirSemantics.Val, False, fun p => p.bodies = []⟩\n",
    )
    .run()
    .unwrap();
    assert!(
        rep_val["specWarnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| w["code"] == "unsatisfiable_safety"),
        "expected Trusted.MirSemantics.Val unsatisfiable_safety: {rep_val}"
    );
}

/// Verifies `inspectSpecVacuity` reduces concrete `BitVec` strict inequalities
/// into `Nat.le` and emits `vacuity_check_truncated` for opaque or >256-body
/// captured programs.
#[test]
fn inspect_spec_vacuity_checks_bitvec_lt_and_truncation() {
    let mut f_bv_lt = Fixture::new(
        "prelude\nimport Expected\n\
         theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
    );
    f_bv_lt.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\n\
         namespace Trusted.MirAst\n\
         structure Program where\n  \
           bodies : List Nat\n  \
           pointerWidthBits : Nat\n  \
           mirProfileVersion : Nat\n  \
           entryDefId : Nat\n  \
           scope : Nat\n  \
           overflowChecks : Bool\n  \
           panicStrategy : Nat\n  \
           hasLocalPanicHandler : Bool\n\
         end Trusted.MirAst\n\
         namespace Trusted.MirSemantics\n\
         structure Val where\n  raw : Nat\n\
         structure Specs where\n  \
           safety : String → List Val → Prop\n  \
           property : Trusted.MirAst.Program → Prop\n\
         structure Crate where\n  \
           program : Trusted.MirAst.Program\n  \
           specs : Specs\n\
         def UnitTheorem (c : Crate) : Prop :=\n  \
           (c.specs.safety \"\" [] ∨ True) ∧ (c.specs.property c.program ∨ True)\n\
         end Trusted.MirSemantics\n",
    );
    f_bv_lt.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\n\
         def Captured.program : Trusted.MirAst.Program := ⟨[], 64, 1, 0, 0, false, 0, false⟩\n",
    );
    f_bv_lt.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
           ⟨fun _ _ => (1 : BitVec 8) < (0 : BitVec 8), fun p => p.bodies = []⟩\n",
    );
    f_bv_lt.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Model\nimport Captured\nimport Spec\n\
         def Expected.claim : Prop :=\n  \
           Trusted.MirSemantics.UnitTheorem\n    \
             (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
    );
    f_bv_lt.set(
        "Proof",
        TargetRole::Proof,
        "prelude\nimport Expected\n\
         theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
    );
    let rep_bv_lt = f_bv_lt.run().unwrap();
    assert!(
        rep_bv_lt["specWarnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| w["code"] == "unsatisfiable_safety"),
        "expected (1 : BitVec 8) < 0 unsatisfiable_safety: {rep_bv_lt}"
    );

    // 2. Non-reducible `Captured.program.bodies` list emits
    //    `vacuity_check_truncated` rather than dropping `Specs.safety`
    //    per-body checks silently, while an opaque outer `Captured.program`
    //    fails closed with `unexpected Program constructor`.
    let make_trunc_prog_fixture = |extra_decl: &str, prog_expr: &str| {
        let mut f = Fixture::new(
            "prelude\nimport Expected\n\
             theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
        );
        f.set(
            "Model",
            TargetRole::Model,
            &format!(
                "prelude\nimport Init.Data.BitVec.Basic\n\
                 namespace Trusted.MirAst\n\
                 structure Program where\n  \
                   bodies : List Nat\n  \
                   pointerWidthBits : Nat\n  \
                   mirProfileVersion : Nat\n  \
                   entryDefId : Nat\n  \
                   scope : Nat\n  \
                   overflowChecks : Bool\n  \
                   panicStrategy : Nat\n  \
                   hasLocalPanicHandler : Bool\n\
                 {extra_decl}\
                 end Trusted.MirAst\n\
                 namespace Trusted.MirSemantics\n\
                 structure Val where\n  raw : Nat\n\
                 structure Specs where\n  \
                   safety : String → List Val → Prop\n  \
                   property : Trusted.MirAst.Program → Prop\n\
                 structure Crate where\n  \
                   program : Trusted.MirAst.Program\n  \
                   specs : Specs\n\
                 def UnitTheorem (c : Crate) : Prop :=\n  \
                   (c.specs.safety \"\" [] ∨ True) ∧ (c.specs.property c.program ∨ True)\n\
                 end Trusted.MirSemantics\n"
            ),
        );
        f.set(
            "Captured",
            TargetRole::Capture,
            &format!("prelude\nimport Model\ndef Captured.program : Trusted.MirAst.Program := {prog_expr}\n"),
        );
        f.set(
            "Spec",
            TargetRole::Specification,
            "prelude\nimport Model\n\
             def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
               ⟨fun _ _ => True, fun p => p.bodies = []⟩\n",
        );
        f.set(
            "Expected",
            TargetRole::Expected,
            "prelude\nimport Model\nimport Captured\nimport Spec\n\
             def Expected.claim : Prop :=\n  \
               Trusted.MirSemantics.UnitTheorem\n    \
                 (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
        );
        f.set(
            "Proof",
            TargetRole::Proof,
            "prelude\nimport Expected\n\
             theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
        );
        f
    };
    let f_trunc = make_trunc_prog_fixture(
        "opaque opaqueBodies : List Nat := []\n",
        "⟨Trusted.MirAst.opaqueBodies, 64, 1, 0, 0, false, 0, false⟩",
    );
    let rep_trunc = f_trunc.run().unwrap();
    assert!(
        rep_trunc["specWarnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| {
                w["code"] == "vacuity_check_truncated"
                    && w["message"]
                        .as_str()
                        .unwrap_or("")
                        .contains("unreducible Captured.program.bodies list")
            }),
        "expected unreducible Captured.program.bodies vacuity_check_truncated: {rep_trunc}"
    );
    let f_opaque_prog = make_trunc_prog_fixture(
        "opaque opaqueProg : Program := ⟨[], 64, 1, 0, 0, false, 0, false⟩\n",
        "Trusted.MirAst.opaqueProg",
    );
    f_opaque_prog.reject_audit("unexpected Program constructor");

    // 3. Captured program exceeding 256 bodies emits explicit
    //    `vacuity_check_truncated` ("after 256 captured bodies").
    let mut f_257 = Fixture::new(
        "prelude\nimport Expected\n\
         theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
    );
    f_257.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\n\
         namespace Trusted.MirAst\n\
         structure Body where\n  \
           argumentCount : Nat\n  \
           locals : List Nat\n  \
           basicBlocks : List Nat\n  \
           isUnsafe : Bool\n  \
           identity : String\n\
         structure Program where\n  \
           bodies : List Body\n  \
           pointerWidthBits : Nat\n  \
           mirProfileVersion : Nat\n  \
           entryDefId : Nat\n  \
           scope : String\n  \
           overflowChecks : Bool\n  \
           panicStrategy : Nat\n  \
           hasLocalPanicHandler : Bool\n\
         def app : List Body → List Body → List Body\n  \
           | [], ys => ys\n  \
           | x :: xs, ys => x :: app xs ys\n\
         def sampleBody : Body := ⟨0, [], [], true, \"fn\"⟩\n\
         def b1 : List Body := [sampleBody]\n\
         def b2 : List Body := app b1 b1\n\
         def b4 : List Body := app b2 b2\n\
         def b8 : List Body := app b4 b4\n\
         def b16 : List Body := app b8 b8\n\
         def b32 : List Body := app b16 b16\n\
         def b64 : List Body := app b32 b32\n\
         def b128 : List Body := app b64 b64\n\
         def b257 : List Body := sampleBody :: app b128 b128\n\
         end Trusted.MirAst\n\
         namespace Trusted.MirSemantics\n\
         structure Val where\n  raw : Nat\n\
         structure Specs where\n  \
           safety : String → List Val → Prop\n  \
           property : Trusted.MirAst.Program → Prop\n\
         structure Crate where\n  \
           program : Trusted.MirAst.Program\n  \
           specs : Specs\n\
         def UnitTheorem (c : Crate) : Prop :=\n  \
           (c.specs.safety \"\" [] ∨ True) ∧ (c.specs.property c.program ∨ True)\n\
         end Trusted.MirSemantics\n",
    );
    f_257.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\n\
         def Captured.program : Trusted.MirAst.Program :=\n  \
           ⟨Trusted.MirAst.b257, 64, 1, 0, \"\", false, 0, false⟩\n",
    );
    f_257.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
           ⟨fun _ _ => True, fun p => p.bodies = []⟩\n",
    );
    f_257.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Model\nimport Captured\nimport Spec\n\
         def Expected.claim : Prop :=\n  \
           Trusted.MirSemantics.UnitTheorem\n    \
             (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
    );
    f_257.set(
        "Proof",
        TargetRole::Proof,
        "prelude\nimport Expected\n\
         theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
    );
    let rep_257 = f_257.run().unwrap();
    assert!(
        rep_257["specWarnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| {
                w["code"] == "vacuity_check_truncated"
                    && w["message"]
                        .as_str()
                        .unwrap_or("")
                        .contains("after 256 captured bodies")
            }),
        "expected after-256 vacuity_check_truncated: {rep_257}"
    );

    // 4. Unsafe bodies with empty `identity` (`""`) fall back to `body#<idx>`
    //    across both `unsatisfiable_safety` and wide-body
    //    `vacuity_check_truncated` (>32 args) so `validate_target_audit_report`
    //    never rejects an empty `"body"` string operationally.
    let mut f_empty_id = Fixture::new(
        "prelude\nimport Expected\n\
         theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
    );
    f_empty_id.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\n\
         namespace Trusted.MirAst\n\
         structure Body where\n  \
           argumentCount : Nat\n  \
           locals : List Nat\n  \
           basicBlocks : List Nat\n  \
           isUnsafe : Bool\n  \
           identity : String\n\
         structure Program where\n  \
           bodies : List Body\n  \
           pointerWidthBits : Nat\n  \
           mirProfileVersion : Nat\n  \
           entryDefId : Nat\n  \
           scope : String\n  \
           overflowChecks : Bool\n  \
           panicStrategy : Nat\n  \
           hasLocalPanicHandler : Bool\n\
         end Trusted.MirAst\n\
         namespace Trusted.MirSemantics\n\
         structure Val where\n  raw : Nat\n\
         structure Specs where\n  \
           safety : String → List Val → Prop\n  \
           property : Trusted.MirAst.Program → Prop\n\
         structure Crate where\n  \
           program : Trusted.MirAst.Program\n  \
           specs : Specs\n\
         def UnitTheorem (c : Crate) : Prop :=\n  \
           (c.specs.safety \"\" [] ∨ True) ∧ (c.specs.property c.program ∨ True)\n\
         end Trusted.MirSemantics\n",
    );
    f_empty_id.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\n\
         def Captured.program : Trusted.MirAst.Program :=\n  \
           ⟨[⟨0, [], [], true, \"\"⟩, ⟨33, [], [], true, \"\"⟩], 64, 1, 0, \"\", false, 0, false⟩\n",
    );
    f_empty_id.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.Specs :=\n  \
           ⟨fun id _ => if id == \"\" then False else True, fun p => p.bodies = []⟩\n",
    );
    f_empty_id.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Model\nimport Captured\nimport Spec\n\
         def Expected.claim : Prop :=\n  \
           Trusted.MirSemantics.UnitTheorem\n    \
             (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
    );
    let rep_empty_id = f_empty_id.run().unwrap();
    let empty_id_warnings = rep_empty_id["specWarnings"].as_array().unwrap();
    assert!(
        empty_id_warnings
            .iter()
            .any(|w| w["code"] == "unsatisfiable_safety" && w["body"] == "body#0"),
        "expected body#0 fallback on empty-identity unsatisfiable_safety: {rep_empty_id}"
    );
    assert!(
        empty_id_warnings
            .iter()
            .any(|w| w["code"] == "vacuity_check_truncated" && w["body"] == "body#1"),
        "expected body#1 fallback on empty-identity vacuity_check_truncated: {rep_empty_id}"
    );

    // 5. `SpecsV2` (`UnitTheoremV2` / `CrateV2` / `Query`) also emits
    //    `vacuity_check_truncated` with `SpecsV2.safety` prefix when an unsafe
    //    body exceeds `maxCheckedArgs` (`32`).
    let mut f_v2_trunc = Fixture::new(
        "prelude\nimport Expected\n\
         theorem Proof.verify : Expected.claim := ⟨.inr trivial, .inr trivial⟩\n",
    );
    f_v2_trunc.request.canonical_root = "Trusted.MirSemantics.UnitTheoremV2".into();
    f_v2_trunc.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\n\
         namespace Trusted.MirAst\n\
         structure Body where\n  \
           argumentCount : Nat\n  \
           locals : List Nat\n  \
           basicBlocks : List Nat\n  \
           isUnsafe : Bool\n  \
           identity : String\n\
         structure Program where\n  \
           bodies : List Body\n  \
           pointerWidthBits : Nat\n  \
           mirProfileVersion : Nat\n  \
           entryDefId : Nat\n  \
           scope : String\n  \
           overflowChecks : Bool\n  \
           panicStrategy : Nat\n  \
           hasLocalPanicHandler : Bool\n\
         end Trusted.MirAst\n\
         namespace Trusted.MirSemantics\n\
         structure Val where\n  raw : Nat\n\
         structure CallerMemory where\n  raw : Nat\n\
         structure Query where\n  \
           args : List Val\n  \
           callerMem : CallerMemory\n\
         structure SpecsV2 where\n  \
           safety : String → Query → Prop\n  \
           property : Trusted.MirAst.Program → Prop\n\
         structure Crate where\n  \
           program : Trusted.MirAst.Program\n  \
           specs : SpecsV2\n\
         structure CrateV2 where\n  \
           program : Trusted.MirAst.Program\n  \
           specs : SpecsV2\n\
         def UnitTheoremV2 (c : CrateV2) : Prop :=\n  \
           (c.specs.safety \"\" ⟨[], ⟨0⟩⟩ ∨ True) ∧ (c.specs.property c.program ∨ True)\n\
         end Trusted.MirSemantics\n",
    );
    f_v2_trunc.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\n\
         def Captured.program : Trusted.MirAst.Program :=\n  \
           ⟨[⟨33, [], [], true, \"wide_v2_fn\"⟩], 64, 2, 0, \"\", false, 0, false⟩\n",
    );
    f_v2_trunc.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         def Spec.specs : Trusted.MirSemantics.SpecsV2 :=\n  \
           ⟨fun _ _ => True, fun p => p.bodies = []⟩\n",
    );
    f_v2_trunc.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Model\nimport Captured\nimport Spec\n\
         def Expected.claim : Prop :=\n  \
           Trusted.MirSemantics.UnitTheoremV2\n    \
             (Trusted.MirSemantics.CrateV2.mk Captured.program Spec.specs)\n",
    );
    let rep_v2_trunc = f_v2_trunc.run().unwrap();
    assert!(
        rep_v2_trunc["specWarnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|w| {
                w["code"] == "vacuity_check_truncated"
                    && w["body"] == "wide_v2_fn"
                    && w["message"]
                        .as_str()
                        .unwrap_or("")
                        .contains("SpecsV2.safety per-body lint skipped unsafe body")
            }),
        "expected SpecsV2 vacuity_check_truncated: {rep_v2_trunc}"
    );
}
