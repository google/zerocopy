// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end coverage for `Trusted.MirSemantics.Contract` specifications.

use std::fs;

use serde_json::json;

use crate::helpers::{
    expect_verified, lean_source, new_workspace, run_verify_strs, subcrate_request_json,
    write_json_file,
};

const GUARDED_SOURCE: &str = "pub unsafe fn guarded_nz(flag: bool) -> bool {
    if !flag {
        unsafe { core::hint::unreachable_unchecked(); }
    }
    true
}

pub fn safe_second() -> bool {
    true
}
";

const GUARDED_SPEC_DECLS: &str = "namespace Spec

open Trusted.MirAst Trusted.MirSemantics

noncomputable def contract : FnContract := {
  safetyPre := fun q => q.args = [.bool true]
  postReturn := fun _ out => out.ret = .bool true
  effects := EffectMask.totalNormal
}

noncomputable def second_contract : FnContract := {
  postReturn := fun _ out => out.ret = .bool true
  effects := EffectMask.totalNormal
}

noncomputable def specs : Specs := ContractSpecs [{
  identity := \"rust-path-v1::guarded_nz\"
  contract := contract
  signature := some { isUnsafe := true, params := [.bool], ret := .bool }
}, {
  identity := \"rust-path-v1::safe_second\"
  contract := second_contract
  signature := some { isUnsafe := false, params := [], ret := .bool }
}]

end Spec";

// The two argument-shape cases that cannot be `ValidEntryArgs` for a single
// `bool` parameter are refuted by unfolding `checkArgsMatch` to
// `checkVal a .bool && false`; `cases hArgs` alone cannot solve that equation.
const GUARDED_PROOF_DECLS: &str = "namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, ?_, trivial⟩
  · intro defId body hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst body
      refine ⟨rfl, rfl, fun args hArgs hSafe => ?_⟩
      cases args with
      | nil => cases hArgs
      | cons a rest =>
        cases rest with
        | cons _ _ =>
          have h : (checkVal a .bool && false) = true := hArgs
          cases hChk : checkVal a .bool <;> rw [hChk] at h <;> cases h
        | nil =>
          have hTrue := hSafe rfl
          injection hTrue with hA
          subst hA
          exact (wellFormed_and_spec_of_wp (entryProgForBody Captured.program 0)
            { args := [.bool true] } 10
            (fun outcome => outcome = .returned ⟨.bool true, ⟨[]⟩⟩)
            (wpProg_of_execProg (fuel := 10) rfl)).1.1
    | succ defId' =>
      cases defId' with
      | zero =>
        injection hGet with hEq
        subst body
        refine ⟨rfl, rfl, fun args hArgs _ => ?_⟩
        cases args with
        | cons _ _ => cases hArgs
        | nil =>
          exact (wellFormed_and_spec_of_wp (entryProgForBody Captured.program 1)
            { args := [] } 10
            (fun outcome => outcome = .returned ⟨.bool true, ⟨[]⟩⟩)
            (wpProg_of_execProg (fuel := 10) rfl)).1.1
      | succ _ => cases hGet
  · refine ⟨0, Captured.program.bodies[0], rfl, rfl, rfl, ?_, ?_⟩
    · refine ⟨rfl, rfl, fun args hArgs => ?_⟩
      cases args with
      | nil => cases hArgs
      | cons a rest =>
        cases rest with
        | cons _ _ =>
          have h : (checkVal a .bool && false) = true := hArgs
          cases hChk : checkVal a .bool <;> rw [hChk] at h <;> cases h
        | nil =>
          refine ⟨fun hSafe => ?_, fun hBeh => ?_⟩
          · have hTrue := hSafe rfl
            injection hTrue with hA
            subst hA
            exact (wellFormed_and_spec_of_wp (entryProgForBody Captured.program 0)
              { args := [.bool true] } 10
              (fun outcome => outcome = .returned ⟨.bool true, ⟨[]⟩⟩)
              (wpProg_of_execProg (fuel := 10) rfl)).1.1
          · have hTrue := hBeh.1 rfl
            injection hTrue with hA
            subst hA
            have hOk := spec_and_behavior_of_wp_eq
              (p := entryProgForBody Captured.program 0)
              (q := { args := [.bool true] })
              (out := .returned ⟨.bool true, ⟨[]⟩⟩)
              (wpProg_of_execProg (fuel := 10) rfl)
            refine ⟨fun out hOut => ?_, fun _ => hOk.2.2.1⟩
            have hEq :=
              (hOk.2.2.2 (fun o => o = .returned ⟨.bool true, ⟨[]⟩⟩) rfl).2 out hOut
            subst hEq
            exact rfl
    · intro _
      exact ⟨[.bool true], rfl, fun _ => rfl, trivial⟩
  · refine ⟨1, Captured.program.bodies[1], rfl, rfl, rfl, ?_, ?_⟩
    · refine ⟨rfl, rfl, fun args hArgs => ?_⟩
      cases args with
      | cons _ _ => cases hArgs
      | nil =>
        have hOk := spec_and_behavior_of_wp_eq
          (p := entryProgForBody Captured.program 1)
          (q := { args := [] })
          (out := .returned ⟨.bool true, ⟨[]⟩⟩)
          (wpProg_of_execProg (fuel := 10) rfl)
        refine ⟨fun _ => hOk.1, fun _ => ⟨fun out hOut => ?_, fun _ => hOk.2.2.1⟩⟩
        have hEq :=
          (hOk.2.2.2 (fun o => o = .returned ⟨.bool true, ⟨[]⟩⟩) rfl).2 out hOut
        subst hEq
        exact rfl
    · intro _
      exact ⟨[], rfl, fun _ => trivial, trivial⟩

end Proof";

#[test]
fn contract_specs_verify_unsafe_guard_end_to_end() {
    let staged = new_workspace("anneal-contract-specs-").stage().unwrap();
    let work = staged.work_dir();
    let rust = work.join("rust");
    let lean = work.join("lean");
    fs::create_dir_all(&rust).unwrap();
    fs::create_dir_all(&lean).unwrap();
    fs::write(rust.join("lib.rs"), GUARDED_SOURCE).unwrap();
    fs::write(
        lean.join("Spec.lean"),
        lean_source("import Trusted.MirSemantics", GUARDED_SPEC_DECLS),
    )
    .unwrap();
    fs::write(
        lean.join("Proof.lean"),
        lean_source("import Expected\nimport Anneal.MirWp", GUARDED_PROOF_DECLS),
    )
    .unwrap();
    let req = subcrate_request_json(&rust, "lib.rs", "guarded", &lean);
    let req_path = write_json_file(&work.join("req.json"), &req);

    let res = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    let ok = expect_verified(&res, "crate_verified", true);
    assert_eq!(json!(ok.taint_reasons), json!([]), "{ok:?}");
}
