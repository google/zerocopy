-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import Anneal.MirWp.Execution

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

private theorem valid_enum_0 :
    ValidEntryArgs Captured.body_0
      [.enumVal
        { id := 873866302, discrWidth := .isize, discrSigned := true,
          tagRepr := .zeroSized, discriminants := [0] }
        0] := by
  unfold ValidEntryArgs
  change checkArgsMatch [_] [_] = true
  rw [checkArgsMatch_cons_iff]
  exact ⟨_, _, rfl, checkVal_enum_iff.mpr ⟨rfl, ⟨⟨0, by decide⟩, rfl⟩⟩, rfl⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id body found
    cases id with
    | zero =>
      injection found with hEq
      subst hEq
      refine bodyVerified_of_safe rfl rfl (fun args valid _ => ?_)
      unfold ValidEntryArgs at valid
      change checkArgsMatch args [_] = true at valid
      rw [checkArgsMatch_cons_iff] at valid
      let ⟨v, rest, hCons, hv, hNil⟩ := valid
      rw [checkArgsMatch_nil_iff] at hNil
      subst hCons; subst hNil
      rw [checkVal_enum_iff] at hv
      let ⟨_, idx, hvEq⟩ := hv
      subst hvEq
      cases idx with
      | mk val hLt =>
        cases val with
        | zero =>
          have hRun :
              Runs .little Captured.body_0 4
                [.enumVal
                  { id := 873866302, discrWidth := .isize, discrSigned := true,
                    tagRepr := .zeroSized, discriminants := [0] }
                  0]
                (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) := rfl
          exact (run_initial_success hRun).1
        | succ _ => exact False.elim (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hLt))
    | succ id => cases found
  · refine ⟨Captured.body_0, _, rfl, rfl, rfl, rfl, ?_⟩
    have hRun :
        Runs .little Captured.body_0 4
          [.enumVal
            { id := 873866302, discrWidth := .isize, discrSigned := true,
              tagRepr := .zeroSized, discriminants := [0] }
            0]
          (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) := rfl
    exact behavior_of_returns rfl rfl valid_enum_0 (run_initial_success hRun).2

end Proof
