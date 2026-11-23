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

private abbrev enumE : EnumTy :=
  { id := 1008302603, discrWidth := .isize, discrSigned := true,
    tagRepr := .scalar .i8 false, discriminants := [0, 1] }

private theorem valid_enum (idx : Fin 2) :
    ValidEntryArgs Captured.body_0 [.enumVal enumE idx.val] := by
  unfold ValidEntryArgs
  change checkArgsMatch [_] [_] = true
  rw [checkArgsMatch_cons_iff]
  exact ⟨_, _, rfl, checkVal_enum_iff.mpr ⟨rfl, ⟨idx, rfl⟩⟩, rfl⟩

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
              Runs Captured.body_0 12 [.enumVal enumE 0]
                (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) := rfl
          exact (run_initial_success hRun).1
        | succ val' =>
          cases val' with
          | zero =>
            have hRun :
                Runs Captured.body_0 12 [.enumVal enumE 1]
                  (.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩) := rfl
            exact (run_initial_success hRun).1
          | succ _ =>
            exact False.elim
              (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hLt)))
    | succ id => cases found
  · refine ⟨Captured.body_0, rfl, rfl, ?_, ?_⟩
    · have hRun :
          Runs Captured.body_0 12 [.enumVal enumE 0]
            (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) := rfl
      exact behavior_of_returns rfl rfl (valid_enum ⟨0, by decide⟩)
        (run_initial_success hRun).2
    · have hRun :
          Runs Captured.body_0 12 [.enumVal enumE 1]
            (.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩) := rfl
      exact behavior_of_returns rfl rfl (valid_enum ⟨1, by decide⟩)
        (run_initial_success hRun).2

end Proof
