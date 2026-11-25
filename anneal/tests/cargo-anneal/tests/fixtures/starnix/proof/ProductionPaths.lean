-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import InitialCache
public import Anneal.MirSymExec
public import Anneal.MirSymExec.Bits
import Init.Data.Option.Lemmas

@[expose] public section

namespace ProductionPaths

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Endianness
  ProductionReduction

/-!
Each concrete `(flag, width)` control choice runs the captured body over a
free input word through the bundled `Anneal.MirSymExec` executor. The kernel
evaluates `symRun` on `sourceBody` itself, so no local, block or statement
index, and no state vector, appears here. Nothing here assumes a result;
`ProductionEndpoints` fixes the expected words.
-/

/-- The free input word: symbolic variable `0` of type `u64`. -/
noncomputable def inputWord : Anneal.MirSymExec.SymScalar := .var 0 .i64 false

/-- Entry arguments with a concrete flag and width and a symbolic value. -/
noncomputable def sArgs (flag : Bool) (width : Nat) :
    List Anneal.MirSymExec.SymVal :=
  [.conc (.bool flag), .conc (dataWidthVal width), .scalar inputWord]

/-- Step budget; a run stops at its first return, so slack costs nothing. -/
def fuel : Nat := 4096

/-- The `u64` word the source returns on one control path, if supported. -/
noncomputable def pathWord (flag : Bool) (width : Nat) :
    Option Anneal.MirSymExec.SymScalar :=
  match Anneal.MirSymExec.symRun sourceBody fuel
      (Anneal.MirSymExec.symEntry sourceBody (sArgs flag width)) with
  | .ret v =>
    match v.asScalar? with
    | some s =>
      if Anneal.MirTotal.intWidthBeqComp s.width .i64 &&
          Anneal.MirTotal.boolBeqComp s.signed false then some s else none
    | none => none
  | _ => none

theorem sArgs_eval (flag : Bool) (width : Nat) (value : Word) :
    (sArgs flag width).map
        (Anneal.MirSymExec.SymVal.eval (Anneal.MirSymExec.wordEnv value)) =
      endianArgs flag width value := by
  have hIn : Anneal.MirSymExec.SymVal.eval (Anneal.MirSymExec.wordEnv value)
      (.scalar inputWord) = u64Val value := by
    show Val.scalar ⟨.i64, false, Anneal.MirTotal.truncateBitsComp .i64
      (BitVec.ofNat 128 value.toNat)⟩ = _
    rw [Anneal.MirSymExec.truncateBitsComp_bitVec_of_lt value (by decide)]
    rfl
  show [Val.bool flag, dataWidthVal width,
    Anneal.MirSymExec.SymVal.eval (Anneal.MirSymExec.wordEnv value)
      (.scalar inputWord)] = _
  rw [hIn]
  rfl

theorem path_sound {flag : Bool} {width : Nat} {s : Anneal.MirSymExec.SymScalar}
    (h : pathWord flag width = some s) (value : Word) :
    Safe sourceBody (endianArgs flag width value) ∧
      Returns sourceBody (endianArgs flag width value)
        (u64Val (s.wordEval value)) := by
  unfold pathWord at h
  cases hRun : Anneal.MirSymExec.symRun sourceBody fuel
      (Anneal.MirSymExec.symEntry sourceBody (sArgs flag width)) with
  | step _ => rw [hRun] at h; cases h
  | stuck => rw [hRun] at h; cases h
  | ret v =>
    rw [hRun] at h
    dsimp only at h
    cases hS : v.asScalar? with
    | none => rw [hS] at h; cases h
    | some s' =>
      rw [hS] at h
      dsimp only at h
      have hMeta := Anneal.MirSymExec.symVal_asScalar?_sound hS
        (Anneal.MirSymExec.wordEnv value)
      cases hTy : (Anneal.MirTotal.intWidthBeqComp s'.width IntWidth.i64 &&
          Anneal.MirTotal.boolBeqComp s'.signed false) with
      | false => rw [hTy] at h; cases h
      | true =>
        rw [hTy] at h
        have hEq : s' = s := Option.some.inj h
        subst hEq
        have hb := (Bool.and_eq_true _ _).mp hTy
        have hW : s'.width = IntWidth.i64 := by
          have hw := hb.1
          rw [Anneal.MirTotal.intWidthBeqComp_eq] at hw
          exact Anneal.MirWp.IntWidth.beq_iff.mp hw
        have hSg : s'.signed = false := by
          have hs := hb.2
          rw [Anneal.MirTotal.boolBeqComp_eq] at hs
          exact beq_iff_eq.mp hs
        have hRuns := Anneal.MirSymExec.symRun_entry hRun
          (Anneal.MirSymExec.wordEnv value)
        rw [sArgs_eval, hMeta.2,
          Anneal.MirSymExec.SymScalar.wordEval_scalar_eq hW hSg hMeta.1] at hRuns
        exact run_initial_success hRuns

end ProductionPaths

end
