-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import GuardRefuteBase
import Trusted.MirSemantics.Contract

/-!
# Positive Sanity Check for `Trusted.MirSemantics.Contract` Guard Mutations

Confirms that a minimal valid `ContractSpecs` + `UnitTheorem` proof obligation
continues to compile and succeed under every single-guard weakening in
`Trusted/MirSemantics/Contract.lean`.

Why `first | exact trivial | ...` is used in tactic mode: individual `Contract`
mutants weaken conjunction or implication targets (such as postconditions,
inhabitation checks, or `ContractEntriesSatisfied`) to `True`, which must not
break positive sanity compilation when proving a valid contract holds.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Valid safe zero-argument unit body with pre-initialized `()` return
place. -/
noncomputable def contractSanityBody : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := false
  identity := "guard_mutation::contract_sanity"
}

/-- Unit-scoped program wrapping `contractSanityBody`. -/
noncomputable def contractSanityProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [contractSanityBody]
}

/-- Valid total-normal contract matching `contractSanityBody`. -/
noncomputable def contractSanitySpec : FnContract := {
  postReturn := fun _ out => out.ret = .unit
  effects := EffectMask.totalNormal
}

/-- Valid signature-checked contract entry matching `contractSanityBody`. -/
noncomputable def contractSanityEntry : ContractEntry := {
  identity := "guard_mutation::contract_sanity"
  contract := contractSanitySpec
  signature := some {
    isUnsafe := false
    params := []
    ret := .unit
  }
}

private noncomputable def contractSanityInitState : State := {
  frames := [{
    defId := 0
    blockIdx := 0
    stmtIdx := 0
    locals := [.immediate (some .unit)]
  }]
  callerMem := ⟨[]⟩
  mem := entryMemory
}

private theorem contract_sanity_reaches_eq :
    ∀ {s : State},
      Reaches (entryProgForBody contractSanityProg 0)
        contractSanityInitState s →
      s = contractSanityInitState := by
  intro s hReach
  induction hReach with
  | refl => rfl
  | @tail s₂ s₃ _ hStep ih =>
    subst ih
    let ⟨c, hChoice, hEval⟩ := hStep
    subst hChoice
    have hDone :
        evalStep (entryProgForBody contractSanityProg 0) 0
          contractSanityInitState =
          .done (.returned ⟨.unit, ⟨[]⟩⟩) := rfl
    rw [hDone] at hEval
    cases hEval

private theorem contract_sanity_wellformed :
    WellFormed (entryProgForBody contractSanityProg 0) queryEmpty := by
  refine ⟨⟨contractSanityInitState, rfl, fun s hReach => ?_⟩,
    fun k hFault => ?_⟩
  · have hEqS := contract_sanity_reaches_eq hReach
    subst hEqS
    exact ⟨0, rfl⟩
  · unfold ReachesResult at hFault
    have hInit :
        initState (entryProgForBody contractSanityProg 0) queryEmpty =
          .ok contractSanityInitState := rfl
    rw [hInit] at hFault
    let ⟨s', hReach, ⟨c, hChoice, hEval⟩⟩ := hFault
    subst hChoice
    have hEqS := contract_sanity_reaches_eq hReach
    subst hEqS
    have hDone :
        evalStep (entryProgForBody contractSanityProg 0) 0
          contractSanityInitState =
          .done (.returned ⟨.unit, ⟨[]⟩⟩) := rfl
    rw [hDone] at hEval
    cases hEval

private theorem contract_sanity_behavior :
    ∀ out : TerminalOut,
      Behavior (entryProgForBody contractSanityProg 0) queryEmpty out →
      out = .returned ⟨.unit, ⟨[]⟩⟩ := by
  intro out hBeh
  unfold Behavior ReachesResult at hBeh
  have hInit :
      initState (entryProgForBody contractSanityProg 0) queryEmpty =
        .ok contractSanityInitState := rfl
  rw [hInit] at hBeh
  let ⟨s', hReach, ⟨c, hChoice, hEval⟩⟩ := hBeh
  subst hChoice
  have hEqS := contract_sanity_reaches_eq hReach
  subst hEqS
  have hDone :
      evalStep (entryProgForBody contractSanityProg 0) 0
        contractSanityInitState =
        .done (.returned ⟨.unit, ⟨[]⟩⟩) := rfl
  rw [hDone] at hEval
  cases hEval
  rfl

private theorem contract_sanity_not_diverges :
    ¬ Diverges (entryProgForBody contractSanityProg 0) queryEmpty := by
  intro ⟨s₀, hInit, trace, hTr0, hSteps⟩
  have hInitRefl :
      initState (entryProgForBody contractSanityProg 0) queryEmpty =
        .ok contractSanityInitState := rfl
  rw [hInitRefl] at hInit
  injection hInit with hEq
  rw [← hEq] at hTr0
  let ⟨c, hChoice, hEval⟩ := hSteps 0
  subst hChoice
  rw [hTr0] at hEval
  have hDone :
      evalStep (entryProgForBody contractSanityProg 0) 0
        contractSanityInitState =
        .done (.returned ⟨.unit, ⟨[]⟩⟩) := rfl
  rw [hDone] at hEval
  cases hEval

theorem contract_positive_sanity_unit_theorem :
    UnitTheorem {
      program := contractSanityProg
      specs := ContractSpecs [contractSanityEntry]
    } := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro defId body hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      refine ⟨rfl, rfl, fun args hArgs _ => ?_⟩
      cases args with
      | nil => exact contract_sanity_wellformed
      | cons _ _ => cases hArgs
    | succ _ =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · refine ⟨rfl, ?_⟩
    first
    | exact trivial
    | refine ⟨?_, trivial⟩
      first
      | exact trivial
      | refine ⟨0, contractSanityBody, rfl, ?_, ?_, ?_, ?_⟩
        · first | exact trivial | exact rfl
        · first | exact trivial | exact rfl
        · refine ⟨?_, ?_, fun args hArgs => ?_⟩
          · first | exact trivial | exact rfl
          · first | exact trivial | exact rfl
          · cases args with
            | cons _ _ => cases hArgs
            | nil =>
              refine ⟨fun _ => ?_, fun _ => ⟨fun out hOut => ?_, fun _ => ?_⟩⟩
              · first | exact trivial | exact contract_sanity_wellformed
              · cases out with
                | returned retOut =>
                  first
                  | exact trivial
                  | have hEq := contract_sanity_behavior _ hOut
                    injection hEq with hRet
                    rw [hRet]
                    exact rfl
                | unwound _ =>
                  exact TerminalOut.noConfusion (contract_sanity_behavior _ hOut)
                | aborted _ =>
                  first
                  | exact trivial
                  | exact TerminalOut.noConfusion
                      (contract_sanity_behavior _ hOut)
              · first | exact trivial | exact contract_sanity_not_diverges
        · first
          | exact trivial
          | intro _
            refine ⟨[], rfl, ?_, trivial⟩
            first | exact trivial | intro _; exact trivial

theorem contract_positive_sanity_safety_lookup :
    (ContractSpecs [contractSanityEntry]).safety
      "guard_mutation::contract_sanity" [] := by
  exact trivial

end GuardMutation
