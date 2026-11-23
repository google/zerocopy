-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp

public section

namespace Anneal.ContractCore

open Trusted.MirAst Trusted.MirSemantics

/-!
# Soundness Theorems and Negative-Control Regressions for `Contract.lean`

Untrusted (`0` TCB LOC) kernel-checked theorems establishing:
1. Backwards compatibility between `ContractSatisfied` and `BodyVerified`, plus
   positive contract satisfaction canaries bound strictly by canonical item path
   and `isUnsafe` signature status (`BodyBoundByPath`).
2. Sound termination asymmetry (`D4`):
   - obligation-side `FnContract` requires `¬ Diverges` by default
     (`loop_cannot_launder_ensures_under_default_total`) and admits divergence
     only with an explicit `mayDiverge := true` opt-out
     (`loop_admitted_with_explicit_mayDiverge_opt_out`);
   - assumption-side `AssumedContract` defaults to partial (`terminates =
     false`, `#3091`) and satisfies general 8-mask realizability equivalence
     (`realizable_iff_valid_choice_inhabited`,
     `default_partial_always_realizable`).
3. Canonical item-path + `isUnsafe` binding regression (`H2`):
   `path_binding_rejects_isUnsafe_mismatch`.
4. Negative-control regression suite covering mutants `M1`–`M4`:
   - `M1`: safe `fn` with `behaviorPre` cannot waive UB
     (`safe_fn_requires_cannot_waive_ub` vs.
     `conflated_pre_wrongly_accepts_unsound_safe_fn`);
   - `M2`: 3-way-only realizability gap witness for
     `(terminates = true, noUnwind = false, noAbort = true)` caught by 8-mask
     `AssumedContractRealizable` (`three_way_only_realizability_gap_witness`);
   - `M3`: `extern "C"` requires `noUnwind = true` vs. missing `noUnwind`
     (`extern_c_default_abi_consistent`, `extern_c_missing_noUnwind_rejected`,
     `extern_c_call_faults_without_noUnwind`,
     `extern_c_call_safe_with_noUnwind`);
   - `M4`: mutual recursion without a decreasing measure is rejected for
     total (`mayDiverge = false`) calls while partial (`mayDiverge = true`)
     mutual recursion is sound without measures (`callEdgeStratified_*`,
     `mutual_recursion_partial_sound`,
     `mutual_recursion_termination_unsound_without_measure`,
     `mutual_recursion_termination_sound_with_measure`).
-/

/-! ## 1. Backwards Compatibility, Path Binding (`H2`), and Canaries -/

/-- Any body satisfying `ContractSatisfied` automatically satisfies the
pre-existing `BodyVerified` judgment under its `safetyPre` and canonical path
binding (preserving 100% backwards compatibility with
`Trusted.MirSemantics.Boundary`). -/
theorem bodyVerified_of_contractSatisfied
    (p : Program) (itemPath : String) (expectedIsUnsafe : Bool)
    (c : FnContract)
    (hSat : ContractSatisfied p itemPath expectedIsUnsafe c) :
    ∃ (defId : DefId) (body : Body),
      BodyBoundByPath p itemPath expectedIsUnsafe defId body ∧
      BodyVerified p defId body (fun args => c.safetyPre { args := args }) := by
  cases hSat with
  | intro defId hEx =>
    cases hEx with
    | intro body hRest =>
      cases hRest with
      | intro hBound hRest2 =>
        cases hRest2 with
        | intro hAdm hRest3 =>
          cases hRest3 with
          | intro hSafe _ =>
            exact ⟨defId, body, hBound, hBound.2.1, hAdm,
              fun args hArgs hPre => hSafe { args := args } ⟨hArgs, rfl⟩ hPre⟩

/-- Single-body program containing `canarySafeUnitBody`
(`"canary::safe_unit"`, `isUnsafe = false`). -/
@[expose] noncomputable def progSafeUnitContract : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [canarySafeUnitBody]
}

/-- Default-total (`mayDiverge := false`), no-unwind, no-abort obligation
contract for `"canary::safe_unit"`. -/
@[expose] def safeUnitTotalContract : FnContract := {
  postReturn := fun _ out => out.ret = .unit ∧ out.callerMem = ⟨[]⟩
  noUnwind := true
  noAbort := true
}

private theorem wpProg_safe_unit :
    Anneal.MirWp.wpProg (entryProgForBody progSafeUnitContract 0) 1
      { args := [] }
      (fun out => out = .returned ⟨.unit, ⟨[]⟩⟩) :=
  Anneal.MirWp.wpProg_of_execProg rfl

/-- Positive canary: `"canary::safe_unit"` (`isUnsafe = false`) satisfies
`safeUnitTotalContract` (total by default) bound strictly by canonical item
path and signature safety. -/
theorem contractSatisfied_safe_unit_canary :
    ContractSatisfied progSafeUnitContract "canary::safe_unit" false
      safeUnitTotalContract := by
  refine ⟨0, canarySafeUnitBody, ⟨rfl, rfl, rfl, rfl⟩, rfl, ?_, ?_⟩
  · intro q hQ _
    cases q with
    | mk args cm =>
      cases hQ with
      | intro hArgs hCm =>
        dsimp only at hCm
        subst hCm
        cases args with
        | nil =>
          exact (Anneal.MirWp.wellFormed_and_spec_of_wp
            (entryProgForBody progSafeUnitContract 0) { args := [] } 1 _
            wpProg_safe_unit).1.1
        | cons _ _ =>
          exact Bool.noConfusion hArgs
  · intro q hQ _
    cases q with
    | mk args cm =>
      cases hQ with
      | intro hArgs hCm =>
        dsimp only at hCm
        subst hCm
        cases args with
        | nil =>
          have hSound := Anneal.MirWp.wellFormed_and_spec_of_wp
            (entryProgForBody progSafeUnitContract 0) { args := [] } 1 _
            wpProg_safe_unit
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro out hBeh
            have hEq := hSound.1.2 (.returned out) hBeh
            injection hEq with hOut
            subst hOut
            exact ⟨rfl, rfl, rfl⟩
          · intro _ hBeh
            have hEq := hSound.1.2 (.unwound _) hBeh
            cases hEq
          · intro _ hBeh
            have hEq := hSound.1.2 (.aborted _) hBeh
            cases hEq
          · intro _
            exact hSound.2.1
          · intro _ _ hBeh
            have hEq := hSound.1.2 (.unwound _) hBeh
            cases hEq
          · intro _ _ hBeh
            have hEq := hSound.1.2 (.aborted _) hBeh
            cases hEq
        | cons _ _ =>
          exact Bool.noConfusion hArgs

/-- Single-body program containing `canaryUnsafeGuardedBody isUnsafeFlag`
(`"canary::unsafe_guarded"`). -/
@[expose] noncomputable def progGuardedBody (isUnsafeFlag : Bool) : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [canaryUnsafeGuardedBody isUnsafeFlag]
}

/-- Default-total obligation contract requiring `args = [.bool true]` as
`safetyPre` for `"canary::unsafe_guarded"` and guaranteeing return `42u32`. -/
@[expose] def unsafeGuardedContract : FnContract := {
  safetyPre := fun q => q.args = [.bool true]
  postReturn := fun _ out => out.ret = u32Val 42 ∧ out.callerMem = ⟨[]⟩
  noUnwind := true
  noAbort := true
}

private theorem wpProg_guarded_true (isUnsafeFlag : Bool) :
    Anneal.MirWp.wpProg (entryProgForBody (progGuardedBody isUnsafeFlag) 0) 3
      { args := [.bool true] }
      (fun out => out = .returned ⟨u32Val 42, ⟨[]⟩⟩) :=
  Anneal.MirWp.wpProg_of_execProg rfl

/-- Positive canary: `"canary::unsafe_guarded"` (`isUnsafe = true`) discharges
`unsafeGuardedContract` under canonical path + safety binding. -/
theorem contractSatisfied_unsafe_guarded_canary :
    ContractSatisfied (progGuardedBody true) "canary::unsafe_guarded" true
      unsafeGuardedContract := by
  refine ⟨0, canaryUnsafeGuardedBody true, ⟨rfl, rfl, rfl, rfl⟩, rfl, ?_, ?_⟩
  · intro q hQ hSafe
    cases q with
    | mk args cm =>
      cases hQ with
      | intro _ hCm =>
        dsimp only at hCm
        subst hCm
        have hEq : args = [.bool true] := hSafe rfl
        subst hEq
        exact (Anneal.MirWp.wellFormed_and_spec_of_wp
          (entryProgForBody (progGuardedBody true) 0) { args := [.bool true] } 3
          _ (wpProg_guarded_true true)).1.1
  · intro q hQ hBehPre
    cases q with
    | mk args cm =>
      cases hQ with
      | intro _ hCm =>
        dsimp only at hCm
        subst hCm
        have hEq : args = [.bool true] := hBehPre.1 rfl
        subst hEq
        have hSound := Anneal.MirWp.wellFormed_and_spec_of_wp
          (entryProgForBody (progGuardedBody true) 0) { args := [.bool true] } 3
          _ (wpProg_guarded_true true)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro out hBeh
          have hRet := hSound.1.2 (.returned out) hBeh
          injection hRet with hOut
          subst hOut
          exact ⟨rfl, rfl, rfl⟩
        · intro _ hBeh
          have hRet := hSound.1.2 (.unwound _) hBeh
          cases hRet
        · intro _ hBeh
          have hRet := hSound.1.2 (.aborted _) hBeh
          cases hRet
        · intro _
          exact hSound.2.1
        · intro _ _ hBeh
          have hRet := hSound.1.2 (.unwound _) hBeh
          cases hRet
        · intro _ _ hBeh
          have hRet := hSound.1.2 (.aborted _) hBeh
          cases hRet

/-- Helper: extract the unique single body `(defId = 0, body = b)` from
`BodyBoundByPath` on a 1-element program. -/
private theorem single_body_bound_eq
    (b : Body) (itemPath : String) (expectedIsUnsafe : Bool)
    (defId : DefId) (body : Body)
    (hBound : BodyBoundByPath
      { scope := .unit, pointerWidthBits := 64, mirProfileVersion := 1,
        bodies := [b] }
      itemPath expectedIsUnsafe defId body) :
    defId = 0 ∧ body = b ∧ b.identity = itemPath ∧
      b.isUnsafe = expectedIsUnsafe := by
  cases defId with
  | zero =>
    have hEq : body = b := by
      have hGet := hBound.2.1
      dsimp only [Trusted.MirSemantics.getElem?] at hGet
      injection hGet with hB
      exact hB.symm
    subst hEq
    exact ⟨rfl, rfl, hBound.2.2.1, hBound.2.2.2⟩
  | succ n =>
    have hGet := hBound.2.1
    dsimp only [Trusted.MirSemantics.getElem?] at hGet
    cases hGet

/-- Negative-control `H2`: claiming `expectedIsUnsafe = true` for a safe body
(`isUnsafe = false`) fails `ContractSatisfied` via `BodyBoundByPath`. -/
theorem path_binding_rejects_isUnsafe_mismatch :
    ¬ ContractSatisfied (progGuardedBody false) "canary::unsafe_guarded" true
      unsafeGuardedContract := by
  intro hSat
  cases hSat with
  | intro defId hEx =>
    cases hEx with
    | intro body hRest =>
      have hEq := single_body_bound_eq (canaryUnsafeGuardedBody false)
        "canary::unsafe_guarded" true defId body hRest.1
      exact Bool.noConfusion hEq.2.2.2

/-! ## 2. Obligation-Side Default Total Correctness (`D4`) -/

/-- Diverging `-> !` function body (`fn spin() -> ! { loop {} }`). -/
@[expose] def canaryNeverReturnBody : Body := {
  argumentCount := 0
  locals := [.never]
  basicBlocks := [{ statements := [], terminator := .goto 0 }]
  isUnsafe := false
  identity := "canary::spin_never"
}

/-- Single-body program containing `"canary::spin_never"`. -/
@[expose] def progSpinNever : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [canaryNeverReturnBody]
}

private noncomputable def spinEntryState : State := {
  frames := [{
    defId := 0
    blockIdx := 0
    stmtIdx := 0
    locals := [.immediate none]
  }]
  callerMem := ⟨[]⟩
  mem := entryMemory
}

private theorem spin_init_ok :
    initState (entryProgForBody progSpinNever 0) { args := [] } =
      .ok spinEntryState :=
  rfl

private theorem spin_step_self :
    evalStep (entryProgForBody progSpinNever 0) 0 spinEntryState =
      .step spinEntryState :=
  rfl

private theorem spin_reaches_self (s : State)
    (hR : Reaches (entryProgForBody progSpinNever 0) spinEntryState s) :
    s = spinEntryState := by
  induction hR with
  | refl => rfl
  | tail _ hStep ih =>
    subst ih
    cases hStep with
    | intro c hC =>
      cases hC with
      | intro hVal hEv =>
        have hZero : c = 0 := hVal
        subst hZero
        rw [spin_step_self] at hEv
        injection hEv with hEq
        exact hEq.symm

private theorem spin_diverges :
    Diverges (entryProgForBody progSpinNever 0) { args := [] } :=
  ⟨spinEntryState, spin_init_ok, fun _ => spinEntryState, rfl,
    fun _ => ⟨0, rfl, spin_step_self⟩⟩

private theorem spin_wellFormed :
    WellFormed (entryProgForBody progSpinNever 0) { args := [] } := by
  refine ⟨⟨spinEntryState, spin_init_ok, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩
  intro k hRes
  unfold ReachesResult at hRes
  rw [spin_init_ok] at hRes
  cases hRes with
  | intro s hS =>
    have hEq := spin_reaches_self s hS.1
    subst hEq
    cases hS.2 with
    | intro c hC =>
      have hZero : c = 0 := hC.1
      subst hZero
      have hEv := hC.2
      rw [spin_step_self] at hEv
      cases hEv

private theorem spin_no_behavior (out : TerminalOut) :
    ¬ Behavior (entryProgForBody progSpinNever 0) { args := [] } out := by
  intro hBeh
  unfold Behavior ReachesResult at hBeh
  rw [spin_init_ok] at hBeh
  cases hBeh with
  | intro s hS =>
    have hEq := spin_reaches_self s hS.1
    subst hEq
    cases hS.2 with
    | intro c hC =>
      have hZero : c = 0 := hC.1
      subst hZero
      have hEv := hC.2
      rw [spin_step_self] at hEv
      cases hEv

/-- Negative-control `D4`: under the obligation-side default (`mayDiverge =
false`), a diverging `loop {}` body CANNOT launder an unprovable `postReturn :=
fun _ _ => False` into `ContractSatisfied`. -/
theorem loop_cannot_launder_ensures_under_default_total :
    ¬ ContractSatisfied progSpinNever "canary::spin_never" false
      { postReturn := fun _ _ => False } := by
  intro hSat
  cases hSat with
  | intro defId hEx =>
    cases hEx with
    | intro body hRest =>
      have hEq := single_body_bound_eq canaryNeverReturnBody
        "canary::spin_never" false defId body hRest.1
      cases hEq with
      | intro hId hB =>
        subst hId
        cases hB with
        | intro hBody _ =>
          subst hBody
          have hEff := hRest.2.2.2 { args := [] } ⟨rfl, rfl⟩
            ⟨fun h => Bool.noConfusion h, trivial⟩
          exact hEff.2.2.2.1 rfl spin_diverges

/-- Positive paired theorem for `D4`: opting out explicitly on the reviewed
spec surface (`mayDiverge := true`) admits a diverging `loop {}` body. -/
theorem loop_admitted_with_explicit_mayDiverge_opt_out :
    ContractSatisfied progSpinNever "canary::spin_never" false
      { postReturn := fun _ _ => False, mayDiverge := true } := by
  refine ⟨0, canaryNeverReturnBody, ⟨rfl, rfl, rfl, rfl⟩, rfl, ?_, ?_⟩
  · intro q hQ _
    cases q with
    | mk args cm =>
      cases hQ with
      | intro hArgs hCm =>
        dsimp only at hCm
        subst hCm
        cases args with
        | nil => exact spin_wellFormed
        | cons _ _ => exact Bool.noConfusion hArgs
  · intro q hQ _
    cases q with
    | mk args cm =>
      cases hQ with
      | intro hArgs hCm =>
        dsimp only at hCm
        subst hCm
        cases args with
        | nil =>
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro out hBeh
            exact False.elim (spin_no_behavior (.returned out) hBeh)
          · intro mem hBeh
            exact False.elim (spin_no_behavior (.unwound mem) hBeh)
          · intro mem hBeh
            exact False.elim (spin_no_behavior (.aborted mem) hBeh)
          · intro hMd
            exact Bool.noConfusion hMd
          · intro hNu
            exact Bool.noConfusion hNu
          · intro hNa
            exact Bool.noConfusion hNa
        | cons _ _ => exact Bool.noConfusion hArgs

/-! ## 3. General 8-Mask `AssumedContractRealizable` Soundness (`U2`) -/

/-- Demonic call-site outcome space for an assumed callee. -/
inductive AssumedCallChoice where
  | ret (out : Out)
  | unwind (mem : CallerMemory)
  | abort (mem : CallerMemory)
  | diverge

/-- Admissibility of a demonic call outcome `ch` under assumed contract `c`.
-/
@[expose] def ValidAssumedChoice (body : Body) (c : AssumedContract)
    (q : Query) : AssumedCallChoice → Prop
  | .ret out => ValidReturnVal body out ∧ c.postReturn q out
  | .unwind mem => c.effects.noUnwind = false ∧ c.postUnwind q mem
  | .abort mem => c.effects.noAbort = false ∧ c.postAbort q mem
  | .diverge => c.effects.terminates = false

/-- `AssumedContractRealizable` is equivalent to inhabitation of the demonic
call-choice relation `ValidAssumedChoice` across all 8 `EffectMask` bit
combinations. -/
theorem realizable_iff_valid_choice_inhabited
    (body : Body) (c : AssumedContract) :
    AssumedContractRealizable body c ↔
    (∀ q : Query, ValidContractQuery body q →
      c.effectiveBehaviorPre body.isUnsafe q →
      ∃ ch : AssumedCallChoice, ValidAssumedChoice body c q ch) := by
  constructor
  · intro hReal q hQ hPre
    cases hReal q hQ hPre with
    | inl hDiv => exact ⟨.diverge, hDiv⟩
    | inr hRest =>
      cases hRest with
      | inl hRet =>
        cases hRet with
        | intro out hOut => exact ⟨.ret out, hOut⟩
      | inr hRest2 =>
        cases hRest2 with
        | inl hUnw =>
          cases hUnw with
          | intro hNu hMem =>
            cases hMem with
            | intro mem hPost => exact ⟨.unwind mem, hNu, hPost⟩
        | inr hAb =>
          cases hAb with
          | intro hNa hMem =>
            cases hMem with
            | intro mem hPost => exact ⟨.abort mem, hNa, hPost⟩
  · intro hInh q hQ hPre
    cases hInh q hQ hPre with
    | intro ch hCh =>
      cases ch with
      | ret out => exact Or.inr (Or.inl ⟨out, hCh⟩)
      | unwind mem =>
        exact Or.inr (Or.inr (Or.inl ⟨hCh.1, mem, hCh.2⟩))
      | abort mem =>
        exact Or.inr (Or.inr (Or.inr ⟨hCh.1, mem, hCh.2⟩))
      | diverge => exact Or.inl hCh

/-- Under the assumption-side default partial mask (`terminates = false`), any
assumed contract is realizable unconditionally, including diverging `-> !`
stubs with `postReturn = False`. -/
theorem default_partial_always_realizable
    (body : Body) (c : AssumedContract)
    (hPart : c.effects.terminates = false) :
    AssumedContractRealizable body c := by
  intro _ _ _
  exact Or.inl hPart

/-- No `Out` value can satisfy `ValidReturnVal` for a `-> !` body because
`checkVal v .never = false` for every `v : Val`. -/
theorem never_return_uninhabited (out : Out) :
    ¬ ValidReturnVal canaryNeverReturnBody out := by
  intro hVal
  dsimp only [ValidReturnVal, canaryNeverReturnBody,
    Trusted.MirSemantics.getElem?] at hVal
  rw [Anneal.MirWp.checkVal_never_false out.ret] at hVal
  exact Bool.noConfusion hVal

/-- Default assumption-side contract for `fn spin() -> !` with
`postReturn := fun _ _ => False` defaults to partial (`terminates = false`) and
is realizable via divergence, preventing vacuous `False` derivation. -/
theorem default_partial_never_return_realizable :
    AssumedContractRealizable canaryNeverReturnBody
      { postReturn := fun _ _ => False } :=
  default_partial_always_realizable canaryNeverReturnBody
    { postReturn := fun _ _ => False } rfl

/-- Escalating an assumed contract with `postReturn := fun _ _ => False` to
`(terminates = true, noUnwind = true, noAbort = true)` fails
`AssumedContractRealizable`. -/
theorem total_unsat_post_not_realizable :
    ¬ AssumedContractRealizable canarySafeUnitBody {
        postReturn := fun _ _ => False
        effects := { terminates := true, noUnwind := true, noAbort := true }
      } := by
  intro hReal
  have hQ : ValidContractQuery canarySafeUnitBody { args := [] } :=
    ⟨rfl, rfl⟩
  have hPre :
      ({ postReturn := fun _ _ => False
         effects := { terminates := true, noUnwind := true, noAbort := true }
       } : AssumedContract).effectiveBehaviorPre false { args := [] } :=
    ⟨fun h => Bool.noConfusion h, trivial⟩
  cases hReal { args := [] } hQ hPre with
  | inl h1 => exact Bool.noConfusion h1
  | inr hRest =>
    cases hRest with
    | inl h2 =>
      cases h2 with
      | intro _ hOut => exact hOut.2
    | inr hRest2 =>
      cases hRest2 with
      | inl h3 => exact Bool.noConfusion h3.1
      | inr h4 => exact Bool.noConfusion h4.1

/-! ## 4. Negative-Control `M1`: Safe `fn` `behaviorPre` Cannot Waive UB -/

/-- Buggy conflated-precondition contract judgment (for contrast with
`ContractSatisfied`): erroneously lets `behaviorPre` gate `WellFormed` even on
safe functions (`body.isUnsafe = false`). -/
@[expose] def ContractSatisfiedConflated (p : Program) (itemPath : String)
    (expectedIsUnsafe : Bool) (c : FnContract) : Prop :=
  ∃ (defId : DefId) (body : Body),
    BodyBoundByPath p itemPath expectedIsUnsafe defId body ∧
    BodyStaticAdmitted p body = true ∧
    ∀ q : Query, ValidContractQuery body q →
      c.behaviorPre q →
      WellFormed (entryProgForBody p defId) q

/-- Contract on safe `"canary::unsafe_guarded"` (`isUnsafe = false`) attempting
to restrict valid inputs to `args = [.bool true]` via `behaviorPre`. -/
@[expose] def badSafeContract : FnContract := {
  safetyPre := fun _ => False
  behaviorPre := fun q => q.args = [.bool true]
}

/-- Contrast theorem for `M1`: the conflated judgment wrongly accepts the
unsound safe function `"canary::unsafe_guarded"` (`isUnsafe = false`) because
`behaviorPre` hides the `flag = false` UB path. -/
theorem conflated_pre_wrongly_accepts_unsound_safe_fn :
    ContractSatisfiedConflated (progGuardedBody false) "canary::unsafe_guarded"
      false badSafeContract := by
  refine ⟨0, canaryUnsafeGuardedBody false, ⟨rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
  intro q hQ hPre
  cases q with
  | mk args cm =>
    cases hQ with
    | intro _ hCm =>
      dsimp only at hCm hPre
      subst hCm
      subst hPre
      exact (Anneal.MirWp.wellFormed_and_spec_of_wp
        (entryProgForBody (progGuardedBody false) 0) { args := [.bool true] } 3
        _ (wpProg_guarded_true false)).1.1

/-- Negative-control `M1` (`U1`): a safe function (`isUnsafe = false`) with
`behaviorPre` (and even `safetyPre = False`) CANNOT waive UB under
`ContractSatisfied`, because `flag = false` reaches `.unreachable`
(`.fault .undefined`). -/
theorem safe_fn_requires_cannot_waive_ub :
    ¬ ContractSatisfied (progGuardedBody false) "canary::unsafe_guarded" false
      badSafeContract := by
  intro hSat
  cases hSat with
  | intro defId hEx =>
    cases hEx with
    | intro body hRest =>
      have hEq := single_body_bound_eq (canaryUnsafeGuardedBody false)
        "canary::unsafe_guarded" false defId body hRest.1
      cases hEq with
      | intro hId hB =>
        subst hId
        cases hB with
        | intro hBody _ =>
          subst hBody
          have hWf :
              WellFormed (entryProgForBody (progGuardedBody false) 0)
                { args := [.bool false] } :=
            hRest.2.2.1 { args := [.bool false] } ⟨rfl, rfl⟩
              (fun h => Bool.noConfusion h)
          have hWpFault :
              Anneal.MirWp.wpFaultProg
                (entryProgForBody (progGuardedBody false) 0) 2
                { args := [.bool false] } .undefined :=
            Anneal.MirWp.wpFaultProg_of_execFaultProg rfl
          exact (Anneal.MirWp.reaches_fault_and_exclusive_of_wpFault
            (entryProgForBody (progGuardedBody false) 0)
            { args := [.bool false] } 2 .undefined hWpFault).2.2.2.2 hWf

/-! ## 5. Negative-Control `M2`: 3-Way-Only Realizability Gap Witness -/

/-- Buggy 3-way-only realizability gate: checks `∃ out, postReturn` only when
all three `EffectMask` flags are `true`. -/
@[expose] def AssumedContractRealizableThreeWayOnly
    (body : Body) (c : AssumedContract) : Prop :=
  c.effects.terminates = true →
  c.effects.noUnwind = true →
  c.effects.noAbort = true →
  ∀ q : Query, ValidContractQuery body q →
    c.effectiveBehaviorPre body.isUnsafe q →
    ∃ out : Out, ValidReturnVal body out ∧ c.postReturn q out

/-- Witness assumed contract with `(terminates = true, noUnwind = false,
noAbort = true)` and unsatisfiable `postReturn` and `postUnwind`. -/
@[expose] def realizabilityHoleContract : AssumedContract := {
  postReturn := fun _ _ => False
  postUnwind := fun _ _ => False
  effects := { terminates := true, noUnwind := false, noAbort := true }
}

/-- Negative-control `M2` (`U2`): the 3-way-only check vacuously accepts
`realizabilityHoleContract`, whereas the general 8-mask
`AssumedContractRealizable` rejects it and `ValidAssumedChoice` is empty. -/
theorem three_way_only_realizability_gap_witness :
    AssumedContractRealizableThreeWayOnly canarySafeUnitBody
      realizabilityHoleContract ∧
    ¬ AssumedContractRealizable canarySafeUnitBody realizabilityHoleContract ∧
    ¬ ∃ ch : AssumedCallChoice,
        ValidAssumedChoice canarySafeUnitBody realizabilityHoleContract
          { args := [] } ch := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ hNu
    exact Bool.noConfusion hNu
  · intro hReal
    have hQ : ValidContractQuery canarySafeUnitBody { args := [] } :=
      ⟨rfl, rfl⟩
    have hPre :
        realizabilityHoleContract.effectiveBehaviorPre false { args := [] } :=
      ⟨fun h => Bool.noConfusion h, trivial⟩
    cases hReal { args := [] } hQ hPre with
    | inl h1 => exact Bool.noConfusion h1
    | inr hRest =>
      cases hRest with
      | inl h2 =>
        cases h2 with
        | intro _ hOut => exact hOut.2
      | inr hRest2 =>
        cases hRest2 with
        | inl h3 =>
          cases h3.2 with
          | intro _ hPu => exact hPu
        | inr h4 => exact Bool.noConfusion h4.1
  · intro hEx
    cases hEx with
    | intro ch hCh =>
      cases ch with
      | ret _ => exact hCh.2
      | unwind _ => exact hCh.2
      | abort _ => exact Bool.noConfusion hCh.1
      | diverge => exact Bool.noConfusion hCh

/-! ## 6. Negative-Control `M3`: `extern "C"` `noUnwind` Consistency -/

/-- Default assumption-side `EffectMask` for ABI `abi`: `.cNoUnwind`
(`extern "C"`) sets `noUnwind := true` while keeping `terminates := false` and
`noAbort := false`; `.rust` and `.cUnwind` leave all three flags `false`. -/
@[expose] def defaultEffectMaskForAbi : AbiKind → EffectMask
  | .rust => ⟨false, false, false⟩
  | .cNoUnwind => { noUnwind := true }
  | .cUnwind => ⟨false, false, false⟩

/-- Default `EffectMask` for `extern "C"` (`AbiKind.cNoUnwind`) sets
`noUnwind = true`, keeps `terminates = false`, and passes
`AssumedAbiConsistent`. -/
theorem extern_c_default_abi_consistent :
    AssumedAbiConsistent .cNoUnwind
      { effects := defaultEffectMaskForAbi .cNoUnwind } ∧
    (defaultEffectMaskForAbi .cNoUnwind).terminates = false :=
  ⟨rfl, rfl⟩

/-- Negative-control `M3a` (`U3`): omitting `noUnwind = true` on an
`extern "C"` (`AbiKind.cNoUnwind`) assumed contract is rejected by
`AssumedAbiConsistent`. -/
theorem extern_c_missing_noUnwind_rejected :
    ¬ AssumedAbiConsistent .cNoUnwind { effects := { noUnwind := false } } := by
  intro hAbi
  exact Bool.noConfusion hAbi

/-- `extern "C-unwind"` (`AbiKind.cUnwind`) permits `noUnwind = false` by
default. -/
theorem extern_c_unwind_permits_unwinding :
    AssumedAbiConsistent .cUnwind
      { effects := defaultEffectMaskForAbi .cUnwind } :=
  trivial

/-- Single-step call-site outcome dispatcher for an assumed callee under
call-site `unwindAct : UnwindAction` (modeling `rustc`'s
`UnwindAction::Unreachable` lowering on `extern "C"` calls). -/
@[expose] def evalAssumedCallStep (unwindAct : UnwindAction) :
    AssumedCallChoice → StepResult Unit TerminalOut
  | .ret out => .done (.returned out)
  | .unwind mem =>
    match unwindAct with
    | .continue_ => .done (.unwound mem)
    | .unreachable => .fault .undefined
    | .terminate => .done (.aborted mem)
    | .cleanup _ => .step ()
  | .abort mem => .done (.aborted mem)
  | .diverge => .step ()

/-- Negative-control `M3b` (`U3`): under `UnwindAction.unreachable` (which
`rustc` emits on every `extern "C"` call), an assumed contract with
`noUnwind = false` and an admissible `postUnwind` state reaches
`.fault .undefined` on the demonic unwind branch. -/
theorem extern_c_call_faults_without_noUnwind
    (body : Body) (c : AssumedContract) (q : Query) (mem : CallerMemory)
    (hNu : c.effects.noUnwind = false) (hPu : c.postUnwind q mem) :
    ∃ ch : AssumedCallChoice,
      ValidAssumedChoice body c q ch ∧
      evalAssumedCallStep .unreachable ch = .fault .undefined :=
  ⟨.unwind mem, ⟨hNu, hPu⟩, rfl⟩

/-- Positive paired theorem for `M3`: when `c.effects.noUnwind = true` and `c`
is realizable at `q`, at least one demonic choice is admissible and NO
admissible choice can fault under `UnwindAction.unreachable`. -/
theorem extern_c_call_safe_with_noUnwind
    (body : Body) (c : AssumedContract) (q : Query)
    (hQ : ValidContractQuery body q)
    (hPre : c.effectiveBehaviorPre body.isUnsafe q)
    (hReal : AssumedContractRealizable body c)
    (hNu : c.effects.noUnwind = true) :
    (∃ ch : AssumedCallChoice, ValidAssumedChoice body c q ch) ∧
    (∀ ch : AssumedCallChoice, ValidAssumedChoice body c q ch →
      ∀ k : FaultKind, evalAssumedCallStep .unreachable ch ≠ .fault k) := by
  refine ⟨(realizable_iff_valid_choice_inhabited body c).mp hReal q hQ hPre, ?_⟩
  intro ch hCh k hFault
  cases ch with
  | ret _ => cases hFault
  | unwind _ =>
    have hEq : true = false := hNu.symm.trans hCh.1
    exact Bool.noConfusion hEq
  | abort _ => cases hFault
  | diverge => cases hFault

/-! ## 7. Negative-Control `M4`: Mutual-Recursion Stratification (`U4`) -/

/-- When `cCaller.mayDiverge = true` (explicit partial opt-out),
`CallEdgeStratified` holds unconditionally without any measure or SCC
acyclicity. -/
theorem callEdgeStratified_partial_unconditional
    (sccRank : DefId → Nat) (callerId calleeId : DefId)
    (cCaller cCallee : FnContract) (qCaller qCallee : Query)
    (hPart : cCaller.mayDiverge = true) :
    CallEdgeStratified sccRank callerId calleeId cCaller cCallee
      qCaller qCallee := by
  intro hTotal
  have hEq : false = true := hTotal.symm.trans hPart
  exact Bool.noConfusion hEq

/-- Negative-control `M4a` (`U4`): mutual recursion inside one SCC
(`sccRank f = sccRank g`) under default total contracts (`mayDiverge = false`)
and no `measure` is rejected by `CallEdgeStratified`. -/
theorem callEdgeStratified_rejects_unmeasured_cycle
    (sccRank : DefId → Nat) (f g : DefId)
    (hSameScc : sccRank g = sccRank f)
    (qF qG : Query) :
    ¬ CallEdgeStratified sccRank f g
        { measure := none }
        { measure := none }
        qF qG := by
  intro hStrat
  have hRes := hStrat rfl
  cases hRes.2 with
  | inl hLt =>
    rw [hSameScc] at hLt
    exact Nat.lt_irrefl (sccRank f) hLt
  | inr hEq => exact hEq.2

/-- Negative-control `M4b` (`U4`): mutual recursion inside one SCC under
default total contracts (`mayDiverge = false`) and a non-decreasing measure
(`m qG = m qF`) is rejected by `CallEdgeStratified`. -/
theorem callEdgeStratified_rejects_nondecreasing_measure
    (sccRank : DefId → Nat) (f g : DefId)
    (hSameScc : sccRank g = sccRank f)
    (m : Query → Nat) (qF qG : Query) (hEqM : m qG = m qF) :
    ¬ CallEdgeStratified sccRank f g
        { measure := some m }
        { measure := some m }
        qF qG := by
  intro hStrat
  have hRes := hStrat rfl
  cases hRes.2 with
  | inl hLt =>
    rw [hSameScc] at hLt
    exact Nat.lt_irrefl (sccRank f) hLt
  | inr hSame =>
    have hLtM : m qG < m qF := hSame.2
    rw [hEqM] at hLtM
    exact Nat.lt_irrefl (m qF) hLtM

/-- Positive paired theorem for `M4`: within the same SCC, a strictly
decreasing `Nat` measure satisfies `CallEdgeStratified`. -/
theorem callEdgeStratified_admits_decreasing_measure
    (sccRank : DefId → Nat) (f g : DefId)
    (hSameScc : sccRank g = sccRank f)
    (mF mG : Query → Nat) (qF qG : Query) (hDec : mG qG < mF qF) :
    CallEdgeStratified sccRank f g
      { measure := some mF }
      { measure := some mG }
      qF qG := by
  intro _
  exact ⟨rfl, Or.inr ⟨hSameScc, hDec⟩⟩

/-- Positive paired theorem for `M4`: an acyclic cross-SCC call
(`sccRank callee < sccRank caller`) satisfies `CallEdgeStratified` without a
`measure`. -/
theorem callEdgeStratified_admits_acyclic_scc
    (sccRank : DefId → Nat) (callerId calleeId : DefId)
    (hRank : sccRank calleeId < sccRank callerId)
    (qCaller qCallee : Query) :
    CallEdgeStratified sccRank callerId calleeId
      { measure := none }
      { measure := none }
      qCaller qCallee := by
  intro _
  exact ⟨rfl, Or.inl hRank⟩

/-! ### Big-Step Soundness Model for Mutual Recursion (`M4` Grounding) -/

private theorem natStrongAux {P : Nat → Prop}
    (h : ∀ n, (∀ k, k < n → P k) → P n) :
    ∀ n k, k < n → P k := by
  intro n
  induction n with
  | zero =>
    intro _ hlt
    exact False.elim (Nat.not_lt_zero _ hlt)
  | succ n ih =>
    intro k hlt
    cases hlt with
    | refl => exact h n ih
    | step hlt' => exact ih k hlt'

private theorem natStrongRec {P : Nat → Prop}
    (h : ∀ n, (∀ k, k < n → P k) → P n) (n : Nat) : P n :=
  natStrongAux h (n + 1) n (Nat.lt_succ_self n)

private theorem lt_add_succ_left (a b : Nat) : a < a + b + 1 :=
  Nat.lt_succ_of_le (Nat.le_add_right a b)

private theorem lt_add_succ_right (a b : Nat) : b < a + b + 1 :=
  Nat.lt_succ_of_le (Nat.le_add_left b a)

/-- Minimal call-capable multi-function language grounding the asymmetry in
`CallEdgeStratified`. -/
inductive MStmt where
  | ret (v : Nat)
  | call (callee : DefId) (arg : Nat) (cont : Nat → MStmt)
  | ub

/-- Concrete big-step evaluation indexed by exact derivation depth `n`. -/
inductive EvalN (prog : DefId → Nat → MStmt) :
    Nat → MStmt → Option Nat → Prop where
  | ret (n v : Nat) : EvalN prog (n + 1) (.ret v) (some v)
  | ub (n : Nat) : EvalN prog (n + 1) .ub none
  | call_ub {n : Nat} {c : DefId} {arg : Nat} {cont : Nat → MStmt} :
      EvalN prog n (prog c arg) none →
      EvalN prog (n + 1) (.call c arg cont) none
  | call_ret {n₁ n₂ r : Nat} {c : DefId} {arg : Nat} {cont : Nat → MStmt}
      {res : Option Nat} :
      EvalN prog n₁ (prog c arg) (some r) →
      EvalN prog n₂ (cont r) res →
      EvalN prog (n₁ + n₂ + 1) (.call c arg cont) res

/-- Measure-free modular partial-correctness judgment (`mayDiverge = true`). -/
inductive StmtModularPartialOk (Pre : DefId → Nat → Prop)
    (Post : DefId → Nat → Nat → Prop) (postOut : Nat → Prop) :
    MStmt → Prop where
  | ret {v : Nat} :
      postOut v →
      StmtModularPartialOk Pre Post postOut (.ret v)
  | call {c : DefId} {arg : Nat} {cont : Nat → MStmt} :
      Pre c arg →
      (∀ r, Post c arg r → StmtModularPartialOk Pre Post postOut (cont r)) →
      StmtModularPartialOk Pre Post postOut (.call c arg cont)

/-- Soundness of measure-free modular mutual recursion for safety and partial
correctness (`mayDiverge = true`): proved by strong induction on depth `n`. -/
theorem mutual_recursion_partial_sound
    (prog : DefId → Nat → MStmt)
    (Pre : DefId → Nat → Prop)
    (Post : DefId → Nat → Nat → Prop)
    (hMod : ∀ f x, Pre f x →
      StmtModularPartialOk Pre Post (Post f x) (prog f x)) :
    ∀ n s postOut,
      StmtModularPartialOk Pre Post postOut s →
      ∀ res, EvalN prog n s res →
        match res with
        | none => False
        | some v => postOut v := by
  intro n
  refine natStrongRec (P := fun n =>
    ∀ s postOut, StmtModularPartialOk Pre Post postOut s →
      ∀ res, EvalN prog n s res →
        match res with
        | none => False
        | some v => postOut v) ?_ n
  intro k ih s postOut hOk res hEval
  cases hEval with
  | ret _ _ =>
    cases hOk with
    | ret hPost => exact hPost
  | ub _ =>
    cases hOk
  | call_ub hCal =>
    cases hOk with
    | call hPreC _ =>
      exact ih _ (Nat.lt_succ_self _) _ _ (hMod _ _ hPreC) none hCal
  | call_ret hCal hCont =>
    cases hOk with
    | call hPreC hContOk =>
      have hPostR := ih _ (lt_add_succ_left _ _) _ _ (hMod _ _ hPreC)
        (some _) hCal
      exact ih _ (lt_add_succ_right _ _) _ postOut (hContOk _ hPostR) _ hCont

/-- Mutually recursive non-terminating pair: `f(x) { g(x) }` and
`g(x) { f(x) }`. -/
@[expose] def mutLoopProg : DefId → Nat → MStmt
  | 0, x => .call 1 x (fun r => .ret r)
  | _, x => .call 0 x (fun r => .ret r)

/-- Negative-control `M4c` (`U4`): without a decreasing measure, `mutLoopProg`
satisfies unmeasured modular verification yet admits zero terminating
executions (`∀ n f x res, ¬ EvalN mutLoopProg n (mutLoopProg f x) res`). -/
theorem mutual_recursion_termination_unsound_without_measure :
    (∀ f x, StmtModularPartialOk (fun _ _ => True) (fun _ _ _ => True)
      (fun _ => True) (mutLoopProg f x)) ∧
    (∀ n f x res, ¬ EvalN mutLoopProg n (mutLoopProg f x) res) := by
  constructor
  · intro f x
    cases f with
    | zero => exact .call trivial (fun _ _ => .ret trivial)
    | succ _ => exact .call trivial (fun _ _ => .ret trivial)
  · intro n
    refine natStrongRec (P := fun n =>
      ∀ f x res, ¬ EvalN mutLoopProg n (mutLoopProg f x) res) ?_ n
    intro k ih f x res hEv
    cases f with
    | zero =>
      cases hEv with
      | call_ub hCal => exact ih _ (Nat.lt_succ_self _) 1 x none hCal
      | call_ret hCal _ => exact ih _ (lt_add_succ_left _ _) 1 x (some _) hCal
    | succ _ =>
      cases hEv with
      | call_ub hCal => exact ih _ (Nat.lt_succ_self _) 0 x none hCal
      | call_ret hCal _ => exact ih _ (lt_add_succ_left _ _) 0 x (some _) hCal

/-- Measure-guarded modular total-correctness judgment (`mayDiverge = false`)
wired directly to `Trusted.MirSemantics.CallEdgeStratified`. -/
inductive StmtModularTotalOk (sccRank : DefId → Nat)
    (contracts : DefId → FnContract) (argQuery : DefId → Nat → Query)
    (Pre : DefId → Nat → Prop) (Post : DefId → Nat → Nat → Prop)
    (callerId : DefId) (callerArg : Nat) (postOut : Nat → Prop) :
    MStmt → Prop where
  | ret (v : Nat) :
      postOut v →
      StmtModularTotalOk sccRank contracts argQuery Pre Post callerId callerArg
        postOut (.ret v)
  | call (c : DefId) (arg : Nat) (cont : Nat → MStmt) :
      Pre c arg →
      CallEdgeStratified sccRank callerId c (contracts callerId) (contracts c)
        (argQuery callerId callerArg) (argQuery c arg) →
      (∀ r, Post c arg r →
        StmtModularTotalOk sccRank contracts argQuery Pre Post callerId
          callerArg postOut (cont r)) →
      StmtModularTotalOk sccRank contracts argQuery Pre Post callerId callerArg
        postOut (.call c arg cont)

/-- Soundness of measure-decreasing modular mutual recursion (`mayDiverge =
false`) within an SCC: discharging `CallEdgeStratified` with `Nat` measures
implies concrete termination and postcondition satisfaction. -/
theorem mutual_recursion_termination_sound_with_measure
    (prog : DefId → Nat → MStmt)
    (sccRank : DefId → Nat)
    (hFlatScc : ∀ f g, sccRank f = sccRank g)
    (meas : DefId → Nat → Nat)
    (contracts : DefId → FnContract)
    (argQuery : DefId → Nat → Query)
    (hContracts : ∀ f,
      (contracts f).mayDiverge = false ∧
      ∃ mQ : Query → Nat,
        (contracts f).measure = some mQ ∧
        ∀ x, mQ (argQuery f x) = meas f x)
    (Pre : DefId → Nat → Prop)
    (Post : DefId → Nat → Nat → Prop)
    (hMod : ∀ f x, Pre f x →
      StmtModularTotalOk sccRank contracts argQuery Pre Post f x (Post f x)
        (prog f x)) :
    ∀ m f x, Pre f x → meas f x = m →
      ∃ n v, EvalN prog n (prog f x) (some v) ∧ Post f x v := by
  intro m
  refine natStrongRec (P := fun m =>
    ∀ f x, Pre f x → meas f x = m →
      ∃ n v, EvalN prog n (prog f x) (some v) ∧ Post f x v) ?_ m
  intro k ihM
  have hStmt :
      ∀ (f : DefId) (x : Nat) (s : MStmt) (postOut : Nat → Prop),
        meas f x = k →
        StmtModularTotalOk sccRank contracts argQuery Pre Post f x postOut s →
        ∃ n v, EvalN prog n s (some v) ∧ postOut v := by
    intro f x s postOut hEqK hOk
    induction hOk with
    | ret v hPost =>
      exact ⟨1, v, .ret 0 v, hPost⟩
    | call c arg _ hPreC hStrat _ ihCont =>
      cases hContracts f with
      | intro hTotalF hExMf =>
        cases hExMf with
        | intro mF hMf =>
          cases hContracts c with
          | intro _ hExMc =>
            cases hExMc with
            | intro mC hMc =>
              have hStep := hStrat hTotalF
              have hLt : meas c arg < k := by
                cases hStep.2 with
                | inl hRankLt =>
                  rw [hFlatScc c f] at hRankLt
                  exact False.elim (Nat.lt_irrefl (sccRank f) hRankLt)
                | inr hSame =>
                  have hM := hSame.2
                  rw [hMf.1, hMc.1] at hM
                  dsimp only at hM
                  rw [hMc.2 arg, hMf.2 x, hEqK] at hM
                  exact hM
              cases ihM (meas c arg) hLt c arg hPreC rfl with
              | intro n₁ hRes1 =>
                cases hRes1 with
                | intro r hEv1Post =>
                  cases ihCont r hEv1Post.2 with
                  | intro n₂ hRes2 =>
                    cases hRes2 with
                    | intro v hEv2Post =>
                      exact ⟨n₁ + n₂ + 1, v,
                        .call_ret hEv1Post.1 hEv2Post.1, hEv2Post.2⟩
  intro f x hPre hEqM
  exact hStmt f x (prog f x) (Post f x) hEqM (hMod f x hPre)

end Anneal.ContractCore

end
