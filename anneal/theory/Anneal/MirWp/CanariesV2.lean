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
public import Init.Data.BitVec.BasicAux
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirSemantics
public import Anneal.MirWp.Core

public section

namespace Anneal.MirWp

open Trusted.MirAst Trusted.MirSemantics

/-!
# Profile v2 Non-Vacuity Canaries

`ExecSoundnessClaimV2 execProgV2` (proved by `wellFormed_and_spec_of_execV2`)
says that `execProgV2 p fuel q post` implies `SatisfiesPostV2 p q post`,
`¬ DivergesV2 p q`, and a terminating `BehaviorV2` satisfying `post`. These
canaries show, on concrete Profile v2 programs, that none of those
predicates is trivially true or trivially false:

- `canary_v2_positive_raw_load`: a raw-pointer load from caller memory is
  `WellFormedV2`, has exactly the expected `BehaviorV2`, does not diverge,
  and satisfies its postcondition, while `execProgV2` rejects a wrong
  postcondition.
- `canary_v2_negative_null_load`: the same body given a null pointer reaches
  `.fault .undefined`, so it is not `WellFormedV2`, satisfies no
  `SatisfiesPostV2` postcondition, and no `execProgV2` premise holds for it.
- `canary_v2_diverges_spin`: a body that jumps to itself forever is
  `WellFormedV2` and satisfies even the postcondition `False`, yet
  `DivergesV2` holds and no `execProgV2` premise holds for it. So the
  `¬ DivergesV2` conjunct of the claim is what excludes it.

These are theory-only theorems; they pin no trusted claim. `anneal-audit`
replays every `theory/` module, so a semantics change that falsified one of
them would fail the audit.
-/

/-- Unsafe Profile v2 body `_0 = copy (*_1)` for `_1 : *const u8`. -/
noncomputable def bodyV2LoadU8 : Body := {
  argumentCount := 1
  locals := [.int .i8 false, .rawPtr .shared (.int .i8 false)]
  basicBlocks := [{
    statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, [.deref]⟩))]
    terminator := .return_
  }]
  isUnsafe := true
  identity := "canary_v2_load_u8"
}

/-- Profile v2 program whose entry body is `bodyV2LoadU8`. -/
noncomputable def progV2LoadU8 : Program := {
  bodies := [bodyV2LoadU8]
  pointerWidthBits := 64
  mirProfileVersion := 2
  scope := .unit
}

/-- Caller memory holding the read-only byte `42` in allocation `1`. -/
noncomputable def callerMemV2Byte42 : CallerMemory := {
  allocations := [{
    allocId := 1
    alignLog2 := 0
    mutability := .shared
    bytes := [.init 42 none]
    live := true
  }]
}

/-- Query passing a pointer to the byte in `callerMemV2Byte42`. -/
noncomputable def queryV2Load42 : Query := {
  args := [.ptr ⟨some 1, 0, .isize⟩]
  callerMem := callerMemV2Byte42
}

/-- Query passing a null pointer without provenance. -/
noncomputable def queryV2LoadNull : Query := {
  args := [.ptr ⟨none, 0, .isize⟩]
}

/-- The terminal outcome of `progV2LoadU8` on `queryV2Load42`. -/
noncomputable def outV2Load42 : TerminalOut :=
  .returned ⟨u8Val 42, callerMemV2Byte42⟩

/-- Safe Profile v2 body whose only block jumps to itself. -/
noncomputable def bodyV2Spin : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .goto 0 }]
  identity := "canary_v2_spin"
}

/-- Profile v2 program whose entry body is `bodyV2Spin`. -/
noncomputable def progV2Spin : Program := {
  bodies := [bodyV2Spin]
  pointerWidthBits := 64
  mirProfileVersion := 2
  scope := .unit
}

/-- Positive canary: loading through a valid `*const u8` is well-formed,
returns exactly `42` with caller memory unchanged, does not diverge, and
satisfies `· = outV2Load42`. `execProgV2` also rejects the postcondition that
the load returns `41`, so the premise of `ExecSoundnessClaimV2` is not
trivially true. -/
theorem canary_v2_positive_raw_load :
    WellFormedV2 progV2LoadU8 queryV2Load42 ∧
    BehaviorV2 progV2LoadU8 queryV2Load42 outV2Load42 ∧
    ¬ DivergesV2 progV2LoadU8 queryV2Load42 ∧
    SatisfiesPostV2 progV2LoadU8 queryV2Load42 (fun o => o = outV2Load42) ∧
    ¬ execProgV2 progV2LoadU8 2 queryV2Load42
      (fun o => o = .returned ⟨u8Val 41, callerMemV2Byte42⟩) := by
  have h := spec_and_behaviorV2_of_exec_eq (p := progV2LoadU8)
    (q := queryV2Load42) (fuel := 2) (out := outV2Load42) rfl
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 _ rfl, ?_⟩
  intro h_wrong
  -- `execProgV2` reduces to the equation `outV2Load42 = .returned ⟨41, _⟩`;
  -- comparing the returned bits refutes it.
  have h_bits := congrArg
    (fun o : TerminalOut => match o with
      | .returned ⟨.scalar sv, _⟩ => sv.bits.toNat
      | _ => 0) h_wrong
  exact absurd h_bits (by decide)

/-- The single `StepV2` of `progV2LoadU8` on `queryV2LoadNull` faults with
`.undefined`: a provenance-free pointer may only be dereferenced at a
non-null address for a zero-sized pointee. -/
theorem progV2LoadU8_null_faults :
    ∃ s₀ : State, initStateV2 progV2LoadU8 queryV2LoadNull = .ok s₀ ∧
      evalStepV2 progV2LoadU8 s₀ = .fault .undefined :=
  ⟨_, rfl, rfl⟩

/-- Negative canary: dereferencing a null `*const u8` reaches
`.fault .undefined`, so `(progV2LoadU8, queryV2LoadNull)` is not
`WellFormedV2`, satisfies no postcondition, and no `execProgV2` premise holds
for it. -/
theorem canary_v2_negative_null_load :
    ReachesResultV2 progV2LoadU8 queryV2LoadNull (.fault .undefined) ∧
    ¬ WellFormedV2 progV2LoadU8 queryV2LoadNull ∧
    (∀ post : TerminalOut → Prop,
      ¬ SatisfiesPostV2 progV2LoadU8 queryV2LoadNull post) ∧
    (∀ (fuel : Nat) (post : TerminalOut → Prop),
      ¬ execProgV2 progV2LoadU8 fuel queryV2LoadNull post) := by
  let ⟨s₀, h_init, h_step⟩ := progV2LoadU8_null_faults
  have h_reach :
      ReachesResultV2 progV2LoadU8 queryV2LoadNull (.fault .undefined) := by
    unfold ReachesResultV2
    rw [h_init]
    exact ⟨s₀, ReachesV2.refl s₀, 0, rfl, h_step⟩
  have h_nwf : ¬ WellFormedV2 progV2LoadU8 queryV2LoadNull :=
    fun h_wf => h_wf.2 .undefined h_reach
  refine ⟨h_reach, h_nwf, fun _ h_sat => h_nwf h_sat.1, ?_⟩
  intro fuel post h_exec
  unfold execProgV2 at h_exec
  rw [h_init] at h_exec
  cases fuel with
  | zero => exact h_exec
  | succ n =>
    change (match evalStepV2 progV2LoadU8 s₀ with
      | .step st' => execOutcomeStateV2 progV2LoadU8 post (fun _ => False) n st'
      | .done out => post out
      | .fault _ => False) at h_exec
    rw [h_step] at h_exec
    exact h_exec

/-- A state that steps to itself reaches only itself. -/
theorem reachesV2_of_self_step {p : Program} {s₀ : State}
    (h_step : evalStepV2 p s₀ = .step s₀) :
    ∀ {s₁ s : State}, ReachesV2 p s₁ s → s₁ = s₀ → s = s₀ := by
  intro s₁ s h_r
  induction h_r with
  | refl => intro h; exact h
  | tail _ h_last ih =>
    intro h
    have h_mid := ih h
    subst h_mid
    let ⟨_, _, h_eval⟩ := h_last
    have h_eval' : evalStepV2 p _ = .step _ := h_eval
    rw [h_step] at h_eval'
    injection h_eval' with h_eq
    exact h_eq.symm

/-- The initial state of `progV2Spin` steps to itself. -/
theorem progV2Spin_self_step :
    ∃ s₀ : State, initStateV2 progV2Spin queryEmpty = .ok s₀ ∧
      evalStepV2 progV2Spin s₀ = .step s₀ :=
  ⟨_, rfl, rfl⟩

/-- Divergence canary: `progV2Spin` is `WellFormedV2` and vacuously satisfies
the postcondition `False` (it has no terminal behavior), yet `DivergesV2`
holds and no `execProgV2` premise holds for it. So `SatisfiesPostV2` alone
does not imply termination, and the `¬ DivergesV2` conjunct of
`ExecSoundnessClaimV2` is not redundant. -/
theorem canary_v2_diverges_spin :
    WellFormedV2 progV2Spin queryEmpty ∧
    SatisfiesPostV2 progV2Spin queryEmpty (fun _ => False) ∧
    DivergesV2 progV2Spin queryEmpty ∧
    (∀ (fuel : Nat) (post : TerminalOut → Prop),
      ¬ execProgV2 progV2Spin fuel queryEmpty post) := by
  let ⟨s₀, h_init, h_step⟩ := progV2Spin_self_step
  -- Every reachable state is `s₀`.
  have h_only : ∀ s, ReachesV2 progV2Spin s₀ s → s = s₀ :=
    fun _ h_r => reachesV2_of_self_step h_step h_r rfl
  -- No reachable state terminates or faults.
  have h_no_end : ∀ res, ReachesResultV2 progV2Spin queryEmpty res →
      res = .step s₀ := by
    intro res h_res
    unfold ReachesResultV2 at h_res
    rw [h_init] at h_res
    let ⟨s, h_r, _, _, h_eval⟩ := h_res
    rw [h_only s h_r] at h_eval
    have h_eval' : evalStepV2 progV2Spin s₀ = res := h_eval
    rw [h_step] at h_eval'
    exact h_eval'.symm
  have h_wf : WellFormedV2 progV2Spin queryEmpty := by
    refine ⟨⟨s₀, h_init, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩
    intro k h_fault
    cases h_no_end _ h_fault
  refine ⟨h_wf, ⟨h_wf, fun out h_b => ?_⟩, ?_, ?_⟩
  · cases h_no_end _ h_b
  · exact ⟨s₀, h_init, fun _ => s₀, rfl, fun _ => ⟨0, rfl, h_step⟩⟩
  · intro fuel post h_exec
    unfold execProgV2 at h_exec
    rw [h_init] at h_exec
    induction fuel with
    | zero => exact h_exec
    | succ n ih =>
      change (match evalStepV2 progV2Spin s₀ with
        | .step st' => execOutcomeStateV2 progV2Spin post (fun _ => False) n st'
        | .done out => post out
        | .fault _ => False) at h_exec
      rw [h_step] at h_exec
      exact ih h_exec

end Anneal.MirWp

end
