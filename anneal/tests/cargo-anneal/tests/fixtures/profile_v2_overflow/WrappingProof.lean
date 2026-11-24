-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Spec
import Expected
import StepLemmas

/-! Proof for the capture of `buggy_add_u8` (body `0`) and `zero_pair` (body
`1`) without overflow checks, where `x + 1` is a wrapping `Add`. With overflow
checks the capture of body `0` differs, so this proof no longer checks; no
proof can, because `x = 255` faults. -/

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp StepLemmas

noncomputable abbrev P : Program := entryProgForBody Captured.program 0

theorem wrapping_run (cm : CallerMemory) (m : MemoryState) (bits : BitVec 128)
    (hT : truncateBits .i8 bits = bits) :
    Runs P (fun o => o = .returned ⟨u8 (BitVec.ofNat 128
      ((bits.toNat + 1) % 256)), extractCallerMemory cm m⟩)
      (st 0 0 [N, im (u8 bits), D] cm m) := by
  have hC := checkVal_u8 hT
  have hLt : bits.toNat < 256 := by
    rw [← hT, toNat_truncateBits]
    exact Nat.mod_lt _ (by decide)
  let x := im (u8 bits)
  let r := BitVec.ofNat 128 ((bits.toNat + 1) % 256)
  have hCr : checkValV2 (u8 r) (.int .i8 false) = true :=
    checkVal_u8 (truncate_u8_ofNat (Nat.mod_lt _ (by decide)))
  have hAdd : evalStepV2 P (st 0 2 [N, x, x] cm m) =
      .step (st 0 3 [im (u8 r), x, N] cm m) := by
    refine step_assign rfl rfl rfl rfl ?_
      (writePlaceDestV2_local (locals := [N, x, N]) hCr rfl rfl)
    change (match evalBinOp .add (u8 bits) (u8 1#128) with
      | .error k => Except.error k
      | .ok res => Except.ok (res, [N, x, N], m)) = _
    rw [add_u8 hT hLt]
  exact runs_step (s' := st 0 1 [N, x, N] cm m) rfl <|
    runs_step
      (step_assign rfl rfl rfl rfl rfl (writePlaceDestV2_local hC rfl rfl)) <|
    runs_step hAdd <|
    runs_step (s' := st 0 4 [im (u8 r), x, D] cm m) rfl <|
    runs_done rfl rfl

theorem wrapping_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q) :
    WellFormedV2 P q ∧ ¬ DivergesV2 P q ∧
    match q.args with
    | [.scalar x] =>
      ∃ out : Out, BehaviorV2 P q (.returned out) ∧
        out.ret = u8 (BitVec.ofNat 128 ((x.bits.toNat + 1) % 256))
    | _ => False := by
  let ⟨bits, hArgs, hT⟩ := args_u8 hValid.2.1
  cases q with
  | mk args cm =>
    dsimp only at hArgs
    subst hArgs
    have hInit : initStateV2 P ⟨[u8 bits], cm⟩ =
        .ok (st 0 0 [N, im (u8 bits), D] cm (entryMemoryWithCaller cm)) :=
      initStateV2_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl hValid
    let ⟨_, hExec⟩ := execProgV2_of_runs hInit (wrapping_run cm _ bits hT)
    let ⟨hWf, hBeh, hNDiv, _⟩ := spec_and_behaviorV2_of_exec_eq hExec
    exact ⟨hWf, hNDiv, _, hBeh, rfl⟩

/-- `zero_pair` takes no arguments and returns `(0, 0)` in one step. -/
theorem zero_pair_wellFormed (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q) :
    WellFormedV2 (entryProgForBody Captured.program 1) q := by
  have hArgs : q.args = [] := by
    cases hA : q.args with
    | nil => rfl
    | cons _ _ => have h := hValid.2.1; rw [hA] at h; cases h
  cases q with
  | mk args cm =>
    dsimp only at hArgs
    subst hArgs
    let P1 := entryProgForBody Captured.program 1
    let s₀ : State :=
      ⟨[⟨1, 0, 0, [N], none, none, none⟩], cm, entryMemoryWithCaller cm⟩
    have hInit : initStateV2 P1 ⟨[], cm⟩ = .ok s₀ :=
      initStateV2_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl hValid
    have hRuns : Runs P1 (fun o => o = .returned ⟨.tuple [u8 0#128, u8 0#128],
        extractCallerMemory cm (entryMemoryWithCaller cm)⟩) s₀ :=
      runs_step (s' := ⟨[⟨1, 0, 1, [im (.tuple [u8 0#128, u8 0#128])],
          none, none, none⟩], cm,
        entryMemoryWithCaller cm⟩) rfl (runs_done rfl rfl)
    let ⟨_, hExec⟩ := execProgV2_of_runs hInit hRuns
    exact (spec_and_behaviorV2_of_exec_eq hExec).1

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro defId body hFound
    match defId, hFound with
    | 0, hFound =>
      have hEq : Captured.body_0 = body := Option.some.inj hFound
      subst hEq
      exact ⟨hFound, rfl, fun q hValid _ => (wrapping_correct q hValid).1⟩
    | 1, hFound =>
      have hEq : Captured.body_1 = body := Option.some.inj hFound
      subst hEq
      exact ⟨hFound, rfl, fun q hValid _ => zero_pair_wellFormed q hValid⟩
    | _ + 2, hFound => cases hFound
  · exact ⟨rfl, fun q hValid => (wrapping_correct q hValid).2⟩

end Proof
