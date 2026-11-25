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

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp StepLemmas

noncomputable abbrev P : Program := entryProgForBody Captured.program 0

/-- Runs `guarded_add_u8` from entry. `x < 255` takes `bb1`, whose
`AddWithOverflow` pair reports no overflow, so `assert(!move (_5.1))`
continues to `bb2`, which moves `_5.0` into the return place. Otherwise `bb3`
returns `255`. -/
theorem guarded_run (cm : CallerMemory) (m : MemoryState) (bits : BitVec 128)
    (hT : truncateBits .i8 bits = bits) (post : TerminalOut → Prop)
    (hInc : bits.toNat < 255 → post (.returned
      ⟨u8 (BitVec.ofNat 128 (bits.toNat + 1)), extractCallerMemory cm m⟩))
    (hSat : ¬ bits.toNat < 255 → post (.returned
      ⟨u8 255#128, extractCallerMemory cm m⟩)) :
    Runs P post (st 0 0 [N, im (u8 bits), D, D, D, N] cm m) := by
  have hC := checkVal_u8 hT
  let x := im (u8 bits)
  have h255 : decodeScalar ⟨.i8, false, 255#128⟩ = Int.ofNat 255 := rfl
  have hLtStep : evalStepV2 P (st 0 3 [N, x, N, x, D, N] cm m) =
      .step (st 0 4 [N, x, im (.bool (decide (Int.ofNat bits.toNat <
        Int.ofNat 255))), N, D, N] cm m) := by
    rw [← h255, ← decode_u8 hT]
    exact step_assign rfl rfl rfl rfl rfl (writePlaceDestV2_local rfl rfl rfl)
  refine runs_step (s' := st 0 1 [N, x, N, D, D, N] cm m) rfl <|
    runs_step (s' := st 0 2 [N, x, N, N, D, N] cm m) rfl <|
    runs_step
      (step_assign rfl rfl rfl rfl rfl (writePlaceDestV2_local hC rfl rfl)) <|
    runs_step hLtStep ?_
  cases hc : decide (Int.ofNat bits.toNat < Int.ofNat 255) with
  | true =>
    have hLt : bits.toNat < 255 := Int.ofNat_lt.mp (of_decide_eq_true hc)
    have hLt' : bits.toNat + 1 < 256 := Nat.succ_lt_succ hLt
    let r := BitVec.ofNat 128 (bits.toNat + 1)
    have hCr : checkValV2 (u8 r) (.int .i8 false) = true :=
      checkVal_u8 (truncate_u8_ofNat hLt')
    have hCt : checkValV2 (.tuple [u8 r, .bool false])
        (.tuple [.int .i8 false, .bool]) = true := by
      change (checkValV2 (u8 r) (.int .i8 false) && (true && true)) = true
      rw [hCr]
      rfl
    have hAdd : evalStepV2 P (st 1 3 [N, x, N, D, x, N] cm m) =
        .step (st 1 4 [N, x, N, D, x, im (.tuple [u8 r, .bool false])]
          cm m) := by
      refine step_assign rfl rfl rfl rfl ?_
        (writePlaceDestV2_local (locals := [N, x, N, D, x, N]) hCt rfl rfl)
      change (match evalBinOp .addWithOverflow (u8 bits) (u8 1#128) with
        | .error k => Except.error k
        | .ok res => Except.ok (res, [N, x, N, D, x, N], m)) = _
      rw [addWithOverflow_u8 hT hLt']
    refine runs_step (s' := st 1 0 [N, x, N, N, D, N] cm m) rfl <|
      runs_step (s' := st 1 1 [N, x, N, D, D, N] cm m) rfl <|
      runs_step (s' := st 1 2 [N, x, N, D, N, N] cm m) rfl <|
      runs_step
        (step_assign rfl rfl rfl rfl rfl (writePlaceDestV2_local hC rfl rfl)) <|
      runs_step hAdd <|
      -- `assert(!move (_5.1))` leaves `_5.0` behind in a partial tuple.
      runs_step (s' := st 2 0
        [N, x, N, D, x, .partialTuple [some (u8 r), none]] cm m) rfl <|
      runs_step (s' := st 2 1 [im (u8 r), x, N, D, x, N] cm m)
        (step_assign rfl rfl rfl rfl rfl
          (writePlaceDestV2_local hCr rfl rfl)) <|
      runs_step (s' := st 2 2 [im (u8 r), x, N, D, D, N] cm m) rfl <|
      runs_step (s' := st 4 0 [im (u8 r), x, N, D, D, N] cm m) rfl <|
      runs_step (s' := st 4 1 [im (u8 r), x, D, D, D, N] cm m) rfl <|
      runs_done rfl (hInc hLt)
  | false =>
    have hNot : ¬ bits.toNat < 255 :=
      fun h => absurd (Int.ofNat_lt.mpr h) (of_decide_eq_false hc)
    exact runs_step (s' := st 3 0 [N, x, N, N, D, N] cm m) rfl <|
      runs_step (s' := st 3 1 [N, x, N, D, D, N] cm m) rfl <|
      runs_step (s' := st 3 2 [im (u8 255#128), x, N, D, D, N] cm m)
        (step_assign rfl rfl rfl rfl rfl
          (writePlaceDestV2_local rfl rfl rfl)) <|
      runs_step (s' := st 4 0 [im (u8 255#128), x, N, D, D, N] cm m) rfl <|
      runs_step (s' := st 4 1 [im (u8 255#128), x, D, D, D, N] cm m) rfl <|
      runs_done rfl (hSat hNot)

theorem guarded_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q) :
    WellFormedV2 P q ∧ ¬ DivergesV2 P q ∧
    match q.args with
    | [.scalar x] =>
      ∃ out : Out, BehaviorV2 P q (.returned out) ∧
        out.ret = u8 (BitVec.ofNat 128 (Spec.saturatingInc x.bits.toNat))
    | _ => False := by
  let ⟨bits, hArgs, hT⟩ := args_u8 hValid.2.1
  cases q with
  | mk args cm =>
    dsimp only at hArgs
    subst hArgs
    let out : Out := ⟨u8 (BitVec.ofNat 128 (Spec.saturatingInc bits.toNat)),
      extractCallerMemory cm (entryMemoryWithCaller cm)⟩
    have hInit : initStateV2 P ⟨[u8 bits], cm⟩ =
        .ok (st 0 0 [N, im (u8 bits), D, D, D, N] cm
          (entryMemoryWithCaller cm)) :=
      initStateV2_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl hValid
    have hRuns := guarded_run cm _ bits hT (fun o => o = .returned out)
      (fun h => by
        change _ = TerminalOut.returned ⟨u8 (BitVec.ofNat 128
          (if bits.toNat < 255 then bits.toNat + 1 else 255)), _⟩
        rw [ite_prop_true h])
      (fun h => by
        change _ = TerminalOut.returned ⟨u8 (BitVec.ofNat 128
          (if bits.toNat < 255 then bits.toNat + 1 else 255)), _⟩
        rw [ite_prop_false h])
    let ⟨_, hExec⟩ := execProgV2_of_runs hInit hRuns
    let ⟨hWf, hBeh, hNDiv, _⟩ := spec_and_behaviorV2_of_exec_eq hExec
    exact ⟨hWf, hNDiv, out, hBeh, rfl⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro defId body hFound
    cases defId with
    | zero =>
      have hEq : Captured.body_0 = body := Option.some.inj hFound
      subst hEq
      exact ⟨hFound, rfl, fun q hValid _ => (guarded_correct q hValid).1⟩
    | succ _ => cases hFound
  · exact ⟨rfl, rfl, fun q hValid => (guarded_correct q hValid).2⟩

end Proof
