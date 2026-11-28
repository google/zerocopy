-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Anneal.MirWp
import Spec
import Expected

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

private theorem wpOutcomeState_step {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s s' : State}
    (hStep : evalStep p 0 s = .step s')
    (hNext : wpOutcomeState p onDone onFault fuel s') :
    wpOutcomeState p onDone onFault (fuel + 1) s :=
  ⟨⟨0, rfl⟩, fun c hc => by
    have hc0 : c = 0 := hc
    rw [hc0, hStep]
    exact hNext⟩

private theorem wpOutcomeState_done {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State} {out : TerminalOut}
    (hStep : evalStep p 0 s = .done out)
    (hDone : onDone out) :
    wpOutcomeState p onDone onFault (fuel + 1) s :=
  ⟨⟨0, rfl⟩, fun c hc => by
    have hc0 : c = 0 := hc
    rw [hc0, hStep]
    exact hDone⟩

private theorem div16_evalBinOp (bits : BitVec 128)
    (hTr : truncateBits .i64 bits = bits)
    (hLt : bits.toNat < Nat.pow 2 64) :
    evalBinOp .div (.scalar ⟨.i64, false, bits⟩)
      (.scalar ⟨.i64, false, BitVec.ofNat 128 16⟩) =
      .ok (.scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.div bits.toNat 16)⟩) := by
  have hDivLt : Nat.div bits.toNat 16 < Nat.pow 2 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLt
  have hDiv128 : Nat.div bits.toNat 16 < Nat.pow 2 128 :=
    Nat.lt_trans hDivLt (by decide)
  have hMod128 :
      (intEmod (Int.ofNat (Nat.div bits.toNat 16))
        (Int.ofNat (Nat.pow 2 128))).toNat = Nat.div bits.toNat 16 := by
    have hM : Nat.mod (Nat.div bits.toNat 16) (Nat.pow 2 128) =
        Nat.div bits.toNat 16 := Nat.mod_eq_of_lt hDiv128
    change (Int.ofNat (Nat.mod (Nat.div bits.toNat 16)
      (Nat.pow 2 128))).toNat = Nat.div bits.toNat 16
    rw [hM]; rfl
  have hTrEq :
      truncateBits .i64 (BitVec.ofNat 128 (Nat.div bits.toNat 16)) =
        BitVec.ofNat 128 (Nat.div bits.toNat 16) := by
    apply bitVec_eq_of_toNat_eq
    rw [toNat_truncateBits]
    have hBv :
        (BitVec.ofNat 128 (Nat.div bits.toNat 16)).toNat =
          Nat.mod (Nat.div bits.toNat 16) (Nat.pow 2 128) := rfl
    have hM128 : Nat.mod (Nat.div bits.toNat 16) (Nat.pow 2 128) =
        Nat.div bits.toNat 16 := Nat.mod_eq_of_lt hDiv128
    rw [hBv, hM128]
    exact Nat.mod_eq_of_lt hDivLt
  dsimp only [evalBinOp, evalArithOp, decodeScalar]
  rw [hTr]
  change (if false then Except.error FaultKind.unsupported
    else if false then Except.error FaultKind.unsupported
    else if false then Except.error FaultKind.undefined
    else if false && true &&
        (Int.ofNat bits.toNat == signedMinInt .i64 &&
          Int.ofNat 16 == Neg.neg 1) then Except.error FaultKind.undefined
    else
      match truncateScalar .i64 false
          (intTdiv (Int.ofNat bits.toNat) (Int.ofNat 16)) with
      | .error k => Except.error k
      | .ok (val, lossy) =>
        if ((decide (intTdiv (Int.ofNat bits.toNat) (Int.ofNat 16) < 0) ||
            decide (intTdiv (Int.ofNat bits.toNat) (Int.ofNat 16) ≥
              HPow.hPow (2 : Int) 128)) || lossy) && false then Except.error FaultKind.undefined
        else if false then Except.error FaultKind.unsupported
        else Except.ok (Val.scalar val)) = _
  dsimp only [truncateScalar, intTdiv, bvOfInt]
  rw [hMod128, hTrEq]
  simp [Bool.and_false, bne_self_eq_false]

private theorem checkVal_u64_inv {v : Val}
    (h : checkVal v (.int .i64 false) = true) :
    ∃ bits : BitVec 128, v = .scalar ⟨.i64, false, bits⟩ ∧
      ScalarVal.wf ⟨.i64, false, bits⟩ = true := by
  unfold checkVal at h
  cases v with
  | scalar sv =>
    cases sv with
    | mk w s bits =>
      cases hwf : ScalarVal.wf ⟨w, s, bits⟩ with
      | false =>
        change (match if ScalarVal.wf ⟨w, s, bits⟩ then some (MirTy.int w s) else none with
          | some ty => MirTy.beq ty (.int .i64 false)
          | none => false) = true at h
        rw [hwf] at h; cases h
      | true =>
        change (match if ScalarVal.wf ⟨w, s, bits⟩ then some (MirTy.int w s) else none with
          | some ty => MirTy.beq ty (.int .i64 false)
          | none => false) = true at h
        rw [hwf] at h
        cases w with
        | i64 =>
          cases s with
          | false => exact ⟨bits, rfl, hwf⟩
          | true => cases h
        | _ => cases h
  | enumVal ety discr =>
    cases hValid : enumAdmitted ety && Nat.blt discr ety.discriminants.length with
    | false =>
      change (match if (enumAdmitted ety && Nat.blt discr ety.discriminants.length) = true
          then some (MirTy.enum ety) else none with
        | some ty => MirTy.beq ty (.int .i64 false)
        | none => false) = true at h
      rw [hValid] at h; cases h
    | true =>
      change (match if (enumAdmitted ety && Nat.blt discr ety.discriminants.length) = true
          then some (MirTy.enum ety) else none with
        | some ty => MirTy.beq ty (.int .i64 false)
        | none => false) = true at h
      rw [hValid] at h; cases h
  | tuple fs =>
    cases fs with
    | nil => cases h
    | cons a r1 =>
      cases r1 with
      | nil => cases a <;> cases h
      | cons b r2 =>
        cases r2 with
        | cons _ _ => cases a <;> cases b <;> cases h
        | nil =>
          cases a with
          | scalar sv =>
            cases b with
            | bool _ =>
              cases hwf : sv.wf with
              | false =>
                change (match if sv.wf = true
                    then some (MirTy.tuple [.int sv.width sv.signed, .bool])
                    else none with
                  | some ty => MirTy.beq ty (.int .i64 false)
                  | none => false) = true at h
                rw [hwf] at h; cases h
              | true =>
                change (match if sv.wf = true
                    then some (MirTy.tuple [.int sv.width sv.signed, .bool])
                    else none with
                  | some ty => MirTy.beq ty (.int .i64 false)
                  | none => false) = true at h
                rw [hwf] at h; cases h
            | _ => cases h
          | _ => cases h
  | _ => cases h

private theorem div16_wf (args : List Val) (hValid : ValidEntryArgs Captured.body_0 args) :
    WellFormed (entryProgForBody Captured.program 0) { args := args } := by
  change checkArgsMatch args [.int .i64 false] = true at hValid
  cases args with
  | nil => cases hValid
  | cons v rest =>
    cases rest with
    | cons a1 rest1 =>
      change checkVal v (.int .i64 false) && checkArgsMatch (a1 :: rest1) [] = true at hValid
      cases h0 : checkVal v (.int .i64 false) <;> rw [h0] at hValid <;> cases hValid
    | nil =>
      change checkVal v (.int .i64 false) && true = true at hValid
      cases h0 : checkVal v (.int .i64 false) with
      | false => rw [h0] at hValid; cases hValid
      | true =>
        let ⟨bits, hvEq, hwf⟩ := checkVal_u64_inv h0
        subst hvEq
        have hTr : truncateBits .i64 bits = bits := by
          unfold ScalarVal.wf at hwf
          exact eq_of_beq hwf
        have hLt : bits.toNat < Nat.pow 2 64 := by
          rw [← hTr, toNat_truncateBits]
          exact Nat.mod_lt _ (by decide)
        have hResWf :
            ScalarVal.wf ⟨.i64, false, BitVec.ofNat 128 (Nat.div bits.toNat 16)⟩ = true := by
          have hDivLt : Nat.div bits.toNat 16 < Nat.pow 2 64 :=
            Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLt
          have hDiv128 : Nat.div bits.toNat 16 < Nat.pow 2 128 :=
            Nat.lt_trans hDivLt (by decide)
          have hResTr :
              truncateBits .i64 (BitVec.ofNat 128 (Nat.div bits.toNat 16)) =
                BitVec.ofNat 128 (Nat.div bits.toNat 16) := by
            apply bitVec_eq_of_toNat_eq
            rw [toNat_truncateBits]
            have hBv :
                (BitVec.ofNat 128 (Nat.div bits.toNat 16)).toNat =
                  Nat.mod (Nat.div bits.toNat 16) (Nat.pow 2 128) := rfl
            have hM128 : Nat.mod (Nat.div bits.toNat 16) (Nat.pow 2 128) =
                Nat.div bits.toNat 16 := Nat.mod_eq_of_lt hDiv128
            rw [hBv, hM128]
            exact Nat.mod_eq_of_lt hDivLt
          unfold ScalarVal.wf
          rw [hResTr]
          exact beq_self_eq_true _
        have hDiv : evalBinOp .div (.scalar ⟨.i64, false, bits⟩)
            (.scalar ⟨.i64, false, BitVec.ofNat 128 16⟩) =
            .ok (.scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.div bits.toNat 16)⟩) :=
          div16_evalBinOp bits hTr hLt
        let vIn : Val := .scalar ⟨.i64, false, bits⟩
        let vOut : Val := .scalar ⟨.i64, false, BitVec.ofNat 128 (Nat.div bits.toNat 16)⟩
        have hCheckIn : checkVal vIn (.int .i64 false) = true := h0
        have hCheckOut : checkVal vOut (.int .i64 false) = true := by
          unfold checkVal
          change (match if ScalarVal.wf ⟨.i64, false, BitVec.ofNat 128 (Nat.div bits.toNat 16)⟩
              then some (MirTy.int .i64 false) else none with
            | some ty => MirTy.beq ty (.int .i64 false)
            | none => false) = true
          rw [hResWf]; rfl
        have hInit :
            initState (entryProgForBody Captured.program 0) { args := [vIn] } =
            .ok (mkState 0 0 [.immediate none, .immediate (some vIn), .dead, .immediate none]) := by
          change (if (!(checkVal vIn (.int .i64 false) && true)) = true then
            Except.error FaultKind.unsupported
          else
            Except.ok (mkState 0 0 [.immediate none, .immediate (some vIn),
              .dead, .immediate none])) = _
          rw [hCheckIn]; rfl
        have hWp :
            wpProg (entryProgForBody Captured.program 0) 10
              { args := [vIn] } (fun _ => True) := by
          unfold wpProg
          rw [hInit]
          refine wpOutcomeState_step (s' := mkState 0 1
            [.immediate none, .immediate (some vIn), .immediate none,
             .immediate none]) rfl ?_
          have hCopy :
              evalStep (entryProgForBody Captured.program 0) 0
                (mkState 0 1 [.immediate none, .immediate (some vIn),
                  .immediate none, .immediate none]) =
              .step (mkState 0 2 [.immediate none, .immediate (some vIn),
                .immediate (some vIn), .immediate none]) := by
            change (match (if (!checkVal vIn (.int .i64 false)) = true then
                Except.error FaultKind.unsupported
              else
                Except.ok ([LocalSlot.immediate none,
                  LocalSlot.immediate (some vIn),
                  LocalSlot.immediate (some vIn),
                  LocalSlot.immediate none], entryMemory)) with
              | Except.error k => StepResult.fault k
              | Except.ok (locals', mem') => StepResult.step (mkState 0 2 locals' 0 mem')) = _
            rw [hCheckIn]; rfl
          refine wpOutcomeState_step hCopy ?_
          refine wpOutcomeState_step (s' := mkState 0 3
            [.immediate none, .immediate (some vIn), .immediate (some vIn),
             .immediate (some (.bool false))]) rfl ?_
          refine wpOutcomeState_step (s' := mkState 1 0
            [.immediate none, .immediate (some vIn), .immediate (some vIn),
             .immediate none]) rfl ?_
          have hDivStep :
              evalStep (entryProgForBody Captured.program 0) 0
                (mkState 1 0 [.immediate none, .immediate (some vIn),
                  .immediate (some vIn), .immediate none]) =
              .step (mkState 1 1 [.immediate (some vOut), .immediate (some vIn),
                .immediate none, .immediate none]) := by
            change (match (match evalBinOp .div vIn
                  (.scalar ⟨.i64, false, BitVec.ofNat 128 16⟩) with
              | Except.error k => Except.error k
              | Except.ok res =>
                Except.ok (res, [LocalSlot.immediate none,
                  LocalSlot.immediate (some vIn), LocalSlot.immediate none,
                  LocalSlot.immediate none], entryMemory)) with
              | Except.error k => StepResult.fault k
              | Except.ok (res, locals1, mem1) =>
                match writePlace locals1 mem1 0 (.int .i64 false) res with
                | Except.error k => StepResult.fault k
                | Except.ok (locals', mem') =>
                  StepResult.step (mkState 1 1 locals' 0 mem')) = _
            rw [hDiv]
            change (match (if (!checkVal vOut (.int .i64 false)) = true then
                Except.error FaultKind.unsupported
              else
                Except.ok ([LocalSlot.immediate (some vOut),
                  LocalSlot.immediate (some vIn), LocalSlot.immediate none,
                  LocalSlot.immediate none], entryMemory)) with
              | Except.error k => StepResult.fault k
              | Except.ok (locals', mem') =>
                StepResult.step (mkState 1 1 locals' 0 mem')) = _
            rw [hCheckOut]; rfl
          refine wpOutcomeState_step hDivStep ?_
          refine wpOutcomeState_step (s' := mkState 1 2
            [.immediate (some vOut), .immediate (some vIn), .dead,
             .immediate none]) rfl ?_
          exact wpOutcomeState_done rfl trivial
        exact (wellFormed_and_spec_of_wp_base _ _ 10 (fun _ => True) hWp).1.1

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, rfl⟩
  intro defId body hBody
  cases defId with
  | zero =>
    change some Captured.body_0 = some body at hBody
    cases hBody
    refine ⟨rfl, by decide, fun args hValid _ => div16_wf args hValid⟩
  | succ _ =>
    change none = some body at hBody
    cases hBody

end Proof
