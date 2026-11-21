-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import VendorArm64Ref.Decode
import VendorArm64Ref.SemanticsScalar
import VendorArm64Ref.SemanticsNeon

/-!
# `VendorArm64Ref.Machine`

Top-level AArch64 Pass-2 single-step and `N`-step operational machine
(`execStep`, `execStepsN`, `Step`, `StepsN`, and `execStepsN_implies_stepsN`).
-/

namespace VendorArm64Ref

def execInstr (exclSpuriousFail : Bool) (lse2Align16B : Bool) (ins : Instr)
    (s : MachineState) : MachineState :=
  match execScalarInstr exclSpuriousFail lse2Align16B ins s with
  | some s' => s'
  | none =>
    match execNeonInstr ins s with
    | some s' => s'
    | none => { s with fault := some .undefinedEncoding }

def execStep (code : CodeMap) (exclSpuriousFail : Bool) (lse2Align16B : Bool)
    (s : MachineState) : MachineState :=
  if s.halted || s.fault.isSome then s
  else
    match fetchWord32 code s.pc with
    | .error f => { s with fault := some f }
    | .ok w =>
      match decodeWord32 w with
      | .error f => { s with fault := some f }
      | .ok ins  => execInstr exclSpuriousFail lse2Align16B ins s

def execStepsN (code : CodeMap) (exclSpuriousFail : Bool) (lse2Align16B : Bool)
    (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec (motive := fun _ => MachineState → MachineState)
    (fun st => st)
    (fun _ ih st => ih (execStep code exclSpuriousFail lse2Align16B st))
    n s

/-- Normative Pass-2 relational single-step transition (`Step`):
    quantifies over demonic `ExclusiveMonitorsPass` spurious clear (`exclSpuriousFail : Bool`). -/
def Step (code : CodeMap) (lse2Align16B : Bool) (s s' : MachineState) : Prop :=
  ∃ exclSpuriousFail : Bool, execStep code exclSpuriousFail lse2Align16B s = s'

inductive StepsN (code : CodeMap) (lse2Align16B : Bool) : Nat → MachineState → MachineState → Prop where
  | zero (s : MachineState) : StepsN code lse2Align16B 0 s s
  | step {n : Nat} {s s1 s2 : MachineState} :
      Step code lse2Align16B s s1 →
      StepsN code lse2Align16B n s1 s2 →
      StepsN code lse2Align16B (n + 1) s s2

theorem execStepsN_implies_stepsN (code : CodeMap) (exclSpuriousFail : Bool)
    (lse2Align16B : Bool) (n : Nat) (s : MachineState) :
    StepsN code lse2Align16B n s (execStepsN code exclSpuriousFail lse2Align16B n s) :=
  Nat.rec (motive := fun k => ∀ st, StepsN code lse2Align16B k st (execStepsN code exclSpuriousFail lse2Align16B k st))
    (fun st => StepsN.zero st)
    (fun _ ih st =>
      StepsN.step ⟨exclSpuriousFail, rfl⟩ (ih (execStep code exclSpuriousFail lse2Align16B st)))
    n s

/-- Computable, kernel-reducible `Nat.rec` list lookup (`0` `isPartial`, instant WHNF on concrete lists). -/
def listGetOpt {α : Type} (xs : List α) (idx : Nat) : Option α :=
  let tail := Nat.rec (motive := fun _ => List α)
    xs
    (fun _ cur => match cur with | [] => [] | _ :: tl => tl)
    idx
  match tail with
  | hd :: _ => some hd
  | []      => none

def loadWordsAt (base : BitVec 64) (words : List (BitVec 32)) : CodeMap :=
  fun addr =>
    let off := (addr - base).toNat
    let wIdx := off / 4
    let bIdx := off % 4
    if addr == base + BitVec.ofNat 64 off then
      match listGetOpt words wIdx with
      | some w => some (BitVec.extractLsb' (bIdx * 8) 8 w)
      | none   => none
    else none

end VendorArm64Ref
