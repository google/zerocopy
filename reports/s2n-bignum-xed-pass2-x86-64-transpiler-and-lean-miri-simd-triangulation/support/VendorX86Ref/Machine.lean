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
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import VendorX86Ref.Types
import VendorX86Ref.Decode
import VendorX86Ref.SemanticsScalar
import VendorX86Ref.SemanticsSimd

/-!
# `VendorX86Ref.Machine`

Top-level relational Pass-2 reference machine (`Step`, `StepsN`) combining
16-byte fetch-window decoding (`decodeRef`) with `execScalar` and `execSimd`.
-/

namespace VendorX86Ref

/-- Fetch 16 architectural bytes starting at `rip`. -/
def fetchWindow16 (code : CodeMap) (rip : BitVec 64) : List (BitVec 8) :=
  [ code (rip + 0#64),  code (rip + 1#64),  code (rip + 2#64),  code (rip + 3#64),
    code (rip + 4#64),  code (rip + 5#64),  code (rip + 6#64),  code (rip + 7#64),
    code (rip + 8#64),  code (rip + 9#64),  code (rip + 10#64), code (rip + 11#64),
    code (rip + 12#64), code (rip + 13#64), code (rip + 14#64), code (rip + 15#64) ]

def execInstr (ins : Instr) (nextRip : BitVec 64) (oracle : UndefOracle) (s : MachineState) :
    MachineState :=
  match execScalar ins nextRip oracle s with
  | some s' => s'
  | none =>
    match execSimd ins nextRip s with
    | some s' => s'
    | none => { s with fault := some .udUnmapped }

/-- Deterministic oracle-parameterized single-step transition of `VendorX86Ref`. -/
def stepWithOracle (code : CodeMap) (oracle : UndefOracle) (s : MachineState) : MachineState :=
  if s.halted || s.fault.isSome then s
  else
    match decodeRef (fetchWindow16 code s.rip) with
    | .fault fk => { s with fault := some fk }
    | .ok ins len => execInstr ins (s.rip + BitVec.ofNat 64 len) oracle s

/-- Relational Pass-2 small-step transition (`∃ oracle, stepWithOracle code oracle s = s'`),
    corresponding to `s2n-bignum`'s relational `x86_step` (`UNDEFINED_VALUES[...]`). -/
def Step (code : CodeMap) (s s' : MachineState) : Prop :=
  ∃ oracle : UndefOracle, stepWithOracle code oracle s = s'

/-- Multi-step relational transition of `VendorX86Ref`. -/
inductive StepsN (code : CodeMap) : Nat → MachineState → MachineState → Prop where
  | zero (s : MachineState) : StepsN code 0 s s
  | succ {n : Nat} {s s1 s2 : MachineState} :
      Step code s s1 → StepsN code n s1 s2 → StepsN code (n + 1) s s2

/-- Deterministic `n`-step runner under a fixed `UndefOracle`. -/
def execStepsN (code : CodeMap) (n : Nat) (oracle : UndefOracle) (s : MachineState) : MachineState :=
  Nat.rec (motive := fun _ => MachineState → MachineState)
    (fun s0 => s0)
    (fun _ ih s0 => ih (stepWithOracle code oracle s0))
    n s

theorem execStepsN_implies_stepsN (code : CodeMap) (n : Nat) (oracle : UndefOracle) (s : MachineState) :
    StepsN code n s (execStepsN code n oracle s) := by
  induction n generalizing s with
  | zero => exact .zero s
  | succ k ih => exact .succ ⟨oracle, rfl⟩ (ih (stepWithOracle code oracle s))

end VendorX86Ref
