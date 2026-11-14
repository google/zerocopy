-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

namespace Anneal.QuarantineProto

abbrev RegId := Nat

structure MachState where
  regs : RegId → BitVec 64

def MachState.read (st : MachState) (r : RegId) : BitVec 64 := st.regs r

def MachState.write (st : MachState) (r : RegId) (v : BitVec 64) : MachState :=
  { regs := fun x => if x == r then v else st.regs x }

inductive CoreExpr where
  | const (v : BitVec 64)
  | var (r : RegId)
  | add (a b : CoreExpr)
  | sub (a b : CoreExpr)
  | mul (a b : CoreExpr)
  | bxor (a b : CoreExpr)
  | band (a b : CoreExpr)
  | bor (a b : CoreExpr)
  | shl (a : CoreExpr) (n : Nat)
  deriving Repr, DecidableEq

def evalExpr (e : CoreExpr) (st : MachState) : BitVec 64 :=
  match e with
  | .const v => v
  | .var r => st.read r
  | .add a b => evalExpr a st + evalExpr b st
  | .sub a b => evalExpr a st - evalExpr b st
  | .mul a b => evalExpr a st * evalExpr b st
  | .bxor a b => evalExpr a st ^^^ evalExpr b st
  | .band a b => evalExpr a st &&& evalExpr b st
  | .bor a b => evalExpr a st ||| evalExpr b st
  | .shl a n => evalExpr a st <<< n

inductive CoreStmt where
  | nop
  | assign (dst : RegId) (rhs : CoreExpr)
  deriving Repr, DecidableEq

def evalStmt (s : CoreStmt) (st : MachState) : MachState :=
  match s with
  | .nop => st
  | .assign dst rhs => st.write dst (evalExpr rhs st)

/-- Witness of semantic refinement between source and optimized CoreStmt. -/
structure StmtDeriv (src tgt : CoreStmt) : Prop where
  sound : ∀ st : MachState, evalStmt tgt st = evalStmt src st

theorem StmtDeriv.refl (s : CoreStmt) : StmtDeriv s s :=
  ⟨fun _ => rfl⟩

theorem StmtDeriv.trans {s1 s2 s3 : CoreStmt} (d1 : StmtDeriv s1 s2) (d2 : StmtDeriv s2 s3) :
    StmtDeriv s1 s3 :=
  ⟨fun st => by rw [d2.sound st, d1.sound st]⟩

structure TargetAbiSpec where
  triple : String
  intArgRegs : Nat
  floatInVectorRegs : Bool
  deriving Repr, DecidableEq

def ProductiveCompiles (abi : TargetAbiSpec) (src tgt : CoreStmt) : Prop :=
  abi.intArgRegs > 0 ∧ StmtDeriv src tgt

end Anneal.QuarantineProto
