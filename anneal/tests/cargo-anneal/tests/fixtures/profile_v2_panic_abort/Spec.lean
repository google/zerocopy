-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def divCeilExpect (a b : Nat) : Nat :=
  (a / b) + (if a % b = 0 then 0 else 1)

def divCeilPostReturn (q : Query) (out : Out) : Prop :=
  match q.args with
  | [.scalar a, .scalar b] =>
    match out.ret with
    | .scalar r =>
      r.width = .isize ∧
      r.signed = false ∧
      r.bits.toNat = divCeilExpect a.bits.toNat b.bits.toNat ∧
      out.callerMem = q.callerMem
    | _ => False
  | _ => False

def divCeilAllowAbort : SafeContractV2 := {
  behaviorPre := fun _ => True
  effects := { allowAbort := true }
  postReturn := divCeilPostReturn
  postAbort := fun q cm =>
    match q.args with
    | [_, .scalar b] => b.bits.toNat = 0 ∧ cm = q.callerMem
    | _ => False
}

def divCeilNoAbort : SafeContractV2 := {
  behaviorPre := fun q =>
    match q.args with
    | [_, .scalar b] => b.bits.toNat ≠ 0
    | _ => False
  effects := EffectMaskV2.noAbort
  postReturn := divCeilPostReturn
}

def writeThenDivSlotPost (q : Query) (cm : CallerMemory) : Prop :=
  match q.args with
  | [.ptr pv, .scalar a, .scalar _] =>
    match pv.allocId with
    | none => False
    | some aid =>
      ∃ mem' : MemoryState,
        storeIndirectV2 (entryMemoryWithCaller q.callerMem) (.int .isize false)
          ⟨aid, pv.offsetBytes.toNat⟩ (.scalar a) = .ok mem' ∧
        cm = extractCallerMemory q.callerMem mem'
  | _ => False

def writeThenDivAllowAbort : SafeContractV2 := {
  behaviorPre := fun _ => True
  effects := { allowAbort := true }
  postReturn := fun q out =>
    match q.args with
    | [.ptr _, .scalar a, .scalar b] =>
      match out.ret with
      | .scalar r =>
        r.width = .isize ∧
        r.signed = false ∧
        r.bits.toNat = a.bits.toNat / b.bits.toNat ∧
        writeThenDivSlotPost q out.callerMem
      | _ => False
    | _ => False
  postAbort := fun q cm =>
    match q.args with
    | [.ptr _, .scalar _, .scalar b] =>
      b.bits.toNat = 0 ∧ writeThenDivSlotPost q cm
    | _ => False
}

def writeThenDivNoAbort : SafeContractV2 := {
  behaviorPre := fun q =>
    match q.args with
    | [_, _, .scalar b] => b.bits.toNat ≠ 0
    | _ => False
  effects := EffectMaskV2.noAbort
  postReturn := writeThenDivAllowAbort.postReturn
}

def property (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 0,
      Trusted.MirSemantics.getElem? p.bodies 1 with
  | some body0, some body1 =>
    BodySatisfiesSafeContractV2 p 0 body0 divCeilAllowAbort ∧
    BodySatisfiesSafeContractV2 p 0 body0 divCeilNoAbort ∧
    BodySatisfiesSafeContractV2 p 1 body1 writeThenDivAllowAbort ∧
    BodySatisfiesSafeContractV2 p 1 body1 writeThenDivNoAbort
  | _, _ => False

def specs : SpecsV2 := ⟨fun _ _ => True, property⟩

end Spec
