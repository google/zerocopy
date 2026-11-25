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

def loadU32Identity : String := "rust-path-v1::load_u32"

def storeU8Identity : String := "rust-path-v1::store_u8"

def loadU32Safety (q : Query) : Prop :=
  match q.args with
  | [.ptr pv] =>
    match pv.allocId with
    | none => False
    | some aid =>
      ∃ a : Allocation,
        findAllocation aid q.callerMem.allocations = some a ∧
        a.live = true ∧
        isInBounds a pv.offsetBytes.toNat 4 = true ∧
        isAligned a pv.offsetBytes.toNat 2 = true ∧
        isSliceAllInit ((a.bytes.drop pv.offsetBytes.toNat).take 4) = true
  | _ => False

def storeU8Safety (q : Query) : Prop :=
  match q.args with
  | [.ptr pv, .scalar _] =>
    match pv.allocId with
    | none => False
    | some aid =>
      ∃ a : Allocation,
        findAllocation aid q.callerMem.allocations = some a ∧
        a.live = true ∧
        a.mutability = .mut ∧
        isInBounds a pv.offsetBytes.toNat 1 = true
  | _ => False

def safetyPre (identity : String) (q : Query) : Prop :=
  if identity = loadU32Identity then loadU32Safety q
  else if identity = storeU8Identity then storeU8Safety q
  else False

def loadU32Post (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 0 with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      loadU32Safety q →
      match q.args with
      | [.ptr pv] =>
        match pv.allocId with
        | none => False
        | some aid =>
          ∃ v : Val,
            loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.int .i32 false)
              ⟨aid, pv.offsetBytes.toNat⟩ = .ok (some v) ∧
            BehaviorV2 (entryProgForBody p 0) q
              (TerminalOut.returned ⟨v, q.callerMem⟩)
      | _ => False

def storeU8Post (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 1 with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      storeU8Safety q →
      match q.args with
      | [.ptr pv, .scalar sv] =>
        match pv.allocId with
        | none => False
        | some aid =>
          ∃ mem' : MemoryState,
            storeIndirectV2 (entryMemoryWithCaller q.callerMem) (.int .i8 false)
              ⟨aid, pv.offsetBytes.toNat⟩ (.scalar sv) = .ok mem' ∧
            BehaviorV2 (entryProgForBody p 1) q
              (TerminalOut.returned ⟨.unit, extractCallerMemory q.callerMem mem'⟩)
      | _ => False

def property (p : Program) : Prop :=
  loadU32Post p ∧ storeU8Post p

def specs : SpecsV2 := ⟨safetyPre, property⟩

end Spec
