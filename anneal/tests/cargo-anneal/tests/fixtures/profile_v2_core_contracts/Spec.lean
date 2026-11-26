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

def subsliceIdentity : String := "rust-path-v1::subslice"

def optUnwrapIdentity : String := "rust-path-v1::opt_unwrap"

def subsliceSafety (q : Query) : Prop :=
  match q.args with
  | [.slicePtr _ len, .scalar aSv, .scalar bSv] =>
    aSv.bits.toNat ≤ bSv.bits.toNat ∧ bSv.bits.toNat ≤ len.toNat
  | _ => False

def optUnwrapSafety (q : Query) : Prop :=
  match q.args with
  | [.optionVal (some _)] => True
  | _ => False

def safetyPre (identity : String) (q : Query) : Prop :=
  if identity = subsliceIdentity then subsliceSafety q
  else if identity = optUnwrapIdentity then optUnwrapSafety q
  else False

def subslicePost (p : Program) : Prop :=
  ∃ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = subsliceIdentity ∧
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      subsliceSafety q →
      match q.args with
      | [.slicePtr ptr _, .scalar aSv, .scalar bSv] =>
        let pOut :=
          match ptr.allocId with
          | none => ptr
          | some _ =>
            { ptr with
              offsetBytes :=
                UInt64.ofNat (ptr.offsetBytes.toNat + aSv.bits.toNat) }
        let outLen := UInt64.ofNat (bSv.bits.toNat - aSv.bits.toNat)
        BehaviorV2 (entryProgForBody p defId) q
          (TerminalOut.returned ⟨.slicePtr pOut outLen, q.callerMem⟩)
      | _ => False

def optUnwrapPost (p : Program) : Prop :=
  ∃ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = optUnwrapIdentity ∧
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      optUnwrapSafety q →
      match q.args with
      | [.optionVal (some v)] =>
        BehaviorV2 (entryProgForBody p defId) q
          (TerminalOut.returned ⟨v, q.callerMem⟩)
      | _ => False

def property (p : Program) : Prop :=
  subslicePost p ∧ optUnwrapPost p

def specs : SpecsV2 := ⟨safetyPre, property⟩

end Spec
