-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.MirSemantics

/-!
# `usize` unchecked arithmetic polyfills

`<usize as util::polyfills::NumExt>::unchecked_add`, `unchecked_sub`, and
`unchecked_mul` (`zerocopy/src/util/mod.rs`) are `unsafe fn`s whose caller
"promises that the addition will not overflow" (respectively, that the
subtraction will not underflow, or that the multiplication will not
overflow). Each one matches on `checked_*` and reaches
`unreachable_unchecked()` on `None`.

The safety precondition of each function is that the mathematical result is a
`usize`. Under that precondition, every body returns exactly the mathematical
result and leaves the caller's memory unchanged.
-/

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def addIdentity : String :=
  "rust-path-v1::<usize as util::polyfills::NumExt>::unchecked_add"

def subIdentity : String :=
  "rust-path-v1::<usize as util::polyfills::NumExt>::unchecked_sub"

def mulIdentity : String :=
  "rust-path-v1::<usize as util::polyfills::NumExt>::unchecked_mul"

/-- The `usize` value `n`. -/
def usizeVal (n : Nat) : Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 n⟩

/-- `self + rhs` does not overflow `usize`. -/
def addSafety (q : Query) : Prop :=
  match q.args with
  | [.scalar a, .scalar b] => a.bits.toNat + b.bits.toNat < Nat.pow 2 64
  | _ => False

/-- `self - rhs` does not underflow. -/
def subSafety (q : Query) : Prop :=
  match q.args with
  | [.scalar a, .scalar b] => b.bits.toNat ≤ a.bits.toNat
  | _ => False

/-- `self * rhs` does not overflow `usize`. -/
def mulSafety (q : Query) : Prop :=
  match q.args with
  | [.scalar a, .scalar b] => a.bits.toNat * b.bits.toNat < Nat.pow 2 64
  | _ => False

def safetyPre (identity : String) (q : Query) : Prop :=
  if identity = addIdentity then addSafety q
  else if identity = subIdentity then subSafety q
  else if identity = mulIdentity then mulSafety q
  else False

/-- On entry `q`, body `defId` of `p` can reach `out`, and every terminal
behavior it has is `out`. -/
def returnsExactly (p : Program) (defId : DefId) (q : Query)
    (out : TerminalOut) : Prop :=
  BehaviorV2 (entryProgForBody p defId) q out ∧
  SatisfiesPostV2 (entryProgForBody p defId) q (fun o => o = out)

/-- Under `safety`, body `defId` of `p` returns exactly `usizeVal (f a b)` for
arguments `a` and `b`, and leaves the caller's memory unchanged. -/
def returnsResult (p : Program) (defId : DefId) (body : Body)
    (safety : Query → Prop) (f : Nat → Nat → Nat) : Prop :=
  ∀ (q : Query),
    ValidEntryArgsV2 body q →
    safety q →
    match q.args with
    | [.scalar a, .scalar b] =>
      returnsExactly p defId q
        (.returned ⟨usizeVal (f a.bits.toNat b.bits.toNat), q.callerMem⟩)
    | _ => False

def bodyPost (p : Program) (defId : DefId) (body : Body) : Prop :=
  if body.identity = addIdentity then
    returnsResult p defId body addSafety (fun a b => a + b)
  else if body.identity = subIdentity then
    returnsResult p defId body subSafety (fun a b => a - b)
  else if body.identity = mulIdentity then
    returnsResult p defId body mulSafety (fun a b => a * b)
  else False

def property (p : Program) : Prop :=
  ∀ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body →
    bodyPost p defId body

def specs : SpecsV2 := ⟨safetyPre, property⟩

end Spec
