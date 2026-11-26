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

def guardedAddIdentity : String := "rust-path-v1::guarded_add_u8"

/-- The saturating increment `guarded_add_u8` computes on `x < 256`. -/
def saturatingInc (x : Nat) : Nat :=
  if x < 255 then x + 1 else 255

/-- The body was captured with `-Coverflow-checks=yes` and returns the
saturating increment without diverging. A failed overflow check would fault
under `--panic unwind` or abort under `--panic abort` instead of returning,
so no overflow check can fire. -/
def property (p : Program) : Prop :=
  p.overflowChecks = true ∧
  match Trusted.MirSemantics.getElem? p.bodies 0 with
  | none => False
  | some body =>
    body.identity = guardedAddIdentity ∧
    ∀ q : Query,
      ValidEntryArgsV2 body q →
      ¬ DivergesV2 (entryProgForBody p 0) q ∧
      match q.args with
      | [.scalar x] =>
        ∃ out : Out,
          BehaviorV2 (entryProgForBody p 0) q (.returned out) ∧
          out.ret =
            .scalar ⟨.i8, false, BitVec.ofNat 128 (saturatingInc x.bits.toNat)⟩
      | _ => False

def specs : SpecsV2 := ⟨fun _ _ => True, property⟩

end Spec
