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

def buggyAddIdentity : String := "rust-path-v1::buggy_add_u8"

/-- `buggy_add_u8` returns the wrapping increment without diverging, and
`BodyVerifiedV2` additionally requires that no execution faults. This holds
only without overflow checks: with them, `x = 255` fails the overflow
`Assert`, which faults under `--panic unwind` and aborts under
`--panic abort`, so the body does not return. -/
def property (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 0 with
  | none => False
  | some body =>
    body.identity = buggyAddIdentity ∧
    ∀ q : Query,
      ValidEntryArgsV2 body q →
      ¬ DivergesV2 (entryProgForBody p 0) q ∧
      match q.args with
      | [.scalar x] =>
        ∃ out : Out,
          BehaviorV2 (entryProgForBody p 0) q (.returned out) ∧
          out.ret =
            .scalar ⟨.i8, false, BitVec.ofNat 128 ((x.bits.toNat + 1) % 256)⟩
      | _ => False

def specs : SpecsV2 := ⟨fun _ _ => True, property⟩

end Spec
