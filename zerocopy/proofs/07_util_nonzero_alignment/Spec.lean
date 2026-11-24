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

/-- All four `util` alignment helpers are safe functions, so `BodyVerifiedV2`
does not consult `safetyPre`. -/
def safetyPre (_identity : String) (_q : Query) : Prop := True

def paddingNeededForId : String :=
  "rust-path-v1::util::padding_needed_for"

def roundDownId : String :=
  "rust-path-v1::util::round_down_to_next_multiple_of_alignment"

def maxId : String :=
  "rust-path-v1::util::max"

def minId : String :=
  "rust-path-v1::util::min"

/-- Pure mathematical power-of-two predicate over `Nat`. -/
def IsPowerOfTwo (n : Nat) : Prop :=
  ∃ k : Nat, n = Nat.pow 2 k

/-- Specification for `util::padding_needed_for`:
on every valid entry `q` with `(len : usize, align : NonZeroUsize)`, execution
is well-formed, terminates normally leaving `q.callerMem` unchanged, and
returns a `usize` scalar `pad` that, whenever `align` is a power of two,
satisfies `pad < align`, `align ∣ len + pad`, and
`pad = (align - len % align) % align`. -/
def paddingNeededForPost (p : Program) : Prop :=
  ∃ defId body,
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = paddingNeededForId ∧
    body.isUnsafe = false ∧
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      match q.args with
      | [.scalar len, .nonZero align] =>
        ∃ res : ScalarVal,
          let out := TerminalOut.returned ⟨.scalar res, q.callerMem⟩
          res.wf ∧
          res.width = .isize ∧
          res.signed = false ∧
          BehaviorV2 (entryProgForBody p defId) q out ∧
          SatisfiesPostV2 (entryProgForBody p defId) q (fun o => o = out) ∧
          (IsPowerOfTwo align.bits.toNat →
            res.bits.toNat < align.bits.toNat ∧
            Nat.mod (len.bits.toNat + res.bits.toNat) align.bits.toNat = 0 ∧
            res.bits.toNat =
              Nat.mod
                (align.bits.toNat - Nat.mod len.bits.toNat align.bits.toNat)
                align.bits.toNat)
      | _ => False

/-- Specification for `util::round_down_to_next_multiple_of_alignment`:
on every valid entry `q` with `(n : usize, align : NonZeroUsize)`, execution
is well-formed, terminates normally leaving `q.callerMem` unchanged, and
returns a `usize` scalar `res` that, whenever `align` is a power of two,
satisfies `res ≤ n < res + align`, `align ∣ res`, and `res = n - n % align`. -/
def roundDownPost (p : Program) : Prop :=
  ∃ defId body,
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = roundDownId ∧
    body.isUnsafe = false ∧
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      match q.args with
      | [.scalar n, .nonZero align] =>
        ∃ res : ScalarVal,
          let out := TerminalOut.returned ⟨.scalar res, q.callerMem⟩
          res.wf ∧
          res.width = .isize ∧
          res.signed = false ∧
          BehaviorV2 (entryProgForBody p defId) q out ∧
          SatisfiesPostV2 (entryProgForBody p defId) q (fun o => o = out) ∧
          (IsPowerOfTwo align.bits.toNat →
            res.bits.toNat ≤ n.bits.toNat ∧
            Nat.mod res.bits.toNat align.bits.toNat = 0 ∧
            n.bits.toNat < res.bits.toNat + align.bits.toNat ∧
            res.bits.toNat =
              n.bits.toNat - Nat.mod n.bits.toNat align.bits.toNat)
      | _ => False

/-- Shared specification for `util::max` and `util::min`:
on every valid entry `q` with `(a : NonZeroUsize, b : NonZeroUsize)`, execution
is well-formed, terminates normally leaving `q.callerMem` unchanged, and
returns a `NonZeroUsize` value whose underlying natural equals `op a b`. -/
def nonZeroBinPost (id : String) (op : Nat → Nat → Nat) (p : Program) : Prop :=
  ∃ defId body,
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = id ∧
    body.isUnsafe = false ∧
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      match q.args with
      | [.nonZero a, .nonZero b] =>
        ∃ res : ScalarVal,
          let out := TerminalOut.returned ⟨.nonZero res, q.callerMem⟩
          res.wf ∧
          res.width = .isize ∧
          res.signed = false ∧
          res.bits.toNat ≠ 0 ∧
          res.bits.toNat = op a.bits.toNat b.bits.toNat ∧
          BehaviorV2 (entryProgForBody p defId) q out ∧
          SatisfiesPostV2 (entryProgForBody p defId) q (fun o => o = out)
      | _ => False

/-- Canonical identity-bound functional specifications for
`util::padding_needed_for`, `util::round_down_to_next_multiple_of_alignment`,
`util::max`, and `util::min`. -/
def property (p : Program) : Prop :=
  paddingNeededForPost p ∧
  roundDownPost p ∧
  nonZeroBinPost maxId Nat.max p ∧
  nonZeroBinPost minId Nat.min p

def specs : SpecsV2 := ⟨safetyPre, property⟩

end Spec
