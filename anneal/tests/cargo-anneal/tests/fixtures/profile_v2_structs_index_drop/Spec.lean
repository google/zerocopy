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

/-- Structural equality of two `[u8; N]` values, as
`<[u8; N] as PartialEq>::eq` computes it. -/
noncomputable def arrayBytesEq (a b : List Val) : Bool :=
  match valEqListWith (arrayValEqV2 (.int .i8 false)) a b with
  | .ok r => r
  | .error _ => false

/-- `make_pair(tag, value)` returns `Pair { tag, value }`, whose value lists
the fields in source order. -/
def makePairPost (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 0 with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      match q.args with
      | [tag, value] =>
        BehaviorV2 (entryProgForBody p 0) q
          (TerminalOut.returned ⟨.tuple [tag, value], q.callerMem⟩)
      | _ => False

/-- `pair_tag(p)` returns the `tag` byte of `*p`, which `rustc` places at
byte offset 4 (after the 4-byte `value` field) when it reorders the fields of
`Pair`. -/
def pairTagPost (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 1 with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      match q.args with
      | [.ptr pv] =>
        match pv.allocId with
        | none => False
        | some aid =>
          ∃ v : Val,
            loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.int .i8 false)
              ⟨aid, pv.offsetBytes.toNat + 4⟩ = .ok (some v) ∧
            BehaviorV2 (entryProgForBody p 1) q
              (TerminalOut.returned ⟨v, q.callerMem⟩)
      | _ => False

/-- `digest_byte(d, i)` returns byte `i % 4` of the digest `*d`. -/
def digestBytePost (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 2 with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      match q.args with
      | [.ptr pv, .scalar i] =>
        match pv.allocId with
        | none => False
        | some aid =>
          ∃ v : Val,
            loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.int .i8 false)
              ⟨aid, pv.offsetBytes.toNat + i.bits.toNat % 4⟩ = .ok (some v) ∧
            BehaviorV2 (entryProgForBody p 2) q
              (TerminalOut.returned ⟨v, q.callerMem⟩)
      | _ => False

/-- `digests_differ(a, b)` (`*a != *b`) returns `true` exactly when the
digests' byte arrays differ. -/
def digestsDifferPost (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 3 with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      match q.args with
      | [.ptr pa, .ptr pb] =>
        match pa.allocId, pb.allocId with
        | some aa, some ab =>
          ∃ a b : List Val,
            loadIndirectV2 (entryMemoryWithCaller q.callerMem)
              (.array (.int .i8 false) 4) ⟨aa, pa.offsetBytes.toNat⟩ =
                .ok (some (.array a)) ∧
            loadIndirectV2 (entryMemoryWithCaller q.callerMem)
              (.array (.int .i8 false) 4) ⟨ab, pb.offsetBytes.toNat⟩ =
                .ok (some (.array b)) ∧
            BehaviorV2 (entryProgForBody p 3) q
              (TerminalOut.returned ⟨.bool (!(arrayBytesEq a b)), q.callerMem⟩)
        | _, _ => False
      | _ => False

/-- The derived `<Digest as PartialEq>::eq(a, b)` returns `true` exactly when
the digests' byte arrays are equal. -/
def digestEqPost (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 4 with
  | none => False
  | some body =>
    ∀ (q : Query),
      ValidEntryArgsV2 body q →
      match q.args with
      | [.ptr pa, .ptr pb] =>
        match pa.allocId, pb.allocId with
        | some aa, some ab =>
          ∃ a b : List Val,
            loadIndirectV2 (entryMemoryWithCaller q.callerMem)
              (.array (.int .i8 false) 4) ⟨aa, pa.offsetBytes.toNat⟩ =
                .ok (some (.array a)) ∧
            loadIndirectV2 (entryMemoryWithCaller q.callerMem)
              (.array (.int .i8 false) 4) ⟨ab, pb.offsetBytes.toNat⟩ =
                .ok (some (.array b)) ∧
            BehaviorV2 (entryProgForBody p 4) q
              (TerminalOut.returned ⟨.bool (arrayBytesEq a b), q.callerMem⟩)
        | _, _ => False
      | _ => False

def property (p : Program) : Prop :=
  makePairPost p ∧ pairTagPost p ∧ digestBytePost p ∧ digestsDifferPost p ∧
    digestEqPost p

def specs : SpecsV2 := ⟨fun _ _ => True, property⟩

end Spec
