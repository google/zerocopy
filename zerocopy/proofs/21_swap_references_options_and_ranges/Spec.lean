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

/-!
# Tuple Swaps over References, Options, Ranges, and Nested Aggregates

Specifies 8 monomorphizations of the generic function
`swap::<T, U>((t, u): (T, U)) -> (U, T) { (u, t) }` in unmodified
`zerocopy/src/lib.rs`, selected with `scope.instantiations`, at pairs of
Profile v2 types:

- shared and mutable references: `(&[u8], &str)`, `(&mut [u8], &[u8; 4])`,
  and `(&u8, &mut u32)`, whose field moves retag the reference
  (`Rvalue.useRetag`);
- `(Option<&u8>, char)`, an option holding a reference;
- `((u8, u16), bool)`, `([u32; 2], Option<bool>)`, `(Ordering, ())`, and
  `(Option<u32>, Range<usize>)`.

Each body is pinned to its identity and proved to be a safe function that,
on every valid entry, receives exactly one pair `(a, b)` and returns `(b, a)`
with caller memory unchanged as its only terminal behavior. Profile v2
validates reference arguments at entry and reference results at return, so
for the reference instantiations this also shows that returning the swapped
references passes those checks.
-/

/-- All 8 bodies are safe functions, so `BodyVerifiedV2` never consults the
safety precondition. -/
def safetyPre (_identity : String) (_q : Query) : Prop := True

/-- On entry `q`, body `defId` is well-formed, returns exactly `out`, and has
no other terminal behavior. -/
def returnsExactly (p : Program) (defId : DefId) (q : Query)
    (out : TerminalOut) : Prop :=
  BehaviorV2 (entryProgForBody p defId) q out ∧
  SatisfiesPostV2 (entryProgForBody p defId) q (fun o => o = out)

/-- Body `defId` is the safe function `identity`, and on every valid entry it
receives exactly one pair `(a, b)` and returns `(b, a)` with caller memory
unchanged. -/
def swapBodyPost (p : Program) (defId : DefId) (identity : String) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => False
  | some body =>
    body.identity = identity ∧ body.isUnsafe = false ∧
    ∀ q : Query, ValidEntryArgsV2 body q →
      ∃ a b : Val, q.args = [.tuple [a, b]] ∧
        returnsExactly p defId q (.returned ⟨.tuple [b, a], q.callerMem⟩)

/-- Identity of `swap::<tyArgs>`. -/
def swapId (tyArgs : String) : String :=
  stringAppend (stringAppend "rust-path-v1::swap::<" tyArgs) ">"

/-- The type arguments of bodies `0` through `7`, in capture order. -/
def swapCases : List String :=
  ["&[u8], &str", "&mut [u8], &[u8; 4]", "&u8, &mut u32", "(u8, u16), bool",
   "[u32; 2], core::option::Option<bool>", "core::cmp::Ordering, ()",
   "core::option::Option<&u8>, char",
   "core::option::Option<u32>, core::ops::range::Range<usize>"]

/-- Bodies `defId, defId + 1, ...` are `swap` at `cases`. -/
def swapPosts (p : Program) : DefId → List String → Prop
  | _, [] => True
  | defId, tys :: rest =>
    swapBodyPost p defId (swapId tys) ∧ swapPosts p (defId + 1) rest

def property (p : Program) : Prop :=
  swapPosts p 0 swapCases

def specs : SpecsV2 := ⟨safetyPre, property⟩

end Spec
