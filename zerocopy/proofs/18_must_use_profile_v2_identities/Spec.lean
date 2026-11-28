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
# `must_use` Identities over Profile v2 Types

Specifies 12 monomorphizations of the generic identity function
`util::macro_util::must_use<T>(t: T) -> T { t }` (`util/macro_util.rs`),
selected with `scope.instantiations`, at reference, slice, `str`, array,
`Range`, `Option`, and scalar types:

- `&[u8; 4]`, `&[u8]`, `&mut u8`, `&str`, and `&u8`, whose bodies are
  `_0 = move _1` with a retag (`Rvalue.useRetag`);
- `()`, `char`, `core::cmp::Ordering`, `core::ops::Range<usize>`,
  `core::option::Option<u32>`, `i8`, and `u64`, whose bodies are
  `_0 = move _1` (`Rvalue.use`).

Unit `15` verifies `must_use` at `bool`, `u8`, `u32`, and `usize` under
Profile v1. These instantiations need Profile v2 (`MirTy.ref`, `MirTy.slice`,
`MirTy.str`, `MirTy.array`, `MirTy.range`, and `MirTy.option`), so the whole
program is Profile v2.

Each body is pinned to its identity and proved to be a safe function that,
on every valid entry, receives exactly one argument `v` and returns `v` with
caller memory unchanged as its only terminal behavior.
-/

/-- All 12 bodies are safe functions, so `BodyVerifiedV2` never consults the
safety precondition. -/
def safetyPre (_identity : String) (_q : Query) : Prop := True

/-- On entry `q`, body `defId` is well-formed, returns exactly `out`, and has
no other terminal behavior. -/
def returnsExactly (p : Program) (defId : DefId) (q : Query)
    (out : TerminalOut) : Prop :=
  BehaviorV2 (entryProgForBody p defId) q out ∧
  SatisfiesPostV2 (entryProgForBody p defId) q (fun o => o = out)

/-- Body `defId` is the safe function `identity`, and on every valid entry it
receives exactly one argument and returns it with caller memory unchanged. -/
def identityBodyPost (p : Program) (defId : DefId) (identity : String) :
    Prop :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => False
  | some body =>
    body.identity = identity ∧ body.isUnsafe = false ∧
    ∀ q : Query, ValidEntryArgsV2 body q →
      ∃ v : Val, q.args = [v] ∧
        returnsExactly p defId q (.returned ⟨v, q.callerMem⟩)

/-- Identity of `util::macro_util::must_use::<tyName>`. -/
def mustUseId (tyName : String) : String :=
  stringAppend (stringAppend "rust-path-v1::util::macro_util::must_use::<"
    tyName) ">"

/-- The type arguments of bodies `0` through `11`, in capture order. -/
def mustUseTypes : List String :=
  ["&[u8; 4]", "&[u8]", "&mut u8", "&str", "&u8", "()", "char",
   "core::cmp::Ordering", "core::ops::range::Range<usize>",
   "core::option::Option<u32>", "i8", "u64"]

/-- Bodies `defId, defId + 1, ...` are `must_use` at `tys`, each the identity
on every valid entry. -/
def identityPosts (p : Program) : DefId → List String → Prop
  | _, [] => True
  | defId, ty :: rest =>
    identityBodyPost p defId (mustUseId ty) ∧ identityPosts p (defId + 1) rest

def property (p : Program) : Prop :=
  identityPosts p 0 mustUseTypes

def specs : SpecsV2 := ⟨safetyPre, property⟩

end Spec
