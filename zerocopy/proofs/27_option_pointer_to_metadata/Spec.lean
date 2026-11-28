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
# `KnownLayout::pointer_to_metadata` for `Option<T>`

Specifies 14 monomorphizations of a generic method in unmodified
`zerocopy/src/`, selected with `scope.instantiations`.

`lib.rs` implements `KnownLayout` for `Option<T>` with
`impl_known_layout!`, whose sized-type arm (`util/macros.rs`) defines

```rust
fn pointer_to_metadata(_ptr: *mut Self) -> () {}
```

This unit covers that method at `T` = `()`, `bool`, and every
fixed-width integer type. Its raw-pointer parameter needs Profile v2.

Each body is pinned to its identity and proved to be a safe function that,
on every valid entry, receives exactly one argument and has exactly one
terminal behavior: it returns `()` with caller memory unchanged.
-/

/-- All 14 bodies are safe functions, so `BodyVerifiedV2` never consults
the safety precondition. -/
def safetyPre (_identity : String) (_q : Query) : Prop := True

/-- On entry `q`, body `defId` is well-formed, returns exactly `out`, and has
no other terminal behavior. -/
def returnsExactly (p : Program) (defId : DefId) (q : Query)
    (out : TerminalOut) : Prop :=
  BehaviorV2 (entryProgForBody p defId) q out ∧
  SatisfiesPostV2 (entryProgForBody p defId) q (fun o => o = out)

/-- Body `defId` is the safe function `identity`, and on every valid entry it
receives exactly one argument and returns `()` with caller memory
unchanged. -/
def returnsUnitPost (p : Program) (defId : DefId) (identity : String) :
    Prop :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => False
  | some body =>
    body.identity = identity ∧ body.isUnsafe = false ∧
    ∀ q : Query, ValidEntryArgsV2 body q →
      ∃ v : Val, q.args = [v] ∧
        returnsExactly p defId q (.returned ⟨.unit, q.callerMem⟩)

/-- Identity of `<Option<tyName> as KnownLayout>::pointer_to_metadata`. -/
def optionPtmId (tyName : String) : String :=
  stringAppend
    (stringAppend "rust-path-v1::_::<impl KnownLayout for core::option::Option<"
      tyName)
    ">>::pointer_to_metadata"

/-- The type arguments `T` of bodies `0` through `13`, in capture
order. -/
def optionTys : List String :=
  ["()", "bool", "i128", "i16", "i32", "i64", "i8", "isize", "u128", "u16",
   "u32", "u64", "u8", "usize"]

/-- Bodies `defId, defId + 1, ...` are `pointer_to_metadata` for `Option<T>`
at the types `tys`. -/
def ptmPosts (p : Program) : DefId → List String → Prop
  | _, [] => True
  | defId, ty :: rest =>
    returnsUnitPost p defId (optionPtmId ty) ∧ ptmPosts p (defId + 1) rest

def property (p : Program) : Prop :=
  p.bodies.length = 14 ∧ ptmPosts p 0 optionTys

def specs : SpecsV2 := ⟨safetyPre, property⟩

end Spec
