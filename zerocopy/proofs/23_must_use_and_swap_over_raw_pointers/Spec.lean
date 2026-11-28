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
# Identity and Swap over Raw Pointers

Specifies 7 monomorphizations of two generic functions in unmodified
`zerocopy/src/`, selected with `scope.instantiations`, whose arguments and
results hold raw pointers:

- `swap::<T, U>((t, u): (T, U)) -> (U, T)` (`lib.rs`) at
  `(*const u8, *mut u16)` and `(*mut [u8], bool)`;
- `util::macro_util::must_use::<T>(t: T) -> T` (`util/macro_util.rs`) at
  `*const [u8]`, `*const u8`, `*mut [u16]`, `*mut u32`, and
  `Option<*const u8>`.

Raw-pointer parameters need Profile v2, so the whole program is Profile v2.
Returning a raw pointer is checked differently from returning a reference:
Profile v2 refuses a returned pointer into a read-only allocation that the
callee created, and the returned memory includes any allocation the callee
created and did not free.

Each body is pinned to its identity and proved to be a safe function that,
on every valid entry, has exactly one terminal behavior with caller memory
unchanged: `swap` receives one pair `(a, b)` and returns `(b, a)`, and
`must_use` receives one argument `v` and returns `v`.
-/

/-- All 7 bodies are safe functions, so `BodyVerifiedV2` never consults the
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

/-- Identity of `swap::<tyArgs>`. -/
def swapId (tyArgs : String) : String :=
  stringAppend (stringAppend "rust-path-v1::swap::<" tyArgs) ">"

/-- Identity of `util::macro_util::must_use::<tyName>`. -/
def mustUseId (tyName : String) : String :=
  stringAppend (stringAppend "rust-path-v1::util::macro_util::must_use::<"
    tyName) ">"

def property (p : Program) : Prop :=
  swapBodyPost p 0 (swapId "*const u8, *mut u16") ∧
  swapBodyPost p 1 (swapId "*mut [u8], bool") ∧
  identityBodyPost p 2 (mustUseId "*const [u8]") ∧
  identityBodyPost p 3 (mustUseId "*const u8") ∧
  identityBodyPost p 4 (mustUseId "*mut [u16]") ∧
  identityBodyPost p 5 (mustUseId "*mut u32") ∧
  identityBodyPost p 6 (mustUseId "core::option::Option<*const u8>")

def specs : SpecsV2 := ⟨safetyPre, property⟩

end Spec
