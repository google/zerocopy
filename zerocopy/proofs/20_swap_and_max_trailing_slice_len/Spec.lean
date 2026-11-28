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
# Tuple Swaps and Maximum Trailing-Slice Lengths

Specifies 16 monomorphizations of two generic functions in unmodified
`zerocopy/src/lib.rs`, selected with `scope.instantiations`:

- `maximum_trailing_slice_len::<T>() -> usize` at `()`, `u32`, `[()]`, `[u8]`,
  `[u16]`, `[u32]`, `[u64]`, `[u128]`, `[[u8; 3]]`, and `str`. The body
  returns the associated constant `T::MAX_LEN`, which `rustc` evaluates from
  `T::LAYOUT`: the largest trailing-slice element count whose byte size fits in
  `DstLayout::MAX_SIZE` (`isize::MAX`) for a slice DST, `usize::MAX` for a
  slice of zero-sized elements, and `0` for a sized type.
- `swap::<T, U>((t, u): (T, U)) -> (U, T)` at `(u8, u32)`, `(bool, char)`,
  `(i16, u64)`, `(usize, isize)`, `(u128, i8)`, and `([u8; 2], u16)`. Its
  tuple parameter and result need Profile v2 (`MirTy.tuple`), so the whole
  program is Profile v2.

Each body is pinned to its identity and proved to be a safe function that, on
every valid entry, has exactly one terminal behavior with caller memory
unchanged: `maximum_trailing_slice_len` returns the `usize` given by
`maxTrailingSliceLen` on the 64-bit target, and `swap` receives one pair
`(a, b)` and returns `(b, a)`.
-/

/-- All 16 bodies are safe functions, so `BodyVerifiedV2` never consults the
safety precondition. -/
def safetyPre (_identity : String) (_q : Query) : Prop := True

/-- On entry `q`, body `defId` is well-formed, returns exactly `out`, and has
no other terminal behavior. -/
def returnsExactly (p : Program) (defId : DefId) (q : Query)
    (out : TerminalOut) : Prop :=
  BehaviorV2 (entryProgForBody p defId) q out ∧
  SatisfiesPostV2 (entryProgForBody p defId) q (fun o => o = out)

/-- The `usize` value `n`. -/
def usizeVal (n : Nat) : Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 n⟩

/-- `isize::MAX` on the 64-bit target, which is `DstLayout::MAX_SIZE`. -/
def isizeMax : Nat := 9223372036854775807

/-- `usize::MAX` on the 64-bit target. -/
def usizeMax : Nat := 18446744073709551615

/-- The maximum trailing-slice element count of `T`, given by the element size
of `T` as a slice DST with no fixed prefix (`some elemSize`) or by `none` if
`T` is sized: `0` for a sized type, `usize::MAX` for a slice of zero-sized
elements, and otherwise the largest element count whose byte size is at most
`isize::MAX`. An element's size is a multiple of its alignment, so no padding
enters the byte size. -/
def maxTrailingSliceLen : Option Nat → Nat
  | none => 0
  | some 0 => usizeMax
  | some elemSize => isizeMax / elemSize

/-- Body `defId` is the safe function `identity`, and on every valid entry it
returns the `usize` `n` with caller memory unchanged. -/
def constBodyPost (p : Program) (defId : DefId) (identity : String)
    (n : Nat) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => False
  | some body =>
    body.identity = identity ∧ body.isUnsafe = false ∧
    ∀ q : Query, ValidEntryArgsV2 body q →
      returnsExactly p defId q (.returned ⟨usizeVal n, q.callerMem⟩)

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

/-- Identity of `maximum_trailing_slice_len::<tyName>`. -/
def maxLenId (tyName : String) : String :=
  stringAppend (stringAppend "rust-path-v1::maximum_trailing_slice_len::<"
    tyName) ">"

/-- Identity of `swap::<tyArgs>`. -/
def swapId (tyArgs : String) : String :=
  stringAppend (stringAppend "rust-path-v1::swap::<" tyArgs) ">"

/-- The type arguments of bodies `0` through `9`, in capture order, each with
the slice element size of the type (`none` for a sized type). -/
def maxLenCases : List (String × Option Nat) :=
  [("()", none),
   ("[()]", some 0),
   ("[[u8; 3]]", some 3),
   ("[u128]", some 16),
   ("[u16]", some 2),
   ("[u32]", some 4),
   ("[u64]", some 8),
   ("[u8]", some 1),
   ("str", some 1),
   ("u32", none)]

/-- The type arguments of bodies `10` through `15`, in capture order. -/
def swapCases : List String :=
  ["[u8; 2], u16", "bool, char", "i16, u64", "u128, i8", "u8, u32",
   "usize, isize"]

/-- Bodies `defId, defId + 1, ...` are `maximum_trailing_slice_len` at
`cases`. -/
def maxLenPosts (p : Program) : DefId → List (String × Option Nat) → Prop
  | _, [] => True
  | defId, (ty, elemSize) :: rest =>
    constBodyPost p defId (maxLenId ty) (maxTrailingSliceLen elemSize) ∧
    maxLenPosts p (defId + 1) rest

/-- Bodies `defId, defId + 1, ...` are `swap` at `cases`. -/
def swapPosts (p : Program) : DefId → List String → Prop
  | _, [] => True
  | defId, tys :: rest =>
    swapBodyPost p defId (swapId tys) ∧ swapPosts p (defId + 1) rest

def property (p : Program) : Prop :=
  maxLenPosts p 0 maxLenCases ∧ swapPosts p 10 swapCases

def specs : SpecsV2 := ⟨safetyPre, property⟩

end Spec
