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
# Tuple Sealing Markers and Tuple Slice Lengths

Specifies 108 monomorphizations of generic items in unmodified
`zerocopy/src/`, selected with `scope.instantiations`, all under Profile v1:

- The `only_derive_is_allowed_to_implement_this_trait` sealing markers
  (empty bodies) of the tuple impls of `FromBytes`, `FromZeros`, `Immutable`,
  and `TryFromBytes` that `impls.rs` generates for every arity from 3 to 26
  (bodies 0-95). Each is instantiated at the first `n` types of
  `tupleTyCycle`.
- `maximum_trailing_slice_len::<T>() -> usize` (`lib.rs`) at 12 slice types
  whose element is a tuple, an array, `bool`, `char`, or `i128` (bodies
  96-107). The body returns `T::MAX_LEN`, which `rustc` evaluates from
  `T::LAYOUT`. The specification gives the element size from Rust's layout,
  including the padding of tuples such as `(u8, u32)` (8 bytes) and
  `(u64, u8)` (16 bytes), and states the result `isize::MAX / elemSize`.

Each body is pinned to its identity and proved to be a safe function with no
parameters that terminates, returning `()` for a marker and the specified
`usize` for `maximum_trailing_slice_len`.
-/

/-- All 108 bodies are safe functions, so `BodyVerified` never consults the
safety precondition. -/
def safetyPre (_identity : String) (_args : List Val) : Prop := True

/-- Total-correctness MIR call outcome at `defId` with empty caller memory. -/
noncomputable def ReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

/-- Body `defId` is the safe, parameterless function `identity`, and it
terminates returning `ret`. -/
noncomputable def returnsPost (p : Program) (defId : DefId)
    (identity : String) (ret : Val) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => False
  | some body =>
    body.identity = identity ∧ body.isUnsafe = false ∧
    body.argumentCount = 0 ∧ ReturnsTotal p defId [] ret

/-- The `usize` value `n`. -/
def usizeVal (n : Nat) : Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 n⟩

/-- `isize::MAX` on the 64-bit target, which is `DstLayout::MAX_SIZE`. -/
def isizeMax : Nat := 9223372036854775807

/-- `maximum_trailing_slice_len::<[E]>()` for an element type `E` of nonzero
size `elemSize`: the largest element count whose byte size is at most
`isize::MAX`. These slice DSTs have no fixed prefix, and an element's size is
a multiple of its alignment, so no padding enters the byte size. -/
def maxSliceLen (elemSize : Nat) : Nat := isizeMax / elemSize

/-- The types the tuple markers are instantiated at: arity `n` uses the
first `n` of these. -/
def tupleTyCycle : List String :=
  ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "u128", "i128",
   "usize", "isize", "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64",
   "u128", "i128", "usize", "isize", "u8", "u16"]

/-- The first `n` elements of `xs`. -/
def takeTys : Nat → List String → List String
  | 0, _ => []
  | _, [] => []
  | n + 1, x :: xs => x :: takeTys n xs

/-- `xs` joined with `", "`. -/
def joinTys : List String → String
  | [] => ""
  | [x] => x
  | x :: rest => stringAppend (stringAppend x ", ") (joinTys rest)

/-- Identity of the sealing marker of `trait` for the tuple of arity
`arity`. -/
def tupleMarkerId (trait : String) (arity : Nat) : String :=
  stringAppend
    (stringAppend
      (stringAppend
        (stringAppend "rust-path-v1::impls::tuples::_::<impl " trait)
        " for (")
      (joinTys (takeTys arity tupleTyCycle)))
    ")>::only_derive_is_allowed_to_implement_this_trait"

/-- Identity of `maximum_trailing_slice_len::<tyName>`. -/
def maxLenId (tyName : String) : String :=
  stringAppend (stringAppend "rust-path-v1::maximum_trailing_slice_len::<"
    tyName) ">"

/-- Bodies `defId, ...` are the markers of `trait` for arities `arity`,
`arity + 1`, ..., `arity + count - 1`. -/
noncomputable def markerPosts (p : Program) (trait : String) :
    DefId → Nat → Nat → Prop
  | _, _, 0 => True
  | defId, arity, count + 1 =>
    returnsPost p defId (tupleMarkerId trait arity) .unit ∧
    markerPosts p trait (defId + 1) (arity + 1) count

/-- The slice types of bodies `96` through `107`, in capture order, each with
the size in bytes of its element. -/
def maxLenCases : List (String × Nat) :=
  [("[((), u8)]", 1),
   ("[(u16, u8)]", 4),
   ("[(u32, u8, u16)]", 8),
   ("[(u64, u8)]", 16),
   ("[(u8, u16, u32)]", 8),
   ("[(u8, u32)]", 8),
   ("[(u8, u8, u8)]", 3),
   ("[(u8,)]", 1),
   ("[[u16; 3]]", 6),
   ("[bool]", 1),
   ("[char]", 4),
   ("[i128]", 16)]

/-- Bodies `defId, defId + 1, ...` are `maximum_trailing_slice_len` at
`cases`. -/
noncomputable def maxLenPosts (p : Program) :
    DefId → List (String × Nat) → Prop
  | _, [] => True
  | defId, (ty, elemSize) :: rest =>
    returnsPost p defId (maxLenId ty) (usizeVal (maxSliceLen elemSize)) ∧
    maxLenPosts p (defId + 1) rest

noncomputable def property (p : Program) : Prop :=
  p.bodies.length = 108 ∧
  markerPosts p "FromBytes" 0 3 24 ∧
  markerPosts p "FromZeros" 24 3 24 ∧
  markerPosts p "Immutable" 48 3 24 ∧
  markerPosts p "TryFromBytes" 72 3 24 ∧
  maxLenPosts p 96 maxLenCases

noncomputable def specs : Specs := ⟨safetyPre, property⟩

end Spec
