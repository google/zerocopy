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
# Sealing Markers of `Option` of Function Pointers

Specifies 156 monomorphizations of generic items in unmodified
`zerocopy/src/`, selected with `scope.instantiations`, all under Profile v1.

`impls.rs` implements `FromZeros`, `TryFromBytes`, and `Immutable` for
`Option<F>`, where `F` is a function pointer type `fn`, `unsafe fn`,
`extern "C" fn`, or `unsafe extern "C" fn` with 0 to 12 parameters
(`unsafe_impl_for_power_set!` over `opt_fn!` and its siblings). Each impl's
`only_derive_is_allowed_to_implement_this_trait` sealing marker has an
empty body. This unit covers all 156 of them. A function pointer with `n`
parameters is instantiated at the first `n` types of `fnParamCycle` and
returns `bool`.

Each body is pinned to its identity, which records the trait and the
instantiated function pointer type, and is proved to be a safe function
with no parameters that terminates returning `()`. Capture order sorts the
bodies by identity: by trait, then by qualifier (`extern "C" fn`, `fn`,
`unsafe extern "C" fn`, `unsafe fn`), then by arity.
-/

/-- All 156 bodies are safe functions, so `BodyVerified` never consults the
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
terminates returning `()`. -/
noncomputable def returnsUnitPost (p : Program) (defId : DefId)
    (identity : String) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => False
  | some body =>
    body.identity = identity ∧ body.isUnsafe = false ∧
    body.argumentCount = 0 ∧ ReturnsTotal p defId [] .unit

/-- The parameter types of the function pointers: arity `n` uses the first
`n` of these. -/
def fnParamCycle : List String :=
  ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "u128", "i128",
   "usize", "isize"]

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

/-- Identity of the sealing marker of `trait` for
`Option<qual fn(P_1, ..., P_arity) -> bool>`, where `qual` is `""`,
`"unsafe "`, `"extern \"C\" "`, or `"unsafe extern \"C\" "`. -/
def optFnMarkerId (trait qual : String) (arity : Nat) : String :=
  stringAppend
    (stringAppend
      (stringAppend
        (stringAppend
          (stringAppend
            (stringAppend "rust-path-v1::impls::_::<impl " trait)
            " for core::option::Option<")
          qual)
        "fn(")
      (joinTys (takeTys arity fnParamCycle)))
    ") -> bool>>::only_derive_is_allowed_to_implement_this_trait"

/-- Bodies `defId, ...` are the markers of `trait` for `qual` function
pointers of arities `arity`, `arity + 1`, ..., `arity + count - 1`. -/
noncomputable def markerPosts (p : Program) (trait qual : String) :
    DefId → Nat → Nat → Prop
  | _, _, 0 => True
  | defId, arity, count + 1 =>
    returnsUnitPost p defId (optFnMarkerId trait qual arity) ∧
    markerPosts p trait qual (defId + 1) (arity + 1) count

noncomputable def property (p : Program) : Prop :=
  p.bodies.length = 156 ∧
  markerPosts p "FromZeros" "extern \"C\" " 0 0 13 ∧
  markerPosts p "FromZeros" "" 13 0 13 ∧
  markerPosts p "FromZeros" "unsafe extern \"C\" " 26 0 13 ∧
  markerPosts p "FromZeros" "unsafe " 39 0 13 ∧
  markerPosts p "Immutable" "extern \"C\" " 52 0 13 ∧
  markerPosts p "Immutable" "" 65 0 13 ∧
  markerPosts p "Immutable" "unsafe extern \"C\" " 78 0 13 ∧
  markerPosts p "Immutable" "unsafe " 91 0 13 ∧
  markerPosts p "TryFromBytes" "extern \"C\" " 104 0 13 ∧
  markerPosts p "TryFromBytes" "" 117 0 13 ∧
  markerPosts p "TryFromBytes" "unsafe extern \"C\" " 130 0 13 ∧
  markerPosts p "TryFromBytes" "unsafe " 143 0 13

noncomputable def specs : Specs := ⟨safetyPre, property⟩

end Spec
