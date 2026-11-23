-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Data.BitVec.BasicAux
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

abbrev UsizeWord := BitVec 64

def usizeVal (n : UsizeWord) : Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 n.toNat⟩

def unsafeId : String :=
  "rust-path-v1::util::macros::__unsafe"

def unitFromId : String :=
  "rust-path-v1::<() as PointerMetadata>::from_elem_count"

def unitToId : String :=
  "rust-path-v1::<() as PointerMetadata>::to_elem_count"

def usizeFromId : String :=
  "rust-path-v1::<usize as PointerMetadata>::from_elem_count"

def usizeToId : String :=
  "rust-path-v1::<usize as PointerMetadata>::to_elem_count"

def u8ImmutableMarkerId : String :=
  "rust-path-v1::impls::_::<impl Immutable for u8>::only_derive_is_allowed_to_implement_this_trait"

def u8TryFromBytesMarkerId : String :=
  "rust-path-v1::impls::_::<impl TryFromBytes for u8>::only_derive_is_allowed_to_implement_this_trait"

def u8FromZerosMarkerId : String :=
  "rust-path-v1::impls::_::<impl FromZeros for u8>::only_derive_is_allowed_to_implement_this_trait"

def u8FromBytesMarkerId : String :=
  "rust-path-v1::impls::_::<impl FromBytes for u8>::only_derive_is_allowed_to_implement_this_trait"

/-- Total-correctness MIR call outcome at `defId` with empty caller memory. -/
noncomputable def ReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

/-- Non-vacuous identity-keyed safety precondition covering all 9 selected
items (distinguishing zero-arg `unsafe` macro fence, `usize`-indexed
`PointerMetadata` inputs, `()` input, and sealed marker sentinels). -/
def safetyPrecondition (identity : String) (args : List Val) : Prop :=
  (identity = unsafeId ∧ args = []) ∨
  (identity = unitFromId ∧ ∃ n : UsizeWord, args = [usizeVal n]) ∨
  (identity = unitToId ∧ args = [.unit]) ∨
  (identity = usizeFromId ∧ ∃ n : UsizeWord, args = [usizeVal n]) ∨
  (identity = usizeToId ∧ ∃ m : UsizeWord, args = [usizeVal m]) ∨
  ((identity = u8ImmutableMarkerId ∨
    identity = u8TryFromBytesMarkerId ∨
    identity = u8FromZerosMarkerId ∨
    identity = u8FromBytesMarkerId) ∧ args = [])

/-- Helper predicate asserting that canonical `identity` lives in `program`, is
safe (`isUnsafe = false`), takes zero args, and terminates returning `()`. -/
noncomputable def UnitMarkerSpec (program : Program) (identity : String) :
    Prop :=
  ∃ d b,
    getElem? program.bodies d = some b ∧
    b.identity = identity ∧
    b.isUnsafe = false ∧
    b.argumentCount = 0 ∧
    ReturnsTotal program d [] .unit

/-- Combined crate-slice specification across all 5 currently capturable
substantive `zerocopy/src/` functions plus 4 representative primitive-trait
sealing markers for `u8` (`Immutable`, `TryFromBytes`, `FromZeros`,
`FromBytes` in `impls.rs`). -/
noncomputable def combinedSliceSpec (program : Program) : Prop :=
  program.bodies.length = 9 ∧
  (∃ dU bU,
    getElem? program.bodies dU = some bU ∧
    bU.identity = unsafeId ∧
    bU.isUnsafe = true ∧
    bU.argumentCount = 0 ∧
    ReturnsTotal program dU [] .unit) ∧
  (∃ dUF bUF dUT bUT,
    getElem? program.bodies dUF = some bUF ∧
    bUF.identity = unitFromId ∧
    bUF.isUnsafe = false ∧
    getElem? program.bodies dUT = some bUT ∧
    bUT.identity = unitToId ∧
    bUT.isUnsafe = false ∧
    (∀ n : UsizeWord, ReturnsTotal program dUF [usizeVal n] .unit) ∧
    ReturnsTotal program dUT [.unit] (usizeVal 0)) ∧
  (∃ dZF bZF dZT bZT,
    getElem? program.bodies dZF = some bZF ∧
    bZF.identity = usizeFromId ∧
    bZF.isUnsafe = false ∧
    getElem? program.bodies dZT = some bZT ∧
    bZT.identity = usizeToId ∧
    bZT.isUnsafe = false ∧
    (∀ n : UsizeWord, ReturnsTotal program dZF [usizeVal n] (usizeVal n)) ∧
    (∀ m : UsizeWord, ReturnsTotal program dZT [usizeVal m] (usizeVal m))) ∧
  UnitMarkerSpec program u8ImmutableMarkerId ∧
  UnitMarkerSpec program u8TryFromBytesMarkerId ∧
  UnitMarkerSpec program u8FromZerosMarkerId ∧
  UnitMarkerSpec program u8FromBytesMarkerId

noncomputable def specs : Specs :=
  ⟨safetyPrecondition, combinedSliceSpec⟩

end Spec
