-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Data.BitVec.BasicAux
public import Trusted.MirSemantics

@[expose] public section

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

def u8ImmutableId : String :=
  "rust-path-v1::impls::_::<impl Immutable for u8>::only_derive_is_allowed_to_implement_this_trait"
def u8TryFromBytesId : String :=
  "rust-path-v1::impls::_::<impl TryFromBytes for u8>::only_derive_is_allowed_to_implement_this_trait"
def u8FromZerosId : String :=
  "rust-path-v1::impls::_::<impl FromZeros for u8>::only_derive_is_allowed_to_implement_this_trait"
def u8FromBytesId : String :=
  "rust-path-v1::impls::_::<impl FromBytes for u8>::only_derive_is_allowed_to_implement_this_trait"

def i8ImmutableId : String :=
  "rust-path-v1::impls::_::<impl Immutable for i8>::only_derive_is_allowed_to_implement_this_trait"
def i8TryFromBytesId : String :=
  "rust-path-v1::impls::_::<impl TryFromBytes for i8>::only_derive_is_allowed_to_implement_this_trait"
def i8FromZerosId : String :=
  "rust-path-v1::impls::_::<impl FromZeros for i8>::only_derive_is_allowed_to_implement_this_trait"
def i8FromBytesId : String :=
  "rust-path-v1::impls::_::<impl FromBytes for i8>::only_derive_is_allowed_to_implement_this_trait"

def u16ImmutableId : String :=
  "rust-path-v1::impls::_::<impl Immutable for u16>::only_derive_is_allowed_to_implement_this_trait"
def u16TryFromBytesId : String :=
  "rust-path-v1::impls::_::<impl TryFromBytes for u16>::only_derive_is_allowed_to_implement_this_trait"
def u16FromZerosId : String :=
  "rust-path-v1::impls::_::<impl FromZeros for u16>::only_derive_is_allowed_to_implement_this_trait"
def u16FromBytesId : String :=
  "rust-path-v1::impls::_::<impl FromBytes for u16>::only_derive_is_allowed_to_implement_this_trait"

def i16ImmutableId : String :=
  "rust-path-v1::impls::_::<impl Immutable for i16>::only_derive_is_allowed_to_implement_this_trait"
def i16TryFromBytesId : String :=
  "rust-path-v1::impls::_::<impl TryFromBytes for i16>::only_derive_is_allowed_to_implement_this_trait"
def i16FromZerosId : String :=
  "rust-path-v1::impls::_::<impl FromZeros for i16>::only_derive_is_allowed_to_implement_this_trait"
def i16FromBytesId : String :=
  "rust-path-v1::impls::_::<impl FromBytes for i16>::only_derive_is_allowed_to_implement_this_trait"

def usizeImmutableId : String :=
  "rust-path-v1::impls::_::<impl Immutable for usize>::only_derive_is_allowed_to_implement_this_trait"
def usizeTryFromBytesId : String :=
  "rust-path-v1::impls::_::<impl TryFromBytes for usize>::only_derive_is_allowed_to_implement_this_trait"
def usizeFromZerosId : String :=
  "rust-path-v1::impls::_::<impl FromZeros for usize>::only_derive_is_allowed_to_implement_this_trait"
def usizeFromBytesId : String :=
  "rust-path-v1::impls::_::<impl FromBytes for usize>::only_derive_is_allowed_to_implement_this_trait"

def isMarkerGroup (id a b c d : String) : Prop :=
  id = a ∨ id = b ∨ id = c ∨ id = d

def isMarkerId (id : String) : Prop :=
  isMarkerGroup id u8ImmutableId u8TryFromBytesId u8FromZerosId u8FromBytesId ∨
  isMarkerGroup id i8ImmutableId i8TryFromBytesId i8FromZerosId i8FromBytesId ∨
  isMarkerGroup id u16ImmutableId u16TryFromBytesId u16FromZerosId u16FromBytesId ∨
  isMarkerGroup id i16ImmutableId i16TryFromBytesId i16FromZerosId i16FromBytesId ∨
  isMarkerGroup id usizeImmutableId usizeTryFromBytesId usizeFromZerosId usizeFromBytesId

/-- Total-correctness MIR call outcome at `defId` with empty caller memory. -/
noncomputable def ReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

/-- Non-vacuous identity-keyed safety precondition covering all 25 selected
`zerocopy/src/` items across two capture shards. -/
def safetyPrecondition (identity : String) (args : List Val) : Prop :=
  (identity = unsafeId ∧ args = []) ∨
  (identity = unitFromId ∧ ∃ n : UsizeWord, args = [usizeVal n]) ∨
  (identity = unitToId ∧ args = [.unit]) ∨
  (identity = usizeFromId ∧ ∃ n : UsizeWord, args = [usizeVal n]) ∨
  (identity = usizeToId ∧ ∃ m : UsizeWord, args = [usizeVal m]) ∨
  (isMarkerId identity ∧ args = [])

/-- Assert that canonical `identity` lives in `program`, is safe
(`isUnsafe = false`), takes zero args, and terminates returning `()`. -/
noncomputable def UnitMarkerSpec (program : Program) (identity : String) :
    Prop :=
  ∃ d b,
    getElem? program.bodies d = some b ∧
    b.identity = identity ∧
    b.isUnsafe = false ∧
    b.argumentCount = 0 ∧
    ReturnsTotal program d [] .unit

/-- Sharded 25-body specification over all 5 substantive `zerocopy/src/`
items plus 20 primitive-trait sealing markers (`u8`, `i8`, `u16`, `i16`,
`usize`, including the 101-byte `impl TryFromBytes for usize` identity). -/
noncomputable def shardedSliceSpec (program : Program) : Prop :=
  program.bodies.length = 25 ∧
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
  UnitMarkerSpec program u8ImmutableId ∧
  UnitMarkerSpec program u8TryFromBytesId ∧
  UnitMarkerSpec program u8FromZerosId ∧
  UnitMarkerSpec program u8FromBytesId ∧
  UnitMarkerSpec program i8ImmutableId ∧
  UnitMarkerSpec program i8TryFromBytesId ∧
  UnitMarkerSpec program i8FromZerosId ∧
  UnitMarkerSpec program i8FromBytesId ∧
  UnitMarkerSpec program u16ImmutableId ∧
  UnitMarkerSpec program u16TryFromBytesId ∧
  UnitMarkerSpec program u16FromZerosId ∧
  UnitMarkerSpec program u16FromBytesId ∧
  UnitMarkerSpec program i16ImmutableId ∧
  UnitMarkerSpec program i16TryFromBytesId ∧
  UnitMarkerSpec program i16FromZerosId ∧
  UnitMarkerSpec program i16FromBytesId ∧
  UnitMarkerSpec program usizeImmutableId ∧
  UnitMarkerSpec program usizeTryFromBytesId ∧
  UnitMarkerSpec program usizeFromZerosId ∧
  UnitMarkerSpec program usizeFromBytesId

noncomputable def specs : Specs :=
  ⟨safetyPrecondition, shardedSliceSpec⟩

end Spec

end
