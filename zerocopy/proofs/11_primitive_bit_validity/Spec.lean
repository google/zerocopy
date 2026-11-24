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

/-!
# Non-Float Primitive Sealing Markers & Bit-Validity Specification

Formal specification for the 15 non-float primitive types (`()`, `bool`, `char`,
and all 12 fixed-width and pointer-sized integer types `u8`..`isize`) in
`zerocopy/src/impls.rs`:

1. **Selected MIR sealing markers (`CapturedMarkerMatrixSpec`):** Binds the 77
   selected verbatim `only_derive_is_allowed_to_implement_this_trait` functions
   for the 15 non-float primitive types in `zerocopy/src/impls.rs` by exact
   count, canonical `b.identity` path, `b.isUnsafe = false`,
   `b.argumentCount = 0`, and total `()` return (`ReturnsTotal`).
2. **Model-side `Trusted.MirSemantics.Bytes` contract
   (`PrimitiveBitValiditySpec`):** Proves model-side `FromZeros`, `FromBytes`,
   `IntoBytes`, `Unaligned`, and `bool`/`char` `TryFromBytes` byte-validity
   conditions over `layoutOfTy`, `encodeVal`, and `decodeVal` for every
   `TargetEndian` (`<{bool,char} as TryFromBytes>::is_safe` MIR bodies are not
   captured here), plus negative model-side refutations for `FromBytes` on
   `bool` (`0x02`) and `char` (`0xD800`) and `Unaligned` on `char` and
   multi-byte integers (`alignLog2 > 0`).
-/

/-- Canonical `rust-path-v1` identities of the 77 trait sealing markers for the
15 non-float primitive types in `zerocopy/src/impls.rs` (canonical SCC shard
order). -/
def primitiveMarkerIdentities : List String := [
  "rust-path-v1::impls::_::<impl FromBytes for ()>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for i128>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for i16>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for i32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for i64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for i8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for isize>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for u128>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for u16>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for u32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for u64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for u8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for usize>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for ()>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for bool>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for char>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for i128>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for i16>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for i32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for i64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for i8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for isize>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for u128>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for u16>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for u32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for u64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for u8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for usize>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for ()>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for bool>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for char>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for i128>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for i16>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for i32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for i64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for i8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for isize>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for u128>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for u16>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for u32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for u64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for u8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for usize>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for ()>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for bool>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for char>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for i128>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for i16>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for i32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for i64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for i8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for isize>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for u128>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for u16>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for u32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for u64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for u8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for usize>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for ()>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for bool>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for char>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for i128>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for i16>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for i32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for i64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for i8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for isize>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for u128>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for u16>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for u32>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for u64>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for u8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for usize>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Unaligned for ()>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Unaligned for bool>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Unaligned for i8>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Unaligned for u8>::only_derive_is_allowed_to_implement_this_trait"
]

/-! ## Part 1: Captured MIR Sealing-Marker Contract -/

/-- Total-correctness MIR call outcome at `defId` with empty caller memory. -/
noncomputable def ReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

/-- Non-vacuous identity-keyed safety precondition over the 77 zero-argument
primitive trait sealing markers. -/
def safetyPrecondition (identity : String) (args : List Val) : Prop :=
  identity ∈ primitiveMarkerIdentities ∧ args = []

/-- Asserts that `program.bodies[defId]` has canonical path `identity`, is safe
(`isUnsafe = false`), takes zero arguments (`argumentCount = 0`), and
terminates returning `()` on `[]`. -/
noncomputable def UnitMarkerAt (program : Program) (defId : DefId)
    (identity : String) : Prop :=
  ∃ b : Body,
    Trusted.MirSemantics.getElem? program.bodies defId = some b ∧
    b.identity = identity ∧
    b.isUnsafe = false ∧
    b.argumentCount = 0 ∧
    ReturnsTotal program defId [] .unit

/-- Complete MIR contract over all 77 captured primitive sealing markers:
exact body count matching `primitiveMarkerIdentities` and indexed `UnitMarkerAt`
agreement at every `defId`. -/
noncomputable def CapturedMarkerMatrixSpec (program : Program) : Prop :=
  program.bodies.length = primitiveMarkerIdentities.length ∧
  ∀ (defId : DefId) (identity : String),
    Trusted.MirSemantics.getElem? primitiveMarkerIdentities defId =
      some identity →
    UnitMarkerAt program defId identity

/-! ## Part 2: Endian-Parametric `Trusted.MirSemantics.Bytes` Contract -/

/-- `FromZeros` semantic contract: `ty` has a sized layout and `layout.size`
zero-initialized bytes decode without fault to a well-formed value of `ty`. -/
noncomputable def IsFromZeros (endian : TargetEndian) (ty : MirTy) : Prop :=
  ∃ layout v,
    layoutOfTy ty = some layout ∧
    decodeVal endian ty (List.replicate layout.size (.init 0 none)) =
      .ok (some v) ∧
    checkVal v ty = true

/-- `FromBytes` semantic contract: `ty` has a sized layout and every
initialized byte sequence of length `layout.size` (with arbitrary byte values
and provenance) decodes without fault to a well-formed value of `ty`. -/
noncomputable def IsFromBytes (endian : TargetEndian) (ty : MirTy) : Prop :=
  ∃ layout,
    layoutOfTy ty = some layout ∧
    ∀ (bs : List AllocByte) (raw : List UInt8),
      bs.length = layout.size →
      initBytes? bs = some raw →
      ∃ v, decodeVal endian ty bs = .ok (some v) ∧ checkVal v ty = true

/-- `IntoBytes` semantic contract: `ty` has a sized layout, every well-formed
value of `ty` encodes without fault, and every encoded byte sequence has length
`layout.size` with all bytes initialized (zero `.uninit` padding) and no
pointer provenance. -/
noncomputable def IsIntoBytes (endian : TargetEndian) (ty : MirTy) : Prop :=
  ∃ layout,
    layoutOfTy ty = some layout ∧
    (∀ v : Val, checkVal v ty = true → ∃ bs, encodeVal endian ty v = .ok bs) ∧
    (∀ (v : Val) (bs : List AllocByte),
      encodeVal endian ty v = .ok bs →
      bs.length = layout.size ∧
      ∃ raw : List UInt8,
        initBytes? bs = some raw ∧
        bs = raw.map (fun b => AllocByte.init b none))

/-- `Unaligned` semantic contract: `ty` has a sized layout with 1-byte
alignment (`alignLog2 = 0`). -/
noncomputable def IsUnaligned (ty : MirTy) : Prop :=
  ∃ layout, layoutOfTy ty = some layout ∧ layout.alignLog2 = 0

/-- Model-side byte-validity condition matching the `<bool as
TryFromBytes>::is_safe` predicate (`*byte < 2`; validator MIR body not
captured): initialized 1-byte sequences decode iff the byte is `< 2`, and fault
with `.undefined` on all bytes `≥ 2`. -/
noncomputable def BoolTryFromBytesSound (endian : TargetEndian) : Prop :=
  ∀ (bs : List AllocByte) (raw : List UInt8),
    bs.length = 1 →
    initBytes? bs = some raw →
    (decodeUInt endian raw < 2 →
      ∃ b : Bool,
        decodeVal endian .bool bs = .ok (some (.bool b)) ∧
        checkVal (.bool b) .bool = true) ∧
    (2 ≤ decodeUInt endian raw →
      decodeVal endian .bool bs = .error .undefined)

/-- Model-side byte-validity condition matching the `<char as
TryFromBytes>::is_safe` predicate (`char::from_u32(c).is_some()`; validator MIR
body not captured): initialized 4-byte sequences decode iff the 32-bit word
satisfies `isUnicodeScalar`, and fault with `.undefined` otherwise. -/
noncomputable def CharTryFromBytesSound (endian : TargetEndian) : Prop :=
  ∀ (bs : List AllocByte) (raw : List UInt8),
    bs.length = 4 →
    initBytes? bs = some raw →
    (isUnicodeScalar (decodeUInt endian raw) = true →
      ∃ c : Char,
        decodeVal endian .char bs = .ok (some (.char c)) ∧
        checkVal (.char c) .char = true) ∧
    (isUnicodeScalar (decodeUInt endian raw) = false →
      decodeVal endian .char bs = .error .undefined)

/-- Model-side bit-validity conditions for the 15 non-float primitive types'
`unsafe_impl!`s in `zerocopy/src/impls.rs` (`()`, `bool`, `char`, and all 12
integer types `IntWidth × Bool`), paired with negative model-side refutations
for `FromBytes` (`bool`, `char`) and `Unaligned` (`char`, `w ≠ .i8`). -/
noncomputable def PrimitiveBitValiditySpec : Prop :=
  (∀ endian : TargetEndian,
    -- `()`: FromZeros, FromBytes, IntoBytes, Unaligned
    IsFromZeros endian .unit ∧
    IsFromBytes endian .unit ∧
    IsIntoBytes endian .unit ∧
    IsUnaligned .unit ∧
    -- `bool`: FromZeros, IntoBytes, Unaligned, TryFromBytes (`< 2`)
    IsFromZeros endian .bool ∧
    IsIntoBytes endian .bool ∧
    IsUnaligned .bool ∧
    BoolTryFromBytesSound endian ∧
    -- `char`: FromZeros, IntoBytes, TryFromBytes (`isUnicodeScalar`)
    IsFromZeros endian .char ∧
    IsIntoBytes endian .char ∧
    CharTryFromBytesSound endian ∧
    -- All 12 integer types (`u8`..`isize` = `IntWidth × Bool`):
    -- FromZeros, FromBytes, IntoBytes
    (∀ (w : IntWidth) (s : Bool),
      IsFromZeros endian (.int w s) ∧
      IsFromBytes endian (.int w s) ∧
      IsIntoBytes endian (.int w s)) ∧
    -- `u8` and `i8`: Unaligned
    (∀ s : Bool, IsUnaligned (.int .i8 s)) ∧
    -- Negative refutation 1: `bool` omits `FromBytes` (`0x02` faults)
    (decodeVal endian .bool [.init 0x02 none] = .error .undefined ∧
      ¬ IsFromBytes endian .bool) ∧
    -- Negative refutation 2: `char` omits `FromBytes` (`0xD800` surrogate)
    (decodeVal endian .char
        ((encodeUInt endian 4 0xD800).map (fun b => .init b none)) =
        .error .undefined ∧
      ¬ IsFromBytes endian .char)) ∧
  -- Negative refutation 3: `char` omits `Unaligned` (`alignLog2 = 2 > 0`)
  ((∃ layout, layoutOfTy .char = some layout ∧ 0 < layout.alignLog2) ∧
    ¬ IsUnaligned .char) ∧
  -- Negative refutation 4: multi-byte integers (`w ≠ .i8`) omit `Unaligned`
  (∀ (w : IntWidth) (s : Bool), w ≠ .i8 →
    (∃ layout,
      layoutOfTy (.int w s) = some layout ∧ 0 < layout.alignLog2) ∧
    ¬ IsUnaligned (.int w s))

noncomputable def specs : Specs :=
  ⟨safetyPrecondition,
    fun program => CapturedMarkerMatrixSpec program ∧ PrimitiveBitValiditySpec⟩

end Spec
