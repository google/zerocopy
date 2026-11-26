-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

/-!
# `NonZero*` and `Option<NonZero*>` Sealing Markers & Niche Bit Validity

Formal specification for the 12 `core::num::NonZero<T>` and 12
`core::option::Option<core::num::NonZero<T>>` integer types (`u8`..`isize`) in
`zerocopy/src/impls.rs`:

1. **Selected MIR sealing markers (`CapturedNicheMatrixSpec`):** Binds the 88
   selected verbatim `only_derive_is_allowed_to_implement_this_trait` functions
   in `zerocopy/src/impls.rs:226-295` (`38` for `NonZero<*>` and `50` for
   `Option<NonZero<*>>`) by exact count, canonical `b.identity` path,
   `b.isUnsafe = false`, `b.argumentCount = 0`, total `()` return
   (`ReturnsTotal`), and memory-preserving execution over every `MemoryState`.
2. **Model-side `Trusted.MirSemantics.Bytes` niche contract
   (`NonZeroNicheBitValiditySpec`):** Proves endian- and signedness-parametric
   byte-validity and zero-niche partition properties over `layoutOfTy`,
   `initBytes?`, `decodeUInt`, `decodeScalar`, `decodeVal`, and `encodeVal`
   (the validator MIR bodies of `<NonZero* as TryFromBytes>::is_safe` are not
   yet captured, pending `TerminatorKind::Call` and generic `transmute_with`
   monomorphization):
   - exact non-zero byte characterization (`decodeIntBytes` returns `some 0`
     iff `ZeroNicheBytes`, for both unsigned and two's-complement signed
     widths);
   - model-side refutations of `FromZeros` and `FromBytes` on `NonZero<*>`
     (`zeroAllocBytes` is initialized of length `w.byteSize` yet violates
     `NonZeroValidBytes`) alongside `NonZeroIntoBytesSound` (`encodeVal` of
     every well-formed non-zero scalar yields `layout.size` bytes with zero
     `.uninit` padding that satisfy `NonZeroValidBytes` and decode back to the
     same integer);
   - the `Option<NonZero<*>>` Niche Partition Theorem (`ZeroNicheBytes` and
     `NonZeroValidBytes` form a disjoint, exhaustive partition of
     `AllInitBytes w.byteSize` while excluding `.uninit`); and
   - 1-byte `.i8` alignment vs. model-side multi-byte alignment refutations for
     `w ≠ .i8` (`0 < (intLayout w).alignLog2`).
-/

/-- Canonical `rust-path-v1` identities of the 88 selected trait sealing markers
for `core::num::NonZero<*>` and `core::option::Option<core::num::NonZero<*>>`
in `zerocopy/src/impls.rs:226-295` (canonical SCC shard order). -/
def nonzeroMarkerIdentities : List String := [
  "rust-path-v1::impls::_::<impl FromBytes for core::option::Option<core::num::nonzero::NonZero<i128>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for core::option::Option<core::num::nonzero::NonZero<i16>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for core::option::Option<core::num::nonzero::NonZero<i32>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for core::option::Option<core::num::nonzero::NonZero<i64>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for core::option::Option<core::num::nonzero::NonZero<i8>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for core::option::Option<core::num::nonzero::NonZero<isize>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for core::option::Option<core::num::nonzero::NonZero<u128>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for core::option::Option<core::num::nonzero::NonZero<u16>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for core::option::Option<core::num::nonzero::NonZero<u32>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for core::option::Option<core::num::nonzero::NonZero<u64>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for core::option::Option<core::num::nonzero::NonZero<u8>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromBytes for core::option::Option<core::num::nonzero::NonZero<usize>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for core::option::Option<core::num::nonzero::NonZero<i128>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for core::option::Option<core::num::nonzero::NonZero<i16>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for core::option::Option<core::num::nonzero::NonZero<i32>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for core::option::Option<core::num::nonzero::NonZero<i64>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for core::option::Option<core::num::nonzero::NonZero<i8>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for core::option::Option<core::num::nonzero::NonZero<isize>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for core::option::Option<core::num::nonzero::NonZero<u128>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for core::option::Option<core::num::nonzero::NonZero<u16>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for core::option::Option<core::num::nonzero::NonZero<u32>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for core::option::Option<core::num::nonzero::NonZero<u64>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for core::option::Option<core::num::nonzero::NonZero<u8>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl FromZeros for core::option::Option<core::num::nonzero::NonZero<usize>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for core::num::nonzero::NonZero<i128>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for core::num::nonzero::NonZero<i16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for core::num::nonzero::NonZero<i32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for core::num::nonzero::NonZero<i64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for core::num::nonzero::NonZero<i8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for core::num::nonzero::NonZero<isize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for core::num::nonzero::NonZero<u128>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for core::num::nonzero::NonZero<u16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for core::num::nonzero::NonZero<u32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for core::num::nonzero::NonZero<u64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for core::num::nonzero::NonZero<u8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Immutable for core::num::nonzero::NonZero<usize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::num::nonzero::NonZero<i128>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::num::nonzero::NonZero<i16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::num::nonzero::NonZero<i32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::num::nonzero::NonZero<i64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::num::nonzero::NonZero<i8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::num::nonzero::NonZero<isize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::num::nonzero::NonZero<u128>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::num::nonzero::NonZero<u16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::num::nonzero::NonZero<u32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::num::nonzero::NonZero<u64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::num::nonzero::NonZero<u8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::num::nonzero::NonZero<usize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::option::Option<core::num::nonzero::NonZero<i128>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::option::Option<core::num::nonzero::NonZero<i16>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::option::Option<core::num::nonzero::NonZero<i32>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::option::Option<core::num::nonzero::NonZero<i64>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::option::Option<core::num::nonzero::NonZero<i8>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::option::Option<core::num::nonzero::NonZero<isize>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::option::Option<core::num::nonzero::NonZero<u128>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::option::Option<core::num::nonzero::NonZero<u16>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::option::Option<core::num::nonzero::NonZero<u32>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::option::Option<core::num::nonzero::NonZero<u64>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::option::Option<core::num::nonzero::NonZero<u8>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl IntoBytes for core::option::Option<core::num::nonzero::NonZero<usize>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::num::nonzero::NonZero<i128>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::num::nonzero::NonZero<i16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::num::nonzero::NonZero<i32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::num::nonzero::NonZero<i64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::num::nonzero::NonZero<i8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::num::nonzero::NonZero<isize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::num::nonzero::NonZero<u128>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::num::nonzero::NonZero<u16>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::num::nonzero::NonZero<u32>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::num::nonzero::NonZero<u64>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::num::nonzero::NonZero<u8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::num::nonzero::NonZero<usize>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::option::Option<core::num::nonzero::NonZero<i128>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::option::Option<core::num::nonzero::NonZero<i16>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::option::Option<core::num::nonzero::NonZero<i32>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::option::Option<core::num::nonzero::NonZero<i64>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::option::Option<core::num::nonzero::NonZero<i8>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::option::Option<core::num::nonzero::NonZero<isize>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::option::Option<core::num::nonzero::NonZero<u128>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::option::Option<core::num::nonzero::NonZero<u16>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::option::Option<core::num::nonzero::NonZero<u32>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::option::Option<core::num::nonzero::NonZero<u64>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::option::Option<core::num::nonzero::NonZero<u8>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl TryFromBytes for core::option::Option<core::num::nonzero::NonZero<usize>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Unaligned for core::num::nonzero::NonZero<i8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Unaligned for core::num::nonzero::NonZero<u8>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Unaligned for core::option::Option<core::num::nonzero::NonZero<i8>>>::only_derive_is_allowed_to_implement_this_trait",
  "rust-path-v1::impls::_::<impl Unaligned for core::option::Option<core::num::nonzero::NonZero<u8>>>::only_derive_is_allowed_to_implement_this_trait"
]

/-! ## Part 1: Selected MIR Sealing-Marker Contract -/

/-- Total-correctness MIR call outcome at `defId` with empty caller memory. -/
def ReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

/-- Non-vacuous identity-keyed safety precondition over the 88 selected
zero-argument trait sealing markers. -/
def safetyPrecondition (identity : String) (args : List Val) : Prop :=
  identity ∈ nonzeroMarkerIdentities ∧ args = []

/-- Asserts that `program.bodies[defId]` has canonical path `identity`, is safe
(`isUnsafe = false`), takes zero arguments (`argumentCount = 0`), satisfies
`ReturnsTotal` returning `()` on `[]`, and steps cleanly to `()` from every
initial `mem : MemoryState` without mutating `mem`. -/
def UnitMarkerAt (program : Program) (defId : DefId)
    (identity : String) : Prop :=
  ∃ b : Body,
    Trusted.MirSemantics.getElem? program.bodies defId = some b ∧
    b.identity = identity ∧
    b.isUnsafe = false ∧
    b.argumentCount = 0 ∧
    ReturnsTotal program defId [] .unit ∧
    ∀ mem : MemoryState,
      ∃ s₁ : State,
        Step program
          { frames := [⟨defId, 0, 0, [.immediate none], none, none, none⟩],
             callerMem := ⟨[]⟩, mem := mem }
          (.step s₁) ∧
        s₁.mem = mem ∧
        Step program s₁ (.done (.returned ⟨.unit, ⟨[]⟩⟩))

/-- MIR contract over the 88 selected `NonZero<*>` and `Option<NonZero<*>>`
trait sealing markers: exact body count matching `nonzeroMarkerIdentities` and
indexed `UnitMarkerAt` agreement at every `defId`. -/
def CapturedNicheMatrixSpec (program : Program) : Prop :=
  program.bodies.length = nonzeroMarkerIdentities.length ∧
  ∀ (defId : DefId) (identity : String),
    Trusted.MirSemantics.getElem? nonzeroMarkerIdentities defId =
      some identity →
    UnitMarkerAt program defId identity

/-! ## Part 2: Model-Side `Trusted.MirSemantics.Bytes` Niche Contract -/

/-- `bs` has exact byte length `n` and every byte in `bs` is initialized
(`initBytes? bs = some raw`, stripping pointer provenance as in `read_scalar`).
-/
def AllInitBytes (n : Nat) (bs : List AllocByte) : Prop :=
  bs.length = n ∧ ∃ raw : List UInt8, initBytes? bs = some raw

/-- Canonical provenance-free all-zero byte slice of length `n`. -/
def zeroAllocBytes (n : Nat) : List AllocByte :=
  List.replicate n (AllocByte.init 0 none)

/-- Zero-niche byte predicate (`Option<NonZero*>::None` representation): `bs`
has length `n` and every byte is an initialized `0x00` byte. -/
def ZeroNicheBytes (n : Nat) (bs : List AllocByte) : Prop :=
  bs.length = n ∧ initBytes? bs = some (List.replicate n 0)

/-- Decode a `w.byteSize`-byte initialized slice `bs` at `(endian, signed, w)`
via `Trusted.MirSemantics` (`initBytes?`, `decodeUInt`, and `decodeScalar`),
returning `some z` on `w.byteSize` initialized bytes and `none` otherwise. -/
noncomputable def decodeIntBytes (endian : TargetEndian) (signed : Bool)
    (w : IntWidth) (bs : List AllocByte) : Option Int :=
  if Nat.beq bs.length w.byteSize then
    match initBytes? bs with
    | some raw =>
      some (decodeScalar ⟨w, signed, BitVec.ofNat 128 (decodeUInt endian raw)⟩)
    | none => none
  else
    none

/-- Model-side byte-validity predicate for `core::num::NonZero<T>` matching the
`!= 0` check of `<NonZero* as TryFromBytes>::is_safe` (whose MIR body is not
captured here): `bs` consists of `w.byteSize` initialized bytes whose decoded
unsigned or two's-complement integer value is non-zero. -/
def NonZeroValidBytes (endian : TargetEndian) (signed : Bool)
    (w : IntWidth) (bs : List AllocByte) : Prop :=
  AllInitBytes w.byteSize bs ∧
  ∃ z : Int, decodeIntBytes endian signed w bs = some z ∧ z ≠ 0

/-- Model-side `IntoBytes` contract for `NonZero<*>` over
`Trusted.MirSemantics.encodeVal`: every well-formed non-zero scalar `sv` of
`(.int w signed)` encodes in byte order `endian` to a byte slice `bs` whose
length is the `layoutOfTy` size, which contains zero `AllocByte.uninit`
(padding) bytes, which satisfies `NonZeroValidBytes` (so the encoding stays out
of the `Option<NonZero<*>>` niche), and which decodes back to `decodeScalar sv`.
-/
def NonZeroIntoBytesSound (endian : TargetEndian) (signed : Bool)
    (w : IntWidth) : Prop :=
  ∀ sv : ScalarVal,
    checkVal (.scalar sv) (.int w signed) = true →
    decodeScalar sv ≠ 0 →
    ∃ (layout : LayoutData) (bs : List AllocByte),
      layoutOfTy (.int w signed) = some layout ∧
      encodeVal endian (.int w signed) (.scalar sv) = .ok bs ∧
      bs.length = layout.size ∧
      AllocByte.uninit ∉ bs ∧
      NonZeroValidBytes endian signed w bs ∧
      decodeIntBytes endian signed w bs = some (decodeScalar sv)

/-- Model-side Niche Partition Theorem for `Option<NonZero<*>>`:
`ZeroNicheBytes w.byteSize` (`None`) and `NonZeroValidBytes endian signed w`
(`Some`) partition `AllInitBytes w.byteSize` into two mutually exclusive,
exhaustive classes while excluding every slice containing `.uninit`. -/
def OptionNonZeroNichePartition (endian : TargetEndian)
    (signed : Bool) (w : IntWidth) : Prop :=
  ∀ bs : List AllocByte,
    (AllInitBytes w.byteSize bs ↔
      (ZeroNicheBytes w.byteSize bs ∨
        NonZeroValidBytes endian signed w bs)) ∧
    ¬ (ZeroNicheBytes w.byteSize bs ∧
      NonZeroValidBytes endian signed w bs) ∧
    (AllocByte.uninit ∈ bs →
      ¬ ZeroNicheBytes w.byteSize bs ∧
      ¬ NonZeroValidBytes endian signed w bs)

/-- Complete model-side byte-validity, niche-partition, `FromZeros`/`FromBytes`
refutation, and alignment specification across all `TargetEndian`, `signed`,
and `IntWidth` combinations. -/
def NonZeroNicheBitValiditySpec : Prop :=
  (∀ (endian : TargetEndian) (signed : Bool) (w : IntWidth),
    -- 1. Bridge to `Trusted.MirSemantics.decodeVal` and `layoutOfTy`
    layoutOfTy (.int w signed) = some (intLayout w) ∧
    (intLayout w).size = w.byteSize ∧
    (∀ bs : List AllocByte,
      AllInitBytes w.byteSize bs →
      ∃ sv : ScalarVal,
        decodeVal endian (.int w signed) bs = .ok (some (.scalar sv)) ∧
        checkVal (.scalar sv) (.int w signed) = true ∧
        decodeIntBytes endian signed w bs = some (decodeScalar sv)) ∧
    -- 2. Non-zero byte characterization (unsigned and two's-complement signed)
    (∀ bs : List AllocByte,
      AllInitBytes w.byteSize bs →
      (decodeIntBytes endian signed w bs = some 0 ↔
        ZeroNicheBytes w.byteSize bs)) ∧
    (∀ bs : List AllocByte,
      NonZeroValidBytes endian signed w bs ↔
        (AllInitBytes w.byteSize bs ∧ ¬ ZeroNicheBytes w.byteSize bs)) ∧
    (∀ raw : List UInt8,
      raw.length = w.byteSize →
      (NonZeroValidBytes endian signed w
        (raw.map (fun b => AllocByte.init b none)) ↔
        raw.map (fun b => AllocByte.init b none) ≠
          zeroAllocBytes w.byteSize)) ∧
    -- Non-vacuity witness: unit value `1` encodes a valid `NonZero*` slice
    NonZeroValidBytes endian signed w
      ((encodeUInt endian w.byteSize 1).map (fun b => AllocByte.init b none)) ∧
    -- 3. Model-side `FromZeros`/`FromBytes` refutation & `IntoBytes` on NonZero
    AllInitBytes w.byteSize (zeroAllocBytes w.byteSize) ∧
    ZeroNicheBytes w.byteSize (zeroAllocBytes w.byteSize) ∧
    ¬ NonZeroValidBytes endian signed w (zeroAllocBytes w.byteSize) ∧
    NonZeroIntoBytesSound endian signed w ∧
    -- Non-vacuity witness: the scalar `1` satisfies both hypotheses of
    -- `NonZeroIntoBytesSound`
    checkVal (.scalar ⟨w, signed, BitVec.ofNat 128 1⟩) (.int w signed) = true ∧
    decodeScalar ⟨w, signed, BitVec.ofNat 128 1⟩ ≠ 0 ∧
    -- 4. Niche Partition Theorem for `Option<NonZero*>`
    OptionNonZeroNichePartition endian signed w) ∧
  -- 5. 1-byte `.i8` alignment vs. multi-byte alignment refutations (`w ≠ .i8`)
  (intLayout .i8).alignLog2 = 0 ∧
  (∀ w : IntWidth, w ≠ .i8 → 0 < (intLayout w).alignLog2)

noncomputable def specs : Specs :=
  ⟨safetyPrecondition, fun program =>
    CapturedNicheMatrixSpec program ∧ NonZeroNicheBitValiditySpec⟩

end Spec
