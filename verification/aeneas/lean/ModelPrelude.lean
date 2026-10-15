/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RustModel
public import RustAeneas.Storage
public import Zerocopy.Types
@[expose] public section

/-!
Extracted integer words store finite bit patterns. Their mathematical models
expose ordinary `Nat` or `Int` values together with proofs of the corresponding
word bounds. A reader of a decoded word can use those bounds directly, without
reintroducing a separate validity premise.

Raw nonzero wrappers need an additional admission check: their extracted shape
can contain zero even though the mathematical nonzero model cannot. These
decoders test that condition and preserve its proof in the accepted value.
-/

open Aeneas.Std
namespace AeneasSpecs

-- The imported PhantomData carrier has no runtime fields. Its value model
-- records only that empty stored value; it makes no claim about ownership,
-- variance, drop checking, or pointer provenance.
@[reducible] instance modelPhantomData (T : Type) :
    RustModel (Zerocopy.core.marker.PhantomData T) :=
  { Model := Unit, «decode» := fun _ => some (),
    representation := some (Rust.Storage.emptyDecoder Zerocopy.core.marker.PhantomData.mk) }

/-- This check fails if the pinned extracted carrier gains runtime fields. -/
theorem phantomData_eq_mk (T : Type) (raw : Zerocopy.core.marker.PhantomData T) :
    raw = Zerocopy.core.marker.PhantomData.mk := by
  cases raw
  rfl


-- A wrapper has exactly its payload's accepted bytes. Missing child storage
-- semantics stay missing; a mathematical decoder never supplies those bytes.
def wrapperRepresentation {A B : Type} [ma : RustModel A] (wrap : A → B) :
    Option (Rust.Storage.BitDecoder B) := ma.representation.map (·.map wrap)

theorem initializedWrapperRepresentation {A B : Type} [ma : RustModel A]
    (wrap : A → B) (child : RustModel.initializedRepresentation A) :
    match wrapperRepresentation wrap with
    | none => False
    | some decoder => decoder.Initialized := by
  cases h : ma.representation with
  | none => simp [RustModel.initializedRepresentation, h] at child
  | some decoder =>
    simp only [RustModel.initializedRepresentation, h] at child
    simp only [wrapperRepresentation, h, Option.map_some]
    exact Rust.Storage.BitDecoder.map_initialized decoder wrap child

-- These providers interpret stored values only. They do not model mutation,
-- aliasing, synchronization, or destruction of the standard-library wrappers.
@[reducible] instance modelManuallyDrop (T : Type) [ma : RustModel T] :
    RustModel (core.mem.manually_drop.ManuallyDrop T) where
  Model := ma.Model
  decode raw := ma.decode raw.value
  representation := wrapperRepresentation core.mem.manually_drop.ManuallyDrop.mk
  representationChoice raw := ma.representationChoice raw.value

@[reducible] instance modelCell (T : Type) [ma : RustModel T] :
    RustModel (core.cell.Cell T) where
  Model := ma.Model
  decode raw := ma.decode raw.value
  representation := wrapperRepresentation core.cell.Cell.mk

@[reducible] instance modelUnsafeCell (T : Type) [ma : RustModel T] :
    RustModel (core.cell.UnsafeCell T) where
  Model := ma.Model
  decode raw := ma.decode raw.value
  representation := wrapperRepresentation core.cell.UnsafeCell.mk

@[reducible] instance modelWrapping (T : Type) [ma : RustModel T] :
    RustModel (Zerocopy.core.num.wrapping.Wrapping T) where
  Model := ma.Model
  decode raw := ma.decode raw._0
  representation := wrapperRepresentation Zerocopy.core.num.wrapping.Wrapping.mk

theorem initializedManuallyDrop (T : Type) [ma : RustModel T]
    (child : RustModel.initializedRepresentation T) :
    RustModel.initializedRepresentation (core.mem.manually_drop.ManuallyDrop T) :=
  initializedWrapperRepresentation core.mem.manually_drop.ManuallyDrop.mk child

theorem initializedCell (T : Type) [ma : RustModel T]
    (child : RustModel.initializedRepresentation T) :
    RustModel.initializedRepresentation (core.cell.Cell T) :=
  initializedWrapperRepresentation core.cell.Cell.mk child

theorem initializedUnsafeCell (T : Type) [ma : RustModel T]
    (child : RustModel.initializedRepresentation T) :
    RustModel.initializedRepresentation (core.cell.UnsafeCell T) :=
  initializedWrapperRepresentation core.cell.UnsafeCell.mk child

theorem initializedWrapping (T : Type) [ma : RustModel T]
    (child : RustModel.initializedRepresentation T) :
    RustModel.initializedRepresentation (Zerocopy.core.num.wrapping.Wrapping T) :=
  initializedWrapperRepresentation Zerocopy.core.num.wrapping.Wrapping.mk child

-- The bounds are proofs stored beside the value. They contribute constraints
-- to the mathematical type without another runtime field or admission test.
structure UnsignedWord (ty : UScalarTy) where
  value : Nat
  bound : value ≤ UScalar.max ty

structure SignedWord (ty : IScalarTy) where
  value : Int
  lower : IScalar.min ty ≤ value
  upper : value ≤ IScalar.max ty

structure NonZeroUnsignedWord (ty : UScalarTy) extends UnsignedWord ty where
  positive : 0 < value

structure NonZeroSignedWord (ty : IScalarTy) extends SignedWord ty where
  nonzero : value ≠ 0

instance {ty : UScalarTy} : CoeOut (UnsignedWord ty) Nat := ⟨UnsignedWord.value⟩
instance {ty : IScalarTy} : CoeOut (SignedWord ty) Int := ⟨SignedWord.value⟩
instance {ty : UScalarTy} : CoeOut (NonZeroUnsignedWord ty) Nat := ⟨fun x => x.value⟩
instance {ty : IScalarTy} : CoeOut (NonZeroSignedWord ty) Int := ⟨fun x => x.value⟩

-- Proof irrelevance makes equal numeric observations sufficient for record
-- equality: two proofs of the same bound do not create distinct word values.
@[ext] theorem UnsignedWord.ext {x y : UnsignedWord ty} (h : x.value = y.value) : x = y := by
  cases x; cases y; simp_all
@[ext] theorem SignedWord.ext {x y : SignedWord ty} (h : x.value = y.value) : x = y := by
  cases x; cases y; simp_all
@[ext] theorem NonZeroUnsignedWord.ext {x y : NonZeroUnsignedWord ty}
    (h : x.value = y.value) : x = y := by
  cases x; cases y; congr 1; exact UnsignedWord.ext h
@[ext] theorem NonZeroSignedWord.ext {x y : NonZeroSignedWord ty}
    (h : x.value = y.value) : x = y := by
  cases x; cases y; congr 1; exact SignedWord.ext h

-- Aeneas scalar values already carry their machine bounds. Transport those
-- existing facts when decoding, instead of retesting valid bit patterns.
def unsignedWord (x : UScalar ty) : UnsignedWord ty :=
  ⟨x.val, by have := x.hBounds; simp only [UScalar.max]; omega⟩
def signedWord (x : IScalar ty) : SignedWord ty :=
  ⟨x.val, by simpa only [IScalar.min] using x.hmin,
    by have := x.hmax; simp only [IScalar.max]; omega⟩

/-- Admission currently checks a little-endian 64-bit extraction target.
The shared initialization theorems are independent of this byte order. -/
def uScalarBitDecoder (ty : UScalarTy) : Rust.Storage.BitDecoder (UScalar ty) :=
  Rust.Storage.AeneasAdapter.unsignedDecoder ty .little

def iScalarBitDecoder (ty : IScalarTy) : Rust.Storage.BitDecoder (IScalar ty) :=
  Rust.Storage.AeneasAdapter.signedDecoder ty .little

abbrev u8BitDecoder := uScalarBitDecoder .U8

@[reducible] instance modelUScalar (ty : UScalarTy) : RustModel (UScalar ty) where
  Model := UnsignedWord ty
  decode x := some (unsignedWord x)
  representation := some (uScalarBitDecoder ty)
@[reducible] instance modelIScalar (ty : IScalarTy) : RustModel (IScalar ty) where
  Model := SignedWord ty
  decode x := some (signedWord x)
  representation := some (iScalarBitDecoder ty)

/-- Char stores a Unicode scalar value in four bytes. Filtering the complete
integer decoder rejects surrogates and out-of-range code points without ever
turning an uninitialized representation into a character. -/
def charBitDecoder : Rust.Storage.BitDecoder Char :=
  (Rust.Storage.integerDecoder 4 .little).filterMap fun word =>
    let value := UInt32.ofNat word.toNat
    if h : isValidChar value then some ⟨value, h⟩ else none

@[reducible] instance modelChar : RustModel Char where
  Model := Char
  decode x := some x
  representation := some charBitDecoder

def nonzeroUScalarBitDecoder (ty : UScalarTy) (Inner : Type) :
    Rust.Storage.BitDecoder (core.num.nonzero.NonZero (UScalar ty) Inner) :=
  (uScalarBitDecoder ty).filterMap fun word =>
    if word.val = 0 then none else some ⟨word⟩

def nonzeroIScalarBitDecoder (ty : IScalarTy) (Inner : Type) :
    Rust.Storage.BitDecoder (core.num.nonzero.NonZero (IScalar ty) Inner) :=
  (iScalarBitDecoder ty).filterMap fun word =>
    if word.val = 0 then none else some ⟨word⟩

@[reducible] instance modelNonZeroUScalar (ty : UScalarTy) (Inner : Type) :
    RustModel (core.num.nonzero.NonZero (UScalar ty) Inner) where
  Model := NonZeroUnsignedWord ty
  decode raw := if h : 0 < raw.val.val then some ⟨unsignedWord raw.val, h⟩ else none
  representation := some (nonzeroUScalarBitDecoder ty Inner)

@[reducible] instance modelNonZeroIScalar (ty : IScalarTy) (Inner : Type) :
    RustModel (core.num.nonzero.NonZero (IScalar ty) Inner) where
  Model := NonZeroSignedWord ty
  decode raw := if h : raw.val.val ≠ 0 then some ⟨signedWord raw.val, h⟩ else none
  representation := some (nonzeroIScalarBitDecoder ty Inner)

-- Rust guarantees the zero niche for these particular standard-library
-- wrappers. Map the full integer decoder: a zero is a successfully decoded
-- Rust None, whereas an earlier byte failure remains a decoding failure.
-- A generic Option<T> has no physical decoder inferred from its payload.
@[reducible] instance (priority := 1001) modelOptionNonZeroUScalar
    (ty : UScalarTy) (Inner : Type) :
    RustModel (Option (core.num.nonzero.NonZero (UScalar ty) Inner)) where
  Model := Option (NonZeroUnsignedWord ty)
  decode := (modelOption (ma := modelNonZeroUScalar ty Inner)).decode
  representation := some ((uScalarBitDecoder ty).map fun word =>
    if word.val = 0 then none else some ⟨word⟩)

@[reducible] instance (priority := 1001) modelOptionNonZeroIScalar
    (ty : IScalarTy) (Inner : Type) :
    RustModel (Option (core.num.nonzero.NonZero (IScalar ty) Inner)) where
  Model := Option (NonZeroSignedWord ty)
  decode := (modelOption (ma := modelNonZeroIScalar ty Inner)).decode
  representation := some ((iScalarBitDecoder ty).map fun word =>
    if word.val = 0 then none else some ⟨word⟩)

theorem initializedUScalar (ty : UScalarTy) :
    RustModel.initializedRepresentation (UScalar ty) :=
  Rust.Storage.AeneasAdapter.unsignedDecoder_initialized ty .little

theorem initializedIScalar (ty : IScalarTy) :
    RustModel.initializedRepresentation (IScalar ty) :=
  Rust.Storage.AeneasAdapter.signedDecoder_initialized ty .little

theorem initializedNonZeroUScalar (ty : UScalarTy) (Inner : Type) :
    RustModel.initializedRepresentation (core.num.nonzero.NonZero (UScalar ty) Inner) :=
  Rust.Storage.BitDecoder.filterMap_initialized _ _ (initializedUScalar ty)

theorem initializedNonZeroIScalar (ty : IScalarTy) (Inner : Type) :
    RustModel.initializedRepresentation (core.num.nonzero.NonZero (IScalar ty) Inner) :=
  Rust.Storage.BitDecoder.filterMap_initialized _ _ (initializedIScalar ty)

theorem initializedOptionNonZeroUScalar (ty : UScalarTy) (Inner : Type) :
    RustModel.initializedRepresentation (Option (core.num.nonzero.NonZero (UScalar ty) Inner)) :=
  Rust.Storage.BitDecoder.map_initialized _ _ (initializedUScalar ty)

theorem initializedOptionNonZeroIScalar (ty : IScalarTy) (Inner : Type) :
    RustModel.initializedRepresentation (Option (core.num.nonzero.NonZero (IScalar ty) Inner)) :=
  Rust.Storage.BitDecoder.map_initialized _ _ (initializedIScalar ty)

abbrev NonZeroUsizeValue := NonZeroUnsignedWord .Usize
abbrev modelNonZeroUsize := modelNonZeroUScalar .Usize core.num.niche_types.NonZeroUsizeInner

@[simp] theorem unsignedWord_value (x : UScalar ty) : (unsignedWord x).value = x.val := rfl
@[simp] theorem signedWord_value (x : IScalar ty) : (signedWord x).value = x.val := rfl
@[simp] theorem decodeUScalar (x : UScalar ty) :
    (modelUScalar ty).decode x = some (unsignedWord x) := rfl
@[simp] theorem decodeIScalar (x : IScalar ty) :
    (modelIScalar ty).decode x = some (signedWord x) := rfl

/-- Reduce an explicit decoder equation to the numeric observation it preserves.
Extensionality handles the bound proofs, so operation proofs need only numbers. -/
theorem decodeUScalar_iff (raw : UScalar ty) (value : UnsignedWord ty) :
    (modelUScalar ty).decode raw = some value ↔ raw.val = value.value := by
  change some (unsignedWord raw) = some value ↔ raw.val = value.value
  simp only [Option.some.injEq]
  exact ⟨fun h => congrArg UnsignedWord.value h, (fun h => UnsignedWord.ext (x := unsignedWord raw) h)⟩

theorem decodeNonZeroUScalar_iff (raw : core.num.nonzero.NonZero (UScalar ty) Inner)
    (value : NonZeroUnsignedWord ty) :
    (modelNonZeroUScalar ty Inner).decode raw = some value ↔ raw.val.val = value.value := by
  change (if h : 0 < raw.val.val then some ⟨unsignedWord raw.val, h⟩ else none) = some value ↔ _
  constructor
  · intro h
    split at h
    · cases Option.some.inj h; rfl
    · contradiction
  · intro h
    -- In the reverse direction, the supplied mathematical value already proves
    -- positivity. Numeric equality transfers it to the raw wrapper and selects
    -- the accepting branch; there is no separate validity assumption.
    have hp : 0 < raw.val.val := h ▸ value.positive
    rw [dif_pos hp]
    congr 1
    exact NonZeroUnsignedWord.ext h

end AeneasSpecs
