/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RustModel
public import Zerocopy.TypesExternal
@[expose] public section

open Aeneas.Std
namespace AeneasSpecs

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

def unsignedWord (x : UScalar ty) : UnsignedWord ty :=
  ⟨x.val, by have := x.hBounds; simp only [UScalar.max]; omega⟩
def signedWord (x : IScalar ty) : SignedWord ty :=
  ⟨x.val, by simpa only [IScalar.min] using x.hmin,
    by have := x.hmax; simp only [IScalar.max]; omega⟩

@[reducible] instance modelUScalar (ty : UScalarTy) : RustModel (UScalar ty) :=
  ⟨UnsignedWord ty, fun x => some (unsignedWord x)⟩
@[reducible] instance modelIScalar (ty : IScalarTy) : RustModel (IScalar ty) :=
  ⟨SignedWord ty, fun x => some (signedWord x)⟩

@[reducible] instance modelNonZeroUScalar (ty : UScalarTy) (Inner : Type) :
    RustModel (core.num.nonzero.NonZero (UScalar ty) Inner) where
  Model := NonZeroUnsignedWord ty
  decode raw := if h : 0 < raw.val.val then some ⟨unsignedWord raw.val, h⟩ else none

@[reducible] instance modelNonZeroIScalar (ty : IScalarTy) (Inner : Type) :
    RustModel (core.num.nonzero.NonZero (IScalar ty) Inner) where
  Model := NonZeroSignedWord ty
  decode raw := if h : raw.val.val ≠ 0 then some ⟨signedWord raw.val, h⟩ else none

abbrev NonZeroUsizeValue := NonZeroUnsignedWord .Usize
abbrev modelNonZeroUsize := modelNonZeroUScalar .Usize core.num.niche_types.NonZeroUsizeInner

@[simp] theorem unsignedWord_value (x : UScalar ty) : (unsignedWord x).value = x.val := rfl
@[simp] theorem signedWord_value (x : IScalar ty) : (signedWord x).value = x.val := rfl
@[simp] theorem decodeUScalar (x : UScalar ty) :
    (modelUScalar ty).decode x = some (unsignedWord x) := rfl
@[simp] theorem decodeIScalar (x : IScalar ty) :
    (modelIScalar ty).decode x = some (signedWord x) := rfl

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
    have hp : 0 < raw.val.val := h ▸ value.positive
    rw [dif_pos hp]
    congr 1
    exact NonZeroUnsignedWord.ext h

end AeneasSpecs
