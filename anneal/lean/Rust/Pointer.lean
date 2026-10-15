/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Std

/-!
Resource-free raw pointer values. Provenance is an opaque parameter, not an
address, permission, allocation witness, or encoding in physical bytes. Merely
having provenance says nothing about whether memory may be accessed. Addresses
and slice counts use unbounded naturals; consumers must establish their target
word bounds when relating these values to Rust.

`cast` covers only raw pointer casts preserving both address and metadata (thin
casts, or compatible wide casts). `withMetadata` models slice-pointer assembly
from a thin data pointer and a count; it does not construct a reference.
`nonNull` checks just the nonzero address and provides no access permission.

Rust correspondence remains a consumer obligation. Relevant documented
premises are the Rust Reference's pointer-to-pointer cast rules, `ptr::cast`,
`ptr::slice_from_raw_parts`, and `NonNull::new`:
https://doc.rust-lang.org/reference/expressions/operator-expr.html#pointer-to-pointer-cast
https://doc.rust-lang.org/std/primitive.pointer.html#method.cast
https://doc.rust-lang.org/std/ptr/fn.slice_from_raw_parts.html
https://doc.rust-lang.org/std/ptr/struct.NonNull.html#method.new
These links identify premises to check for the consumer's version and scope;
they introduce no axioms here. There is no byte encoder, dereference, allocation,
mutation, liveness, or borrow operation in this module.
-/

namespace Rust.Pointer

/-- A raw pointer value, independent of the state of any referent. -/
structure Value (Provenance : Type u) (Metadata : Type v) where
  address : Nat
  provenance : Option Provenance
  metadata : Metadata

abbrev Thin (Provenance : Type u) := Value Provenance Unit
abbrev Slice (Provenance : Type u) := Value Provenance Nat

/-- An address-and-metadata-preserving cast changes only the Rust pointee type,
which is deliberately absent from this resource-free carrier. -/
def cast (pointer : Value Provenance Metadata) : Value Provenance Metadata := pointer

/-- Assemble metadata without acquiring permission or changing provenance. -/
def withMetadata (data : Thin Provenance) (metadata : Metadata) :
    Value Provenance Metadata := ⟨data.address, data.provenance, metadata⟩

/-- Extract the thin data pointer, discarding only metadata. -/
def dataPointer (pointer : Value Provenance Metadata) : Thin Provenance :=
  ⟨pointer.address, pointer.provenance, ()⟩

/-- Extract metadata without examining provenance. -/
def metadata (pointer : Value Provenance Metadata) : Metadata := pointer.metadata

/-- Provenance presence is a value property, not an access permission. -/
def hasProvenance (pointer : Value Provenance Metadata) : Prop :=
  pointer.provenance.isSome = true

/-- Identify the opaque token without claiming what access it permits. -/
def Carries (pointer : Value Provenance Metadata) (token : Provenance) : Prop :=
  pointer.provenance = some token

/-- Preservation includes absence and retains the same token when present.
The operation may change metadata without changing provenance. -/
def PreservesProvenance (before : Value Provenance BeforeMetadata)
    (after : Value Provenance AfterMetadata) : Prop :=
  after.provenance = before.provenance

/-- Raw pointer equality observes address and metadata, independently of the
opaque provenance. This is distinct from Lean equality of the entire carrier. -/
def equal (left right : Value Provenance Metadata) : Prop :=
  left.address = right.address ∧ left.metadata = right.metadata

instance [DecidableEq Metadata] (left right : Value Provenance Metadata) :
    Decidable (equal left right) := by
  unfold equal
  infer_instance

/-- Non-nullness alone does not imply alignment, validity, or dereferenceability. -/
abbrev NonNull (Provenance : Type u) (Metadata : Type v) :=
  { pointer : Value Provenance Metadata // pointer.address ≠ 0 }

def nonNull (pointer : Value Provenance Metadata) : Option (NonNull Provenance Metadata) :=
  if h : pointer.address = 0 then none else some ⟨pointer, h⟩

@[simp] theorem cast_eq (pointer : Value Provenance Metadata) : cast pointer = pointer := rfl

theorem cast_preservesProvenance (pointer : Value Provenance Metadata) :
    PreservesProvenance pointer (cast pointer) := rfl

theorem withMetadata_preservesProvenance (data : Thin Provenance) (m : Metadata) :
    PreservesProvenance data (withMetadata data m) := rfl

theorem dataPointer_preservesProvenance (pointer : Value Provenance Metadata) :
    PreservesProvenance pointer (dataPointer pointer) := rfl

@[simp] theorem withMetadata_provenance (data : Thin Provenance) (m : Metadata) :
    (withMetadata data m).provenance = data.provenance := rfl

@[simp] theorem metadata_withMetadata (data : Thin Provenance) (m : Metadata) :
    metadata (withMetadata data m) = m := rfl

@[simp] theorem dataPointer_withMetadata (data : Thin Provenance) (m : Metadata) :
    dataPointer (withMetadata data m) = data := by
  cases data
  rfl

@[simp] theorem withMetadata_dataPointer (pointer : Value Provenance Metadata) :
    withMetadata (dataPointer pointer) (metadata pointer) = pointer := by
  cases pointer
  rfl

@[simp] theorem nonNull_eq_none_iff (pointer : Value Provenance Metadata) :
    nonNull pointer = none ↔ pointer.address = 0 := by
  simp [nonNull]

/-- The successful guard returns the exact pointer, including opaque provenance. -/
theorem nonNull_eq_some_iff (pointer : Value Provenance Metadata)
    (result : NonNull Provenance Metadata) :
    nonNull pointer = some result ↔ result.val = pointer := by
  by_cases h : pointer.address = 0
  · simp [nonNull, h]
    intro eq
    exact result.property ((congrArg Value.address eq).trans h)
  · simp only [nonNull, h, ↓reduceDIte, Option.some.injEq]
    constructor
    · intro eq
      exact (congrArg Subtype.val eq).symm
    · intro eq
      exact Subtype.ext eq.symm

@[simp] theorem equal_refl (pointer : Value Provenance Metadata) : equal pointer pointer :=
  ⟨rfl, rfl⟩

/-- Equal Rust pointer values may have different provenance. No equality test
or decision procedure for the opaque provenance parameter is required. -/
theorem equal_ignores_provenance (address : Nat) (m : Metadata)
    (left right : Option Provenance) :
    equal (⟨address, left, m⟩ : Value Provenance Metadata) ⟨address, right, m⟩ :=
  ⟨rfl, rfl⟩

end Rust.Pointer
