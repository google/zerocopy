/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Rust.Pointer
import Std.Tactic

/-!
Numerical byte-range relations between raw pointer values. Source and destination
metadata may have different types or values. The caller supplies their byte
extents separately; an extent is not a slice element count. Connecting an extent
to a Rust type's metadata and layout remains the consumer's obligation.

`Projection` places the destination's entire byte interval within the source's
interval and preserves the exact optional provenance. Empty destinations still
have a bounded start, including the source's one-past endpoint. `Cast` adds an
equal start address; `CastExact` also requires equal byte extents. These are
predicates on modeled values, not implementations of Rust operations. An
arbitrary Rust raw pointer cast need not satisfy these additional extent bounds.

Addresses and extents are unbounded naturals. Word-size conclusions below require
explicit bounds, including representability of an empty destination's start.
None of these relations establishes allocation, permissions, alignment,
initialization, referent validity, liveness, or a right to dereference. The
resource-free carrier and its consumer correspondence obligations are described
in `Rust.Pointer`; no Rust execution semantics or axioms are added here.
-/

namespace Rust.Pointer

/-- A forward subrange with the same opaque provenance, including its absence. -/
def Projection (source : Value Provenance SourceMetadata)
    (destination : Value Provenance DestinationMetadata)
    (sourceExtent destinationExtent : Nat) : Prop :=
  ∃ offset : Nat,
    destination.address = source.address + offset ∧
    offset + destinationExtent ≤ sourceExtent ∧
    PreservesProvenance source destination

/-- A projection that retains the start address, while metadata may change. -/
def Cast (source : Value Provenance SourceMetadata)
    (destination : Value Provenance DestinationMetadata)
    (sourceExtent destinationExtent : Nat) : Prop :=
  Projection source destination sourceExtent destinationExtent ∧
    destination.address = source.address

/-- A cast that also retains the byte extent, independently of metadata equality. -/
def CastExact (source : Value Provenance SourceMetadata)
    (destination : Value Provenance DestinationMetadata)
    (sourceExtent destinationExtent : Nat) : Prop :=
  Cast source destination sourceExtent destinationExtent ∧
    destinationExtent = sourceExtent

variable {p : Value P M} {q : Value P N} {r : Value P O}
  {sourceExtent middleExtent destinationExtent : Nat}

theorem projection_refl (p : Value P M) (extent : Nat) :
    Projection p p extent extent :=
  ⟨0, by simp, by simp, rfl⟩

/-- Both premises use the same intermediate pointer, including its exact metadata,
and the same intermediate byte extent. -/
theorem projection_trans
    (first : Projection p q sourceExtent middleExtent)
    (second : Projection q r middleExtent destinationExtent) :
    Projection p r sourceExtent destinationExtent := by
  obtain ⟨a, ha, hba, hpa⟩ := first
  obtain ⟨b, hb, hbb, hpb⟩ := second
  refine ⟨a + b, by omega, by omega, ?_⟩
  exact hpb.trans hpa

theorem projection_preservesProvenance
    (h : Projection p q sourceExtent destinationExtent) :
    PreservesProvenance p q := by
  obtain ⟨_, _, _, provenance⟩ := h
  exact provenance

/-- The exact token is preserved without requiring decidable provenance equality. -/
theorem projection_carries
    (h : Projection p q sourceExtent destinationExtent) (token : P)
    (carried : Carries p token) : Carries q token :=
  (projection_preservesProvenance h).trans carried

theorem projection_hasProvenance
    (h : Projection p q sourceExtent destinationExtent) :
    hasProvenance q ↔ hasProvenance p := by
  unfold hasProvenance
  rw [projection_preservesProvenance h]

theorem projection_address_le
    (h : Projection p q sourceExtent destinationExtent) :
    p.address ≤ q.address := by
  obtain ⟨offset, address, _, _⟩ := h
  omega

theorem projection_extent_le
    (h : Projection p q sourceExtent destinationExtent) :
    destinationExtent ≤ sourceExtent := by
  obtain ⟨offset, _, bound, _⟩ := h
  omega

theorem projection_end_le
    (h : Projection p q sourceExtent destinationExtent) :
    q.address + destinationExtent ≤ p.address + sourceExtent := by
  obtain ⟨offset, address, bound, _⟩ := h
  omega

/-- This endpoint characterization includes empty intervals; byte-set inclusion
alone would not bound the start of an empty destination. -/
theorem projection_iff_bounds :
    Projection p q sourceExtent destinationExtent ↔
      p.address ≤ q.address ∧
      q.address + destinationExtent ≤ p.address + sourceExtent ∧
      PreservesProvenance p q := by
  constructor
  · intro h
    exact ⟨projection_address_le h, projection_end_le h,
      projection_preservesProvenance h⟩
  · rintro ⟨start, finish, provenance⟩
    exact ⟨q.address - p.address, by omega, by omega, provenance⟩

theorem projection_empty_iff :
    Projection p q sourceExtent 0 ↔
      p.address ≤ q.address ∧ q.address ≤ p.address + sourceExtent ∧
      PreservesProvenance p q := by
  simpa using (projection_iff_bounds (p := p) (q := q)
    (sourceExtent := sourceExtent) (destinationExtent := 0))

/-- Every byte in the destination's half-open interval lies in the source's. -/
theorem projection_byte_bounds
    (h : Projection p q sourceExtent destinationExtent) (address : Nat)
    (inside : q.address ≤ address ∧ address < q.address + destinationExtent) :
    p.address ≤ address ∧ address < p.address + sourceExtent := by
  have := projection_address_le h
  have := projection_end_le h
  omega

theorem projection_start_lt_end
    (h : Projection p q sourceExtent destinationExtent)
    (nonempty : 0 < destinationExtent) :
    q.address < p.address + sourceExtent := by
  have := projection_end_le h
  omega

/-- Forward natural-number offsets preserve nonzero starts. -/
theorem projection_nonzero
    (h : Projection p q sourceExtent destinationExtent)
    (nonzero : p.address ≠ 0) : q.address ≠ 0 := by
  have := projection_address_le h
  omega

theorem projection_nonNull
    (h : Projection p q sourceExtent destinationExtent)
    (nonzero : p.address ≠ 0) : ∃ result, nonNull q = some result := by
  let result : NonNull P N := ⟨q, projection_nonzero h nonzero⟩
  exact ⟨result, (nonNull_eq_some_iff q result).mpr rfl⟩

/-- A source end at most the word limit bounds destination ends as naturals.
An empty destination at the limit still needs a strict representability check. -/
theorem projection_word_end_le
    (h : Projection p q sourceExtent destinationExtent) (wordBits : Nat)
    (sourceBound : p.address + sourceExtent ≤ 2 ^ wordBits) :
    q.address + destinationExtent ≤ 2 ^ wordBits :=
  Nat.le_trans (projection_end_le h) sourceBound

/-- A representable source end makes both destination endpoints representable,
including the start of an empty destination at the source's one-past endpoint. -/
theorem projection_word_bounds
    (h : Projection p q sourceExtent destinationExtent) (wordBits : Nat)
    (sourceBound : p.address + sourceExtent < 2 ^ wordBits) :
    q.address < 2 ^ wordBits ∧ q.address + destinationExtent < 2 ^ wordBits := by
  have := projection_end_le h
  omega

/-- With the strict source-end premise, reducing either destination endpoint
modulo the target word modulus does not wrap it. -/
theorem projection_word_noWrap
    (h : Projection p q sourceExtent destinationExtent) (wordBits : Nat)
    (sourceBound : p.address + sourceExtent < 2 ^ wordBits) :
    q.address % (2 ^ wordBits) = q.address ∧
      (q.address + destinationExtent) % (2 ^ wordBits) =
        q.address + destinationExtent := by
  have bounds := projection_word_bounds h wordBits sourceBound
  exact ⟨Nat.mod_eq_of_lt bounds.1, Nat.mod_eq_of_lt bounds.2⟩

/-- The projection's actual offset addition also agrees with word reduction. -/
theorem projection_offset_noWrap
    (h : Projection p q sourceExtent destinationExtent) (wordBits : Nat)
    (sourceBound : p.address + sourceExtent < 2 ^ wordBits) :
    ∃ offset : Nat, offset + destinationExtent ≤ sourceExtent ∧
      p.address + offset = q.address ∧
      (p.address + offset) % (2 ^ wordBits) = q.address := by
  have noWrap := (projection_word_noWrap h wordBits sourceBound).1
  obtain ⟨offset, address, bound, _⟩ := h
  exact ⟨offset, bound, address.symm, by simpa only [← address] using noWrap⟩

theorem cast_refl (p : Value P M) (extent : Nat) : Cast p p extent extent :=
  ⟨projection_refl p extent, rfl⟩

theorem cast_trans
    (first : Cast p q sourceExtent middleExtent)
    (second : Cast q r middleExtent destinationExtent) :
    Cast p r sourceExtent destinationExtent :=
  ⟨projection_trans first.1 second.1, second.2.trans first.2⟩

/-- Equal starts reduce containment to an extent comparison and provenance. -/
theorem cast_iff :
    Cast p q sourceExtent destinationExtent ↔
      q.address = p.address ∧ destinationExtent ≤ sourceExtent ∧
      PreservesProvenance p q := by
  constructor
  · intro h
    exact ⟨h.2, projection_extent_le h.1, projection_preservesProvenance h.1⟩
  · rintro ⟨address, bound, provenance⟩
    exact ⟨⟨0, by simpa using address, by simpa using bound, provenance⟩, address⟩

theorem castExact_refl (p : Value P M) (extent : Nat) : CastExact p p extent extent :=
  ⟨cast_refl p extent, rfl⟩

theorem castExact_trans
    (first : CastExact p q sourceExtent middleExtent)
    (second : CastExact q r middleExtent destinationExtent) :
    CastExact p r sourceExtent destinationExtent :=
  ⟨cast_trans first.1 second.1, second.2.trans first.2⟩

theorem castExact_iff :
    CastExact p q sourceExtent destinationExtent ↔
      q.address = p.address ∧ destinationExtent = sourceExtent ∧
      PreservesProvenance p q := by
  constructor
  · intro h
    exact ⟨h.1.2, h.2, projection_preservesProvenance h.1.1⟩
  · rintro ⟨address, extent, provenance⟩
    exact ⟨cast_iff.mpr ⟨address, by omega, provenance⟩, extent⟩

/-- Reinterpreting a pointer preserves its numeric geometry when the requested
extent fits. This is a value theorem, not an interpretation of native casts. -/
theorem cast_shrink (pointer : Value P M) (sourceExtent destinationExtent : Nat)
    (fits : destinationExtent ≤ sourceExtent) :
    Cast pointer (cast pointer) sourceExtent destinationExtent :=
  cast_iff.mpr ⟨rfl, fits, rfl⟩

/-- Forgetting metadata can describe a zero-byte destination at the same start. -/
theorem cast_to_unit (pointer : Value P M) (sourceExtent : Nat) :
    Cast pointer (dataPointer pointer) sourceExtent 0 :=
  cast_iff.mpr ⟨rfl, Nat.zero_le _, rfl⟩

/-- Metadata assembly keeps the address and provenance; containment still needs
an explicit comparison of the actual source and destination extents. -/
theorem withMetadata_cast (pointer : Thin P) (metadata : M)
    (sourceExtent destinationExtent : Nat) (fits : destinationExtent ≤ sourceExtent) :
    Cast pointer (withMetadata pointer metadata) sourceExtent destinationExtent :=
  cast_iff.mpr ⟨rfl, fits, rfl⟩

/-- A byte-slice view uses a byte count. A bare slice-pointer cast would retain
an element count instead. Native usize representability is a separate premise. -/
theorem slice_as_bytes (pointer : Slice P) (stride : Nat) :
    CastExact pointer (withMetadata (dataPointer pointer) (pointer.metadata * stride))
      (pointer.metadata * stride) (pointer.metadata * stride) :=
  castExact_iff.mpr ⟨rfl, rfl, rfl⟩

/-- The two numeric subregions meet at exactly the split count, even when every
element occupies zero bytes. This theorem constructs no Rust pointer and needs
no access permission; native pointer arithmetic needs its own interpretation. -/
theorem slice_split (pointer : Slice P) (stride count : Nat)
    (within : count ≤ pointer.metadata) :
    Projection pointer (withMetadata (dataPointer pointer) count)
      (pointer.metadata * stride) (count * stride) ∧
    Projection pointer
      (⟨pointer.address + count * stride, pointer.provenance,
        pointer.metadata - count⟩ : Slice P)
      (pointer.metadata * stride) ((pointer.metadata - count) * stride) := by
  constructor
  · exact ⟨0, by simp [withMetadata, dataPointer], by
      simpa using Nat.mul_le_mul_right stride within, rfl⟩
  · refine ⟨count * stride, rfl, ?_, rfl⟩
    have sum : count + (pointer.metadata - count) = pointer.metadata := by omega
    rw [← Nat.add_mul, sum]
    exact Nat.le_refl _

end Rust.Pointer
