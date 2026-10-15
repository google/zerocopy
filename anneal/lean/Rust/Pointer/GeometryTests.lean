/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Rust.Pointer.Geometry

/-!
Boundary examples for the resource-free geometry. Byte extents are explicit,
including when slice counts differ. These are Lean theorems about the model;
they do not establish that an extracted Rust operation implements a relation.
`RustTests` imports these declarations through `RustPointerTests` and audits
all their transitive axioms with the shared library's allowlist.
-/

namespace Rust.Pointer.GeometryTests

-- No decidable equality instance is needed for the opaque provenance parameter.
theorem opaque_identity {P M : Type} (p : Value P M) (extent : Nat) :
    Projection p p extent extent ∧ Cast p p extent extent ∧
      CastExact p p extent extent :=
  ⟨projection_refl p extent, cast_refl p extent, castExact_refl p extent⟩

-- Composition uses the same exact middle value, with its metadata and extent.
theorem heterogeneous_composition {P M N O : Type}
    (p : Value P M) (q : Value P N) (r : Value P O) (a b c : Nat)
    (first : Projection p q a b) (second : Projection q r b c) :
    Projection p r a c := projection_trans first second

theorem cast_composition {P M N O : Type}
    (p : Value P M) (q : Value P N) (r : Value P O) (a b c : Nat)
    (first : Cast p q a b) (second : Cast q r b c) :
    Cast p r a c := cast_trans first second

theorem exact_cast_composition {P M N O : Type}
    (p : Value P M) (q : Value P N) (r : Value P O) (a b c : Nat)
    (first : CastExact p q a b) (second : CastExact q r b c) :
    CastExact p r a c := castExact_trans first second

theorem metadata_changing_projection_chain :
    Projection (⟨100, some 7, ()⟩ : Thin Nat)
      (⟨105, some 7, true⟩ : Value Nat Bool) 8 1 :=
  projection_trans (q := (⟨102, some 7, 2⟩ : Slice Nat)) (middleExtent := 4)
    ⟨2, rfl, by decide, rfl⟩ ⟨3, rfl, by decide, rfl⟩

theorem exact_token_preserved {P M N : Type}
    (p : Value P M) (q : Value P N) (a b : Nat) (token : P)
    (h : Projection p q a b) (carried : Carries p token) : Carries q token :=
  projection_carries h token carried

theorem nonNull_preserved {P M N : Type}
    (p : Value P M) (q : Value P N) (a b : Nat)
    (h : Projection p q a b) (nonzero : p.address ≠ 0) :
    ∃ result, nonNull q = some result := projection_nonNull h nonzero

-- An interior destination and one at the source's end are both bounded.
theorem empty_inside :
    Projection (⟨100, some 7, 4⟩ : Slice Nat) (⟨103, some 7, ()⟩ : Thin Nat) 8 0 :=
  ⟨3, rfl, by decide, rfl⟩

theorem empty_one_past :
    Projection (⟨100, some 7, 4⟩ : Slice Nat) (⟨108, some 7, ()⟩ : Thin Nat) 8 0 :=
  ⟨8, rfl, by decide, rfl⟩

theorem empty_before_source_rejected :
    ¬Projection (⟨100, some 7, ()⟩ : Thin Nat) ⟨99, some 7, ()⟩ 8 0 := by
  intro h
  have := projection_address_le h
  contradiction

theorem empty_beyond_source_rejected :
    ¬Projection (⟨100, some 7, ()⟩ : Thin Nat) ⟨109, some 7, ()⟩ 8 0 := by
  intro h
  have := projection_end_le h
  contradiction

theorem positive_at_one_past_rejected :
    ¬Projection (⟨100, some 7, ()⟩ : Thin Nat) ⟨108, some 7, ()⟩ 8 1 := by
  intro h
  have := projection_end_le h
  contradiction

-- An 8-bit wrapping addition from 250 to 2 is not a natural-number projection.
theorem wrapping_destination_rejected :
    (250 + 8) % (2 ^ 8) = 2 ∧
      ¬Projection (⟨250, some 7, ()⟩ : Thin Nat) ⟨2, some 7, ()⟩ 16 1 := by
  refine ⟨by decide, ?_⟩
  intro h
  have := projection_address_le h
  contradiction

theorem different_provenance_rejected :
    ¬Projection (⟨100, some 1, ()⟩ : Thin Nat) ⟨100, some 2, ()⟩ 8 8 := by
  intro h
  have impossible : (some 2 : Option Nat) = some 1 := projection_preservesProvenance h
  contradiction

-- Absence is preserved exactly; geometry does not require a provenance token.
theorem absent_provenance :
    CastExact (⟨100, none, ()⟩ : Thin Nat) (⟨100, none, 0⟩ : Slice Nat) 0 0 :=
  ⟨⟨⟨0, rfl, by decide, rfl⟩, rfl⟩, rfl⟩

-- The counts describe different element layouts: 3 two-byte elements and 6
-- one-byte elements have equal byte extent. Count equality is not a cast premise.
theorem different_counts_equal_extent :
    CastExact (⟨100, some 7, 3⟩ : Slice Nat) ⟨100, some 7, 6⟩ (3 * 2) (6 * 1) :=
  ⟨⟨⟨0, rfl, by decide, rfl⟩, rfl⟩, rfl⟩

-- Distinct zero-sized slice counts also retain their distinct metadata.
theorem zero_sized_counts :
    CastExact (⟨100, some 7, 3⟩ : Slice Nat) ⟨100, some 7, 9⟩ (3 * 0) (9 * 0) ∧
      ¬equal (⟨100, some 7, 3⟩ : Slice Nat) ⟨100, some 7, 9⟩ :=
  ⟨⟨⟨⟨0, rfl, by decide, rfl⟩, rfl⟩, rfl⟩, by decide⟩

theorem shifted_projection_is_not_cast :
    Projection (⟨100, some 7, ()⟩ : Thin Nat) ⟨102, some 7, ()⟩ 8 4 ∧
      ¬Cast (⟨100, some 7, ()⟩ : Thin Nat) ⟨102, some 7, ()⟩ 8 4 := by
  refine ⟨⟨2, rfl, by decide, rfl⟩, ?_⟩
  intro h
  have := h.2
  contradiction

theorem smaller_cast_is_not_exact :
    Cast (⟨100, some 7, 4⟩ : Slice Nat) ⟨100, some 7, 2⟩ 8 4 ∧
      ¬CastExact (⟨100, some 7, 4⟩ : Slice Nat) ⟨100, some 7, 2⟩ 8 4 := by
  refine ⟨⟨⟨0, rfl, by decide, rfl⟩, rfl⟩, ?_⟩
  intro h
  have := h.2
  contradiction

theorem larger_extent_rejected :
    ¬Projection (⟨100, some 7, 4⟩ : Slice Nat) ⟨100, some 7, 5⟩ 8 10 := by
  intro h
  have := projection_extent_le h
  contradiction

-- Merely identifying middle addresses cannot replace the exact middle pointer
-- and byte extent: these two slice metadata choices describe different ranges.
theorem intermediate_extent_is_necessary :
    Projection (⟨10, some 7, ()⟩ : Thin Nat) (⟨10, some 7, 0⟩ : Slice Nat) 1 0 ∧
    Projection (⟨10, some 7, 2⟩ : Slice Nat) (⟨11, some 7, ()⟩ : Thin Nat) 2 1 ∧
    ¬Projection (⟨10, some 7, ()⟩ : Thin Nat) ⟨11, some 7, ()⟩ 1 1 := by
  refine ⟨⟨0, rfl, by decide, rfl⟩, ⟨1, rfl, by decide, rfl⟩, ?_⟩
  intro h
  have := projection_end_le h
  contradiction

theorem bounded_noWrap :
    (108 : Nat) % (2 ^ 8) = 108 ∧ (108 + 0) % (2 ^ 8) = 108 + 0 :=
  projection_word_noWrap empty_one_past 8 (by decide)

-- A non-strict end bound allows an unrepresentable empty start at the modulus.
-- This is why the no-wrap theorem requires a strict bound even for zero extent.
theorem strict_word_bound_is_necessary :
    Projection (⟨250, some 7, ()⟩ : Thin Nat) ⟨256, some 7, ()⟩ 6 0 ∧
      250 + 6 ≤ 2 ^ 8 ∧ (256 : Nat) % (2 ^ 8) ≠ 256 :=
  ⟨⟨6, rfl, by decide, rfl⟩, by decide, by decide⟩

end Rust.Pointer.GeometryTests

-- These constructions describe the arithmetic used by familiar cast/project
-- operations without assigning native pointer execution semantics.
example (pointer : Rust.Pointer.Slice P) (stride : Nat) :
    Rust.Pointer.CastExact pointer
      (Rust.Pointer.withMetadata (Rust.Pointer.dataPointer pointer) (pointer.metadata * stride))
      (pointer.metadata * stride) (pointer.metadata * stride) :=
  Rust.Pointer.slice_as_bytes pointer stride

example (pointer : Rust.Pointer.Slice P) (count : Nat) (within : count ≤ pointer.metadata) :
    Rust.Pointer.Projection pointer
      (⟨pointer.address, pointer.provenance, count⟩ : Rust.Pointer.Slice P) 0 0 := by
  simpa [Rust.Pointer.withMetadata, Rust.Pointer.dataPointer] using
    (Rust.Pointer.slice_split pointer 0 count within).1

example (pointer : Rust.Pointer.Value P M) :
    Rust.Pointer.Cast pointer (Rust.Pointer.dataPointer pointer) 0 0 :=
  Rust.Pointer.cast_to_unit pointer 0
