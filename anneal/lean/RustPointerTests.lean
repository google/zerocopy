/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Rust.Pointer
import Rust.Pointer.GeometryTests

open Rust.Pointer

-- The laws quantify over an opaque provenance type, with no equality instance.
example {P : Type} (p : Value P Nat) : (cast p).provenance = p.provenance := rfl
example {P : Type} (p : Thin P) (count : Nat) :
    dataPointer (withMetadata p count) = p := dataPointer_withMetadata p count
example {P : Type} (p : Value P Nat) :
    withMetadata (dataPointer p) (metadata p) = p := withMetadata_dataPointer p

-- Count zero and unbounded mathematical counts are valid raw value inputs.
example : metadata (withMetadata (⟨0, none, ()⟩ : Thin Nat) 0) = 0 := rfl
example : metadata (withMetadata (⟨1, some 7, ()⟩ : Thin Nat) (2^128)) = 2^128 := rfl

-- Provenance presence, non-nullness, and pointer equality are independent.
example : hasProvenance (⟨0, some 7, ()⟩ : Thin Nat) := rfl
example : nonNull (⟨0, some 7, ()⟩ : Thin Nat) = none := by
  exact (nonNull_eq_none_iff _).mpr rfl
example : ∃ result, nonNull (⟨1, none, ()⟩ : Thin Nat) = some result := by
  exact ⟨⟨⟨1, none, ()⟩, by decide⟩, rfl⟩
example : equal (⟨42, some 1, 3⟩ : Slice Nat) ⟨42, some 2, 3⟩ :=
  equal_ignores_provenance _ _ _ _
example : ¬ equal (⟨42, some 1, 3⟩ : Slice Nat) ⟨42, some 1, 4⟩ := by
  decide
example : ¬ equal (⟨42, some 1, 3⟩ : Slice Nat) ⟨43, some 1, 3⟩ := by
  decide

example {P M : Type} (p : Value P M) (r : NonNull P M)
    (success : nonNull p = some r) : r.val.provenance = p.provenance := by
  rw [(nonNull_eq_some_iff p r).mp success]
