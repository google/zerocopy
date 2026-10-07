/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Std.Tactic

namespace Rust

/-- A nonzero power of two, independently of any machine word width. -/
def IsAlignment (n : Nat) : Prop :=
  0 < n ∧ ∃ (k : Nat), n = 2^k

@[simp] theorem alignment_one : IsAlignment 1 := ⟨by decide, 0, by rfl⟩

/-- An unbounded mathematical layout. This alone makes no compiler correspondence claim. -/
structure Layout where
  size : Nat
  align : Nat
  isAlignment : IsAlignment align
  sizeAligned : align ∣ size

/-- Rounds `val` up to the nearest multiple of `align`. -/
abbrev roundUpToAlign (val align : Nat) : Nat :=
  ((val + align - 1) / align) * align

/-- A theorem stating that rounding up always produces a value greater than or equal to the original value. -/
theorem roundUpToAlign_ge (val align : Nat) (h : 0 < align) :
  val ≤ roundUpToAlign val align := by
  dsimp [roundUpToAlign]
  have h1 : ((val + align - 1) / align) * align + (val + align - 1) % align = val + align - 1 := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod _ _
  have h2 : (val + align - 1) % align < align := Nat.mod_lt _ h
  omega

/-- A theorem stating that if the resulting padded value is non-zero, it must be at least the alignment. -/
theorem align_le_roundUpToAlign (val align : Nat) (h_val : 0 < val) (h_align : 0 < align) :
  align ≤ roundUpToAlign val align := by
  dsimp [roundUpToAlign]
  have h_val_align : align ≤ val + align - 1 := by omega
  have h_div_pos : 1 ≤ (val + align - 1) / align := Nat.div_pos h_val_align h_align
  have h_mul : 1 * align ≤ ((val + align - 1) / align) * align := Nat.mul_le_mul_right align h_div_pos
  omega

/-- Rounding produces a multiple even when the alignment is zero. -/
theorem roundUpToAlign_aligned (val align : Nat) : align ∣ roundUpToAlign val align :=
  ⟨_, Nat.mul_comm _ _⟩

/-- Static geometry of a type ending in a dynamically sized slice. -/
structure SliceDstLayout where
  trailingOffset : Nat
  elementSize : Nat
  align : Nat
  isAlignment : IsAlignment align

abbrev reprCSliceDstSize (info : SliceDstLayout) (elemCount : Nat) : Nat :=
  roundUpToAlign (info.trailingOffset + elemCount * info.elementSize) info.align

theorem reprCSliceDstSize_aligned (info : SliceDstLayout) (elemCount : Nat) :
    info.align ∣ reprCSliceDstSize info elemCount :=
  roundUpToAlign_aligned _ _

end Rust
