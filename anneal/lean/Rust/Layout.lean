/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Std.Tactic

/-!
This module describes object sizes and alignments using unbounded natural
numbers. Sharing the arithmetic lets frontends reuse the same proofs while
keeping their machine-word limits and Rust layout assumptions explicit.

The proof fields below constrain mathematical values: for example, constructing
a `Layout` requires proving that its size is a multiple of its alignment. They
do not prove that these values describe a particular Rust type. A consumer must
establish that connection separately before using the geometry for that type.
-/

namespace Rust

/--
The numerical condition on a Rust alignment: positive and a power of two.
There is no upper bound here; a frontend supplies the limits of its target.
-/
def IsAlignment (n : Nat) : Prop :=
  0 < n ∧ ∃ (k : Nat), n = 2^k

@[simp] theorem alignment_one : IsAlignment 1 := ⟨by decide, 0, by rfl⟩

/--
The size and alignment of a complete object, including its final padding.
Requiring `align ∣ size` means placing another object immediately after this one
preserves alignment. Size zero is allowed, as it is for Rust's zero-sized types.
-/
structure Layout where
  size : Nat
  align : Nat
  isAlignment : IsAlignment align
  sizeAligned : align ∣ size

/--
Rounds a byte count up to the nearest multiple of a positive alignment.

The formula is total even for zero alignment: Lean's natural-number division by
zero returns zero, so this definition does too. That case is useful for testing
the formula's exact behavior, but is not a valid Rust alignment. The theorems
about rounding upward therefore require `0 < align` explicitly.
-/
abbrev roundUpToAlign (val align : Nat) : Nat :=
  ((val + align - 1) / align) * align

/-- Rounding to a positive alignment never makes an object smaller. -/
theorem roundUpToAlign_ge (val align : Nat) (h : 0 < align) :
  val ≤ roundUpToAlign val align := by
  dsimp [roundUpToAlign]
  -- Division with remainder expresses the rounded multiple in terms of the
  -- original count. Since the remainder is less than `align`, the preceding
  -- addition of `align - 1` prevents the multiple from falling below `val`.
  have h1 : ((val + align - 1) / align) * align + (val + align - 1) % align = val + align - 1 := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod _ _
  have h2 : (val + align - 1) % align < align := Nat.mod_lt _ h
  omega

/-- A positive byte count rounds to at least one full alignment unit. -/
theorem align_le_roundUpToAlign (val align : Nat) (h_val : 0 < val) (h_align : 0 < align) :
  align ≤ roundUpToAlign val align := by
  dsimp [roundUpToAlign]
  -- Show that the quotient is at least one before multiplying by alignment.
  have h_val_align : align ≤ val + align - 1 := by omega
  have h_div_pos : 1 ≤ (val + align - 1) / align := Nat.div_pos h_val_align h_align
  have h_mul : 1 * align ≤ ((val + align - 1) / align) * align := Nat.mul_le_mul_right align h_div_pos
  omega

/--
The rounded size is a multiple of the supplied alignment. This algebraic fact
also holds at alignment zero, where the rounded size is zero; it does not make
zero a valid alignment.
-/
theorem roundUpToAlign_aligned (val align : Nat) : align ∣ roundUpToAlign val align :=
  ⟨_, Nat.mul_comm _ _⟩

/--
The static data needed to size an object ending in a dynamically sized slice.
`trailingOffset` is the start of the slice payload, `elementSize` is its stride,
and `align` is the alignment of the containing object. A zero stride is allowed.
The frontend must establish these values from the actual Rust layout.
-/
structure SliceDstLayout where
  trailingOffset : Nat
  elementSize : Nat
  align : Nat
  isAlignment : IsAlignment align

/--
Adds the slice payload to its starting offset, then pads the complete object.
The count is unbounded and the calculation cannot overflow. A machine-level
sizing operation needs a separate proof of its checked or wrapping behavior.
-/
abbrev reprCSliceDstSize (info : SliceDstLayout) (elemCount : Nat) : Nat :=
  roundUpToAlign (info.trailingOffset + elemCount * info.elementSize) info.align

/-- Final padding gives an aligned complete size for every slice length. -/
theorem reprCSliceDstSize_aligned (info : SliceDstLayout) (elemCount : Nat) :
    info.align ∣ reprCSliceDstSize info elemCount :=
  roundUpToAlign_aligned _ _

end Rust
