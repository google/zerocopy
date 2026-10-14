/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Rust
import Aeneas.Std.Core
import Aeneas.Tactic.Solver.ScalarTac

open Aeneas.Std
namespace Rust.Machine

/-- An Aeneas `Usize` carrier validated as a Rust alignment. -/
structure Alignment where
  val : Usize
  isValid : IsAlignment val.val


@[simp] theorem Alignment_val {val} {h} : (@Alignment.mk val h).val = val := rfl
@[simp] theorem Alignment_isValid (a : Alignment) : Rust.IsAlignment a.val.val := a.isValid
instance : Inhabited Alignment := ⟨⟨Usize.ofNatCore 1 (by scalar_tac), Rust.alignment_one⟩⟩

structure SpecLayout where
  size : Nat
  align : Alignment
  sizeAligned : align.val.val ∣ size

/-- Forget the frontend's machine-bounded alignment representation. -/
abbrev SpecLayout.toGeometry (lay : SpecLayout) : Rust.Layout :=
  ⟨lay.size, lay.align.val.val, lay.align.isValid, lay.sizeAligned⟩

/--
  A numerical layout with machine-bounded size and alignment.

  Its size is represented by `Usize` and its alignment satisfies the Rust
  alignment predicate. These bounds do not establish that an allocation exists,
  is live, or has valid pointer provenance.
-/
structure Layout where
  size : Usize
  align : Alignment
  sizeAligned : align.val.val ∣ size.val

/--
  A proof that a mathematical layout's size fits within `Usize.max`.

  This numerical bound permits a `Usize` representation; it does not establish
  allocation existence, liveness, or pointer provenance.
-/
class FitsInUsize (lay : SpecLayout) : Prop where
  fits : lay.size ≤ Usize.max

/--
  Converts a mathematical layout to a machine-bounded numerical layout.

  The required proof bounds the size by `Usize.max`.
-/
@[simp]
def SpecLayout.toLayout (lay : SpecLayout) [FitsInUsize lay] : Layout :=
  {
    size := Usize.ofNatCore lay.size (by
      have := FitsInUsize.fits (lay := lay)
      scalar_tac),
    align := lay.align,
    sizeAligned := lay.sizeAligned
  }

/--
  Converts a machine-bounded numerical layout to its mathematical layout.

  The `Usize` carrier supplies the bound needed to prove that the resulting
  `SpecLayout` also fits in `Usize`.
-/
@[simp]
def Layout.toSpecLayout (lay : Layout) : SpecLayout :=
  { size := lay.size.val, align := lay.align, sizeAligned := lay.sizeAligned }

instance (lay : Layout) : FitsInUsize lay.toSpecLayout where
  fits := by
    dsimp [Layout.toSpecLayout]
    scalar_tac

structure SpecSliceDstLayout where
  trailingOffset : Nat
  elementSize : Nat
  align : Alignment

abbrev SpecSliceDstLayout.toGeometry (info : SpecSliceDstLayout) : Rust.SliceDstLayout :=
  ⟨info.trailingOffset, info.elementSize, info.align.val.val, info.align.isValid⟩

structure Allocation where
  base : Usize
  size : Usize
  addresses : Set Nat

  -- `base` is not equal to null (address 0)
  base_not_null : base.val ≠ 0

  -- `size <= isize::MAX`
  size_le_isize_max : size.val ≤ Isize.max

  -- `base + size <= usize::MAX`
  base_add_size_le_usize_max : base.val + size.val ≤ Usize.max

  -- For all addresses `a` in `addresses`, `a` is in the range `base .. (base + size)`
  bounds : ∀ a ∈ addresses, base.val ≤ a ∧ a < base.val + size.val

/-- Forget the frontend's machine bounds, retaining the shared allocation geometry. -/
abbrev Allocation.toGeometry (a : Allocation) : Rust.Allocation :=
  ⟨a.base.val, a.size.val, fun addr => addr ∈ a.addresses, a.bounds⟩

namespace Allocation

-- Consequence 1: `a - base` does not overflow `isize`
theorem offset_le_isize_max (alloc : Allocation) (a : Nat) (ha : a ∈ alloc.addresses) :
    a - alloc.base.val ≤ Isize.max := by
  have h_sub := Rust.Allocation.offset_lt_size alloc.toGeometry a ha
  change a - alloc.base.val < alloc.size.val at h_sub
  have h_size : alloc.size.val ≤ Isize.max := alloc.size_le_isize_max
  omega

-- Consequence 2: `a - base` is non-negative
-- (This is trivially true in Lean for `Nat` subtraction when `alloc.base ≤ a`,
-- which we prove here to show the offset is well-defined mathematically).
theorem offset_non_negative (alloc : Allocation) (a : Nat) (ha : a ∈ alloc.addresses) :
    alloc.base.val ≤ a :=
  Rust.Allocation.offset_non_negative alloc.toGeometry a ha

-- Consequence 3: `base + o` will not wrap around the address space (overflow `usize`)
-- `o = a - base`, so `base + o` is just `a` if `base <= a` (which we proved above).
theorem address_le_usize_max (alloc : Allocation) (a : Nat) (ha : a ∈ alloc.addresses) :
    a ≤ Usize.max := by
  have h_lt := Rust.Allocation.address_lt_end alloc.toGeometry a ha
  change a < alloc.base.val + alloc.size.val at h_lt
  have h_max : alloc.base.val + alloc.size.val ≤ Usize.max := alloc.base_add_size_le_usize_max
  omega

end Allocation

structure Referent where
  -- The start address of the referent
  address : Usize
  -- The size of the referent in bytes
  size : Usize
  -- The mathematical set of addresses that make up the referent
  addresses : Set Nat

  bounds : ∀ a ∈ addresses, address.val ≤ a ∧ a < address.val + size.val

  addresses_are_usizes : ∀ a ∈ addresses, a ≤ Usize.max

instance : Nonempty Referent :=
  ⟨{ address := Usize.ofNatCore 0 (by scalar_tac), size := Usize.ofNatCore 0 (by scalar_tac), addresses := ∅,
     bounds := by
       intro a h
       simp at h,
     addresses_are_usizes := by
       intro a h
       simp at h }⟩

/-- Forget the frontend's machine bounds, retaining the shared referent geometry. -/
abbrev Referent.toGeometry (r : Referent) : Rust.Referent :=
  ⟨r.address.val, r.size.val, fun addr => addr ∈ r.addresses, r.bounds⟩

/--
  A predicate indicating that a referent's set of addresses fills the contiguous
  range `[address, address + size)`. This means every address in that range
  belongs to the referent's addresses.
-/
def Referent.IsContiguous (r : Referent) : Prop :=
  Rust.Referent.IsContiguous r.toGeometry

/--
  A predicate indicating that a referent fits entirely within a given allocation.
  This means that all logical addresses of the referent are addresses allocated
  in the allocation, and the contiguous address range of the referent is
  a sub-range of the contiguous address range of the allocation.
-/
def FitsInAllocation (r : Referent) (a : Allocation) : Prop :=
  Rust.FitsInAllocation r.toGeometry a.toGeometry

/--
  A helper theorem proving that any address belonging to a referent that
  fits in an allocation is strictly less than the allocation's upper bound.
-/
theorem FitsInAllocation.address_bounds_alloc (r : Referent) (a : Allocation) (h : FitsInAllocation r a) (addr : Nat) (ha : addr ∈ r.addresses) :
  addr < a.base.val + a.size.val := by
  exact Rust.FitsInAllocation.address_bounds_alloc r.toGeometry a.toGeometry h addr ha


end Rust.Machine
