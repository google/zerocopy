/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Std.Tactic

namespace Rust

/-- Allocation geometry; machine bounds and Rust provenance are separate obligations.
Addresses are an arbitrary predicate, so contiguity is not assumed. -/
structure Allocation where
  base : Nat
  size : Nat
  addresses : Nat → Prop
  bounds : ∀ a, addresses a → base ≤ a ∧ a < base + size

namespace Allocation

theorem offset_lt_size (alloc : Allocation) (a : Nat) (ha : alloc.addresses a) :
    a - alloc.base < alloc.size := by
  have := alloc.bounds a ha
  omega

theorem offset_non_negative (alloc : Allocation) (a : Nat) (ha : alloc.addresses a) :
    alloc.base ≤ a := (alloc.bounds a ha).left

theorem address_lt_end (alloc : Allocation) (a : Nat) (ha : alloc.addresses a) :
    a < alloc.base + alloc.size := (alloc.bounds a ha).right

end Allocation

/-- Geometry of the bytes addressed by a pointer, independent of its frontend encoding. -/
structure Referent where
  address : Nat
  size : Nat
  addresses : Nat → Prop
  bounds : ∀ a, addresses a → address ≤ a ∧ a < address + size

abbrev Referent.IsContiguous (r : Referent) : Prop :=
  ∀ a, r.address ≤ a ∧ a < r.address + r.size → r.addresses a

abbrev FitsInAllocation (r : Referent) (a : Allocation) : Prop :=
  (∀ ⦃addr⦄, r.addresses addr → a.addresses addr) ∧
  a.base ≤ r.address ∧ r.address + r.size ≤ a.base + a.size

theorem FitsInAllocation.address_bounds_alloc (r : Referent) (a : Allocation)
    (h : FitsInAllocation r a) (addr : Nat) (ha : r.addresses addr) :
    addr < a.base + a.size :=
  a.address_lt_end addr (h.left ha)

end Rust
