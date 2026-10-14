/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Std.Tactic

/-!
An allocation and a pointer's referent have different byte footprints. An
allocation bounds the available storage; a referent describes the bytes of the
object a pointer addresses. This module relates those footprints numerically.

Addresses and sizes are unbounded `Nat` values. The structures do not establish
that storage exists, remains alive, is initialized, or may be accessed through a
particular pointer. Frontends retain those obligations, together with target
address limits and provenance. Here, an address set is a predicate `Nat → Prop`,
so the geometry needs neither a particular set representation nor a frontend.
-/

namespace Rust

/--
An allocation's base, byte size, and admitted byte addresses. Every member of
`addresses` must lie in the half-open interval `[base, base + size)`. The reverse
inclusion is not required: the predicate may describe only part of that range.
-/
structure Allocation where
  base : Nat
  size : Nat
  addresses : Nat → Prop
  bounds : ∀ a, addresses a → base ≤ a ∧ a < base + size

namespace Allocation

/-- An admitted byte's offset is strictly inside the allocation's size. -/
theorem offset_lt_size (alloc : Allocation) (a : Nat) (ha : alloc.addresses a) :
    a - alloc.base < alloc.size := by
  have := alloc.bounds a ha
  omega

/--
An admitted address is not below the base. Natural-number subtraction truncates
at zero; this premise ensures subtracting the base really describes an offset.
-/
theorem offset_non_negative (alloc : Allocation) (a : Nat) (ha : alloc.addresses a) :
    alloc.base ≤ a := (alloc.bounds a ha).left

/-- The allocation's end address is excluded from its admitted bytes. -/
theorem address_lt_end (alloc : Allocation) (a : Nat) (ha : alloc.addresses a) :
    a < alloc.base + alloc.size := (alloc.bounds a ha).right

end Allocation

/--
The starting address, size, and byte footprint of an object addressed by a
pointer. Like `Allocation`, this bounds members of the footprint without
requiring every address in the range to be a member. A zero-sized referent has
no member addresses, but still has a starting address.
-/
structure Referent where
  address : Nat
  size : Nat
  addresses : Nat → Prop
  bounds : ∀ a, addresses a → address ≤ a ∧ a < address + size

/--
Requires the referent's footprint to fill its entire half-open byte interval.
Together with `Referent.bounds`, this makes the predicate exactly that interval.
-/
abbrev Referent.IsContiguous (r : Referent) : Prop :=
  ∀ a, r.address ≤ a ∧ a < r.address + r.size → r.addresses a

/--
Every referent byte belongs to the allocation, and the referent's endpoints fit
within the allocation's endpoints. These are separate requirements: inclusion
alone says nothing about the start of an empty footprint. The endpoint checks
allow a zero-sized referent at the allocation's end, without admitting a byte
there. This is a geometric condition, not permission to dereference a pointer.
-/
abbrev FitsInAllocation (r : Referent) (a : Allocation) : Prop :=
  (∀ ⦃addr⦄, r.addresses addr → a.addresses addr) ∧
  a.base ≤ r.address ∧ r.address + r.size ≤ a.base + a.size

/--
Footprint inclusion transfers the allocation's upper bound to each referent
byte. Consumers can reuse this fact without unfolding the allocation record.
-/
theorem FitsInAllocation.address_bounds_alloc (r : Referent) (a : Allocation)
    (h : FitsInAllocation r a) (addr : Nat) (ha : r.addresses addr) :
    addr < a.base + a.size :=
  a.address_lt_end addr (h.left ha)

end Rust
