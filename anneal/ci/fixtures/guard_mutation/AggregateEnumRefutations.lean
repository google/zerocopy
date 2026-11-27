-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import GuardRefuteBase
import PositiveSanity

/-!
# Refutations for `Rvalue.aggregateEnum` in `Trusted/MirSemantics/Step.lean`

Each theorem pins one check of `evalRvalueV2`'s `.aggregateEnum` arm or of
`evalAggregateEnum`: the destination-type check, the variant-index bound, the
`enumAdmitted` check, and the `Ordering` declaration-index mapping and bound.
The anti-overreach positive canary `positive_sanity_v2_aggregate_enum` lives
in `PositiveSanity.lean`, which the runner compiles on every mutant before
this module.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Two-variant enum whose discriminants collide, so `enumAdmitted` rejects
it. -/
noncomputable def collidingEnumTy : EnumTy :=
  { reprU8EnumTy with discriminants := [10, 10] }

/-- Guard `step_v2_aggregate_enum_dst_type`: an `Ordering` aggregate assigned
to a `reprU8EnumTy` destination faults with `.unsupported`. -/
theorem refute_step_v2_aggregate_enum_dst_type :
    evalRvalueV2 [] [] MemoryState.empty (.enum reprU8EnumTy)
      (.aggregateEnum .ordering 0) = .error .unsupported :=
  rfl

/-- Guard `step_v2_aggregate_enum_variant_range`: variant index `2` of the
two-variant `reprU8EnumTy` faults with `.unsupported`. -/
theorem refute_step_v2_aggregate_enum_variant_range :
    evalRvalueV2 [] [] MemoryState.empty (.enum reprU8EnumTy)
      (.aggregateEnum (.enum reprU8EnumTy) 2) = .error .unsupported :=
  rfl

/-- Guard `step_v2_aggregate_enum_admitted`: a variant of the unadmitted
`collidingEnumTy` faults with `.unsupported`. -/
theorem refute_step_v2_aggregate_enum_admitted :
    evalRvalueV2 [] [] MemoryState.empty (.enum collidingEnumTy)
      (.aggregateEnum (.enum collidingEnumTy) 0) = .error .unsupported :=
  rfl

/-- Guard `step_v2_aggregate_enum_ordering_order`: `Ordering` declaration
index `0` is `Less`. -/
theorem refute_step_v2_aggregate_enum_ordering_order :
    evalRvalueV2 [] [] MemoryState.empty .ordering
      (.aggregateEnum .ordering 0) =
      .ok (.ordering .less, [], MemoryState.empty) :=
  rfl

/-- Guard `step_v2_aggregate_enum_ordering_range`: `Ordering` declaration
index `3` faults with `.unsupported`. -/
theorem refute_step_v2_aggregate_enum_ordering_range :
    evalRvalueV2 [] [] MemoryState.empty .ordering
      (.aggregateEnum .ordering 3) =
      .error .unsupported :=
  rfl

end GuardMutation
