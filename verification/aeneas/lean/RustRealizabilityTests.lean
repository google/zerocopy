/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RustRealizabilityModels
import all RustModel
import all ModelPrelude
import all Rust.Storage
@[expose] public section

open Aeneas.Std AeneasSpecs Rust.Storage
namespace RustRealizabilityTests

example (ty : UScalarTy) : RustModel.realizableRepresentation (UScalar ty) := realizableUScalar ty
example (ty : IScalarTy) : RustModel.realizableRepresentation (IScalar ty) := realizableIScalar ty
example : RustModel.realizableRepresentation Char := realizableChar
example : RustModel.realizableRepresentation Bool := realizableBool
example (ty : UScalarTy) (Inner : Type) :
    RustModel.realizableRepresentation (core.num.nonzero.NonZero (UScalar ty) Inner) :=
  realizableNonZeroUScalar ty Inner
example (ty : IScalarTy) (Inner : Type) :
    RustModel.realizableRepresentation (Option (core.num.nonzero.NonZero (IScalar ty) Inner)) :=
  realizableOptionNonZeroIScalar ty Inner
example : RustModel.realizableRepresentation
    (Aeneas.Std.Array (Aeneas.Std.Array Bool (2#usize)) (3#usize)) :=
  RustModel.realizable_array _ _ (RustModel.realizable_array _ _ realizableBool)
example : RustModel.realizableRepresentation (Aeneas.Std.Array Unit (4#usize)) :=
  RustModel.realizable_array _ _ realizableUnit
example (T : Type) : RustModel.realizableRepresentation
    (Aeneas.Std.Array (Zerocopy.core.marker.PhantomData T) (3#usize)) :=
  RustModel.realizable_array _ _ (realizablePhantomData T)

-- Source existence cannot be inferred from initialization alone: this
-- initialized decoder realizes false, while the provider also admits true.
@[reducible] def missingTrue : RustModel Bool where
  Model := Bool
  «decode» := some
  storage := some (.fixed (emptyDecoder false))

example : @RustModel.initializedRepresentation Bool missingTrue := emptyDecoder_initialized false
example : ¬ @RustModel.realizableRepresentation Bool missingTrue := by
  intro realizable
  obtain ⟨bytes, accepted⟩ := realizable true ⟨true, rfl⟩
  have empty : bytes = [] := List.length_eq_zero_iff.mp
    (BitDecoder.run_length (emptyDecoder false) bytes true accepted)
  subst bytes
  contradiction

-- Missing physical semantics remain unavailable even when no raw values exist.
@[reducible] def noPhysical : RustModel Empty where
  Model := Empty
  «decode» := some
example : ¬ @RustModel.realizableRepresentation Empty noPhysical := by
  change ¬ False
  exact not_false

-- With an explicit decoder, an uninhabited raw carrier is vacuous and needs
-- no Inhabited instance. Empty arrays of this element carrier are realizable.
@[reducible] def emptyPhysical : RustModel Empty where
  Model := Empty
  «decode» := some
  storage := some (.fixed { byteSize := 0, «decode» := fun _ => none })

theorem emptyRealizable : @RustModel.realizableRepresentation Empty emptyPhysical := by
  intro raw
  cases raw

example : @RustModel.realizableRepresentation (Aeneas.Std.Array Empty (0#usize))
    (@modelArray Empty (0#usize) emptyPhysical) :=
  @RustModel.realizable_array Empty emptyPhysical (0#usize) emptyRealizable

-- Distinct bytes may represent the same raw value; realizability supplies
-- existence and does not impose uniqueness or a canonical inverse.
@[reducible] def ambiguous : RustModel Bool where
  Model := Unit
  «decode» raw := if raw then none else some ()
  storage := some (.fixed ((uScalarBitDecoder .U8).map fun _ => false))

theorem ambiguousRealizable : @RustModel.realizableRepresentation Bool ambiguous := by
  intro raw valid
  cases raw with
  | false => exact ⟨[AMByte.init 0], rfl⟩
  | true => obtain ⟨value, accepted⟩ := valid; contradiction

example : ((uScalarBitDecoder .U8).map fun _ => false).run [AMByte.init 0] = some false := rfl
example : ((uScalarBitDecoder .U8).map fun _ => false).run [AMByte.init 1] = some false := rfl
example : [AMByte.init 0] ≠ [AMByte.init 1] := by decide

end RustRealizabilityTests
