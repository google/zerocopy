/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RustRepresentation
import all RustModel
import all ModelPrelude
@[expose] public section

/-!
These tests challenge representation admission, including the distinction
between physical validity and a retained provider's optional invariant. They
are pure Lean model tests, not executions of invalid Rust.
-/

open Aeneas Aeneas.Std AeneasSpecs Rust.Storage
namespace RustRepresentationTests

example (ty : UScalarTy) : RustModel.completeRepresentation (UScalar ty) := completeUScalar ty
example (ty : IScalarTy) : RustModel.completeRepresentation (IScalar ty) := completeIScalar ty
example (ty : UScalarTy) : RustModel.zeroRepresentation (UScalar ty) := zeroUScalar ty
example (ty : IScalarTy) : RustModel.zeroRepresentation (IScalar ty) := zeroIScalar ty
example : RustModel.completeRepresentation Unit := completeUnit
example : RustModel.zeroRepresentation Bool := zeroBool

example : RustModel.completeRepresentation (Aeneas.Std.Array U16 (3#usize)) :=
  RustModel.complete_array _ _ (completeUScalar .U16)
example : RustModel.completeRepresentation (Aeneas.Std.Array Unit (4#usize)) :=
  RustModel.complete_array _ _ completeUnit
example : RustModel.completeRepresentation (Aeneas.Std.Array U8 (0#usize)) :=
  RustModel.complete_array _ _ (completeUScalar .U8)
example : RustModel.zeroRepresentation
    (Aeneas.Std.Array (Aeneas.Std.Array Bool (2#usize)) (3#usize)) :=
  RustModel.zero_array _ _ (RustModel.zero_array _ _ zeroBool)

-- An initialized byte of value two refutes boolean completeness, although
-- zero itself is admitted. This is a proved counterexample, not a tactic failure.
example : ¬ RustModel.completeRepresentation Bool := by
  intro complete
  obtain ⟨raw, value, physical, _⟩ := complete [AMByte.init 2] rfl (by simp [Initialized])
  rw [boolDecoder_run_two] at physical
  contradiction

-- NonZero rejects the integer zero pattern at its physical decoding stage.
theorem nonzeroU8_not_zero : ¬ RustModel.zeroRepresentation
    (core.num.nonzero.NonZero U8 core.num.niche_types.NonZeroU8Inner) := by
  intro zero
  obtain ⟨raw, value, physical, _⟩ := zero
  change none = some raw at physical
  contradiction
example : ¬ RustModel.completeRepresentation
    (core.num.nonzero.NonZero U8 core.num.niche_types.NonZeroU8Inner) := by
  intro complete
  have zero := RustModel.completeRepresentation_zeroRepresentation _ complete
  obtain ⟨raw, value, physical, _⟩ := zero
  change none = some raw at physical
  contradiction
example : (modelNonZeroUScalar .U8 core.num.niche_types.NonZeroU8Inner).zeroedResult =
    .fail .undef :=
  ((modelNonZeroUScalar .U8 core.num.niche_types.NonZeroU8Inner).zeroedResult_eq_fail_iff).mpr
    nonzeroU8_not_zero

-- Missing physical semantics fail closed even for an inhabited raw carrier.
example : ¬ RustModel.completeRepresentation Nat := by
  simp [RustModel.completeRepresentation, RustModel.representation]
example : ¬ RustModel.zeroRepresentation Nat := by
  simp [RustModel.zeroRepresentation, RustModel.representation]
example : modelNat.zeroedResult = .fail .undef := rfl

-- The same physical domain with a provider rejecting zero must reject the
-- zero law and the guarded operation. Physical success alone is insufficient.
@[reducible] def rejectsZero : RustModel U8 where
  Model := Unit
  decode raw := if raw.val = 0 then none else some ()
  representation := some (uScalarBitDecoder .U8)

theorem rejectsZero_not_zero : ¬ @RustModel.zeroRepresentation U8 rejectsZero := by
  intro zero
  obtain ⟨raw, value, physical, model⟩ := zero
  change some (0#u8) = some raw at physical
  cases Option.some.inj physical
  change none = some value at model
  contradiction
example : rejectsZero.zeroedResult = .fail .undef :=
  rejectsZero.zeroedResult_eq_fail_iff.mpr rejectsZero_not_zero

theorem bool_zeroed : modelBool.zeroedResult = .ok false := by
  exact (modelBool.zeroedResult_eq_ok_iff false).mpr ⟨boolDecoder, rfl, rfl, false, rfl⟩
example : modelUnit.zeroedResult = .ok () := by
  exact (modelUnit.zeroedResult_eq_ok_iff ()).mpr ⟨unitDecoder, rfl, rfl, (), rfl⟩
example : (modelUScalar .U16).zeroedResult = .ok (0#u16) := by
  exact ((modelUScalar .U16).zeroedResult_eq_ok_iff _).mpr
    ⟨uScalarBitDecoder .U16, rfl, rfl, unsignedWord (0#u16), rfl⟩
example : (modelIScalar .I16).zeroedResult = .ok (0#i16) := by
  exact ((modelIScalar .I16).zeroedResult_eq_ok_iff _).mpr
    ⟨iScalarBitDecoder .I16, rfl, rfl, signedWord (0#i16), rfl⟩
example : modelBool.zeroedModel = .ok false := by
  unfold RustModel.zeroedModel
  rw [bool_zeroed, RustModel.decodeResult_ok]
  rfl
example : RustModel.zeroedValue false := bool_zeroed

-- Zero law success retains the actual provider's mathematical witness.
example {Raw : Type} (m : RustModel Raw) (law : @RustModel.zeroRepresentation Raw m) :
    ∃ raw value, m.zeroedResult = .ok raw ∧ m.decode raw = some value :=
  m.zeroedResult_admitted law

-- Permitting divergence must not permit a forbidden zero construction. The
-- same backstop applies even if the caller discards the result entirely.
example {Raw : Type} (m : RustModel Raw) (rejected : ¬ @RustModel.zeroRepresentation Raw m) :
    ¬ WP.spec m.zeroedResult (fun _ => True) := by
  rw [m.zeroedResult_eq_fail_iff.mpr rejected]
  simp
example {Raw : Type} (m : RustModel Raw) (rejected : ¬ @RustModel.zeroRepresentation Raw m) :
    ¬ WP.dspec m.zeroedResult (fun _ => True) := by
  rw [m.zeroedResult_eq_fail_iff.mpr rejected]
  simp

end RustRepresentationTests
