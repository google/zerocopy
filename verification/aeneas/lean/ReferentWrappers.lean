/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import ReferentValidity
import all RustModel
import all ModelPrelude
@[expose] public section

/-!
A transparent wrapper has its payload's safe byte domain when its physical
decoder maps payload values and its mathematical decoder admits exactly those
mapped values that the payload admits. These two premises refer to the actual
providers. They require neither a preferred encoding nor an inhabited payload.

The equivalences below concern stored bytes only. In particular, the Cell and
UnsafeCell results do not supply aliasing or mutation permissions.
-/

open Aeneas.Std AeneasSpecs Rust.Storage
namespace Zerocopy.Referent

/-- Every successful mapped physical result comes from a payload. It therefore
suffices to compare mathematical admission on those mapped values; no inverse
function or model-value equality is needed. A missing payload decoder leaves
both safe domains empty. -/
theorem safeBytes_wrapper_iff {A B : Type} [ma : RustModel A] [mb : RustModel B]
    (wrap : A → B)
    (representation : mb.representation = wrapperRepresentation wrap)
    (admission : ∀ raw, (∃ value, mb.decode (wrap raw) = some value) ↔
      ∃ value, ma.decode raw = some value)
    (bytes : List AMByte) : safeBytes mb bytes ↔ safeBytes ma bytes := by
  cases available : ma.representation with
  | none => simp [safeBytes, representation, wrapperRepresentation, available]
  | some decoder =>
    constructor
    · rintro ⟨outer, installed, wrapped, value, physical, mathematical⟩
      have sameDecoder : outer = decoder.map wrap := by
        apply Option.some.inj
        rw [← installed, representation, wrapperRepresentation, available]
        rfl
      subst outer
      rw [BitDecoder.run_map] at physical
      cases language : decoder.run bytes with
      | none => simp [language] at physical
      | some raw =>
        have sameValue : wrap raw = wrapped := by simpa [language] using physical
        subst wrapped
        obtain ⟨mathematical, mathematicalChild⟩ := (admission raw).mp ⟨value, mathematical⟩
        exact ⟨decoder, available, raw, mathematical, language, mathematicalChild⟩
    · rintro ⟨actual, installed, raw, value, physical, mathematical⟩
      have sameDecoder : actual = decoder := Option.some.inj (installed.symm.trans available)
      subst actual
      obtain ⟨mathematical, mathematicalWrapper⟩ := (admission raw).mpr ⟨value, mathematical⟩
      refine ⟨decoder.map wrap, ?_, wrap raw, mathematical, ?_, mathematicalWrapper⟩
      · simp only [representation, wrapperRepresentation, available, Option.map_some]
      · rw [BitDecoder.run_map, physical]
        rfl

theorem safeBytes_manuallyDrop_iff (T : Type) [ma : RustModel T] (bytes : List AMByte) :
    safeBytes (inferInstance : RustModel (core.mem.manually_drop.ManuallyDrop T)) bytes ↔
      safeBytes ma bytes :=
  safeBytes_wrapper_iff core.mem.manually_drop.ManuallyDrop.mk rfl (fun _ => Iff.rfl) bytes

theorem safeBytes_cell_iff (T : Type) [ma : RustModel T] (bytes : List AMByte) :
    safeBytes (inferInstance : RustModel (core.cell.Cell T)) bytes ↔ safeBytes ma bytes :=
  safeBytes_wrapper_iff core.cell.Cell.mk rfl (fun _ => Iff.rfl) bytes

theorem safeBytes_unsafeCell_iff (T : Type) [ma : RustModel T] (bytes : List AMByte) :
    safeBytes (inferInstance : RustModel (core.cell.UnsafeCell T)) bytes ↔ safeBytes ma bytes :=
  safeBytes_wrapper_iff core.cell.UnsafeCell.mk rfl (fun _ => Iff.rfl) bytes

theorem safeBytes_wrapping_iff (T : Type) [ma : RustModel T] (bytes : List AMByte) :
    safeBytes (inferInstance : RustModel (Zerocopy.core.num.wrapping.Wrapping T)) bytes ↔
      safeBytes ma bytes :=
  safeBytes_wrapper_iff Zerocopy.core.num.wrapping.Wrapping.mk rfl (fun _ => Iff.rfl) bytes

/-- The generated model decodes its child before constructing a wrapper model.
Its actual definition, rather than its physical layout alone, proves admission. -/
theorem safeBytes_unalign_iff (T : Type) [ma : RustModel T] (bytes : List AMByte) :
    safeBytes (inferInstance : RustModel (Zerocopy.wrappers.Unalign T)) bytes ↔
      safeBytes ma bytes := by
  apply safeBytes_wrapper_iff Zerocopy.wrappers.Unalign.mk rfl ?_ bytes
  intro raw
  cases decoded : ma.decode raw <;>
    simp [RustModel.decode, Zerocopy.wrappers.Unalign.decode, Zerocopy.wrappers.Unalign.decodeFields, decoded]

theorem safeBytes_readOnly_iff (T : Type) [ma : RustModel T] (bytes : List AMByte) :
    safeBytes (inferInstance : RustModel (Zerocopy.wrappers.read_only_def.ReadOnly T)) bytes ↔
      safeBytes ma bytes := by
  apply safeBytes_wrapper_iff Zerocopy.wrappers.read_only_def.ReadOnly.mk rfl ?_ bytes
  intro raw
  cases decoded : ma.decode raw <;>
    simp [RustModel.decode, Zerocopy.wrappers.read_only_def.ReadOnly.decode,
      Zerocopy.wrappers.read_only_def.ReadOnly.decodeFields, decoded]

end Zerocopy.Referent
