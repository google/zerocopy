/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RustRealizability
@[expose] public section

/-!
A raw value need not identify its bytes uniquely. Two byte strings can decode
into the same raw value, yet a cast into a byte-observing destination can tell
those strings apart. Selecting one canonical string would discard permitted
Rust outcomes.

We retain a preferred string in each model provider. Selection validates that
preference and falls back only when another representation exists. The generic
proof quantifies over the provider, and the coverage theorem varies just its
preference while fixing its physical and mathematical decoders. Together those
facts cover every represented outcome without adding effects to Aeneas's Result.

A preference is a function of the raw value, not an execution history. Admission
therefore rejects repeated conversions, loops, and recursion in this fragment,
and only admits generic forwarding whose provider remains universally bound.
Supporting independent choices at multiple conversions needs a richer model.

This module proves byte-level admission. Rust correspondence, actual layout,
valid reference access, and the absence of destructor effects remain separate
premises or independently checked obligations. Numeric bytes carry no provenance.
-/

open Aeneas.Std Rust.Storage
namespace AeneasSpecs
namespace RustModel

/-- The physical decoder accepts these bytes as this raw value. -/
def represented {Raw : Type u} (m : RustModel Raw) (raw : Raw) (bytes : List AMByte) : Prop :=
  match m.representation with
  | none => False
  | some decoder => decoder.run bytes = some raw

@[simp] theorem withChoice_decode {Raw : Type u} (m : RustModel Raw)
    (choose : Raw → List AMByte) : (m.withChoice choose).decode = m.decode := rfl

@[simp] theorem withChoice_representation {Raw : Type u} (m : RustModel Raw)
    (choose : Raw → List AMByte) : (m.withChoice choose).representation = m.representation := rfl

@[simp] theorem withChoice_represented {Raw : Type u} (m : RustModel Raw)
    (choose : Raw → List AMByte) (raw : Raw) (bytes : List AMByte) :
    (m.withChoice choose).represented raw bytes ↔ m.represented raw bytes := Iff.rfl

@[simp] theorem withChoice_initialized {Raw : Type u} (m : RustModel Raw)
    (choose : Raw → List AMByte) :
    @initializedRepresentation Raw (m.withChoice choose) ↔ @initializedRepresentation Raw m := Iff.rfl

@[simp] theorem withChoice_realizable {Raw : Type u} (m : RustModel Raw)
    (choose : Raw → List AMByte) :
    @realizableRepresentation Raw (m.withChoice choose) ↔ @realizableRepresentation Raw m := Iff.rfl

@[simp] theorem withChoice_complete {Raw : Type u} (m : RustModel Raw)
    (choose : Raw → List AMByte) :
    @completeRepresentation Raw (m.withChoice choose) ↔ @completeRepresentation Raw m := Iff.rfl

@[simp] theorem withChoice_valid {Raw : Type u} (m : RustModel Raw)
    (choose : Raw → List AMByte) (raw : Raw) :
    @isValid Raw (m.withChoice choose) raw ↔ @isValid Raw m raw := Iff.rfl

@[simp] theorem withChoice_zero {Raw : Type u} (m : RustModel Raw)
    (choose : Raw → List AMByte) :
    @zeroRepresentation Raw (m.withChoice choose) ↔ @zeroRepresentation Raw m := Iff.rfl

/-- Check the preference, then fall back to an accepted representation. The
fallback establishes existence; varying the preference covers every choice. -/
noncomputable def selectedBytes {Raw : Type u} (m : RustModel Raw) (raw : Raw) :
    Result (List AMByte) := by
  classical
  exact if preferred : m.represented raw (m.representationChoice raw) then
    .ok (m.representationChoice raw)
  else if possible : ∃ bytes, m.represented raw bytes then
    .ok (Classical.choose possible)
  else .fail .undef

theorem selectedBytes_represented {Raw : Type u} (m : RustModel Raw) (raw : Raw)
    (bytes : List AMByte) (selected : m.selectedBytes raw = .ok bytes) :
    m.represented raw bytes := by
  classical
  unfold selectedBytes at selected
  split at selected
  · have equal : m.representationChoice raw = bytes := by simpa using selected
    exact equal ▸ ‹m.represented raw (m.representationChoice raw)›
  · split at selected
    · have accepted := Classical.choose_spec ‹∃ bytes, m.represented raw bytes›
      have equal : Classical.choose ‹∃ bytes, m.represented raw bytes› = bytes := by simpa using selected
      exact equal ▸ accepted
    · simp at selected

theorem selectedBytes_exists {Raw : Type u} (m : RustModel Raw) (raw : Raw)
    (possible : ∃ bytes, m.represented raw bytes) :
    ∃ bytes, m.selectedBytes raw = .ok bytes ∧ m.represented raw bytes := by
  classical
  unfold selectedBytes
  split
  · exact ⟨_, rfl, ‹m.represented raw (m.representationChoice raw)›⟩
  · exact ⟨_, rfl, Classical.choose_spec possible⟩

/-- A constant preference can select any accepted representation of this input. -/
theorem selectedBytes_withChoice {Raw : Type u} (m : RustModel Raw) (raw : Raw)
    (bytes : List AMByte) (accepted : m.represented raw bytes) :
    (m.withChoice (fun _ => bytes)).selectedBytes raw = .ok bytes := by
  classical
  simp only [selectedBytes, withChoice, represented] at *
  exact dif_pos accepted

/-- Equal-width byte copying followed by language validity and model admission.
This is the selected fragment of transmute_copy, not a model of resource ownership. -/
noncomputable def transmuteCopyResult {Src : Type u} {Dst : Type v}
    (source : RustModel Src) (destination : RustModel Dst) (src : Src) : Result Dst :=
  match source.representation, destination.representation with
  | some sourceDecoder, some destinationDecoder => do
      if sourceDecoder.byteSize = destinationDecoder.byteSize then
        let bytes ← source.selectedBytes src
        let raw ← Result.ofOption (destinationDecoder.run bytes) .undef
        let _ ← Result.ofOption (destination.decode raw) .undef
        .ok raw
      else .fail .undef
  | _, _ => .fail .undef

/-- Both values decode from the same bytes. This relation keeps all accepted
representations, independently of the operational preference. -/
def byteCastWith {Src : Type u} {Dst : Type v} (source : RustModel Src)
    (destination : RustModel Dst) (src : Src) (dst : Dst) : Prop :=
  ∃ bytes, source.represented src bytes ∧ destination.represented dst bytes

/-- Contracts retain the source and destination providers implicitly. -/
def byteCast {Src : Type u} {Dst : Type v} [source : RustModel Src]
    [destination : RustModel Dst] (src : Src) (dst : Dst) : Prop :=
  source.byteCastWith destination src dst

theorem transmuteCopyResult_of_selected {Src : Type u} {Dst : Type v}
    (source : RustModel Src) (destination : RustModel Dst) (src : Src)
    (sourceDecoder : BitDecoder Src) (destinationDecoder : BitDecoder Dst)
    (hs : source.representation = some sourceDecoder)
    (hd : destination.representation = some destinationDecoder)
    (width : sourceDecoder.byteSize = destinationDecoder.byteSize)
    (bytes : List AMByte) (dst : Dst) (value : destination.Model)
    (selected : source.selectedBytes src = .ok bytes)
    (physical : destinationDecoder.run bytes = some dst)
    (admitted : destination.decode dst = some value) :
    source.transmuteCopyResult destination src = .ok dst := by
  simp [transmuteCopyResult, hs, hd, width, selected, physical, admitted]

theorem transmuteCopyResult_rejects_physical {Src : Type u} {Dst : Type v}
    (source : RustModel Src) (destination : RustModel Dst) (src : Src)
    (sourceDecoder : BitDecoder Src) (destinationDecoder : BitDecoder Dst)
    (hs : source.representation = some sourceDecoder)
    (hd : destination.representation = some destinationDecoder)
    (width : sourceDecoder.byteSize = destinationDecoder.byteSize)
    (bytes : List AMByte) (selected : source.selectedBytes src = .ok bytes)
    (rejected : destinationDecoder.run bytes = none) :
    source.transmuteCopyResult destination src = .fail .undef := by
  simp [transmuteCopyResult, hs, hd, width, selected, rejected]

theorem transmuteCopyResult_rejects_model {Src : Type u} {Dst : Type v}
    (source : RustModel Src) (destination : RustModel Dst) (src : Src)
    (sourceDecoder : BitDecoder Src) (destinationDecoder : BitDecoder Dst)
    (hs : source.representation = some sourceDecoder)
    (hd : destination.representation = some destinationDecoder)
    (width : sourceDecoder.byteSize = destinationDecoder.byteSize)
    (bytes : List AMByte) (dst : Dst) (selected : source.selectedBytes src = .ok bytes)
    (physical : destinationDecoder.run bytes = some dst)
    (rejected : destination.decode dst = none) :
    source.transmuteCopyResult destination src = .fail .undef := by
  simp [transmuteCopyResult, hs, hd, width, selected, physical, rejected]

/-- Initialization, realizability, and destination completeness compose without
selecting a canonical representation as the only possible Rust outcome. -/
theorem transmuteCopyResult_admitted {Src : Type u} {Dst : Type v}
    (source : RustModel Src) (destination : RustModel Dst) (src : Src)
    (initialized : @initializedRepresentation Src source)
    (realizable : @realizableRepresentation Src source)
    (complete : @completeRepresentation Dst destination)
    (sameWidth : source.representation.map (·.byteSize) = destination.representation.map (·.byteSize))
    (valid : @isValid Src source src) :
    ∃ dst value, source.transmuteCopyResult destination src = .ok dst ∧
      destination.decode dst = some value ∧ source.byteCastWith destination src dst := by
  cases hs : source.representation with
  | none =>
    cases hd : destination.representation with
    | none => simp [completeRepresentation, hd] at complete
    | some decoder => simp [hs, hd] at sameWidth
  | some sd =>
    cases hd : destination.representation with
    | none => simp [completeRepresentation, hd] at complete
    | some dd =>
      have initialized := source.initialized_fixed sd hs initialized
      have realizable := source.realizable_fixed sd hs realizable
      simp only [completeRepresentation, hd] at complete
      have width : sd.byteSize = dd.byteSize := by simpa [hs, hd] using sameWidth
      obtain ⟨initial, initialAccepted⟩ := realizable src valid
      have possible : ∃ bytes, source.represented src bytes :=
        ⟨initial, by simpa [represented, hs] using initialAccepted⟩
      obtain ⟨bytes, selected, accepted⟩ := source.selectedBytes_exists src possible
      have physical : sd.run bytes = some src := by simpa [represented, hs] using accepted
      obtain ⟨dst, value, decoded, admitted⟩ := complete bytes
        ((sd.run_length bytes src physical).trans width) (initialized bytes src physical)
      exact ⟨dst, value,
        transmuteCopyResult_of_selected source destination src sd dd hs hd width bytes dst value
          selected decoded admitted,
        admitted, bytes, accepted, by simpa [represented, hd] using decoded⟩

/-- Every admitted destination interpretation of any source representation is
an execution of the extracted primitive with the same decoders and a changed
preference. This is the coverage fact needed by an all-choices contract. -/
theorem transmuteCopyResult_covers {Src : Type u} {Dst : Type v}
    (source : RustModel Src) (destination : RustModel Dst) (src : Src)
    (sourceDecoder : BitDecoder Src) (destinationDecoder : BitDecoder Dst)
    (hs : source.representation = some sourceDecoder)
    (hd : destination.representation = some destinationDecoder)
    (width : sourceDecoder.byteSize = destinationDecoder.byteSize)
    (bytes : List AMByte) (dst : Dst) (value : destination.Model)
    (sourcePhysical : sourceDecoder.run bytes = some src)
    (destinationPhysical : destinationDecoder.run bytes = some dst)
    (admitted : destination.decode dst = some value) :
    (source.withChoice (fun _ => bytes)).transmuteCopyResult destination src = .ok dst := by
  apply transmuteCopyResult_of_selected (source.withChoice (fun _ => bytes)) destination src sourceDecoder destinationDecoder
    hs hd width bytes dst value
  · exact source.selectedBytes_withChoice src bytes (by simpa [represented, hs] using sourcePhysical)
  · exact destinationPhysical
  · exact admitted

/-- A choice-independent postcondition proved for every preference holds for
all represented outcomes. The quantifier cannot be replaced by one provider. -/
theorem transmuteCopyResult_allChoices {Src : Type u} {Dst : Type v}
    (source : RustModel Src) (destination : RustModel Dst) (src : Src) (post : Dst → Prop)
    (verified : ∀ choose dst,
      (source.withChoice choose).transmuteCopyResult destination src = .ok dst → post dst)
    (sourceDecoder : BitDecoder Src) (destinationDecoder : BitDecoder Dst)
    (hs : source.representation = some sourceDecoder)
    (hd : destination.representation = some destinationDecoder)
    (width : sourceDecoder.byteSize = destinationDecoder.byteSize)
    (bytes : List AMByte) (dst : Dst) (value : destination.Model)
    (sourcePhysical : sourceDecoder.run bytes = some src)
    (destinationPhysical : destinationDecoder.run bytes = some dst)
    (admitted : destination.decode dst = some value) : post dst :=
  verified (fun _ => bytes) dst (transmuteCopyResult_covers source destination src
    sourceDecoder destinationDecoder hs hd width bytes dst value
    sourcePhysical destinationPhysical admitted)

end RustModel

/-- ManuallyDrop preserves the preferred bytes as well as the physical decoder. -/
@[simp] theorem manuallyDrop_choice {T : Type} (m : RustModel T) (raw : T) :
    (modelManuallyDrop T (ma := m)).representationChoice ⟨raw⟩ = m.representationChoice raw := rfl

@[simp] theorem manuallyDrop_representation {T : Type} (m : RustModel T) :
    (modelManuallyDrop T (ma := m)).representation =
      m.representation.map (·.map core.mem.manually_drop.ManuallyDrop.mk) := by
  change (wrapperStorage _ _ _).bind PhysicalStorage.fixed? = _
  exact wrapperStorage_fixed? _ _ _

theorem manuallyDrop_represented {T : Type} (m : RustModel T) (raw : T) (bytes : List AMByte) :
    (modelManuallyDrop T (ma := m)).represented ⟨raw⟩ bytes ↔ m.represented raw bytes := by
  unfold RustModel.represented
  rw [manuallyDrop_representation]
  cases h : m.representation with
  | none => simp
  | some decoder =>
    simp only [Option.map_some, BitDecoder.run_map]
    cases decoder.run bytes <;> simp

theorem byteCast_manuallyDrop_iff {Src Dst : Type} (source : RustModel Src)
    (destination : RustModel Dst) (src : Src) (dst : Dst) :
    @RustModel.byteCast (core.mem.manually_drop.ManuallyDrop Src) Dst
      (modelManuallyDrop Src (ma := source)) destination ⟨src⟩ dst ↔
      @RustModel.byteCast Src Dst source destination src dst := by
  simp only [RustModel.byteCast, RustModel.byteCastWith, manuallyDrop_represented]

theorem manuallyDrop_withChoice {T : Type} (m : RustModel T)
    (choose : T → List AMByte) :
    modelManuallyDrop T (ma := m.withChoice choose) =
      (modelManuallyDrop T (ma := m)).withChoice (fun raw => choose raw.value) := rfl

@[simp] theorem manuallyDrop_width {T : Type} (m : RustModel T) :
    (modelManuallyDrop T (ma := m)).representation.map (·.byteSize) =
      m.representation.map (·.byteSize) := by
  rw [manuallyDrop_representation]
  cases h : m.representation <;> simp [BitDecoder.map]

theorem manuallyDrop_realizable {T : Type} (m : RustModel T)
    (realizable : @RustModel.realizableRepresentation T m) :
    @RustModel.realizableRepresentation (core.mem.manually_drop.ManuallyDrop T)
      (modelManuallyDrop T (ma := m)) := by
  exact realizableManuallyDrop T realizable

end AeneasSpecs
