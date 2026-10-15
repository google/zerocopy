/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import TransmuteModel
@[expose] public section

open Aeneas Aeneas.Std AeneasSpecs Rust.Storage
namespace Zerocopy.Proofs

/-- The retained static assertion checks both successful size queries before
constructing ManuallyDrop or invoking the byte-copy interpretation. -/
theorem transmute_copy_eq_primitive {Src Dst : Type}
    (source : IntoBytes Src) (destination : FromBytes Dst) (src : Src)
    [ms : RustModel Src] [md : RustModel Dst]
    (same_size : ∃ width : Usize, core.mem.size_of Src = .ok width ∧
      core.mem.size_of Dst = .ok width) :
    util.macro_util.transmute_copy source destination src =
      (modelManuallyDrop Src (ma := ms)).transmuteCopyResult md ⟨src⟩ := by
  obtain ⟨width, hs, hd⟩ := same_size
  simp only [util.macro_util.transmute_copy,
    PairPhantomDataPhantomData.Insts.ZerocopyUtilMacro_utilTransmute_copyStaticAssert.ASSERT,
    hs, hd]
  simp only [Aeneas.Std.massert, core.mem.manually_drop.ManuallyDrop.new, core.mem.transmute_copy]
  simp only [bind_ok, ite_true, decide_true]

/-- This distinct assertion outcome also checks that the extracted guard was
retained. A theorem about only equal-size calls cannot detect its removal. -/
theorem transmute_copy_rejects_unequal {Src Dst : Type}
    (source : IntoBytes Src) (destination : FromBytes Dst) (src : Src)
    [ms : RustModel Src] [md : RustModel Dst] (sourceSize destinationSize : Usize)
    (hs : core.mem.size_of Src = .ok sourceSize)
    (hd : core.mem.size_of Dst = .ok destinationSize)
    (different : sourceSize ≠ destinationSize) :
    util.macro_util.transmute_copy source destination src = .fail .assertionFailure := by
  simp only [util.macro_util.transmute_copy,
    PairPhantomDataPhantomData.Insts.ZerocopyUtilMacro_utilTransmute_copyStaticAssert.ASSERT,
    hs, hd]
  simp [different, Aeneas.Std.massert]

/-- The native helper's successful size queries establish equal physical
widths. Initialization, source realizability, and destination completeness then
prove that its result is admitted and has a common byte representation. -/
theorem transmute_copy_admitted {Src Dst : Type}
    (source : IntoBytes Src) (destination : FromBytes Dst) (src : Src)
    [ms : RustModel Src] [md : RustModel Dst]
    (initialized : @RustModel.initializedRepresentation Src ms)
    (realizable : @RustModel.realizableRepresentation Src ms)
    (complete : @RustModel.completeRepresentation Dst md)
    (valid : @isValid Src ms src)
    (same_size : RustModel.sameSize Src Dst) :
    ∃ dst value, util.macro_util.transmute_copy source destination src = .ok dst ∧
      md.decode dst = some value ∧ RustModel.byteCast src dst := by
  obtain ⟨width, sourceSize, destinationSize, sourceWidth, destinationWidth⟩ := same_size
  have equalWidths : ms.representation.map (·.byteSize) = md.representation.map (·.byteSize) :=
    sourceWidth.trans destinationWidth.symm
  obtain ⟨dst, value, executed, admitted, related⟩ :=
    RustModel.transmuteCopyResult_admitted (modelManuallyDrop Src (ma := ms)) md ⟨src⟩
      (initializedManuallyDrop Src initialized) (manuallyDrop_realizable ms realizable)
      complete (by simpa only [manuallyDrop_width] using equalWidths) valid
  refine ⟨dst, value, ?_, admitted, ?_⟩
  · rw [transmute_copy_eq_primitive source destination src ⟨width, sourceSize, destinationSize⟩]
    exact executed
  · exact (byteCast_manuallyDrop_iff ms md src dst).mp related

/-- The extracted caller retains the exact providers and delegates to the
verified helper. It introduces no new semantic premise. -/
theorem transmute_copy_caller_admitted {Src Dst : Type}
    (source : IntoBytes Src) (destination : FromBytes Dst) (src : Src)
    [ms : RustModel Src] [md : RustModel Dst]
    (initialized : @RustModel.initializedRepresentation Src ms)
    (realizable : @RustModel.realizableRepresentation Src ms)
    (complete : @RustModel.completeRepresentation Dst md)
    (valid : @isValid Src ms src)
    (same_size : RustModel.sameSize Src Dst) :
    ∃ dst value, util.generic_transmute.transmute_copy_caller source destination src = .ok dst ∧
      md.decode dst = some value ∧ RustModel.byteCast src dst := by
  simpa only [util.generic_transmute.transmute_copy_caller] using
    transmute_copy_admitted source destination src initialized realizable complete valid same_size

theorem transmute_copy_spec : Specs.transmute_copy_spec := by
  intro Src Dst source destination src ms md sourceLaw destinationLaw _ mathSrc decoded same_size
  obtain ⟨initialized, realizable⟩ :=
    @TraitLaws.into_bytes_initialized.holds Src source ms sourceLaw
  have complete := @TraitLaws.from_bytes_valid.holds Dst destination md destinationLaw
  obtain ⟨dst, value, executed, admitted, related⟩ :=
    transmute_copy_admitted source destination src initialized realizable complete
      ⟨mathSrc, decoded⟩ same_size
  rw [executed]
  exact ⟨value, admitted, related⟩

theorem transmute_copy_caller_spec : Specs.transmute_copy_caller_spec := by
  intro Src Dst source destination src ms md sourceLaw destinationLaw zeroLaw mathSrc decoded same_size
  have helper := @transmute_copy_spec Src Dst source destination src ms md
    sourceLaw destinationLaw zeroLaw mathSrc decoded same_size
  unfold util.generic_transmute.transmute_copy_caller
  step with helper as ⟨dst, value, admitted, related⟩
  exact ⟨value, admitted, related⟩

/-- Every represented, admitted output occurs in this native helper's family
of executions. Only the source preference changes; both decoders and the Rust
arguments stay fixed. -/
theorem transmute_copy_covers {Src Dst : Type}
    (source : IntoBytes Src) (destination : FromBytes Dst) (src : Src)
    (ms : RustModel Src) (md : RustModel Dst)
    (same_size : @RustModel.sameSize Src Dst ms md)
    (sd : BitDecoder Src) (dd : BitDecoder Dst)
    (hs : ms.representation = some sd) (hd : md.representation = some dd)
    (bytes : List AMByte) (dst : Dst) (value : md.Model)
    (sourcePhysical : sd.run bytes = some src)
    (destinationPhysical : dd.run bytes = some dst)
    (admitted : md.decode dst = some value) :
    @util.macro_util.transmute_copy Src Dst source destination src
      (ms.withChoice (fun _ => bytes)) md = .ok dst := by
  obtain ⟨size, sourceSize, destinationSize, _, _⟩ := same_size
  rw [@transmute_copy_eq_primitive Src Dst source destination src
    (ms.withChoice (fun _ => bytes)) md ⟨size, sourceSize, destinationSize⟩]
  rw [manuallyDrop_withChoice]
  have width : sd.byteSize = dd.byteSize :=
    (sd.run_length bytes src sourcePhysical).symm.trans (dd.run_length bytes dst destinationPhysical)
  exact RustModel.transmuteCopyResult_covers (modelManuallyDrop Src (ma := ms)) md ⟨src⟩
    (sd.map core.mem.manually_drop.ManuallyDrop.mk) dd
    (by rw [manuallyDrop_representation, hs]; rfl) hd width bytes dst value
    (by simp [BitDecoder.run_map, sourcePhysical]) destinationPhysical admitted

theorem transmute_copy_caller_covers {Src Dst : Type}
    (source : IntoBytes Src) (destination : FromBytes Dst) (src : Src)
    (ms : RustModel Src) (md : RustModel Dst)
    (same_size : @RustModel.sameSize Src Dst ms md)
    (sd : BitDecoder Src) (dd : BitDecoder Dst)
    (hs : ms.representation = some sd) (hd : md.representation = some dd)
    (bytes : List AMByte) (dst : Dst) (value : md.Model)
    (sourcePhysical : sd.run bytes = some src)
    (destinationPhysical : dd.run bytes = some dst)
    (admitted : md.decode dst = some value) :
    @util.generic_transmute.transmute_copy_caller Src Dst source destination src
      (ms.withChoice (fun _ => bytes)) md = .ok dst := by
  simpa only [util.generic_transmute.transmute_copy_caller] using
    transmute_copy_covers source destination src ms md same_size sd dd hs hd
      bytes dst value sourcePhysical destinationPhysical admitted

/-- Universal provider proofs cover every represented output of the actual
extracted helper, including outputs from distinct encodings of one raw input. -/
theorem transmute_copy_allChoices {Src Dst : Type}
    (source : IntoBytes Src) (destination : FromBytes Dst) (src : Src)
    (ms : RustModel Src) (md : RustModel Dst) (post : Dst → Prop)
    (verified : ∀ choose dst,
      @util.macro_util.transmute_copy Src Dst source destination src (ms.withChoice choose) md =
        .ok dst → post dst)
    (same_size : @RustModel.sameSize Src Dst ms md)
    (sd : BitDecoder Src) (dd : BitDecoder Dst)
    (hs : ms.representation = some sd) (hd : md.representation = some dd)
    (bytes : List AMByte) (dst : Dst) (value : md.Model)
    (sourcePhysical : sd.run bytes = some src)
    (destinationPhysical : dd.run bytes = some dst)
    (admitted : md.decode dst = some value) : post dst :=
  verified (fun _ => bytes) dst (transmute_copy_covers source destination src ms md
    same_size sd dd hs hd bytes dst value sourcePhysical destinationPhysical admitted)

end Zerocopy.Proofs
