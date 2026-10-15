/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Specs
public import TraitLaws
public import ReferentWrappers
public import Proofs.FromBytes
public import Proofs.IntoBytes
@[expose] public section

/-!
Each implementation theorem keeps the native function's complete input prefix,
then adds exactly the providers and input laws required by the proof audit.
The conclusion names the actual extracted dictionary. Wrapper implications use
both decoder stages of the canonical providers; they do not choose encodings.
-/

open Aeneas Aeneas.Std AeneasSpecs
namespace Zerocopy.Proofs

@[instance] theorem pointer.invariant.Uninit.Insts.ZerocopyPointerInvariantValidity_law :
    TraitLaws.validity_kind pointer.invariant.Uninit
      Zerocopy.pointer.invariant.Uninit.Insts.ZerocopyPointerInvariantValidity :=
  ⟨⟨.uninit, rfl, by
    simp [Zerocopy.pointer.invariant.Uninit.Insts.ZerocopyPointerInvariantValidity.KIND,
      Referent.nativeKind]⟩⟩

@[instance] theorem pointer.invariant.AsInitialized.Insts.ZerocopyPointerInvariantValidity_law :
    TraitLaws.validity_kind pointer.invariant.AsInitialized
      Zerocopy.pointer.invariant.AsInitialized.Insts.ZerocopyPointerInvariantValidity :=
  ⟨⟨.asInitialized, rfl, by
    simp [Zerocopy.pointer.invariant.AsInitialized.Insts.ZerocopyPointerInvariantValidity.KIND,
      Referent.nativeKind]⟩⟩

@[instance] theorem pointer.invariant.Initialized.Insts.ZerocopyPointerInvariantValidity_law :
    TraitLaws.validity_kind pointer.invariant.Initialized
      Zerocopy.pointer.invariant.Initialized.Insts.ZerocopyPointerInvariantValidity :=
  ⟨⟨.initialized, rfl, by
    simp [Zerocopy.pointer.invariant.Initialized.Insts.ZerocopyPointerInvariantValidity.KIND,
      Referent.nativeKind]⟩⟩

@[instance] theorem pointer.invariant.Safe.Insts.ZerocopyPointerInvariantValidity_law :
    TraitLaws.validity_kind pointer.invariant.Safe
      Zerocopy.pointer.invariant.Safe.Insts.ZerocopyPointerInvariantValidity :=
  ⟨⟨.safe, rfl, by
    simp [Zerocopy.pointer.invariant.Safe.Insts.ZerocopyPointerInvariantValidity.KIND,
      Referent.nativeKind]⟩⟩

@[instance] theorem pointer.transmute.TransmuteFromDstSrcSafeInitialized.Blanket_law
    {Src : Type} (Dst : Type) (dictionary : IntoBytes Src)
    [source : RustModel Src] [destination : RustModel Dst]
    [law : TraitLaws.into_bytes_initialized Src dictionary] :
    TraitLaws.transmute_from Dst Src pointer.invariant.Safe pointer.invariant.Initialized
      (Zerocopy.pointer.transmute.TransmuteFromDstSrcSafeInitialized.Blanket Dst dictionary) :=
  ⟨Referent.safe_to_initialized Src Dst
    (@TraitLaws.into_bytes_initialized.holds Src dictionary source law).1⟩

@[instance] theorem pointer.transmute.TransmuteFromDstSrcInitializedSafe.Blanket_law
    (Src : Type) {Dst : Type} (dictionary : FromBytes Dst)
    [source : RustModel Src] [destination : RustModel Dst]
    [law : TraitLaws.from_bytes_valid Dst dictionary]
    [_parentLaw : TraitLaws.from_zeros_valid Dst dictionary.FromZerosInst] :
    TraitLaws.transmute_from Dst Src pointer.invariant.Initialized pointer.invariant.Safe
      (Zerocopy.pointer.transmute.TransmuteFromDstSrcInitializedSafe.Blanket Src dictionary) :=
  ⟨Referent.initialized_to_safe Src Dst
    (@TraitLaws.from_bytes_valid.holds Dst dictionary destination law)⟩

@[instance] theorem pointer.transmute.TransmuteFromDstSrcInitializedInitialized.Blanket_law
    (Src Dst : Type) [source : RustModel Src] [destination : RustModel Dst] :
    TraitLaws.transmute_from Dst Src pointer.invariant.Initialized pointer.invariant.Initialized
      (Zerocopy.pointer.transmute.TransmuteFromDstSrcInitializedInitialized.Blanket Src Dst) :=
  ⟨Referent.initialized_identity Src Dst⟩

@[instance] theorem pointer.transmute.TransmuteFromDstSrcVUninit.Blanket_law
    (Src Dst : Type) {V : Type} (dictionary : pointer.invariant.Validity V)
    [source : RustModel Src] [destination : RustModel Dst] [meaning : RustModel V]
    [law : TraitLaws.validity_kind V dictionary] :
    TraitLaws.transmute_from Dst Src V pointer.invariant.Uninit
      (Zerocopy.pointer.transmute.TransmuteFromDstSrcVUninit.Blanket Src Dst dictionary) := by
  obtain ⟨marker, identified, _⟩ := @TraitLaws.validity_kind.holds V dictionary meaning law
  exact ⟨Referent.forget Src Dst V ⟨marker, identified⟩⟩

-- Each direction uses the same proved safe-domain equivalence. The theorem
-- inputs preserve the native implementation prefix before the payload provider.

@[instance] theorem core.mem.manually_drop.ManuallyDrop.Insts.ZerocopyPointerTransmuteTransmuteFromTSafeSafe_law
    (T : Type) [meaning : RustModel T] :
    TraitLaws.transmute_from (_root_.core.mem.manually_drop.ManuallyDrop T) T pointer.invariant.Safe pointer.invariant.Safe
      (Zerocopy.core.mem.manually_drop.ManuallyDrop.Insts.ZerocopyPointerTransmuteTransmuteFromTSafeSafe T) :=
  ⟨Referent.safe_transfer_of_implication T (_root_.core.mem.manually_drop.ManuallyDrop T)
    (fun bytes => (Referent.safeBytes_manuallyDrop_iff T bytes).mpr)⟩

@[instance] theorem pointer.transmute.TransmuteFromTManuallyDropSafeSafe.Blanket_law
    (T : Type) [meaning : RustModel T] :
    TraitLaws.transmute_from T (_root_.core.mem.manually_drop.ManuallyDrop T) pointer.invariant.Safe pointer.invariant.Safe
      (Zerocopy.pointer.transmute.TransmuteFromTManuallyDropSafeSafe.Blanket T) :=
  ⟨Referent.safe_transfer_of_implication (_root_.core.mem.manually_drop.ManuallyDrop T) T
    (fun bytes => (Referent.safeBytes_manuallyDrop_iff T bytes).mp)⟩

@[instance] theorem wrappers.Unalign.Insts.ZerocopyPointerTransmuteTransmuteFromTSafeSafe_law
    (T : Type) [meaning : RustModel T] :
    TraitLaws.transmute_from (Zerocopy.wrappers.Unalign T) T pointer.invariant.Safe pointer.invariant.Safe
      (Zerocopy.wrappers.Unalign.Insts.ZerocopyPointerTransmuteTransmuteFromTSafeSafe T) :=
  ⟨Referent.safe_transfer_of_implication T (Zerocopy.wrappers.Unalign T)
    (fun bytes => (Referent.safeBytes_unalign_iff T bytes).mpr)⟩

@[instance] theorem pointer.transmute.TransmuteFromTUnalignSafeSafe.Blanket_law
    (T : Type) [meaning : RustModel T] :
    TraitLaws.transmute_from T (Zerocopy.wrappers.Unalign T) pointer.invariant.Safe pointer.invariant.Safe
      (Zerocopy.pointer.transmute.TransmuteFromTUnalignSafeSafe.Blanket T) :=
  ⟨Referent.safe_transfer_of_implication (Zerocopy.wrappers.Unalign T) T
    (fun bytes => (Referent.safeBytes_unalign_iff T bytes).mp)⟩

@[instance] theorem core.num.wrapping.Wrapping.Insts.ZerocopyPointerTransmuteTransmuteFromTSafeSafe_law
    (T : Type) [meaning : RustModel T] :
    TraitLaws.transmute_from (Zerocopy.core.num.wrapping.Wrapping T) T pointer.invariant.Safe pointer.invariant.Safe
      (Zerocopy.core.num.wrapping.Wrapping.Insts.ZerocopyPointerTransmuteTransmuteFromTSafeSafe T) :=
  ⟨Referent.safe_transfer_of_implication T (Zerocopy.core.num.wrapping.Wrapping T)
    (fun bytes => (Referent.safeBytes_wrapping_iff T bytes).mpr)⟩

@[instance] theorem pointer.transmute.TransmuteFromTWrappingSafeSafe.Blanket_law
    (T : Type) [meaning : RustModel T] :
    TraitLaws.transmute_from T (Zerocopy.core.num.wrapping.Wrapping T) pointer.invariant.Safe pointer.invariant.Safe
      (Zerocopy.pointer.transmute.TransmuteFromTWrappingSafeSafe.Blanket T) :=
  ⟨Referent.safe_transfer_of_implication (Zerocopy.core.num.wrapping.Wrapping T) T
    (fun bytes => (Referent.safeBytes_wrapping_iff T bytes).mp)⟩

@[instance] theorem core.cell.UnsafeCell.Insts.ZerocopyPointerTransmuteTransmuteFromTSafeSafe_law
    (T : Type) [meaning : RustModel T] :
    TraitLaws.transmute_from (_root_.core.cell.UnsafeCell T) T pointer.invariant.Safe pointer.invariant.Safe
      (Zerocopy.core.cell.UnsafeCell.Insts.ZerocopyPointerTransmuteTransmuteFromTSafeSafe T) :=
  ⟨Referent.safe_transfer_of_implication T (_root_.core.cell.UnsafeCell T)
    (fun bytes => (Referent.safeBytes_unsafeCell_iff T bytes).mpr)⟩

@[instance] theorem pointer.transmute.TransmuteFromTUnsafeCellSafeSafe.Blanket_law
    (T : Type) [meaning : RustModel T] :
    TraitLaws.transmute_from T (_root_.core.cell.UnsafeCell T) pointer.invariant.Safe pointer.invariant.Safe
      (Zerocopy.pointer.transmute.TransmuteFromTUnsafeCellSafeSafe.Blanket T) :=
  ⟨Referent.safe_transfer_of_implication (_root_.core.cell.UnsafeCell T) T
    (fun bytes => (Referent.safeBytes_unsafeCell_iff T bytes).mp)⟩

@[instance] theorem core.cell.Cell.Insts.ZerocopyPointerTransmuteTransmuteFromTSafeSafe_law
    (T : Type) [meaning : RustModel T] :
    TraitLaws.transmute_from (_root_.core.cell.Cell T) T pointer.invariant.Safe pointer.invariant.Safe
      (Zerocopy.core.cell.Cell.Insts.ZerocopyPointerTransmuteTransmuteFromTSafeSafe T) :=
  ⟨Referent.safe_transfer_of_implication T (_root_.core.cell.Cell T)
    (fun bytes => (Referent.safeBytes_cell_iff T bytes).mpr)⟩

@[instance] theorem pointer.transmute.TransmuteFromTCellSafeSafe.Blanket_law
    (T : Type) [meaning : RustModel T] :
    TraitLaws.transmute_from T (_root_.core.cell.Cell T) pointer.invariant.Safe pointer.invariant.Safe
      (Zerocopy.pointer.transmute.TransmuteFromTCellSafeSafe.Blanket T) :=
  ⟨Referent.safe_transfer_of_implication (_root_.core.cell.Cell T) T
    (fun bytes => (Referent.safeBytes_cell_iff T bytes).mp)⟩

@[instance] theorem wrappers.read_only_def.ReadOnly.Insts.ZerocopyPointerTransmuteTransmuteFromTSafeSafe_law
    (T : Type) [meaning : RustModel T] :
    TraitLaws.transmute_from (Zerocopy.wrappers.read_only_def.ReadOnly T) T pointer.invariant.Safe pointer.invariant.Safe
      (Zerocopy.wrappers.read_only_def.ReadOnly.Insts.ZerocopyPointerTransmuteTransmuteFromTSafeSafe T) :=
  ⟨Referent.safe_transfer_of_implication T (Zerocopy.wrappers.read_only_def.ReadOnly T)
    (fun bytes => (Referent.safeBytes_readOnly_iff T bytes).mpr)⟩

@[instance] theorem pointer.transmute.TransmuteFromTReadOnlySafeSafe.Blanket_law
    (T : Type) [meaning : RustModel T] :
    TraitLaws.transmute_from T (Zerocopy.wrappers.read_only_def.ReadOnly T) pointer.invariant.Safe pointer.invariant.Safe
      (Zerocopy.pointer.transmute.TransmuteFromTReadOnlySafeSafe.Blanket T) :=
  ⟨Referent.safe_transfer_of_implication (Zerocopy.wrappers.read_only_def.ReadOnly T) T
    (fun bytes => (Referent.safeBytes_readOnly_iff T bytes).mp)⟩

-- Retain both dictionaries and their laws, as the Rust where-clauses require.
-- The canonical wrapper domains also prove the implication directly, including
-- the case where no payload decoder is installed. No size premise is added.

@[instance] theorem core.cell.UnsafeCell.Insts.ZerocopyPointerTransmuteTransmuteFromCellSafeSafe_law
    {T : Type}
    (first : pointer.transmute.TransmuteFrom T (_root_.core.cell.Cell T)
      pointer.invariant.Safe pointer.invariant.Safe)
    (second : pointer.transmute.TransmuteFrom (_root_.core.cell.UnsafeCell T) T
      pointer.invariant.Safe pointer.invariant.Safe)
    [meaning : RustModel T]
    [_firstLaw : TraitLaws.transmute_from T (_root_.core.cell.Cell T)
      pointer.invariant.Safe pointer.invariant.Safe first]
    [_secondLaw : TraitLaws.transmute_from (_root_.core.cell.UnsafeCell T) T
      pointer.invariant.Safe pointer.invariant.Safe second] :
    TraitLaws.transmute_from (_root_.core.cell.UnsafeCell T) (_root_.core.cell.Cell T)
      pointer.invariant.Safe pointer.invariant.Safe
      (Zerocopy.core.cell.UnsafeCell.Insts.ZerocopyPointerTransmuteTransmuteFromCellSafeSafe
        first second) :=
  ⟨Referent.safe_transfer_of_implication (_root_.core.cell.Cell T) (_root_.core.cell.UnsafeCell T)
    (fun bytes admitted => (Referent.safeBytes_unsafeCell_iff T bytes).mpr
      ((Referent.safeBytes_cell_iff T bytes).mp admitted))⟩

@[instance] theorem core.cell.Cell.Insts.ZerocopyPointerTransmuteTransmuteFromUnsafeCellSafeSafe_law
    {T : Type}
    (first : pointer.transmute.TransmuteFrom T (_root_.core.cell.UnsafeCell T)
      pointer.invariant.Safe pointer.invariant.Safe)
    (second : pointer.transmute.TransmuteFrom (_root_.core.cell.Cell T) T
      pointer.invariant.Safe pointer.invariant.Safe)
    [meaning : RustModel T]
    [_firstLaw : TraitLaws.transmute_from T (_root_.core.cell.UnsafeCell T)
      pointer.invariant.Safe pointer.invariant.Safe first]
    [_secondLaw : TraitLaws.transmute_from (_root_.core.cell.Cell T) T
      pointer.invariant.Safe pointer.invariant.Safe second] :
    TraitLaws.transmute_from (_root_.core.cell.Cell T) (_root_.core.cell.UnsafeCell T)
      pointer.invariant.Safe pointer.invariant.Safe
      (Zerocopy.core.cell.Cell.Insts.ZerocopyPointerTransmuteTransmuteFromUnsafeCellSafeSafe
        first second) :=
  ⟨Referent.safe_transfer_of_implication (_root_.core.cell.UnsafeCell T) (_root_.core.cell.Cell T)
    (fun bytes admitted => (Referent.safeBytes_cell_iff T bytes).mpr
      ((Referent.safeBytes_unsafeCell_iff T bytes).mp admitted))⟩

@[instance] theorem pointer.invariant.CastableFromDTSTUninitUninit.Blanket_law (ST DT : Type) :
    TraitLaws.castable_from DT ST pointer.invariant.Uninit pointer.invariant.Uninit
      (Zerocopy.pointer.invariant.CastableFromDTSTUninitUninit.Blanket ST DT) :=
  ⟨Or.inl ⟨rfl, rfl⟩⟩

@[instance] theorem pointer.invariant.CastableFromDTSTInitializedInitialized.Blanket_law
    (ST DT : Type) :
    TraitLaws.castable_from DT ST pointer.invariant.Initialized pointer.invariant.Initialized
      (Zerocopy.pointer.invariant.CastableFromDTSTInitializedInitialized.Blanket ST DT) :=
  ⟨Or.inr ⟨rfl, rfl⟩⟩

-- These empty Rust bodies still receive their exact dictionary laws. The
-- specification also checks admission of the successful Unit result.

theorem require_transfer_spec : Specs.require_transfer_spec := by
  intro Src Dst SV DV dictionary
  intros
  simp only [pointer.referent_checks.require_transfer, WP.spec_ok]
  exact ⟨(), rfl,
    @TraitLaws.transmute_from.holds Dst Src SV DV dictionary _ _ _ _ inferInstance⟩

theorem require_type_independent_spec : Specs.require_type_independent_spec := by
  intro Src Dst SV DV dictionary
  intros
  simp only [pointer.referent_checks.require_type_independent, WP.spec_ok]
  exact ⟨(), rfl, @TraitLaws.castable_from.holds Dst Src SV DV dictionary inferInstance⟩

theorem compose_safe_transfers_spec : Specs.compose_safe_transfers_spec := by
  intro Src Mid Dst first second
  intros
  simp only [pointer.referent_checks.compose_safe_transfers, WP.spec_ok]
  refine ⟨(), rfl, Referent.safe_trans Src Mid Dst ?_ ?_ (by assumption)⟩
  · exact @TraitLaws.transmute_from.holds Mid Src pointer.invariant.Safe pointer.invariant.Safe
      first _ _ _ _ inferInstance
  · exact @TraitLaws.transmute_from.holds Dst Mid pointer.invariant.Safe pointer.invariant.Safe
      second _ _ _ _ inferInstance

theorem concrete_transfers_spec : Specs.concrete_transfers_spec := by
  simp only [Specs.concrete_transfers_spec, pointer.referent_checks.concrete_transfers,
    pointer.referent_checks.require_transfer, pointer.referent_checks.require_type_independent,
    bind_ok, WP.spec_ok]
  refine ⟨(), rfl, ?_, ?_, ?_⟩
  · exact Referent.safe_to_initialized Bool U8 Rust.Storage.boolDecoder_initialized
  · exact Referent.forget U8 Bool pointer.invariant.Initialized ⟨.initialized, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

end Zerocopy.Proofs
