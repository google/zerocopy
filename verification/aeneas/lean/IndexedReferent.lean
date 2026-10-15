/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import RustModel
public import Rust.Referent
@[expose] public section

/-!
This adapter compares byte domains at two explicit metadata values. Each view
retains the provider's sole installed physical profile; its metadata type,
equality test and decoder are projections of that profile. Width equality does
not identify metadata, even for zero-sized referents.

These are numeric storage implications. They do not interpret native pointer
execution and do not replace the existing type-level TransmuteFrom contract.
-/

open Rust.Storage
namespace AeneasSpecs
namespace PhysicalStorage

def Metadata : PhysicalStorage Raw → Type
  | .fixed _ => Unit
  | .indexed metadata _ _ => metadata

def metadataEquality : (physical : PhysicalStorage Raw) → DecidableEq physical.Metadata
  | .fixed _ => by change DecidableEq Unit; infer_instance
  | .indexed _ equality _ => equality

def decoder : (physical : PhysicalStorage Raw) → StorageDecoder physical.Metadata Raw
  | .fixed decoder => decoder.asStorageDecoder
  | .indexed _ _ decoder => decoder

/-- Mapping a wrapper preserves the child's metadata type and values. -/
def mapMetadata (physical : PhysicalStorage A) (wrap : A → B) (unwrap : B → A)
    (inverse : ∀ raw, unwrap (wrap raw) = raw) :
    physical.Metadata → (physical.map wrap unwrap inverse).Metadata := by
  cases physical <;> exact id

theorem map_metadata (physical : PhysicalStorage A) (wrap : A → B) (unwrap : B → A)
    (inverse : ∀ raw, unwrap (wrap raw) = raw) (raw : A) :
    (physical.map wrap unwrap inverse).decoder.metadata (wrap raw) =
      physical.mapMetadata wrap unwrap inverse (physical.decoder.metadata raw) := by
  cases physical with
  | fixed decoder => rfl
  | indexed metadata equality decoder =>
    change decoder.metadata (unwrap (wrap raw)) = decoder.metadata raw
    rw [inverse]

theorem map_width (physical : PhysicalStorage A) (wrap : A → B) (unwrap : B → A)
    (inverse : ∀ raw, unwrap (wrap raw) = raw) (metadata : physical.Metadata) :
    (physical.map wrap unwrap inverse).decoder.byteSize
      (physical.mapMetadata wrap unwrap inverse metadata) = physical.decoder.byteSize metadata := by
  cases physical <;> rfl

end PhysicalStorage

namespace IndexedReferent

/-- Naming storage requires evidence that this exact provider installed it. -/
structure StorageView {Raw : Type u} (meaning : RustModel Raw) where
  physical : PhysicalStorage Raw
  installed : meaning.storage = some physical

namespace StorageView

abbrev Metadata {meaning : RustModel Raw} (view : StorageView meaning) :=
  view.physical.Metadata

instance {meaning : RustModel Raw} (view : StorageView meaning) : DecidableEq view.Metadata :=
  view.physical.metadataEquality

def decoder {meaning : RustModel Raw} (view : StorageView meaning) :
    StorageDecoder view.Metadata Raw := view.physical.decoder

theorem initialized {meaning : RustModel Raw} (view : StorageView meaning)
    (law : @RustModel.initializedRepresentation Raw meaning) : view.decoder.Initialized := by
  rcases view with ⟨physical, installed⟩
  have physicalLaw : physical.Initialized := by
    simpa only [RustModel.initializedRepresentation, installed] using law
  cases physical with
  | fixed decoder =>
    exact decoder.asStorageDecoder_initialized physicalLaw
  | indexed metadata equality decoder => exact physicalLaw

/-- Unsupported storage cannot be repaired by choosing a decoder in a view. -/
theorem absent {meaning : RustModel Raw} (missing : meaning.storage = none) :
    ¬ Nonempty (StorageView meaning) := by
  rintro ⟨view⟩
  have installed := view.installed
  rw [missing] at installed
  contradiction

end StorageView

def safeAt {meaning : RustModel Raw} (view : StorageView meaning)
    (metadata : view.Metadata) (bytes : List AMByte) : Prop :=
  Rust.Referent.Safe view.decoder meaning.decode metadata bytes

def transferAt {source : RustModel Src} {destination : RustModel Dst}
    (sourceView : StorageView source) (sourceMetadata : sourceView.Metadata)
    (destinationView : StorageView destination) (destinationMetadata : destinationView.Metadata)
    (sourceState destinationState : Rust.Referent.State) : Prop :=
  Rust.Referent.Transfer (sourceView.decoder.byteSize sourceMetadata)
    (safeAt sourceView sourceMetadata) sourceState
    (destinationView.decoder.byteSize destinationMetadata)
    (safeAt destinationView destinationMetadata) destinationState

theorem safe_to_initialized {source : RustModel Src} {destination : RustModel Dst}
    (sourceView : StorageView source) (sm : sourceView.Metadata)
    (destinationView : StorageView destination) (dm : destinationView.Metadata)
    (law : sourceView.decoder.Initialized) :
    transferAt sourceView sm destinationView dm .safe .initialized :=
  Rust.Referent.safe_to_initialized _ source.decode law sm _ _

theorem initialized_to_safe {source : RustModel Src} {destination : RustModel Dst}
    (sourceView : StorageView source) (sm : sourceView.Metadata)
    (destinationView : StorageView destination) (dm : destinationView.Metadata)
    (law : destinationView.decoder.CompleteWith destination.decode) :
    transferAt sourceView sm destinationView dm .initialized .safe :=
  Rust.Referent.initialized_to_safe _ destination.decode law dm _ _

/-- A local completeness proof need cover only this destination metadata. -/
theorem initialized_to_safe_at {source : RustModel Src} {destination : RustModel Dst}
    (sourceView : StorageView source) (sm : sourceView.Metadata)
    (destinationView : StorageView destination) (dm : destinationView.Metadata)
    (law : ∀ bytes, bytes.length = destinationView.decoder.byteSize dm →
      Rust.Storage.Initialized bytes → safeAt destinationView dm bytes) :
    transferAt sourceView sm destinationView dm .initialized .safe := by
  intro width bytes admitted
  exact ⟨admitted.1.trans width, law bytes (admitted.1.trans width) admitted.2⟩

/-- The same middle view and metadata occur in both premises. A width guard
cannot silently substitute a different zero-sized referent count. -/
theorem transfer_trans {source : RustModel Src} {middle : RustModel Mid}
    {destination : RustModel Dst}
    (sourceView : StorageView source) (sm : sourceView.Metadata)
    (middleView : StorageView middle) (mm : middleView.Metadata)
    (destinationView : StorageView destination) (dm : destinationView.Metadata)
    (firstState middleState lastState : Rust.Referent.State)
    (first : transferAt sourceView sm middleView mm firstState middleState)
    (second : transferAt middleView mm destinationView dm middleState lastState)
    (width : sourceView.decoder.byteSize sm = middleView.decoder.byteSize mm) :
    transferAt sourceView sm destinationView dm firstState lastState :=
  Rust.Referent.transfer_trans _ _ _ _ _ _ _ _ _ first second width

end IndexedReferent
end AeneasSpecs
