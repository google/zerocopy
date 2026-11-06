import AnnealResearch.DeadData
import AnnealResearch.MemoryInvariants

/-!
Owned controls for dead-allocation content normalization. All positive operation
equations use the existing factored raw-memory kernel and the normalizer.
Dead means explicitly freed in this API, not merely a consumed Rust Drop
obligation. There is no physical-space, physical-secret-erasure, or Rust
post-Drop-access claim.

Normalization itself preserves the existing structural StateWF predicate.
Same alone does not transport it: an ignored dead byte can contain a forged
fragment ID. The explicit counterexample below retains that distinction.
No structural theorem assumes or establishes NoUB.
-/

namespace AnnealResearch.DeadDataControls

open MiniRustReference (Byte Ptr Kind UB Result)

namespace Admission

theorem source_lookup (state : MiniRustFactored.State) (id : Nat)
    (metadata : MiniRustFactored.Metadata) (found : state.metadata id = some metadata) :
    (MiniRustFactored.reify state).allocations id =
      some (MiniRustFactored.materialize metadata (state.cells id)) := by
  rw [MiniRustFactored.reify_lookup, found]
  rfl

theorem normalized_lookup (state : MiniRustFactored.State) (id : Nat)
    (metadata : MiniRustFactored.Metadata) (found : state.metadata id = some metadata) :
    (MiniRustFactored.reify (DeadData.normalize state)).allocations id =
      some (MiniRustFactored.materialize metadata ((DeadData.normalize state).cells id)) := by
  change (state.metadata id).map
    (fun metadata => MiniRustFactored.materialize metadata ((DeadData.normalize state).cells id)) = _
  rw [found]
  rfl

theorem normalized_record {state : MiniRustFactored.State} {id : Nat}
    {allocation : MiniRustReference.Allocation}
    (found : (MiniRustFactored.reify (DeadData.normalize state)).allocations id = some allocation) :
    ∃ metadata, state.metadata id = some metadata ∧
      allocation = MiniRustFactored.materialize metadata ((DeadData.normalize state).cells id) := by
  cases selected : state.metadata id with
  | none =>
      have absent : (MiniRustFactored.reify (DeadData.normalize state)).allocations id = none := by
        change (state.metadata id).map _ = none
        rw [selected]
        rfl
      rw [absent] at found
      cases found
  | some metadata =>
      exact ⟨metadata, rfl,
        (Option.some.inj ((normalized_lookup state id metadata selected).symm.trans found)).symm⟩

/-- Forward admission for this normalizer, not arbitrary Same-related states.
The dead-byte branch becomes Uninit, which is structurally admitted. -/
theorem normalize_preserves_StateWF (state : MiniRustFactored.State)
    (wf : MiniRustReference.StateWF (MiniRustFactored.reify state)) :
    MiniRustReference.StateWF (MiniRustFactored.reify (DeadData.normalize state)) := by
  constructor
  · intro id
    constructor
    · rintro ⟨allocation, found⟩
      obtain ⟨metadata, selected, _⟩ := normalized_record found
      exact (wf.domain id).1
        ⟨MiniRustFactored.materialize metadata (state.cells id), source_lookup state id metadata selected⟩
    · intro minted
      obtain ⟨allocation, found⟩ := (wf.domain id).2 minted
      cases selected : state.metadata id with
      | none => simp [MiniRustFactored.reify, selected] at found
      | some metadata =>
          exact ⟨MiniRustFactored.materialize metadata ((DeadData.normalize state).cells id),
            normalized_lookup state id metadata selected⟩
  · intro id allocation found
    obtain ⟨metadata, selected, same⟩ := normalized_record found
    rw [same]
    exact wf.geometry id (MiniRustFactored.materialize metadata (state.cells id))
      (source_lookup state id metadata selected)
  · intro id allocation offset found inside
    obtain ⟨metadata, selected, same⟩ := normalized_record found
    rw [same] at inside ⊢
    change MiniRustReference.ByteWF (MiniRustFactored.reify (DeadData.normalize state))
      ((DeadData.normalize state).cells id offset)
    by_cases dead : metadata.live = false
    · rw [DeadData.normalize_dead_cell state id metadata selected dead offset]
      exact True.intro
    · have unchanged : (DeadData.normalize state).cells id offset = state.cells id offset := by
        simp [DeadData.normalize, selected, dead]
      rw [unchanged]
      have known := wf.knownFragments id
        (MiniRustFactored.materialize metadata (state.cells id)) offset
        (source_lookup state id metadata selected) inside
      exact MiniRustReference.byteWF_mono (Nat.le_refl _) known
  · intro id first otherId second firstFound secondFound different firstLive secondLive
    obtain ⟨metadata, selected, firstEq⟩ := normalized_record firstFound
    obtain ⟨otherMetadata, otherSelected, secondEq⟩ := normalized_record secondFound
    have sourceFirstLive : (MiniRustFactored.materialize metadata (state.cells id)).live = true := by
      simpa only [firstEq, MiniRustFactored.materialize] using firstLive
    have sourceSecondLive : (MiniRustFactored.materialize otherMetadata (state.cells otherId)).live = true := by
      simpa only [secondEq, MiniRustFactored.materialize] using secondLive
    have separate := wf.liveSeparation id (MiniRustFactored.materialize metadata (state.cells id))
      otherId (MiniRustFactored.materialize otherMetadata (state.cells otherId))
      (source_lookup state id metadata selected) (source_lookup state otherId otherMetadata otherSelected)
      different sourceFirstLive sourceSecondLive
    simpa only [firstEq, secondEq, MiniRustFactored.materialize, MiniRustReference.overlaps] using separate

theorem numeric_singleton_WF (memory : MiniRustReference.State) (value : Fin 256) :
    MiniRustReference.BytesWF memory [Byte.init value none] := by
  intro index inside
  have zero : index = 0 := by
    simp only [List.length_singleton] at inside
    omega
  subst index
  exact True.intro

end Admission

namespace Concrete

def seven : Byte := .init 7 none
def nine : Byte := .init 9 none
def liveMetadata : MiniRustFactored.Metadata := ⟨8, 1, 8, .heap, true⟩
def deadMetadata : MiniRustFactored.Metadata := ⟨8, 1, 8, .heap, false⟩
def stale : Ptr := ⟨8, some 0⟩
def fresh : Ptr := ⟨8, some 1⟩

def allocated0 : MiniRustFactored.State := MiniRustFactored.append MiniRustFactored.empty liveMetadata
def stored0 : MiniRustFactored.State := MiniRustFactored.writeCells allocated0 0 0 [seven]
def freed0 : MiniRustFactored.State := MiniRustFactored.setMetadata stored0 0 deadMetadata
def cleared : MiniRustFactored.State := DeadData.normalize freed0
def allocated1 : MiniRustFactored.State := MiniRustFactored.append cleared liveMetadata
def stored1 : MiniRustFactored.State := MiniRustFactored.writeCells allocated1 1 0 [nine]

theorem allocation_step :
    MiniRustFactored.allocateAt MiniRustFactored.empty .heap 1 8 8 = .ok (stale, allocated0) := rfl

theorem live_store_step : MiniRustFactored.store allocated0 stale [seven] 8 = .ok stored0 := rfl

theorem live_raw_roundtrip : MiniRustFactored.load stored0 stale 1 8 = .ok ([seven], stored0) := rfl

theorem free_step : MiniRustFactored.free stored0 stale .heap 1 8 = .ok freed0 := rfl

theorem genuinely_erases_nonzero_dead_byte :
    freed0.cells 0 0 = seven ∧ cleared.cells 0 0 = .uninit ∧
    freed0.cells 0 0 ≠ cleared.cells 0 0 := ⟨rfl, rfl, by decide⟩

theorem identity_and_tombstone_retained :
    cleared.next = 1 ∧ cleared.metadata = freed0.metadata ∧
    cleared.metadata 0 = some deadMetadata := ⟨rfl, rfl, rfl⟩

theorem erased_state_is_Same : DeadData.Same freed0 cleared := DeadData.normalize_same freed0

theorem fresh_id_address_reuse :
    MiniRustFactored.allocateAt cleared .heap 1 8 8 = .ok (fresh, allocated1) ∧
    fresh.addr = stale.addr ∧ fresh.provenance ≠ stale.provenance ∧ allocated1.next = 2 :=
  ⟨rfl, rfl, by decide, rfl⟩

theorem replacement_store_step : MiniRustFactored.store allocated1 fresh [nine] 8 = .ok stored1 := rfl

theorem replacement_raw_roundtrip : MiniRustFactored.load stored1 fresh 1 8 = .ok ([nine], stored1) := rfl

theorem normalized_replacement_roundtrip :
    DeadData.load stored1 fresh 1 8 = .ok ([nine], DeadData.normalize stored1) := rfl

theorem stale_positive_load_remains_UB :
    MiniRustFactored.load cleared stale 1 8 = .ub .dead ∧
    MiniRustFactored.load stored1 stale 1 8 = .ub .dead ∧
    DeadData.load stored1 stale 1 8 = .ub .dead := ⟨rfl, rfl, rfl⟩

theorem aligned_zero_length :
    MiniRustFactored.load MiniRustFactored.empty ⟨0, none⟩ 0 8 =
      .ok ([], MiniRustFactored.empty) ∧
    MiniRustFactored.load cleared stale 0 8 = .ok ([], cleared) ∧
    MiniRustFactored.store cleared stale [] 8 = .ok cleared := ⟨rfl, rfl, rfl⟩

theorem alignment_precedes_zero_length :
    MiniRustFactored.load cleared ⟨9, some 0⟩ 0 8 = .ub .misalignedLoad ∧
    MiniRustFactored.store cleared ⟨9, some 0⟩ [] 8 = .ub .misalignedStore ∧
    DeadData.load cleared ⟨9, some 0⟩ 0 8 = .ub .misalignedLoad := ⟨rfl, rfl, rfl⟩

theorem allocated0_WF : MemoryInvariants.targetWF allocated0 :=
  MemoryInvariants.target_allocateAt_preserves_WF MemoryInvariants.empty_targetWF
    (show MiniRustReference.AlignWF 8 from ⟨3, rfl⟩) allocation_step

theorem stored0_WF : MemoryInvariants.targetWF stored0 :=
  MemoryInvariants.target_store_preserves_WF allocated0_WF
    (Admission.numeric_singleton_WF _ 7) live_store_step

theorem freed0_WF : MemoryInvariants.targetWF freed0 :=
  MemoryInvariants.target_free_preserves_WF stored0_WF free_step

theorem cleared_WF : MemoryInvariants.targetWF cleared :=
  Admission.normalize_preserves_StateWF freed0 freed0_WF

theorem allocated1_WF : MemoryInvariants.targetWF allocated1 :=
  MemoryInvariants.target_allocateAt_preserves_WF cleared_WF
    (show MiniRustReference.AlignWF 8 from ⟨3, rfl⟩) fresh_id_address_reuse.1

theorem stored1_WF : MemoryInvariants.targetWF stored1 :=
  MemoryInvariants.target_store_preserves_WF allocated1_WF
    (Admission.numeric_singleton_WF _ 9) replacement_store_step

/-- Structural admission retains a dangling positive-size pointer's UB. -/
theorem admitted_stale_pointer :
    MiniRustReference.PtrWF (MiniRustFactored.reify cleared) stale ∧
    MiniRustFactored.load cleared stale 1 8 = .ub .dead := by
  refine ⟨?_, rfl⟩
  change 8 < MiniRustReference.addressLimit ∧ 0 < 1
  exact ⟨by decide, by decide⟩

end Concrete

namespace Negative

open Concrete

def erasedLive : MiniRustFactored.State := MiniRustFactored.writeCells stored0 0 0 [.uninit]

theorem live_erasure_changes_raw_reply :
    MiniRustFactored.load stored0 stale 1 8 = .ok ([seven], stored0) ∧
    MiniRustFactored.load erasedLive stale 1 8 = .ok ([.uninit], erasedLive) := ⟨rfl, rfl⟩

theorem live_erasure_not_Same : ¬ DeadData.Same stored0 erasedLive := by
  intro same
  have changed := same.live_cells 0 liveMetadata rfl rfl 0
  change seven = Byte.uninit at changed
  cases changed

def deletedTombstone : MiniRustFactored.State :=
  ⟨cleared.next, (fun id => if id = 0 then none else cleared.metadata id), cleared.cells⟩

theorem tombstone_deletion_changes_failure :
    MiniRustFactored.load cleared stale 1 8 = .ub .dead ∧
    MiniRustFactored.load deletedTombstone stale 1 8 = .unsupported := ⟨rfl, rfl⟩

theorem tombstone_deletion_not_Same : ¬ DeadData.Same cleared deletedTombstone := by
  intro same
  have changed := congrFun same.metadata_eq 0
  change some deadMetadata = none at changed
  cases changed

theorem cleared_has_no_live_metadata (id : Nat) (metadata : MiniRustFactored.Metadata)
    (found : cleared.metadata id = some metadata) : metadata.live = false := by
  by_cases zero : id = 0
  · subst id
    change some deadMetadata = some metadata at found
    have same := Option.some.inj found
    cases same
    rfl
  · have missing : cleared.metadata id = none := by
      simp [cleared, DeadData.normalize, freed0, MiniRustFactored.setMetadata,
        stored0, MiniRustFactored.writeCells, allocated0, MiniRustFactored.append,
        MiniRustFactored.empty, zero]
    rw [missing] at found
    cases found

/-- Same ignores the dead byte, while StateWF still constrains its fragment ID. -/
def forgedDeadFragment : MiniRustFactored.State :=
  ⟨cleared.next, cleared.metadata,
    fun id offset => if id = 0 ∧ offset = 0 then .init 5 (some ⟨1, 0⟩)
      else cleared.cells id offset⟩

theorem forged_dead_still_Same : DeadData.Same cleared forgedDeadFragment := by
  refine ⟨rfl, rfl, ?_⟩
  intro id metadata found live offset
  have dead := cleared_has_no_live_metadata id metadata found
  rw [dead] at live
  cases live

theorem forged_dead_not_StateWF : ¬ MemoryInvariants.targetWF forgedDeadFragment := by
  intro wf
  have found : (MiniRustFactored.reify forgedDeadFragment).allocations 0 =
      some (MiniRustFactored.materialize deadMetadata (forgedDeadFragment.cells 0)) :=
    Admission.source_lookup forgedDeadFragment 0 deadMetadata rfl
  have known := wf.knownFragments 0
    (MiniRustFactored.materialize deadMetadata (forgedDeadFragment.cells 0)) 0 found (by decide)
  change 1 < 1 at known
  omega

theorem Same_does_not_transport_StateWF :
    MemoryInvariants.targetWF cleared ∧ DeadData.Same cleared forgedDeadFragment ∧
    ¬ MemoryInvariants.targetWF forgedDeadFragment :=
  ⟨cleared_WF, forged_dead_still_Same, forged_dead_not_StateWF⟩

end Negative

namespace AllocatorBoundary

/-- Same argument as the existing admitted address-limit alignment control,
instantiated for this identical factored allocation-candidate condition. -/
theorem no_candidate_at_address_limit (state : MiniRustFactored.State) (size address : Nat) :
    ¬ MiniRustFactored.AllocationCandidate state size MiniRustReference.addressLimit address := by
  rintro ⟨positive, aligned, bounded, _⟩
  have below : address < MiniRustReference.addressLimit := by omega
  rw [Nat.mod_eq_of_lt below] at aligned
  omega

theorem impossible_alignment_is_admitted : MiniRustReference.AlignWF MiniRustReference.addressLimit :=
  ⟨64, rfl⟩

/-- Every candidate is absent; this is not an OOM or UB outcome. -/
theorem absent_allocator_candidate (address : Nat) :
    MiniRustFactored.allocateAt MiniRustFactored.empty .heap 0 MiniRustReference.addressLimit address =
      .noChoice := by
  simp only [MiniRustFactored.allocateAt,
    ite_eq_right (show ¬ MiniRustReference.sizeLimit ≤ 0 by decide),
    ite_eq_right (show MiniRustReference.addressLimit ≠ 0 by decide),
    ite_eq_right (no_candidate_at_address_limit MiniRustFactored.empty 0 address)]

theorem normalized_allocator_choice_is_still_absent (address : Nat) :
    DeadData.allocateAt MiniRustFactored.empty .heap 0 MiniRustReference.addressLimit address = .noChoice := by
  rw [DeadData.allocateAt, absent_allocator_candidate]
  rfl

end AllocatorBoundary

#print axioms Admission.normalize_preserves_StateWF
#print axioms Concrete.allocation_step
#print axioms Concrete.live_store_step
#print axioms Concrete.live_raw_roundtrip
#print axioms Concrete.free_step
#print axioms Concrete.genuinely_erases_nonzero_dead_byte
#print axioms Concrete.identity_and_tombstone_retained
#print axioms Concrete.erased_state_is_Same
#print axioms Concrete.fresh_id_address_reuse
#print axioms Concrete.replacement_store_step
#print axioms Concrete.replacement_raw_roundtrip
#print axioms Concrete.normalized_replacement_roundtrip
#print axioms Concrete.stale_positive_load_remains_UB
#print axioms Concrete.aligned_zero_length
#print axioms Concrete.alignment_precedes_zero_length
#print axioms Concrete.allocated0_WF
#print axioms Concrete.stored0_WF
#print axioms Concrete.freed0_WF
#print axioms Concrete.cleared_WF
#print axioms Concrete.allocated1_WF
#print axioms Concrete.stored1_WF
#print axioms Concrete.admitted_stale_pointer
#print axioms Negative.live_erasure_changes_raw_reply
#print axioms Negative.live_erasure_not_Same
#print axioms Negative.tombstone_deletion_changes_failure
#print axioms Negative.tombstone_deletion_not_Same
#print axioms Negative.forged_dead_still_Same
#print axioms Negative.forged_dead_not_StateWF
#print axioms Negative.Same_does_not_transport_StateWF
#print axioms AllocatorBoundary.no_candidate_at_address_limit
#print axioms AllocatorBoundary.impossible_alignment_is_admitted
#print axioms AllocatorBoundary.absent_allocator_candidate
#print axioms AllocatorBoundary.normalized_allocator_choice_is_still_absent

end AnnealResearch.DeadDataControls
