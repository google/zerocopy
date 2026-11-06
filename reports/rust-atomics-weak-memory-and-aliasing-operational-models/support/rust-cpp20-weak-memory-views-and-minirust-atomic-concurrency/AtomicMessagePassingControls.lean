import AnnealResearch.AtomicMessagePassing

/-!
Concrete controls for the owned, selected six-event interface. Raw memory is a
fixed initialized validity snapshot; graph initialization/publication and valid
atomic-reference/permission/target premises remain separate. The classifier is
mathematical and noncomputable. No source/hardware adequacy or NoUB claim.
-/
namespace AnnealResearch.AtomicMessagePassingControls

open AtomicMessagePassing

/-- Inversion of an actual classifier observation, with no extra admission. -/
theorem observed_sound (state : MiniRustReference.State) (handles : Handles)
    (mode : Mode) (rf : RF) (locations : Locations) (values : Nat × Nat)
    (observed : runCandidate state handles mode rf = .observed locations values) :
    flagValue rf = 1 ∧ gates state handles = .ok locations ∧ Shape locations ∧
      SelectedRules locations mode rf ∧ values = returned rf := by
  classical
  by_cases branch : flagValue rf = 1
  · cases checked : gates state handles with
    | ub event diagnostic => simp [runCandidate, branch, checked] at observed
    | unsupported event => simp [runCandidate, branch, checked] at observed
    | noChoice event => simp [runCandidate, branch, checked] at observed
    | ok actual =>
        by_cases geometry : Shape actual
        · by_cases admitted : SelectedRules actual mode rf
          · have same : actual = locations ∧ returned rf = values := by
              simpa [runCandidate, branch, checked, geometry, admitted] using observed
            rcases same with ⟨rfl, rfl⟩
            exact ⟨branch, rfl, geometry, admitted, rfl⟩
          · simp [runCandidate, branch, checked, geometry, admitted] at observed
        · simp [runCandidate, branch, checked, geometry] at observed
  · simp [runCandidate, branch] at observed

/-- The generic RA claim applies directly to actual classifier results. -/
theorem ra_observed_values (state : MiniRustReference.State) (handles : Handles)
    (rf : RF) (locations : Locations) (values : Nat × Nat)
    (observed : runCandidate state handles .releaseAcquire rf = .observed locations values) :
    values = (1, 1) := by
  obtain ⟨one, _checked, geometry, rules, bound⟩ :=
    observed_sound state handles .releaseAcquire rf locations values observed
  have dataOne := ra_flag_one_data_one locations geometry rf rules one
  rw [bound]
  simp [returned, one, dataOne]

theorem ra_no_observed_stale (state : MiniRustReference.State) (handles : Handles)
    (rf : RF) (locations : Locations) :
    runCandidate state handles .releaseAcquire rf ≠ .observed locations (1, 0) := by
  intro observed
  have impossible := ra_observed_values state handles rf locations (1, 0) observed
  simp at impossible

def zeroByte : MiniRustReference.Byte := .init 0 none
def zeroBytes : List MiniRustReference.Byte := [zeroByte, zeroByte]

def block (base : Nat) (live : Bool) : MiniRustReference.Allocation :=
  { base := base
    size := 2
    align := 2
    kind := .global
    live := live
    data := fun _ => zeroByte }

/-- Complete independent snapshot maps, including the retained dead record. -/
def raw (dataLive : Bool) : MiniRustReference.State :=
  { next := 2
    allocations := fun id =>
      if id = 0 then some (block 16 dataLive)
      else if id = 1 then some (block 32 true)
      else none }

def initial : MiniRustReference.State := raw true
def deadData : MiniRustReference.State := raw false
def dataPointer : MiniRustReference.Ptr := ⟨16, some 0⟩
def flagPointer : MiniRustReference.Ptr := ⟨32, some 1⟩

def handles : Handles :=
  ⟨⟨dataPointer, 0⟩, ⟨flagPointer, 1⟩, ⟨flagPointer, 2⟩, ⟨dataPointer, 3⟩⟩

def dataSpan : Span := ⟨0, 0, 2⟩
def flagSpan : Span := ⟨1, 0, 2⟩
def locations : Locations := ⟨dataSpan, flagSpan, flagSpan, dataSpan⟩

private theorem initial_records (id : Nat) (allocation : MiniRustReference.Allocation)
    (found : initial.allocations id = some allocation) :
    (id = 0 ∧ allocation = block 16 true) ∨ (id = 1 ∧ allocation = block 32 true) := by
  by_cases zero : id = 0
  · subst id
    have same : block 16 true = allocation := by simpa [initial, raw] using found
    exact Or.inl ⟨rfl, same.symm⟩
  · by_cases one : id = 1
    · subst id
      have same : block 32 true = allocation := by simpa [initial, raw] using found
      exact Or.inr ⟨rfl, same.symm⟩
    · simp [initial, raw, zero, one] at found

theorem initial_StateWF : MiniRustReference.StateWF initial := by
  constructor
  · intro id
    by_cases zero : id = 0
    · subst id; simp [initial, raw]
    · by_cases one : id = 1
      · subst id; simp [initial, raw]
      · constructor
        · rintro ⟨allocation, found⟩
          simp [initial, raw, zero, one] at found
        · intro below
          change id < 2 at below
          omega
  · intro id allocation found
    rcases initial_records id allocation found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      exact ⟨by decide, ⟨1, rfl⟩, by decide, by decide, by decide⟩
  · intro id allocation offset found _inside
    rcases initial_records id allocation found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp [block, zeroByte, MiniRustReference.ByteWF]
  · intro id first other second found otherFound different _firstLive _secondLive
    rcases initial_records id first found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases initial_records other second otherFound with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact False.elim (different rfl)
      · simp [MiniRustReference.overlaps, block]
    · rcases initial_records other second otherFound with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [MiniRustReference.overlaps, block]
      · exact False.elim (different rfl)

theorem initial_operand_admission :
    MiniRustReference.PtrWF initial dataPointer ∧
    MiniRustReference.PtrWF initial flagPointer ∧ MiniRustReference.AlignWF 2 := by
  refine ⟨?_, ?_, ⟨1, rfl⟩⟩
  · change (16 : Nat) < MiniRustReference.addressLimit ∧ (0 : Nat) < 2
    exact ⟨by decide, by decide⟩
  · change (32 : Nat) < MiniRustReference.addressLimit ∧ (1 : Nat) < 2
    exact ⟨by decide, by decide⟩

theorem initial_initialized (id : Nat) (allocation : MiniRustReference.Allocation)
    (found : initial.allocations id = some allocation) (offset : Nat) :
    allocation.data offset = zeroByte := by
  rcases initial_records id allocation found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem selected_shape : Shape locations := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro same
    have ids := congrArg Span.allocation same
    change (0 : Nat) = 1 at ids
    omega
  · exact Or.inl (by decide)

/-- Actual raw bytes are zero although the RA atomic result below is (1,1). -/
theorem actual_raw_zero_loads :
    MiniRustReference.load initial dataPointer 2 2 = .ok (zeroBytes, initial) ∧
    MiniRustReference.load initial flagPointer 2 2 = .ok (zeroBytes, initial) := by
  exact ⟨rfl, rfl⟩

theorem actual_positive_gates :
    writeGate initial handles.dataStore = .ok dataSpan ∧
    writeGate initial handles.flagStore = .ok flagSpan ∧
    readGate initial handles.flagLoad = .ok flagSpan ∧
    readGate initial handles.dataLoad = .ok dataSpan ∧
    gates initial handles = .ok locations := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem actual_ra : runCandidate initial handles .releaseAcquire bothStores =
    .observed locations (1, 1) := by
  exact run_candidate_observed initial handles .releaseAcquire bothStores locations rfl
    actual_positive_gates.2.2.2.2 selected_shape
    (both_stores_rules locations selected_shape .releaseAcquire)

theorem actual_relaxed_stale : runCandidate initial handles .relaxed staleData =
    .observed locations (1, 0) := by
  exact run_candidate_observed initial handles .relaxed staleData locations rfl
    actual_positive_gates.2.2.2.2 selected_shape
    (relaxed_stale_rules locations selected_shape)

def wrongSupplier : RF := ⟨.dataStore, .dataStore⟩

theorem wrong_supplier_same_values : returned wrongSupplier = returned bothStores := by
  rfl

theorem wrong_supplier_not_valid : ¬ RFValid locations wrongSupplier := by
  intro valid
  exact selected_shape.separate valid.flagLocation

theorem wrong_supplier_not_rules (mode : Mode) : ¬ SelectedRules locations mode wrongSupplier := by
  intro rules
  exact wrong_supplier_not_valid rules.suppliers

theorem actual_wrong_supplier (mode : Mode) :
    runCandidate initial handles mode wrongSupplier = .inconsistent locations := by
  have one : flagValue wrongSupplier = 1 := rfl
  simp [runCandidate, one, actual_positive_gates.2.2.2.2, selected_shape,
    wrong_supplier_not_rules mode]

def dataAlias : Handle := ⟨MiniRustReference.wrappingOffset dataPointer 0, 77⟩
def aliasHandles : Handles := { handles with dataLoad := dataAlias }

theorem alias_pointer : dataAlias.pointer = dataPointer := by
  decide

theorem alias_handle_distinct : dataAlias ≠ handles.dataLoad := by
  intro same
  have labels := congrArg Handle.label same
  change (77 : Nat) = 3 at labels
  omega

theorem alias_actual_location : readGate initial dataAlias = .ok dataSpan := by
  change readGate initial ⟨MiniRustReference.wrappingOffset dataPointer 0, 77⟩ = .ok dataSpan
  have pointer : MiniRustReference.wrappingOffset dataPointer 0 = dataPointer := alias_pointer
  rw [pointer]
  rfl

theorem alias_actual_gates : gates initial aliasHandles = .ok locations := by
  simp only [gates, aliasHandles, bindGate, atEvent,
    actual_positive_gates.1, actual_positive_gates.2.1,
    actual_positive_gates.2.2.1, alias_actual_location, locations]

/-- The actual alias resolves to the same complete profile; every RF/mode uses
the identical selected graph predicates and mathematical classifier thereafter. -/
theorem alias_substitution (mode : Mode) (rf : RF) :
    gates initial aliasHandles = gates initial handles ∧
    runCandidate initial aliasHandles mode rf = runCandidate initial handles mode rf := by
  refine ⟨?_, ?_⟩
  · rw [alias_actual_gates, actual_positive_gates.2.2.2.2]
  · simp only [runCandidate, alias_actual_gates, actual_positive_gates.2.2.2.2]

theorem alias_rules_substitution (mode : Mode) (rf : RF) (original aliased : Locations)
    (first : gates initial handles = .ok original)
    (second : gates initial aliasHandles = .ok aliased) :
    SelectedRules original mode rf ↔ SelectedRules aliased mode rf := by
  have same : original = aliased := Gate.ok.inj
    (first.symm.trans ((alias_substitution mode rf).1.symm.trans second))
  cases same
  exact Iff.rfl

theorem alias_selected_graph (mode : Mode) :
    ∃ resolved, gates initial aliasHandles = .ok resolved ∧ resolved = locations ∧
      SelectedRules resolved mode bothStores := by
  exact ⟨locations, alias_actual_gates, rfl, both_stores_rules locations selected_shape mode⟩

theorem actual_alias_outcomes :
    runCandidate initial aliasHandles .releaseAcquire bothStores = .observed locations (1, 1) ∧
    runCandidate initial aliasHandles .relaxed staleData = .observed locations (1, 0) := by
  constructor
  · rw [(alias_substitution .releaseAcquire bothStores).2]
    exact actual_ra
  · rw [(alias_substitution .relaxed staleData).2]
    exact actual_relaxed_stale

def noProvenancePointer : MiniRustReference.Ptr := ⟨16, none⟩
def noProvenanceHandles : Handles :=
  { handles with dataLoad := ⟨noProvenancePointer, 3⟩ }
def misalignedPointer : MiniRustReference.Ptr := ⟨17, some 0⟩
def misalignedHandles : Handles :=
  { handles with dataLoad := ⟨misalignedPointer, 3⟩ }

theorem actual_no_provenance_load :
    MiniRustReference.load initial noProvenancePointer 2 2 = .ub .noProvenance := by
  rfl

theorem actual_dead_load :
    MiniRustReference.load deadData dataPointer 2 2 = .ub .dead := by
  rfl

theorem actual_misalignment_before_bounds :
    MiniRustReference.load initial misalignedPointer 2 2 = .ub .misalignedLoad ∧
    MiniRustReference.checkPtr initial misalignedPointer 2 = .ub .bounds := by
  exact ⟨rfl, rfl⟩

/-- B fails before producing its span; the good D/F/A gates were not replaced. -/
theorem actual_no_provenance_gates :
    gates initial noProvenanceHandles = .ub .b .noProvenance := by
  rfl

/-- Validation stops at the first actual write gate D, not at B. -/
theorem actual_dead_gates : gates deadData handles = .ub .d .dead := by
  rfl

theorem actual_misaligned_gates :
    gates initial misalignedHandles = .ub .b .misalignedLoad := by
  rfl

theorem actual_no_provenance_result (mode : Mode) :
    runCandidate initial noProvenanceHandles mode bothStores = .ordinaryUB .b .noProvenance := by
  exact run_candidate_ordinary_ub initial noProvenanceHandles mode bothStores .b .noProvenance
    rfl actual_no_provenance_gates

theorem actual_dead_result (mode : Mode) :
    runCandidate deadData handles mode bothStores = .ordinaryUB .d .dead := by
  exact run_candidate_ordinary_ub deadData handles mode bothStores .d .dead rfl actual_dead_gates

theorem actual_misaligned_result (mode : Mode) :
    runCandidate initial misalignedHandles mode bothStores = .ordinaryUB .b .misalignedLoad := by
  exact run_candidate_ordinary_ub initial misalignedHandles mode bothStores .b .misalignedLoad
    rfl actual_misaligned_gates

theorem invalid_no_observation (mode : Mode) (resolved : Locations) (values : Nat × Nat) :
    runCandidate initial noProvenanceHandles mode bothStores ≠ .observed resolved values ∧
    runCandidate deadData handles mode bothStores ≠ .observed resolved values ∧
    runCandidate initial misalignedHandles mode bothStores ≠ .observed resolved values := by
  rw [actual_no_provenance_result mode, actual_dead_result mode, actual_misaligned_result mode]
  refine ⟨?_, ?_, ?_⟩
  · intro impossible
    cases impossible
  · intro impossible
    cases impossible
  · intro impossible
    cases impossible

theorem invalid_ordering_independent :
    runCandidate initial noProvenanceHandles .releaseAcquire bothStores =
      runCandidate initial noProvenanceHandles .relaxed bothStores ∧
    runCandidate deadData handles .releaseAcquire bothStores =
      runCandidate deadData handles .relaxed bothStores ∧
    runCandidate initial misalignedHandles .releaseAcquire bothStores =
      runCandidate initial misalignedHandles .relaxed bothStores := by
  simp only [actual_no_provenance_result, actual_dead_result, actual_misaligned_result,
    and_self]

def zeroFlag : RF := ⟨.initialFlag, .dataStore⟩
def badProducerHandles : Handles :=
  { handles with dataStore := ⟨noProvenancePointer, 0⟩ }

/-- This is the classifier's selected-branch limit, not a model of running B
on a zero flag, nor a full flag-zero execution or source-safety theorem. -/
theorem zero_flag_bad_B_outside (mode : Mode) :
    MiniRustReference.load initial misalignedPointer 2 2 = .ub .misalignedLoad ∧
    runCandidate initial misalignedHandles mode zeroFlag = .outsideBranch 0 := by
  exact ⟨actual_misalignment_before_bounds.1,
    flag_zero_outside initial misalignedHandles mode zeroFlag rfl⟩

/-- The prefilter validates none of D/F/A/B; it is not all-prefix UB freedom. -/
theorem zero_flag_bad_producer_outside (mode : Mode) :
    MiniRustReference.store initial noProvenancePointer oneBytes 2 = .ub .noProvenance ∧
    runCandidate initial badProducerHandles mode zeroFlag = .outsideBranch 0 := by
  exact ⟨rfl, flag_zero_outside initial badProducerHandles mode zeroFlag rfl⟩

theorem latest_alternative_controls :
    LatestOnly locations bothStores sequentialSchedule ∧
    (∀ schedule, ¬ LatestOnly locations staleData schedule) ∧
    SelectedRules locations .relaxed staleData := by
  exact ⟨sequential_both_stores_latest locations selected_shape,
    stale_not_latest locations selected_shape, relaxed_stale_rules locations selected_shape⟩

#print axioms observed_sound
#print axioms ra_observed_values
#print axioms ra_no_observed_stale
#print axioms initial_StateWF
#print axioms initial_operand_admission
#print axioms initial_initialized
#print axioms selected_shape
#print axioms actual_raw_zero_loads
#print axioms actual_positive_gates
#print axioms actual_ra
#print axioms actual_relaxed_stale
#print axioms wrong_supplier_same_values
#print axioms wrong_supplier_not_valid
#print axioms wrong_supplier_not_rules
#print axioms actual_wrong_supplier
#print axioms alias_pointer
#print axioms alias_handle_distinct
#print axioms alias_actual_location
#print axioms alias_actual_gates
#print axioms alias_substitution
#print axioms alias_rules_substitution
#print axioms alias_selected_graph
#print axioms actual_alias_outcomes
#print axioms actual_no_provenance_load
#print axioms actual_dead_load
#print axioms actual_misalignment_before_bounds
#print axioms actual_no_provenance_gates
#print axioms actual_dead_gates
#print axioms actual_misaligned_gates
#print axioms actual_no_provenance_result
#print axioms actual_dead_result
#print axioms actual_misaligned_result
#print axioms invalid_no_observation
#print axioms invalid_ordering_independent
#print axioms zero_flag_bad_B_outside
#print axioms zero_flag_bad_producer_outside
#print axioms latest_alternative_controls

end AnnealResearch.AtomicMessagePassingControls
