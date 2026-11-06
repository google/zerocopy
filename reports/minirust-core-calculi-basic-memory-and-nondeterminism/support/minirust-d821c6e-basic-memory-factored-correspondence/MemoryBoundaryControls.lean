import AnnealResearch.MemoryExamples

/-!
Source-boundary controls and a deliberately incorrect lifetime implementation.
The mutation retains numeric alignment but resolves a live block by address,
discarding the stale provenance identity. Its safety does not imply reference
safety. The impossible allocator case uses an admitted power-of-two alignment.
-/
namespace AnnealResearch.MemoryBoundaryControls

open Execution MemoryExecution MiniRustReference MemoryExamples

theorem no_candidate_at_address_limit (s : State) (size addr : Nat) :
    ¬ AllocationCandidate s size addressLimit addr := by
  rintro ⟨positive, aligned, bounded, _⟩
  have below : addr < addressLimit := by omega
  rw [Nat.mod_eq_of_lt below] at aligned
  omega

theorem impossible_alignment_admitted : AlignWF addressLimit := ⟨64, rfl⟩

theorem impossible_alignment_no_choice (candidate : Nat) :
    allocateAt empty .heap 0 addressLimit candidate = .noChoice := by
  simp only [allocateAt,
    ite_eq_right (show ¬ sizeLimit ≤ 0 by decide),
    ite_eq_right (show addressLimit ≠ 0 by decide),
    ite_eq_right (no_candidate_at_address_limit empty 0 candidate)]

theorem actual_empty_choice_no_progress (continuation : Reply → Plan) :
    NoUB SourceStep Bad
      (.running empty (.call (.allocate .heap 0 addressLimit) continuation) []) ∧
    ¬ ReachableProgress SourceStep
      (AllowedStop (fun result => result = .machineStop))
      (.running empty (.call (.allocate .heap 0 addressLimit) continuation) []) := by
  apply empty_choice_safe_without_progress
  intro candidate
  simp [sourceExecute, impossible_alignment_no_choice, liftResult]

theorem oversized_before_choice (candidate : Nat) :
    allocateAt empty .heap sizeLimit addressLimit candidate = .ub .allocationTooLarge :=
  oversized_allocation empty .heap sizeLimit addressLimit candidate (Nat.le_refl _)

theorem remaining_free_error_order :
    free allocated0 stale .heap 99 2 = .ub .freeSize ∧
    free allocated0 stale .heap 1 2 = .ub .freeAlign ∧
    free freed0 ⟨9, some 0⟩ .global 99 2 = .ub .doubleFree := ⟨rfl, rfl, rfl⟩

theorem aligned_zero_length_controls :
    load empty ⟨0, none⟩ 0 8 = .ok ([], empty) ∧
    load freed0 stale 0 8 = .ok ([], freed0) ∧
    store freed0 stale [] 8 = .ok freed0 := ⟨rfl, rfl, rfl⟩

/-- Keep alignment checking; change only the identity-sensitive lookup on loads.
All non-load dispatch still uses the original reference evaluator. -/
def mutantExecute (candidate : Nat) (s : State) (op : Op) : EvalAnswer State :=
  match op with
  | .load p len align =>
    if align = 0 then .unsupported
    else if p.addr % align ≠ 0 then .ub .misalignedLoad
    else liftResult (fun value => (.bytes value.1, value.2)) (addressOnlyLoad s p len)
  | other => sourceExecute candidate s other

abbrev MutantStep := Step mutantExecute

theorem mutated_bad_then_spin_safe :
    NoUB MutantStep Bad (.running stored1 badThenSpin []) := by
  let initial : Config State := .running stored1 badThenSpin []
  apply invariant_noUB
    (Invariant := fun s : Config State => s = initial ∨
      ∃ trace : List Event, s = .running stored1 .spin trace) (Or.inl rfl)
  · intro s t invariant edge
    obtain ⟨candidate, edge⟩ := edge
    rcases invariant with rfl | ⟨trace, rfl⟩
    · have successor : next mutantExecute candidate initial =
        some (.running stored1 .spin
          [.answered (.load stale 1 1) (.bytes [seven])]) := rfl
      rw [successor] at edge
      have same := Option.some.inj edge
      subst t
      exact Or.inr ⟨_, rfl⟩
    · change some (Config.running stored1 .spin (trace ++ [.spin])) = some t at edge
      have same := Option.some.inj edge
      subst t
      exact Or.inr ⟨_, rfl⟩
  · intro s invariant bad
    rcases invariant with rfl | ⟨trace, rfl⟩
    · exact bad
    · exact bad

theorem mutation_invalidates_safety_transfer :
    NoUB MutantStep Bad (.running stored1 badThenSpin []) ∧
    ¬ NoUB SourceStep Bad (.running stored1 badThenSpin []) :=
  ⟨mutated_bad_then_spin_safe, bad_prefix_before_spin.2.1⟩

#print axioms no_candidate_at_address_limit
#print axioms impossible_alignment_admitted
#print axioms impossible_alignment_no_choice
#print axioms actual_empty_choice_no_progress
#print axioms oversized_before_choice
#print axioms remaining_free_error_order
#print axioms aligned_zero_length_controls
#print axioms mutated_bad_then_spin_safe
#print axioms mutation_invalidates_safety_transfer

end AnnealResearch.MemoryBoundaryControls
