import AnnealResearch.TreeAllocation
import AnnealResearch.TreeMemoryEncoding

/-!
Owned allocation outcomes: an explicit Nat candidate witnesses an actual
allocateAt branch, and every noChoice result is excluded. UB and unsupported
remain outcomes with their complete original residual state.

Coverage is an exact image through full reification. Reification need not be
injective on arbitrary F stores, so the reverse direction supplies an actual F
outcome rather than claiming every representative of its reification executes.
There is no choice-aware client, candidate-existence or source-helper theorem.
-/
namespace AnnealResearch.TreeAllocationChoices

def ReferenceHasOutcome : TreeMemory.Result A → Prop
  | .noChoice _ => False
  | .ok _ _ | .ub _ _ | .unsupported _ _ => True

def FactoredHasOutcome : TreeFactoredMemory.Result A → Prop
  | .noChoice _ => False
  | .ok _ _ | .ub _ _ | .unsupported _ _ => True

/-- No width/WF/valid-candidate or successful-result restriction is present. -/
def ReferenceOutcome (state : TreeMemory.State) (kind : MiniRustReference.Kind)
    (size align : Nat) (answer : TreeMemory.Result TreeMemory.Pointer) : Prop :=
  ReferenceHasOutcome answer ∧
    ∃ address : Nat, TreeMemory.allocateAt state kind size align address = answer

def FactoredOutcome (state : TreeFactoredMemory.State) (kind : MiniRustReference.Kind)
    (size align : Nat) (answer : TreeFactoredMemory.Result TreeMemory.Pointer) : Prop :=
  FactoredHasOutcome answer ∧
    ∃ address : Nat, TreeFactoredMemory.allocateAt state kind size align address = answer

theorem hasOutcome_translate_iff (answer : TreeFactoredMemory.Result A) :
    ReferenceHasOutcome (TreeFactoredMemory.translate answer) ↔
      FactoredHasOutcome answer := by
  cases answer <;> rfl

theorem same_candidate (state : TreeFactoredMemory.State) (kind : MiniRustReference.Kind)
    (size align address : Nat) :
    TreeMemory.allocateAt (TreeFactoredMemory.reify state) kind size align address =
      TreeFactoredMemory.translate
        (TreeFactoredMemory.allocateAt state kind size align address) :=
  TreeAllocation.allocateAt_agrees state kind size align address

theorem reference_noChoice_excluded (state residual : TreeMemory.State)
    (kind : MiniRustReference.Kind) (size align : Nat) :
    ¬ ReferenceOutcome state kind size align (.noChoice residual) := by
  intro outcome
  exact outcome.1

theorem factored_noChoice_excluded (state residual : TreeFactoredMemory.State)
    (kind : MiniRustReference.Kind) (size align : Nat) :
    ¬ FactoredOutcome state kind size align (.noChoice residual) := by
  intro outcome
  exact outcome.1

/-- The same explicit address witnesses every translated actual F outcome. -/
theorem factored_to_reference {state : TreeFactoredMemory.State}
    {kind : MiniRustReference.Kind} {size align : Nat}
    {answer : TreeFactoredMemory.Result TreeMemory.Pointer}
    (outcome : FactoredOutcome state kind size align answer) :
    ReferenceOutcome (TreeFactoredMemory.reify state) kind size align
      (TreeFactoredMemory.translate answer) := by
  refine ⟨(hasOutcome_translate_iff answer).2 outcome.1, ?_⟩
  obtain ⟨address, chosen⟩ := outcome.2
  refine ⟨address, ?_⟩
  rw [same_candidate, chosen]

/-- Every actual R outcome from the reified input is covered by an actual F
branch at its own address witness, including complete terminal errors. -/
theorem reference_to_factored {state : TreeFactoredMemory.State}
    {kind : MiniRustReference.Kind} {size align : Nat}
    {answer : TreeMemory.Result TreeMemory.Pointer}
    (outcome : ReferenceOutcome (TreeFactoredMemory.reify state) kind size align answer) :
    ∃ factored, FactoredOutcome state kind size align factored ∧
      TreeFactoredMemory.translate factored = answer := by
  obtain ⟨address, chosen⟩ := outcome.2
  let factored := TreeFactoredMemory.allocateAt state kind size align address
  have translated : TreeFactoredMemory.translate factored = answer := by
    rw [← same_candidate]
    exact chosen
  have enabled : FactoredHasOutcome factored := by
    apply (hasOutcome_translate_iff factored).1
    rw [translated]
    exact outcome.1
  exact ⟨factored, ⟨enabled, ⟨address, rfl⟩⟩, translated⟩

/-- Equality of the complete outcome sets after mapping, with no domain
premise or assertion that either set is nonempty for an arbitrary request. -/
theorem outcome_exact_image (state : TreeFactoredMemory.State)
    (kind : MiniRustReference.Kind) (size align : Nat)
    (answer : TreeMemory.Result TreeMemory.Pointer) :
    ReferenceOutcome (TreeFactoredMemory.reify state) kind size align answer ↔
      ∃ factored, FactoredOutcome state kind size align factored ∧
        TreeFactoredMemory.translate factored = answer := by
  constructor
  · exact reference_to_factored
  · rintro ⟨factored, outcome, rfl⟩
    exact factored_to_reference outcome

/-- Every owned R input is covered via the existing exact memory encoding.
Encoding imposes no WellSized, raw WF, liveness, path or NoUB premise. -/
theorem arbitrary_reference_exact_image (state : TreeMemory.State)
    (kind : MiniRustReference.Kind) (size align : Nat)
    (answer : TreeMemory.Result TreeMemory.Pointer) :
    ReferenceOutcome state kind size align answer ↔
      ∃ factored, FactoredOutcome (TreeMemoryEncoding.encodeMemory state)
        kind size align factored ∧ TreeFactoredMemory.translate factored = answer := by
  simpa only [TreeMemoryEncoding.reify_encode_memory] using
    outcome_exact_image (TreeMemoryEncoding.encodeMemory state) kind size align answer

/-- An actual terminal UB outcome exists even when address zero is not a valid
candidate: oversize is checked before candidate testing. -/
theorem reference_oversize_outcome (state : TreeMemory.State)
    (kind : MiniRustReference.Kind) (size align : Nat)
    (large : MiniRustReference.sizeLimit ≤ size) :
    ReferenceOutcome state kind size align (.ub (.basic .allocationTooLarge) state) := by
  refine ⟨True.intro, 0, ?_⟩
  simp [TreeMemory.allocateAt, MiniRustReference.allocateAt, large]

theorem factored_oversize_outcome (state : TreeFactoredMemory.State)
    (kind : MiniRustReference.Kind) (size align : Nat)
    (large : MiniRustReference.sizeLimit ≤ size) :
    FactoredOutcome state kind size align (.ub (.basic .allocationTooLarge) state) := by
  refine ⟨True.intro, 0, ?_⟩
  simp [TreeFactoredMemory.allocateAt, MiniRustReference.allocateAt, large]

/-- The represented zero-alignment limitation also remains an actual outcome,
with exact original residual, rather than being silently filtered. -/
theorem reference_zero_align_outcome (state : TreeMemory.State)
    (kind : MiniRustReference.Kind) (size : Nat) (small : size < MiniRustReference.sizeLimit) :
    ReferenceOutcome state kind size 0 (.unsupported .basicRepresentation state) := by
  refine ⟨True.intro, 0, ?_⟩
  have notLarge : ¬ MiniRustReference.sizeLimit ≤ size := Nat.not_le.mpr small
  simp [TreeMemory.allocateAt, MiniRustReference.allocateAt, notLarge]

theorem factored_zero_align_outcome (state : TreeFactoredMemory.State)
    (kind : MiniRustReference.Kind) (size : Nat) (small : size < MiniRustReference.sizeLimit) :
    FactoredOutcome state kind size 0 (.unsupported .basicRepresentation state) := by
  refine ⟨True.intro, 0, ?_⟩
  have notLarge : ¬ MiniRustReference.sizeLimit ≤ size := Nat.not_le.mpr small
  simp [TreeFactoredMemory.allocateAt, MiniRustReference.allocateAt, notLarge]

#print axioms hasOutcome_translate_iff
#print axioms same_candidate
#print axioms reference_noChoice_excluded
#print axioms factored_noChoice_excluded
#print axioms factored_to_reference
#print axioms reference_to_factored
#print axioms outcome_exact_image
#print axioms arbitrary_reference_exact_image
#print axioms reference_oversize_outcome
#print axioms factored_oversize_outcome
#print axioms reference_zero_align_outcome
#print axioms factored_zero_align_outcome

end AnnealResearch.TreeAllocationChoices
