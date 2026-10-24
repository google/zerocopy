import AnnealResearch.TreeAllocation
import AnnealResearch.ReferenceInvariants

/-!
Separate structural admission for the actual shared raw allocator and the
direct R/F allocation wrappers. Public all-result raw preservation assumes only
input raw StateWF and request AlignWF, never candidate/success/NoUB admission.

Success equations are observations of actual outcomes. Raw StateWF makes old
next a fresh raw ID; the independent PairedPresence predicate is additionally
needed to infer that the corresponding old optional tree was absent. These
conditions are not added to allocation correspondence or width/live closure.
-/
namespace AnnealResearch.TreeAllocationFreshness

def referenceResidual : TreeMemory.Result A → TreeMemory.State
  | .ok _ state | .ub _ state | .unsupported _ state | .noChoice state => state

def factoredResidual : TreeFactoredMemory.Result A → TreeFactoredMemory.State
  | .ok _ state | .ub _ state | .unsupported _ state | .noChoice state => state

def rawResidual (before : MiniRustReference.State) :
    MiniRustReference.Result (MiniRustReference.Ptr × MiniRustReference.State) →
      MiniRustReference.State
  | .ok (_, after) => after
  | .ub _ | .unsupported | .noChoice => before

theorem raw_preserves_StateWF (state : MiniRustReference.State)
    (kind : MiniRustReference.Kind) (size align address : Nat)
    (wf : MiniRustReference.StateWF state) (awf : MiniRustReference.AlignWF align) :
    MiniRustReference.StateWF
      (rawResidual state (MiniRustReference.allocateAt state kind size align address)) := by
  cases chosen : MiniRustReference.allocateAt state kind size align address with
  | ub fault => exact wf
  | unsupported => exact wf
  | noChoice => exact wf
  | ok created =>
    rcases created with ⟨pointer, raw⟩
    exact MiniRustReference.allocateAt_preserves_StateWF wf awf chosen

theorem reference_preserves_raw_StateWF (state : TreeMemory.State)
    (kind : MiniRustReference.Kind) (size align address : Nat)
    (wf : MiniRustReference.StateWF state.raw) (awf : MiniRustReference.AlignWF align) :
    MiniRustReference.StateWF
      (referenceResidual (TreeMemory.allocateAt state kind size align address)).raw := by
  unfold TreeMemory.allocateAt
  cases chosen : MiniRustReference.allocateAt state.raw kind size align address with
  | ub fault => exact wf
  | unsupported => exact wf
  | noChoice => exact wf
  | ok created =>
    rcases created with ⟨pointer, raw⟩
    exact MiniRustReference.allocateAt_preserves_StateWF wf awf chosen

theorem factored_preserves_raw_StateWF (state : TreeFactoredMemory.State)
    (kind : MiniRustReference.Kind) (size align address : Nat)
    (wf : MiniRustReference.StateWF state.raw) (awf : MiniRustReference.AlignWF align) :
    MiniRustReference.StateWF
      (factoredResidual (TreeFactoredMemory.allocateAt state kind size align address)).raw := by
  unfold TreeFactoredMemory.allocateAt
  cases chosen : MiniRustReference.allocateAt state.raw kind size align address with
  | ub fault => exact wf
  | unsupported => exact wf
  | noChoice => exact wf
  | ok created =>
    rcases created with ⟨pointer, raw⟩
    exact MiniRustReference.allocateAt_preserves_StateWF wf awf chosen

/-- No WF premise: this is what actual R success says, including the executed
candidate and exact complete state, rather than a successful-command admission. -/
theorem reference_success_shape {state after : TreeMemory.State}
    {pointer : TreeMemory.Pointer} {kind : MiniRustReference.Kind} {size align address : Nat}
    (success : TreeMemory.allocateAt state kind size align address = .ok pointer after) :
    pointer = { addr := address, provenance := some (state.raw.next, []) } ∧
    after = { TreeMemory.setTree state state.raw.next (TreeAllocation.referenceRoot size) with
      raw := MiniRustReference.append state.raw
        (MiniRustReference.freshAllocation kind size align address) } ∧
    size < MiniRustReference.sizeLimit ∧
    MiniRustReference.AllocationCandidate state.raw size align address := by
  unfold TreeMemory.allocateAt at success
  cases chosen : MiniRustReference.allocateAt state.raw kind size align address with
  | ub fault => simp [chosen] at success
  | unsupported => simp [chosen] at success
  | noChoice => simp [chosen] at success
  | ok created =>
    rcases created with ⟨rawPointer, raw⟩
    simp only [chosen] at success
    obtain ⟨rfl, rfl, small, candidate⟩ := MiniRustReference.allocateAt_success_shape chosen
    cases success
    exact ⟨rfl, rfl, small, candidate⟩

theorem factored_success_shape {state after : TreeFactoredMemory.State}
    {pointer : TreeMemory.Pointer} {kind : MiniRustReference.Kind} {size align address : Nat}
    (success : TreeFactoredMemory.allocateAt state kind size align address = .ok pointer after) :
    pointer = { addr := address, provenance := some (state.raw.next, []) } ∧
    after = { TreeFactoredMemory.setTree state state.raw.next (TreeAllocation.factoredRoot size) with
      raw := MiniRustReference.append state.raw
        (MiniRustReference.freshAllocation kind size align address) } ∧
    size < MiniRustReference.sizeLimit ∧
    MiniRustReference.AllocationCandidate state.raw size align address := by
  unfold TreeFactoredMemory.allocateAt at success
  cases chosen : MiniRustReference.allocateAt state.raw kind size align address with
  | ub fault => simp [chosen] at success
  | unsupported => simp [chosen] at success
  | noChoice => simp [chosen] at success
  | ok created =>
    rcases created with ⟨rawPointer, raw⟩
    simp only [chosen] at success
    obtain ⟨rfl, rfl, small, candidate⟩ := MiniRustReference.allocateAt_success_shape chosen
    cases success
    exact ⟨rfl, rfl, small, candidate⟩

theorem reference_success_identity {state after : TreeMemory.State}
    {pointer : TreeMemory.Pointer} {kind : MiniRustReference.Kind} {size align address : Nat}
    (success : TreeMemory.allocateAt state kind size align address = .ok pointer after) :
    pointer.addr = address ∧ pointer.provenance = some (state.raw.next, []) ∧
    after.raw.next = state.raw.next + 1 ∧
    after.trees state.raw.next = some (TreeAllocation.referenceRoot size) ∧
    after.currentFrame = state.currentFrame := by
  obtain ⟨rfl, rfl, _, _⟩ := reference_success_shape success
  exact ⟨rfl, rfl, rfl, by simp [TreeMemory.setTree], rfl⟩

theorem factored_success_identity {state after : TreeFactoredMemory.State}
    {pointer : TreeMemory.Pointer} {kind : MiniRustReference.Kind} {size align address : Nat}
    (success : TreeFactoredMemory.allocateAt state kind size align address = .ok pointer after) :
    pointer.addr = address ∧ pointer.provenance = some (state.raw.next, []) ∧
    after.raw.next = state.raw.next + 1 ∧
    after.trees state.raw.next = some (TreeAllocation.factoredRoot size) ∧
    after.currentFrame = state.currentFrame := by
  obtain ⟨rfl, rfl, _, _⟩ := factored_success_shape success
  exact ⟨rfl, rfl, rfl, by simp [TreeFactoredMemory.setTree], rfl⟩

theorem next_raw_absent {state : MiniRustReference.State}
    (wf : MiniRustReference.StateWF state) : state.allocations state.next = none := by
  cases found : state.allocations state.next with
  | none => rfl
  | some allocation =>
    have impossible := (wf.domain state.next).1 ⟨allocation, found⟩
    exact False.elim ((Nat.lt_irrefl _) impossible)

/-- Every present old record is below next, so an actual append cannot overwrite
it. No candidate or successful-access premise appears in this raw list fact. -/
theorem append_preserves_old {state : MiniRustReference.State}
    (wf : MiniRustReference.StateWF state) (fresh : MiniRustReference.Allocation)
    {id : Nat} {allocation : MiniRustReference.Allocation}
    (found : state.allocations id = some allocation) :
    (MiniRustReference.append state fresh).allocations id = some allocation := by
  have minted := (wf.domain id).1 ⟨allocation, found⟩
  have different : id ≠ state.next := Nat.ne_of_lt minted
  simpa only [MiniRustReference.append, ite_eq_right different] using found

theorem reference_success_preserves_old {state after : TreeMemory.State}
    {pointer : TreeMemory.Pointer} {kind : MiniRustReference.Kind} {size align address : Nat}
    (wf : MiniRustReference.StateWF state.raw)
    (success : TreeMemory.allocateAt state kind size align address = .ok pointer after) :
    ∀ id allocation, state.raw.allocations id = some allocation →
      after.raw.allocations id = some allocation := by
  obtain ⟨_, rfl, _, _⟩ := reference_success_shape success
  intro id allocation found
  exact append_preserves_old wf _ found

theorem factored_success_preserves_old {state after : TreeFactoredMemory.State}
    {pointer : TreeMemory.Pointer} {kind : MiniRustReference.Kind} {size align address : Nat}
    (wf : MiniRustReference.StateWF state.raw)
    (success : TreeFactoredMemory.allocateAt state kind size align address = .ok pointer after) :
    ∀ id allocation, state.raw.allocations id = some allocation →
      after.raw.allocations id = some allocation := by
  obtain ⟨_, rfl, _, _⟩ := factored_success_shape success
  intro id allocation found
  exact append_preserves_old wf _ found

/-- A separate joint-presence invariant. It says nothing about tree contents,
source construction, pointer paths, sizes, liveness, frames or NoUB. -/
def PairedPresence {Tree : Type} (raw : MiniRustReference.State)
    (trees : Nat → Option Tree) : Prop :=
  ∀ id, (∃ tree, trees id = some tree) ↔
    (∃ allocation, raw.allocations id = some allocation)

/-- Coordinated replacement preserves presence even on a malformed raw map.
It neither needs raw StateWF nor implies raw freshness. -/
theorem pairedPresence_append {Tree : Type} {raw : MiniRustReference.State}
    {trees : Nat → Option Tree} (paired : PairedPresence raw trees)
    (allocation : MiniRustReference.Allocation) (tree : Tree) :
    PairedPresence (MiniRustReference.append raw allocation)
      (fun selected => if selected = raw.next then some tree else trees selected) := by
  intro selected
  by_cases same : selected = raw.next
  · simp [MiniRustReference.append, same]
  · simpa only [MiniRustReference.append, ite_eq_right same] using paired selected

theorem reference_preserves_pairedPresence (state : TreeMemory.State)
    (kind : MiniRustReference.Kind) (size align address : Nat)
    (paired : PairedPresence state.raw state.trees) :
    PairedPresence
      (referenceResidual (TreeMemory.allocateAt state kind size align address)).raw
      (referenceResidual (TreeMemory.allocateAt state kind size align address)).trees := by
  unfold TreeMemory.allocateAt
  cases chosen : MiniRustReference.allocateAt state.raw kind size align address with
  | ub fault => exact paired
  | unsupported => exact paired
  | noChoice => exact paired
  | ok created =>
    rcases created with ⟨pointer, raw⟩
    obtain ⟨_, rfl, _, _⟩ := MiniRustReference.allocateAt_success_shape chosen
    exact pairedPresence_append paired _ (TreeAllocation.referenceRoot size)

theorem factored_preserves_pairedPresence (state : TreeFactoredMemory.State)
    (kind : MiniRustReference.Kind) (size align address : Nat)
    (paired : PairedPresence state.raw state.trees) :
    PairedPresence
      (factoredResidual (TreeFactoredMemory.allocateAt state kind size align address)).raw
      (factoredResidual (TreeFactoredMemory.allocateAt state kind size align address)).trees := by
  unfold TreeFactoredMemory.allocateAt
  cases chosen : MiniRustReference.allocateAt state.raw kind size align address with
  | ub fault => exact paired
  | unsupported => exact paired
  | noChoice => exact paired
  | ok created =>
    rcases created with ⟨pointer, raw⟩
    obtain ⟨_, rfl, _, _⟩ := MiniRustReference.allocateAt_success_shape chosen
    exact pairedPresence_append paired _ (TreeAllocation.factoredRoot size)

theorem next_tree_absent {Tree : Type} {raw : MiniRustReference.State}
    {trees : Nat → Option Tree} (wf : MiniRustReference.StateWF raw)
    (paired : PairedPresence raw trees) : trees raw.next = none := by
  cases found : trees raw.next with
  | none => rfl
  | some tree =>
    obtain ⟨allocation, allocationFound⟩ := (paired raw.next).1 ⟨tree, found⟩
    rw [next_raw_absent wf] at allocationFound
    cases allocationFound

/-- Tree freshness requires both stated structural predicates. It is not inferred
from raw WF alone, and is not added to the operational correspondence domain. -/
theorem reference_fresh_input_pair (state : TreeMemory.State)
    (wf : MiniRustReference.StateWF state.raw)
    (paired : PairedPresence state.raw state.trees) :
    state.raw.allocations state.raw.next = none ∧ state.trees state.raw.next = none :=
  ⟨next_raw_absent wf, next_tree_absent wf paired⟩

theorem factored_fresh_input_pair (state : TreeFactoredMemory.State)
    (wf : MiniRustReference.StateWF state.raw)
    (paired : PairedPresence state.raw state.trees) :
    state.raw.allocations state.raw.next = none ∧ state.trees state.raw.next = none :=
  ⟨next_raw_absent wf, next_tree_absent wf paired⟩

#print axioms raw_preserves_StateWF
#print axioms reference_preserves_raw_StateWF
#print axioms factored_preserves_raw_StateWF
#print axioms reference_success_shape
#print axioms factored_success_shape
#print axioms reference_success_identity
#print axioms factored_success_identity
#print axioms next_raw_absent
#print axioms append_preserves_old
#print axioms reference_success_preserves_old
#print axioms factored_success_preserves_old
#print axioms pairedPresence_append
#print axioms reference_preserves_pairedPresence
#print axioms factored_preserves_pairedPresence
#print axioms next_tree_absent
#print axioms reference_fresh_input_pair
#print axioms factored_fresh_input_pair

end AnnealResearch.TreeAllocationFreshness
