import AnnealResearch.TreeAllocation
import AnnealResearch.ReferenceInvariants
import AnnealResearch.TreeMemoryEncoding
import AnnealResearch.TreeMemoryDomain
import AnnealResearch.TreeLiveTransfer

/-!
Separate all-result structural-width and live-matching closure for actual
allocation birth. Coordinated append plus whole-tree replacement handles a
new record directly; neither SameSizeMap nor NoNewLive is assumed.

Public width theorems require only their existing input width predicate, and
public matching theorems require only input LiveKinds. Actual success supplies
the raw append shape internally. Errors/noChoice keep input state. No StateWF,
AlignWF, candidate/success, freshness, valid-path or NoUB admission is added.
F closures share the R proof through unconditional full-result correspondence.
-/

namespace AnnealResearch.TreeAllocationDomain

open TreeMemoryEncoding (RWellSized)
open TreeLiveKinds (LiveKinds)

/-- Observe every actual reference residual, including all terminal categories. -/
def RResultWellSized (answer : TreeMemory.Result A) : Prop :=
  RWellSized (TreeLiveMemory.residual answer)

/-- Replace both sides of the allocation/tree pair at old next. Existing raw
records or stray trees at that selected ID may be overwritten on malformed maps;
only other IDs use the original width premise. No freshness is assumed. -/
theorem reference_append_sized (state : TreeMemory.State) (fresh : MiniRustReference.Allocation)
    (root : TreeReference.Node) (sized : RWellSized state)
    (rootWidth : TreeReference.arraysSized root fresh.size = true) :
    RWellSized { TreeMemory.setTree state state.raw.next root with
      raw := MiniRustReference.append state.raw fresh } := by
  intro id allocation tree rawFound treeFound
  by_cases selected : id = state.raw.next
  · subst id
    have sameAllocation : fresh = allocation := by
      simpa [MiniRustReference.append] using rawFound
    have sameTree : root = tree := by
      simpa [TreeMemory.setTree] using treeFound
    subst allocation
    subst tree
    exact rootWidth
  · have oldRaw : state.raw.allocations id = some allocation := by
      simpa only [MiniRustReference.append, ite_eq_right selected] using rawFound
    have oldTree : state.trees id = some tree := by
      simpa only [TreeMemory.setTree, ite_eq_right selected] using treeFound
    exact sized id allocation tree oldRaw oldTree

/-- New live records need their own matching root; requiring a prior live record
would exclude allocation itself. Other IDs retain their exact old records. -/
theorem reference_append_live (state : TreeMemory.State) (fresh : MiniRustReference.Allocation)
    (root : TreeReference.Node) (matching : LiveKinds state)
    (rootMatching : TreeReference.kindsMatch root = true) :
    LiveKinds { TreeMemory.setTree state state.raw.next root with
      raw := MiniRustReference.append state.raw fresh } := by
  intro id allocation tree rawFound alive treeFound
  by_cases selected : id = state.raw.next
  · subst id
    have sameTree : root = tree := by
      simpa [TreeMemory.setTree] using treeFound
    subst tree
    exact rootMatching
  · have oldRaw : state.raw.allocations id = some allocation := by
      simpa only [MiniRustReference.append, ite_eq_right selected] using rawFound
    have oldTree : state.trees id = some tree := by
      simpa only [TreeMemory.setTree, ite_eq_right selected] using treeFound
    exact matching id allocation tree oldRaw alive oldTree

/-- Sole public premise is the natural input width domain. The output observer
includes ok, UB, unsupported and noChoice without filtering bad outcomes. -/
theorem reference_preserves_width (state : TreeMemory.State) (kind : MiniRustReference.Kind)
    (size align address : Nat) (sized : RWellSized state) :
    RResultWellSized (TreeMemory.allocateAt state kind size align address) := by
  unfold RResultWellSized TreeMemory.allocateAt
  cases chosen : MiniRustReference.allocateAt state.raw kind size align address with
  | ub fault => exact sized
  | unsupported => exact sized
  | noChoice => exact sized
  | ok created =>
    rcases created with ⟨pointer, raw⟩
    obtain ⟨_, rfl, _, _⟩ := MiniRustReference.allocateAt_success_shape chosen
    exact reference_append_sized state
      (MiniRustReference.freshAllocation kind size align address)
      (TreeAllocation.referenceRoot size) sized (TreeAllocation.referenceRoot_width size)

/-- Sole public premise is input LiveKinds. No width or source-style raw
admission is needed for this algebraic all-residual property. -/
theorem reference_preserves_live (state : TreeMemory.State) (kind : MiniRustReference.Kind)
    (size align address : Nat) (matching : LiveKinds state) :
    TreeLiveMemory.ResultLiveKinds (TreeMemory.allocateAt state kind size align address) := by
  unfold TreeLiveMemory.ResultLiveKinds TreeMemory.allocateAt
  cases chosen : MiniRustReference.allocateAt state.raw kind size align address with
  | ub fault => exact matching
  | unsupported => exact matching
  | noChoice => exact matching
  | ok created =>
    rcases created with ⟨pointer, raw⟩
    obtain ⟨_, rfl, _, _⟩ := MiniRustReference.allocateAt_success_shape chosen
    exact reference_append_live state
      (MiniRustReference.freshAllocation kind size align address)
      (TreeAllocation.referenceRoot size) matching (TreeAllocation.referenceRoot_matching size)

/-- Natural recursive width is exactly the existing F domain after reification.
Absent optional trees remain absent; dead records retain width obligations. -/
theorem wellSized_reify_iff (state : TreeFactoredMemory.State) :
    RWellSized (TreeFactoredMemory.reify state) ↔ TreeFactoredMemory.WellSized state := by
  constructor
  · intro sized id allocation tree rawFound treeFound
    have reifiedTree : (TreeFactoredMemory.reify state).trees id =
        some (TreeCorrespondence.reify tree) := by
      simp only [TreeFactoredMemory.reify, treeFound, Option.map_some]
    have query := sized id allocation (TreeCorrespondence.reify tree) rawFound reifiedTree
    rw [TreeQueries.arraysSized_reify] at query
    exact query
  · intro sized id allocation node rawFound treeFound
    cases found : state.trees id with
    | none => simp [TreeFactoredMemory.reify, found] at treeFound
    | some tree =>
      have same : TreeCorrespondence.reify tree = node := by
        simpa only [TreeFactoredMemory.reify, found, Option.map_some, Option.some.injEq] using treeFound
      subst node
      rw [TreeQueries.arraysSized_reify]
      exact sized id allocation tree rawFound found

theorem resultWellSized_translate (answer : TreeFactoredMemory.Result A) :
    RResultWellSized (TreeFactoredMemory.translate answer) ↔
      TreeMemoryDomain.ResultWellSized answer := by
  cases answer with
  | ok value state => exact wellSized_reify_iff state
  | ub fault state => exact wellSized_reify_iff state
  | unsupported reason state => exact wellSized_reify_iff state
  | noChoice state => exact wellSized_reify_iff state

/-- Shared proof transport through unconditional branch agreement; only the
input F width predicate is required, independently of matching. -/
theorem factored_preserves_width (state : TreeFactoredMemory.State) (kind : MiniRustReference.Kind)
    (size align address : Nat) (sized : TreeFactoredMemory.WellSized state) :
    TreeMemoryDomain.ResultWellSized (TreeFactoredMemory.allocateAt state kind size align address) := by
  have reference := reference_preserves_width (TreeFactoredMemory.reify state) kind size align address
    ((wellSized_reify_iff state).2 sized)
  rw [TreeAllocation.allocateAt_agrees state kind size align address] at reference
  exact (resultWellSized_translate _).mp reference

/-- Unlike transfers of earlier tree operations, allocation agreement requires
no width domain. Hence this F matching closure requires only input matching. -/
theorem factored_preserves_live (state : TreeFactoredMemory.State) (kind : MiniRustReference.Kind)
    (size align address : Nat) (matching : TreeLiveTransfer.LiveKinds state) :
    TreeLiveTransfer.ResultLiveKinds (TreeFactoredMemory.allocateAt state kind size align address) := by
  have reference := reference_preserves_live (TreeFactoredMemory.reify state) kind size align address matching
  rw [TreeAllocation.allocateAt_agrees state kind size align address] at reference
  exact (TreeLiveTransfer.resultLiveKinds_translate _).mp reference

#print axioms reference_append_sized
#print axioms reference_append_live
#print axioms reference_preserves_width
#print axioms reference_preserves_live
#print axioms wellSized_reify_iff
#print axioms resultWellSized_translate
#print axioms factored_preserves_width
#print axioms factored_preserves_live

end AnnealResearch.TreeAllocationDomain
