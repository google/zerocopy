import AnnealResearch.TreeKindAccess
import AnnealResearch.TreeMemory
import AnnealResearch.TreeRawGeometry

/-!
LiveKinds observes permission/protector matching only at actual present live
allocation/tree pairs. NoNewLive is a sufficient raw transport relation: every
live after-record has a live before-record at the same ID. It does not constrain
sizes, bytes or other metadata and is independent of SameSizeMap.

Raw-success facts are derived from the actual selected kernel, without StateWF,
NoUB, liveness, bounds, provenance or byte-validity admission. Generic transports
are not yet full memory-operation boundary theorems. Release can return a live
mismatch after conversion and failure, so all-residual release preservation is
deliberately not asserted.
-/

namespace AnnealResearch.TreeLiveKinds

open TreePermissions
open TreeMemory (State Tree)

def LiveKinds (state : State) : Prop :=
  ∀ id allocation tree, state.raw.allocations id = some allocation →
    allocation.live = true → state.trees id = some tree →
    TreeReference.kindsMatch tree = true

def NoNewLive (before after : MiniRustReference.State) : Prop :=
  ∀ id allocation, after.allocations id = some allocation → allocation.live = true →
    ∃ old, before.allocations id = some old ∧ old.live = true

theorem noNewLive_refl (state : MiniRustReference.State) : NoNewLive state state := by
  intro id allocation found alive
  exact ⟨allocation, found, alive⟩

theorem noNewLive_trans {first second third : MiniRustReference.State}
    (left : NoNewLive first second) (right : NoNewLive second third) :
    NoNewLive first third := by
  intro id allocation found alive
  obtain ⟨middle, middleFound, middleLive⟩ := right id allocation found alive
  exact left id middle middleFound middleLive

theorem noNewLive_replace {before : MiniRustReference.State} {id : Nat}
    {old fresh : MiniRustReference.Allocation}
    (found : before.allocations id = some old)
    (liveBack : fresh.live = true → old.live = true) :
    NoNewLive before (MiniRustReference.replace before id fresh) := by
  intro selected allocation afterFound alive
  by_cases sameId : selected = id
  · subst selected
    have sameAllocation : fresh = allocation := by
      simpa [MiniRustReference.replace] using afterFound
    subst allocation
    exact ⟨old, found, liveBack alive⟩
  · refine ⟨allocation, ?_, alive⟩
    simpa only [MiniRustReference.replace, ite_eq_right sameId] using afterFound

theorem load_noNewLive {before after : MiniRustReference.State}
    {pointer : MiniRustReference.Ptr} {size align : Nat} {bytes : List MiniRustReference.Byte}
    (success : MiniRustReference.load before pointer size align = .ok (bytes, after)) :
    NoNewLive before after := by
  rw [TreeRawGeometry.load_success_raw success]
  exact noNewLive_refl before

/-- An actual successful store changes only the checked allocation's data.
The success equation is inspected, not imposed as an admission on clients. -/
theorem store_noNewLive {before after : MiniRustReference.State}
    {pointer : MiniRustReference.Ptr} {bytes : List MiniRustReference.Byte} {align : Nat}
    (success : MiniRustReference.store before pointer bytes align = .ok after) :
    NoNewLive before after := by
  by_cases zeroAlign : align = 0
  · simp [MiniRustReference.store, zeroAlign] at success
  · by_cases misaligned : pointer.addr % align ≠ 0
    · simp [MiniRustReference.store, zeroAlign, misaligned] at success
    · simp only [MiniRustReference.store, ite_eq_right zeroAlign,
        ite_eq_right misaligned] at success
      cases checked : MiniRustReference.checkPtr before pointer bytes.length with
      | ub fault => simp [checked] at success
      | unsupported => simp [checked] at success
      | noChoice => simp [checked] at success
      | ok maybeSpan =>
        cases maybeSpan with
        | none =>
          simp only [checked] at success
          have same : before = after := MiniRustReference.Result.ok.inj success
          rw [← same]
          exact noNewLive_refl before
        | some span =>
          simp only [checked] at success
          have found := TreeRawGeometry.checkPtr_some_lookup checked
          have same := MiniRustReference.Result.ok.inj success
          rw [← same]
          apply noNewLive_replace found
          intro alive
          exact alive

theorem free_noNewLive {before after : MiniRustReference.State}
    {pointer : MiniRustReference.Ptr} {kind : MiniRustReference.Kind} {size align : Nat}
    (success : MiniRustReference.free before pointer kind size align = .ok after) :
    NoNewLive before after := by
  obtain ⟨id, allocation, found, rfl⟩ := TreeRawGeometry.free_success_shape success
  apply noNewLive_replace found
  intro impossible
  cases impossible

theorem liveKinds_with_raw (state : State) (raw : MiniRustReference.State)
    (matching : LiveKinds state) (noNew : NoNewLive state.raw raw) :
    LiveKinds { state with raw } := by
  intro id allocation tree rawFound alive treeFound
  obtain ⟨old, oldFound, oldLive⟩ := noNew id allocation rawFound alive
  exact matching id old tree oldFound oldLive treeFound

/-- A newly installed tree needs matching only when the selected actual raw
allocation is live. No old tree or permission-width premise is required. -/
theorem liveKinds_setTree (state : State) (id : Nat) (tree : Tree)
    (matching : LiveKinds state)
    (localMatching : ∀ allocation, state.raw.allocations id = some allocation →
      allocation.live = true → TreeReference.kindsMatch tree = true) :
    LiveKinds (TreeMemory.setTree state id tree) := by
  intro selected allocation selectedTree rawFound alive treeFound
  by_cases sameId : selected = id
  · subst selected
    have sameTree : tree = selectedTree := by
      simpa [TreeMemory.setTree] using treeFound
    subst selectedTree
    exact localMatching allocation rawFound alive
  · have oldTree : state.trees selected = some selectedTree := by
      simpa only [TreeMemory.setTree, ite_eq_right sameId] using treeFound
    exact matching selected allocation selectedTree rawFound alive oldTree

theorem liveKinds_replace_tree (state : State) (id : Nat) (before after : Tree)
    (matching : LiveKinds state) (present : state.trees id = some before)
    (preserved : TreeReference.kindsMatch after = TreeReference.kindsMatch before) :
    LiveKinds (TreeMemory.setTree state id after) := by
  apply liveKinds_setTree state id after matching
  intro allocation found alive
  rw [preserved]
  exact matching id allocation before found alive present

theorem liveKinds_commit (state : State) (id : Nat) (before after : Tree)
    (raw : MiniRustReference.State) (matching : LiveKinds state)
    (present : state.trees id = some before)
    (preserved : TreeReference.kindsMatch after = TreeReference.kindsMatch before)
    (noNew : NoNewLive state.raw raw) :
    LiveKinds { TreeMemory.setTree state id after with raw } := by
  exact liveKinds_with_raw (TreeMemory.setTree state id after) raw
    (liveKinds_replace_tree state id before after matching present preserved) noNew

theorem liveKinds_with_frame (state : State) (frame : List TreeMemory.Provenance)
    (matching : LiveKinds state) : LiveKinds { state with currentFrame := frame } := matching

/-- Generic setter transport instantiated with the actual public tree access
residual, on every status. Full load/store/free boundaries remain separate. -/
theorem liveKinds_access_tree (state : State) (id : Nat) (tree : Tree)
    (path : Option TreeReference.Path) (kind : AccessKind) (offset size : Nat)
    (matching : LiveKinds state) (present : state.trees id = some tree) :
    LiveKinds (TreeMemory.setTree state id
      (TreeReference.access tree path kind offset size).state) := by
  exact liveKinds_replace_tree state id tree _ matching present
    (TreeKindAccess.access_matching tree path kind offset size)

#print axioms noNewLive_refl
#print axioms noNewLive_trans
#print axioms noNewLive_replace
#print axioms load_noNewLive
#print axioms store_noNewLive
#print axioms free_noNewLive
#print axioms liveKinds_with_raw
#print axioms liveKinds_setTree
#print axioms liveKinds_replace_tree
#print axioms liveKinds_commit
#print axioms liveKinds_with_frame
#print axioms liveKinds_access_tree

end AnnealResearch.TreeLiveKinds
