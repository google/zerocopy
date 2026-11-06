import AnnealResearch.ReferenceInvariants
import AnnealResearch.TreeFactoredMemory
import AnnealResearch.TreeLiveKinds

/-!
Admission controls for the unchanged raw allocation API. These explicit maps are
malformed with respect to raw StateWF. Tree width and permission/protector matching
do not repair the raw ID domain, and are not a claim of Rust source reachability.
No allocation wrapper or new runtime guard is defined here.
-/
namespace AnnealResearch.TreeAllocationAdmissionControls

open TreePermissions

/-- A real one-byte live record, already containing a number. -/
def oldBlock : MiniRustReference.Allocation :=
  { base := 16, size := 1, align := 1, kind := .heap, live := true
    data := fun _ => .init ⟨7, by decide⟩ none }

/-- The actual raw allocation result's data is uninitialized. -/
def freshBlock : MiniRustReference.Allocation :=
  { base := 16, size := 1, align := 1, kind := .heap, live := true
    data := fun _ => .uninit }

def root : TreeFactored.State :=
  { topology := .node .nil
    store := fun _ => ⟨[.unprot .unique], .no⟩ }

theorem root_width :
    TreeFactored.arrayLengthsTree root.topology [] root.store 1 = true := by
  simp [root, TreeFactored.arrayLengthsTree, TreeFactored.arrayLengthsForest]

theorem root_reify :
    TreeCorrespondence.reify root = .mk [.unprot .unique] .no [] := by
  simp [root, TreeCorrespondence.reify, TreeCorrespondence.reifyTree,
    TreeCorrespondence.reifyForest]

theorem root_matching : TreeReference.kindsMatch (TreeCorrespondence.reify root) = true := by
  rw [root_reify]
  simp [TreeReference.kindsMatch, TreeReference.childrenMatch,
    Permission.matchesProtector, Permission.isProt, Protected.yes]

/-- A single optional tree at an explicit ID; no relation to next is assumed. -/
def oneTree (raw : MiniRustReference.State) (id : Nat) : TreeFactoredMemory.State :=
  { raw, trees := fun selected => if selected = id then some root else none
    currentFrame := [] }

theorem oneTree_sized (raw : MiniRustReference.State) (id : Nat)
    (width : ∀ allocation, raw.allocations id = some allocation → allocation.size = 1) :
    TreeFactoredMemory.WellSized (oneTree raw id) := by
  intro selected allocation tree rawFound treeFound
  by_cases same : selected = id
  · subst selected
    have sameTree : root = tree := by simpa [oneTree] using treeFound
    subst tree
    rw [width allocation rawFound]
    exact root_width
  · simp [oneTree, same] at treeFound

theorem oneTree_liveKinds (raw : MiniRustReference.State) (id : Nat) :
    TreeLiveKinds.LiveKinds (TreeFactoredMemory.reify (oneTree raw id)) := by
  intro selected allocation tree rawFound alive treeFound
  by_cases same : selected = id
  · subst selected
    have sameTree : TreeCorrespondence.reify root = tree := by
      simpa [TreeFactoredMemory.reify, oneTree] using treeFound
    subst tree
    exact root_matching
  · simp [TreeFactoredMemory.reify, oneTree, same] at treeFound

/-- Present live ID0 is outside the minted range, since next is zero. -/
def outsideCount : MiniRustReference.State :=
  { next := 0, allocations := fun id => if id = 0 then some oldBlock else none }

def overwritten : MiniRustReference.State := MiniRustReference.append outsideCount freshBlock

theorem outsideCount_present_live_overlap :
    outsideCount.allocations 0 = some oldBlock ∧ oldBlock.live = true ∧
      MiniRustReference.overlaps oldBlock 16 1 :=
  ⟨rfl, rfl, Or.inl rfl⟩

theorem outsideCount_scan_omits_record :
    MiniRustReference.liveOverlap outsideCount 16 1 = false := rfl

theorem outsideCount_not_StateWF : ¬ MiniRustReference.StateWF outsideCount := by
  intro wf
  have impossible := (wf.domain 0).1 ⟨oldBlock, rfl⟩
  change 0 < 0 at impossible
  omega

theorem outsideCount_sized : TreeFactoredMemory.WellSized (oneTree outsideCount 0) := by
  apply oneTree_sized
  intro allocation found
  have same : oldBlock = allocation := by simpa [outsideCount] using found
  subst allocation
  rfl

theorem outsideCount_matching :
    TreeLiveKinds.LiveKinds (TreeFactoredMemory.reify (oneTree outsideCount 0)) :=
  oneTree_liveKinds outsideCount 0

/-- A real raw branch overwrites the live ID0 record at its same base. -/
theorem outsideCount_allocate :
    MiniRustReference.allocateAt outsideCount .heap 1 1 16 =
      .ok (⟨16, some 0⟩, overwritten) := rfl

theorem overwritten_observations :
    overwritten.next = 1 ∧ overwritten.allocations 0 = some freshBlock ∧
      oldBlock.data 0 = .init ⟨7, by decide⟩ none ∧ freshBlock.data 0 = .uninit :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem overwritten_sized : TreeFactoredMemory.WellSized (oneTree overwritten 0) := by
  apply oneTree_sized
  intro allocation found
  have same : freshBlock = allocation := by
    simpa [overwritten, MiniRustReference.append, outsideCount] using found
  subst allocation
  rfl

/-- The opposite malformed-domain direction: next already counts a missing ID0. -/
def hole : MiniRustReference.State :=
  { next := 1, allocations := fun _ => none }

def holeAfter : MiniRustReference.State := MiniRustReference.append hole freshBlock

theorem hole_not_StateWF : ¬ MiniRustReference.StateWF hole := by
  intro wf
  have counted : 0 < hole.next := by decide
  obtain ⟨allocation, found⟩ := (wf.domain 0).2 counted
  change (none : Option MiniRustReference.Allocation) = some allocation at found
  cases found

theorem hole_allocate :
    MiniRustReference.allocateAt hole .heap 1 1 16 =
      .ok (⟨16, some 1⟩, holeAfter) := rfl

theorem holeAfter_observations :
    holeAfter.next = 2 ∧ holeAfter.allocations 0 = none ∧
      holeAfter.allocations 1 = some freshBlock := ⟨rfl, rfl, rfl⟩

theorem holeAfter_not_StateWF : ¬ MiniRustReference.StateWF holeAfter := by
  intro wf
  have counted : 0 < holeAfter.next := by decide
  obtain ⟨allocation, found⟩ := (wf.domain 0).2 counted
  change (none : Option MiniRustReference.Allocation) = some allocation at found
  cases found

theorem holeAfter_sized : TreeFactoredMemory.WellSized (oneTree holeAfter 1) := by
  apply oneTree_sized
  intro allocation found
  have same : freshBlock = allocation := by
    simpa [holeAfter, MiniRustReference.append, hole] using found
  subst allocation
  rfl

theorem holeAfter_matching :
    TreeLiveKinds.LiveKinds (TreeFactoredMemory.reify (oneTree holeAfter 1)) :=
  oneTree_liveKinds holeAfter 1

/-- Every optional tree has a corresponding raw record: a deliberately separate
joint-presence predicate, not an asserted source-image characterization. -/
def TreesHaveRaw (state : TreeFactoredMemory.State) : Prop :=
  ∀ id tree, state.trees id = some tree →
    ∃ allocation, state.raw.allocations id = some allocation

def stray : TreeFactoredMemory.State := oneTree MiniRustReference.empty 7

theorem stray_raw_StateWF : MiniRustReference.StateWF stray.raw :=
  MiniRustReference.emptyStateWF

theorem stray_sized : TreeFactoredMemory.WellSized stray := by
  apply oneTree_sized
  intro allocation found
  change (none : Option MiniRustReference.Allocation) = some allocation at found
  cases found

theorem stray_matching : TreeLiveKinds.LiveKinds (TreeFactoredMemory.reify stray) :=
  oneTree_liveKinds MiniRustReference.empty 7

theorem stray_missing_raw : ¬ TreesHaveRaw stray := by
  intro present
  obtain ⟨allocation, found⟩ := present 7 root rfl
  change (none : Option MiniRustReference.Allocation) = some allocation at found
  cases found

/-- Both tree predicates can hold nonvacuously at an actual live record while
raw structural admission fails. -/
theorem width_and_matching_do_not_imply_rawWF :
    ∃ state : TreeFactoredMemory.State,
      TreeFactoredMemory.WellSized state ∧
      TreeLiveKinds.LiveKinds (TreeFactoredMemory.reify state) ∧
      ¬ MiniRustReference.StateWF state.raw :=
  ⟨oneTree outsideCount 0, outsideCount_sized, outsideCount_matching,
    outsideCount_not_StateWF⟩

theorem rawWF_width_matching_do_not_imply_tree_presence :
    ∃ state : TreeFactoredMemory.State,
      MiniRustReference.StateWF state.raw ∧ TreeFactoredMemory.WellSized state ∧
      TreeLiveKinds.LiveKinds (TreeFactoredMemory.reify state) ∧ ¬ TreesHaveRaw state :=
  ⟨stray, stray_raw_StateWF, stray_sized, stray_matching, stray_missing_raw⟩

#print axioms root_width
#print axioms root_reify
#print axioms root_matching
#print axioms oneTree_sized
#print axioms oneTree_liveKinds
#print axioms outsideCount_present_live_overlap
#print axioms outsideCount_scan_omits_record
#print axioms outsideCount_not_StateWF
#print axioms outsideCount_sized
#print axioms outsideCount_matching
#print axioms outsideCount_allocate
#print axioms overwritten_observations
#print axioms overwritten_sized
#print axioms hole_not_StateWF
#print axioms hole_allocate
#print axioms holeAfter_observations
#print axioms holeAfter_not_StateWF
#print axioms holeAfter_sized
#print axioms holeAfter_matching
#print axioms stray_raw_StateWF
#print axioms stray_sized
#print axioms stray_matching
#print axioms stray_missing_raw
#print axioms width_and_matching_do_not_imply_rawWF
#print axioms rawWF_width_matching_do_not_imply_tree_presence

end AnnealResearch.TreeAllocationAdmissionControls
