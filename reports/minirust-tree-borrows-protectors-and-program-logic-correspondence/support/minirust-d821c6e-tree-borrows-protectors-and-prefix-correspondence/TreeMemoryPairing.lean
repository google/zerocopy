import AnnealResearch.TreeFactoredMemory
import AnnealResearch.TreePairing

/-!
Explicit full-memory representatives for prior constructed reference histories.
Raw allocations and ordered frame lists are supplied directly. No success is
extracted from a result with a fallback. These are representation/domain controls;
actual factored operation agreement is a separate theorem layer.
-/
namespace AnnealResearch.TreeMemoryPairing

open TreePermissions

abbrev F := TreeFactoredMemory.State

def single (allocation : MiniRustReference.Allocation) (tree : TreeFactored.State)
    (frame : List TreeMemory.Provenance) : F :=
  { raw := { next := 1, allocations := fun id => if id = 0 then some allocation else none }
    trees := fun id => if id = 0 then some tree else none
    currentFrame := frame }

theorem single_sized (allocation : MiniRustReference.Allocation) (tree : TreeFactored.State)
    (frame : List TreeMemory.Provenance)
    (uniform : TreeFactored.arrayLengthsTree tree.topology [] tree.store allocation.size = true) :
    TreeFactoredMemory.WellSized (single allocation tree frame) := by
  intro id foundAllocation foundTree allocationFound treeFound
  by_cases zero : id = 0
  · subst id
    simp only [single] at allocationFound treeFound
    cases allocationFound
    cases treeFound
    exact uniform
  · simp [single, zero] at allocationFound

def readState (protection : Protected) : F :=
  single (TreeMemoryControls.block 1) (TreePairing.readState protection) [(0, [0, 0])]

def writeState (protection : Protected) : F :=
  single TreeMemoryControls.writtenBlock (TreePairing.writeState protection) [(0, [0, 0])]

theorem read_reify (protection : Protected) :
    TreeFactoredMemory.reify (readState protection) = TreeMemoryControls.readState protection := by
  unfold TreeFactoredMemory.reify readState single TreeMemoryControls.readState
    TreeMemoryControls.stateAB TreeMemoryControls.stateA TreeMemoryControls.initial
    TreeMemory.setTree
  dsimp only
  congr 1
  funext id
  by_cases zero : id = 0 <;> simp [zero, TreePairing.read_reify]

theorem write_reify (protection : Protected) :
    TreeFactoredMemory.reify (writeState protection) = TreeMemoryControls.writeState protection := by
  unfold TreeFactoredMemory.reify writeState single TreeMemoryControls.writeState
    TreeMemoryControls.readState TreeMemoryControls.stateAB TreeMemoryControls.stateA
    TreeMemoryControls.initial TreeMemory.setTree MiniRustReference.replace
  dsimp only
  congr 1
  · congr 1
    funext id
    by_cases zero : id = 0 <;> simp [zero]
  · funext id
    by_cases zero : id = 0 <;> simp [zero, TreePairing.write_reify]

theorem read_sized (protection : Protected) : TreeFactoredMemory.WellSized (readState protection) :=
  single_sized _ _ _ (TreePairing.read_uniform_arrays protection)

theorem write_sized (protection : Protected) : TreeFactoredMemory.WellSized (writeState protection) :=
  single_sized _ _ _ (TreePairing.write_uniform_arrays protection)

/-- Same one-allocation geometry, with a separately explicit two-byte tree. -/
def twoTopology : TreeFactored.Topology := .node (.cons TreePairing.leaf .nil)
def twoStore : TreeFactored.Store
  | [] => ⟨[.unprot .unique, .unprot .unique], .no⟩
  | [0] => ⟨[.prot (.reserved false false), .prot (.reserved true false)], .strong⟩
  | _ => TreePairing.absentEntry

def twoRead : F := single (TreeMemoryControls.block 2) ⟨twoTopology, twoStore⟩ [(0, [0])]

theorem two_reify : TreeFactoredMemory.reify twoRead = TreeMemoryControls.twoRead := by
  unfold TreeFactoredMemory.reify twoRead single TreeMemoryControls.twoRead
    TreeMemoryControls.initial TreeMemory.setTree
  congr 1
  funext id
  by_cases zero : id = 0 <;>
    simp [zero, TreeCorrespondence.reify, TreeCorrespondence.reifyTree,
      TreeCorrespondence.reifyForest, twoTopology, twoStore, TreePairing.leaf,
      TreeMemoryControls.twoTree]

theorem two_sized : TreeFactoredMemory.WellSized twoRead := by
  apply single_sized
  simp [TreeMemoryControls.block, twoTopology, twoStore, TreePairing.leaf,
    TreeFactored.arrayLengthsTree, TreeFactored.arrayLengthsForest]

/-- A dead record is still in the geometry domain and retains its tree/frame. -/
def deadWeak : F :=
  single { TreeMemoryControls.writtenBlock with live := false }
    (TreePairing.writeState .weak) [(0, [0, 0])]

theorem dead_weak_reify :
    TreeFactoredMemory.reify deadWeak = TreeMemoryControls.deadWeak := by
  unfold TreeFactoredMemory.reify deadWeak single TreeMemoryControls.deadWeak
    TreeMemoryControls.freed TreeMemoryControls.writeState TreeMemoryControls.readState
    TreeMemoryControls.stateAB TreeMemoryControls.stateA TreeMemoryControls.initial
    TreeMemory.setTree MiniRustReference.replace
  dsimp only
  congr 1
  · congr 1
    funext id
    by_cases zero : id = 0 <;> simp [zero]
  · funext id
    by_cases zero : id = 0 <;> simp [zero, TreePairing.write_reify]

theorem dead_weak_sized : TreeFactoredMemory.WellSized deadWeak :=
  single_sized _ _ _ (TreePairing.write_uniform_arrays .weak)

/-- Only shape-admitted: no reference construction/reachability claim. -/
def liveFailureStore : TreeFactored.Store
  | [] => ⟨[.unprot .frozen], .no⟩
  | [0] => ⟨[.prot .unique], .strong⟩
  | _ => TreePairing.absentEntry

def liveFailure : F :=
  single (TreeMemoryControls.block 1) ⟨twoTopology, liveFailureStore⟩ [(0, [0])]

theorem live_failure_reify :
    TreeFactoredMemory.reify liveFailure = TreeMemoryControls.liveFailure := by
  unfold TreeFactoredMemory.reify liveFailure single TreeMemoryControls.liveFailure
    TreeMemoryControls.initial TreeMemory.setTree
  congr 1
  funext id
  by_cases zero : id = 0 <;>
    simp [zero, TreeCorrespondence.reify, TreeCorrespondence.reifyTree,
      TreeCorrespondence.reifyForest, twoTopology, liveFailureStore, TreePairing.leaf,
      TreeMemoryControls.liveFailureTree]

theorem live_failure_sized : TreeFactoredMemory.WellSized liveFailure := by
  apply single_sized
  simp [TreeMemoryControls.block, twoTopology, liveFailureStore, TreePairing.leaf,
    TreeFactored.arrayLengthsTree, TreeFactored.arrayLengthsForest]

#print axioms single_sized
#print axioms read_reify
#print axioms write_reify
#print axioms read_sized
#print axioms write_sized
#print axioms two_reify
#print axioms two_sized
#print axioms dead_weak_reify
#print axioms dead_weak_sized
#print axioms live_failure_reify
#print axioms live_failure_sized

end AnnealResearch.TreeMemoryPairing
