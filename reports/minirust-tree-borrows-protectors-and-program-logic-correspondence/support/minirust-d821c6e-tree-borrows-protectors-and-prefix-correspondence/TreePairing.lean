import AnnealResearch.TreeQueries
import AnnealResearch.TreeMemoryControls

/-!
Concrete coverage of the frozen representation relation for the independently
constructed reference history.  The topology includes root R, children A/B in
that order, and T below A.  Every represented path has an explicit payload.

No operation agreement is assumed or proved here.  The old reference reborrow
and write equations are reused only to identify the history's actual resulting
tree.  The factored runner is not defined by executing/reifying the reference.
No general inverse encoding, source-state coverage or Rust adequacy is claimed.
The parent owns compiler checks.
-/
namespace AnnealResearch.TreePairing

open TreePermissions

def leaf : TreeFactored.Topology := .node .nil
def aTopology : TreeFactored.Topology := .node (.cons leaf .nil)
def topology : TreeFactored.Topology := .node (.cons aTopology (.cons leaf .nil))

def absentEntry : TreeFactored.Entry := ⟨[], .no⟩

def readStore (protection : Protected) : TreeFactored.Store
  | [] => ⟨[.unprot .unique], .no⟩
  | [0] => ⟨[.unprot .reserved], .no⟩
  | [1] => ⟨[.unprot .reserved], .no⟩
  | [0, 0] => ⟨[.prot (.reserved true false)], protection⟩
  | _ => absentEntry

def writeStore (protection : Protected) : TreeFactored.Store
  | [] => ⟨[.unprot .unique], .no⟩
  | [0] => ⟨[.unprot .unique], .no⟩
  | [1] => ⟨[.unprot .disabled], .no⟩
  | [0, 0] => ⟨[.prot .unique], protection⟩
  | _ => absentEntry

def readState (protection : Protected) : TreeFactored.State := ⟨topology, readStore protection⟩
def writeState (protection : Protected) : TreeFactored.State := ⟨topology, writeStore protection⟩

theorem read_reify (protection : Protected) :
    TreeCorrespondence.reify (readState protection) = TreeMemoryControls.treeRead protection := rfl

theorem write_reify (protection : Protected) :
    TreeCorrespondence.reify (writeState protection) = TreeMemoryControls.treeWrite protection := rfl

theorem read_related (protection : Protected) :
    TreeCorrespondence.Related (TreeMemoryControls.treeRead protection) (readState protection) :=
  (read_reify protection).symm

theorem write_related (protection : Protected) :
    TreeCorrespondence.Related (TreeMemoryControls.treeWrite protection) (writeState protection) :=
  (write_reify protection).symm

theorem all_four_paths_present :
    TreeFactored.findTopology topology [] = some topology ∧
    TreeFactored.findTopology topology [0] = some aTopology ∧
    TreeFactored.findTopology topology [1] = some leaf ∧
    TreeFactored.findTopology topology [0, 0] = some leaf := ⟨rfl, rfl, rfl, rfl⟩

theorem read_uniform_arrays (protection : Protected) :
    TreeFactored.arrayLengthsTree topology [] (readStore protection) 1 = true := by
  change TreeFactored.arrayLengthsTree (readState protection).topology []
    (readState protection).store 1 = true
  rw [← TreeQueries.arraysSized_reify (readState protection) 1, read_reify]
  simp [TreeMemoryControls.treeRead, TreeReference.arraysSized, TreeReference.childrenSized]

theorem write_uniform_arrays (protection : Protected) :
    TreeFactored.arrayLengthsTree topology [] (writeStore protection) 1 = true := by
  change TreeFactored.arrayLengthsTree (writeState protection).topology []
    (writeState protection).store 1 = true
  rw [← TreeQueries.arraysSized_reify (writeState protection) 1, write_reify]
  simp [TreeMemoryControls.treeWrite, TreeReference.arraysSized, TreeReference.childrenSized]

theorem read_public_arrays (protection : Protected) :
    TreeFactored.arrayLengths (readState protection) = true := by
  rw [← TreeQueries.arrayLengths_reify_root (readState protection), read_reify]
  simp [TreeMemoryControls.treeRead, TreeReference.Node.permissions,
    TreeReference.arraysSized, TreeReference.childrenSized]

theorem write_public_arrays (protection : Protected) :
    TreeFactored.arrayLengths (writeState protection) = true := by
  rw [← TreeQueries.arrayLengths_reify_root (writeState protection), write_reify]
  simp [TreeMemoryControls.treeWrite, TreeReference.Node.permissions,
    TreeReference.arraysSized, TreeReference.childrenSized]

theorem read_strong_query (protection : Protected) :
    TreeFactored.containsStrong (readState protection) = decide (protection = .strong) := by
  rw [← TreeQueries.containsStrong_reify (readState protection), read_reify]
  simp [TreeMemoryControls.treeRead, TreeReference.containsStrong,
    TreeReference.childrenContainStrong, Permission.preventsDeallocation,
    PPermission.preventsDeallocation]

theorem write_strong_query (protection : Protected) :
    TreeFactored.containsStrong (writeState protection) = decide (protection = .strong) := by
  rw [← TreeQueries.containsStrong_reify (writeState protection), write_reify]
  simp [TreeMemoryControls.treeWrite, TreeReference.containsStrong,
    TreeReference.childrenContainStrong, Permission.preventsDeallocation,
    PPermission.preventsDeallocation]

/-- Generic p=no remains a syntactic mismatch, rather than being filtered out.
Actual reference construction below is asserted only for Strong and Weak. -/
theorem read_kind_query (protection : Protected) :
    TreeFactored.matchesProtectors (readState protection) = protection.yes := by
  rw [← TreeQueries.kindsMatch_reify (readState protection), read_reify]
  cases protection <;>
    simp [TreeMemoryControls.treeRead, TreeReference.kindsMatch, TreeReference.childrenMatch,
      Permission.matchesProtector, Permission.isProt, Protected.yes]

theorem write_kind_query (protection : Protected) :
    TreeFactored.matchesProtectors (writeState protection) = protection.yes := by
  rw [← TreeQueries.kindsMatch_reify (writeState protection), write_reify]
  cases protection <;>
    simp [TreeMemoryControls.treeWrite, TreeReference.kindsMatch, TreeReference.childrenMatch,
      Permission.matchesProtector, Permission.isProt, Protected.yes]

def initialStore : TreeFactored.Store
  | [] => ⟨[.unprot .unique], .no⟩
  | _ => absentEntry

def initialState : TreeFactored.State := ⟨leaf, initialStore⟩

theorem initial_reify : TreeCorrespondence.reify initialState =
    TreeReference.Node.mk [.unprot .unique] .no [] := rfl

theorem initial_root_covered : (TreeMemoryControls.initial 1).trees 0 =
    some (TreeCorrespondence.reify initialState) := rfl

/-- The reference result is an actual checked reborrow chain, not a claimed
factored execution. The paired factored state is separately explicit above. -/
theorem constructed_strong_read_covered :
    TreeMemoryControls.constructRead .strong =
      .ok TreeMemoryControls.t (TreeMemoryControls.readState .strong) ∧
    (TreeMemoryControls.readState .strong).trees 0 =
      some (TreeCorrespondence.reify (readState .strong)) := by
  constructor
  · exact TreeMemoryControls.full_strong_construction
  · rw [read_reify]
    simp [TreeMemoryControls.readState, TreeMemory.setTree]

theorem constructed_weak_read_covered :
    TreeMemoryControls.constructRead .weak =
      .ok TreeMemoryControls.t (TreeMemoryControls.readState .weak) ∧
    (TreeMemoryControls.readState .weak).trees 0 =
      some (TreeCorrespondence.reify (readState .weak)) := by
  constructor
  · exact TreeMemoryControls.full_weak_construction
  · rw [read_reify]
    simp [TreeMemoryControls.readState, TreeMemory.setTree]

theorem actual_strong_write_covered :
    TreeMemory.store (TreeMemoryControls.readState .strong) TreeMemoryControls.t
      [TreeMemoryControls.seven] 1 = .ok () (TreeMemoryControls.writeState .strong) ∧
    (TreeMemoryControls.writeState .strong).trees 0 =
      some (TreeCorrespondence.reify (writeState .strong)) := by
  constructor
  · exact TreeMemoryControls.actual_strong_write
  · rw [write_reify]
    simp [TreeMemoryControls.writeState, TreeMemory.setTree]

theorem actual_weak_write_covered :
    TreeMemory.store (TreeMemoryControls.readState .weak) TreeMemoryControls.t
      [TreeMemoryControls.seven] 1 = .ok () (TreeMemoryControls.writeState .weak) ∧
    (TreeMemoryControls.writeState .weak).trees 0 =
      some (TreeCorrespondence.reify (writeState .weak)) := by
  constructor
  · exact TreeMemoryControls.actual_weak_write
  · rw [write_reify]
    simp [TreeMemoryControls.writeState, TreeMemory.setTree]

theorem absent_two : ¬ TreeCorrespondence.representedTree topology [] [2] := by
  simp [TreeCorrespondence.representedTree, TreeCorrespondence.representedForest,
    topology, aTopology, leaf]

theorem read_absent_entry_irrelevant (protection : Protected) (entry : TreeFactored.Entry) :
    TreeCorrespondence.reify ⟨topology, TreeFactored.overwrite (readStore protection) [2] entry⟩ =
      TreeCorrespondence.reify (readState protection) :=
  TreeCorrespondence.overwrite_absent_preserves_reify topology [] [2]
    (readStore protection) entry absent_two

theorem write_absent_entry_irrelevant (protection : Protected) (entry : TreeFactored.Entry) :
    TreeCorrespondence.reify ⟨topology, TreeFactored.overwrite (writeStore protection) [2] entry⟩ =
      TreeCorrespondence.reify (writeState protection) :=
  TreeCorrespondence.overwrite_absent_preserves_reify topology [] [2]
    (writeStore protection) entry absent_two

#print axioms read_reify
#print axioms write_reify
#print axioms read_related
#print axioms write_related
#print axioms all_four_paths_present
#print axioms read_uniform_arrays
#print axioms write_uniform_arrays
#print axioms read_public_arrays
#print axioms write_public_arrays
#print axioms read_strong_query
#print axioms write_strong_query
#print axioms read_kind_query
#print axioms write_kind_query
#print axioms initial_reify
#print axioms initial_root_covered
#print axioms constructed_strong_read_covered
#print axioms constructed_weak_read_covered
#print axioms actual_strong_write_covered
#print axioms actual_weak_write_covered
#print axioms absent_two
#print axioms read_absent_entry_irrelevant
#print axioms write_absent_entry_irrelevant

end AnnealResearch.TreePairing
