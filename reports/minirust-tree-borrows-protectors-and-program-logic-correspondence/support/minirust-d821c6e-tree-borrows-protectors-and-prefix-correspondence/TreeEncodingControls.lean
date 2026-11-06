import AnnealResearch.TreeEncodingNormalization
import AnnealResearch.TreeMemoryPairing

/-!
An explicit absent-cell discriminator for reverse tree encoding. The represented
tree is one protected Cell leaf with a Strong flag. Its total store additionally
contains a two-permission Weak entry at the absent path [0]. Normalization
preserves the represented value/flag and full recursive reification, while
replacing that absent entry with the explicit zero-length default.

The memory controls pair the tree with an actual present live size-one raw
allocation and an explicit frame. WellSized is checked against this metadata;
it does not inspect absent tree cells. No operation, safety, historical
reachability, allocator universality or source/helper adequacy is inferred.
-/

namespace AnnealResearch.TreeEncodingControls

open TreePermissions
open TreeFactored (Path Entry Store State)
open TreeEncodingNormalization (normalize)

def leaf : TreeFactored.Topology := .node .nil

def rootEntry : Entry := ⟨[.prot .cell], .strong⟩
def absentEntry : Entry := ⟨[.unprot .unique, .unprot .frozen], .weak⟩

def store : Store
  | [] => rootEntry
  | [0] => absentEntry
  | _ => TreeEncoding.defaultEntry

def specimen : State := ⟨leaf, store⟩

theorem missing_child : TreeFactored.findTopology specimen.topology [0] = none := rfl

theorem normalized_root : (normalize specimen).store [] = rootEntry :=
  TreeEncodingNormalization.normalize_found specimen [] leaf rfl

theorem normalized_root_value_flag :
    ((normalize specimen).store []).permissions = [.prot .cell] ∧
      ((normalize specimen).store []).protection = .strong := by
  rw [normalized_root]
  exact ⟨rfl, rfl⟩

theorem normalized_absent :
    (normalize specimen).store [0] = TreeEncoding.defaultEntry :=
  TreeEncodingNormalization.normalize_missing specimen [0] missing_child

theorem normalization_changes_state : normalize specimen ≠ specimen := by
  intro same
  have impossible : TreeEncoding.defaultEntry = absentEntry := by
    calc
      TreeEncoding.defaultEntry = (normalize specimen).store [0] := normalized_absent.symm
      _ = specimen.store [0] := congrArg (fun state : State => state.store [0]) same
      _ = absentEntry := rfl
  have lengths := congrArg (fun entry : Entry => entry.permissions.length) impossible
  change (0 : Nat) = 2 at lengths
  omega

theorem reification_same :
    TreeCorrespondence.reify (normalize specimen) = TreeCorrespondence.reify specimen :=
  TreeEncodingNormalization.normalize_reify specimen

theorem specimen_uniform :
    TreeFactored.arrayLengthsTree specimen.topology [] specimen.store 1 = true := by
  simp [specimen, leaf, store, rootEntry, TreeFactored.arrayLengthsTree,
    TreeFactored.arrayLengthsForest]

theorem normalized_uniform :
    TreeFactored.arrayLengthsTree (normalize specimen).topology []
      (normalize specimen).store 1 = true := by
  rw [TreeEncodingNormalization.normalize_arrayLengthsTree]
  exact specimen_uniform

/-- Exact formula of the prior all-query geometry relation, repeated locally
to avoid importing a separate operation-preservation experiment. -/
def AllQueryGeometry (before after : State) : Prop :=
  after.topology = before.topology ∧
    ∀ query, (after.store query).permissions.length = (before.store query).permissions.length

theorem not_allQueryGeometry : ¬ AllQueryGeometry specimen (normalize specimen) := by
  intro geometry
  have lengths := geometry.2 [0]
  rw [normalized_absent] at lengths
  change (0 : Nat) = 2 at lengths
  omega

def memory : TreeFactoredMemory.State :=
  TreeMemoryPairing.single (TreeMemoryControls.block 1) specimen [(0, [])]

def normalizedMemory : TreeFactoredMemory.State :=
  TreeMemoryPairing.single (TreeMemoryControls.block 1) (normalize specimen) [(0, [])]

theorem actual_present_records :
    memory.raw.allocations 0 = some (TreeMemoryControls.block 1) ∧
      memory.trees 0 = some specimen ∧
      normalizedMemory.raw.allocations 0 = some (TreeMemoryControls.block 1) ∧
      normalizedMemory.trees 0 = some (normalize specimen) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem memory_wellSized : TreeFactoredMemory.WellSized memory :=
  TreeMemoryPairing.single_sized _ _ _ specimen_uniform

theorem normalizedMemory_wellSized : TreeFactoredMemory.WellSized normalizedMemory :=
  TreeMemoryPairing.single_sized _ _ _ normalized_uniform

theorem same_raw_and_frame :
    normalizedMemory.raw = memory.raw ∧
      normalizedMemory.currentFrame = memory.currentFrame := ⟨rfl, rfl⟩

theorem memory_reification_same :
    TreeFactoredMemory.reify normalizedMemory = TreeFactoredMemory.reify memory := by
  unfold TreeFactoredMemory.reify normalizedMemory memory TreeMemoryPairing.single
  congr 1
  funext id
  by_cases zero : id = 0 <;> simp [zero, reification_same]

#print axioms missing_child
#print axioms normalized_root
#print axioms normalized_root_value_flag
#print axioms normalized_absent
#print axioms normalization_changes_state
#print axioms reification_same
#print axioms specimen_uniform
#print axioms normalized_uniform
#print axioms not_allQueryGeometry
#print axioms actual_present_records
#print axioms memory_wellSized
#print axioms normalizedMemory_wellSized
#print axioms same_raw_and_frame
#print axioms memory_reification_same

end AnnealResearch.TreeEncodingControls
