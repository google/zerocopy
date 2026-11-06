import AnnealResearch.TreeMemoryPairing
import AnnealResearch.TreeMemoryDomain
import AnnealResearch.TreeTraversalGeometryPublic

/-!
Independent bounded controls for structural closure. The live-Frozen input is
the existing explicit shape-admitted fixture, with no program-reachability or
Rust-source construction claim. Actual factored unprotect/traversal/release
equations are proved directly; no pending wrapper-preservation theorem and no
default success extraction is used.

Resizing controls deliberately change one permission list or one actual raw
allocation-size field. They are fault injections, not altered frozen runners.
Width can remain correct while permissions and flags cease to match.
-/

namespace AnnealResearch.TreeGeometryControls

open TreePermissions

def beforeTree : TreeFactored.State :=
  ⟨TreeMemoryPairing.twoTopology, TreeMemoryPairing.liveFailureStore⟩

/-- The expected changed payload is explicit; this pure selected-entry update
does not invoke unprotect, releaseTraverse, or memory release. -/
def convertedTree : TreeFactored.State :=
  ⟨TreeMemoryPairing.twoTopology,
    TreeFactored.setPermissions TreeMemoryPairing.liveFailureStore [0] [.unprot .unique]⟩

def changedState : TreeFactoredMemory.State :=
  TreeFactoredMemory.setTree TreeMemoryPairing.liveFailure 0 convertedTree

theorem converted_payloads :
    convertedTree.store [] = ⟨[.unprot .frozen], .no⟩ ∧
      convertedTree.store [0] = ⟨[.unprot .unique], .strong⟩ := ⟨rfl, rfl⟩

theorem actual_unprotect :
    TreeFactored.unprotectAt beforeTree [0] = .ok [some .write] convertedTree := rfl

theorem actual_traversal_UB :
    TreeFactored.releaseTraverse convertedTree [0] [some .write] =
      .ub .unprotectedLocalWriteFrozen convertedTree := by
  simp [TreeFactored.releaseTraverse, TreeFactored.findTopology, TreeFactored.Forest.get?,
    TreeFactored.arrayLengths, TreeFactored.arrayLengthsTree, TreeFactored.arrayLengthsForest,
    convertedTree, TreeMemoryPairing.twoTopology, TreePairing.leaf,
    TreeMemoryPairing.liveFailureStore, TreeFactored.setPermissions, TreeFactored.overwrite,
    TreeFactored.releaseCore, TreeFactored.releaseTree, TreeFactored.releaseOffsets,
    TreeFactored.transitionAt, TreeFactored.permissionAt, TreeFactored.Result.bind,
    TreeFactored.Result.mapState, TreeFactored.nodeRelation, Permission.transition,
    UPermission.transition, UPermission.localWrite] <;> rfl

/-- The error commits conversion before the live traversal fails at the root. -/
theorem actual_release_UB :
    TreeFactoredMemory.release TreeMemoryPairing.liveFailure (0, [0]) =
      .ub (.tree .unprotectedLocalWriteFrozen) changedState := by
  change TreeFactoredMemory.release
      (TreeMemoryPairing.single (TreeMemoryControls.block 1) beforeTree [(0, [0])]) (0, [0]) =
    .ub (.tree .unprotectedLocalWriteFrozen)
      (TreeFactoredMemory.setTree
        (TreeMemoryPairing.single (TreeMemoryControls.block 1) beforeTree [(0, [0])])
        0 convertedTree)
  simp [TreeFactoredMemory.release, TreeMemoryPairing.single, TreeMemoryControls.block,
    actual_unprotect, actual_traversal_UB] <;> rfl

theorem converted_geometry : TreeMemoryDomain.SameTreeGeometry beforeTree convertedTree := by
  refine ⟨rfl, ?_⟩
  exact TreeTraversalGeometry.setPermissions_sameLengths
    TreeMemoryPairing.liveFailureStore [0] [.unprot .unique] rfl

theorem changed_sized : TreeFactoredMemory.WellSized changedState := by
  exact TreeMemoryDomain.wellSized_replace_tree TreeMemoryPairing.liveFailure 0 beforeTree
    convertedTree TreeMemoryPairing.live_failure_sized rfl converted_geometry

theorem actual_UB_residual_sized :
    TreeFactoredMemory.WellSized
      (TreeFactoredMemory.release TreeMemoryPairing.liveFailure (0, [0])).residual := by
  rw [actual_release_UB]
  exact changed_sized

theorem changed_state : changedState ≠ TreeMemoryPairing.liveFailure := by
  intro same
  have payload := congrArg
    (fun state : TreeFactoredMemory.State =>
      (state.trees 0).map (fun tree => (tree.store [0]).permissions)) same
  simp [changedState, TreeFactoredMemory.setTree, TreeMemoryPairing.liveFailure,
    TreeMemoryPairing.single, convertedTree, TreeFactored.setPermissions,
    TreeFactored.overwrite, TreeMemoryPairing.liveFailureStore] at payload

/-- This actual changed UB residual remains width-admitted even though the
converted Unprot child retains its Strong flag and fails kind matching. -/
theorem converted_kind_mismatch : TreeFactored.matchesProtectors convertedTree = false := by
  simp [TreeFactored.matchesProtectors, TreeFactored.matchingTree,
    TreeFactored.matchingForest, convertedTree, TreeMemoryPairing.twoTopology,
    TreePairing.leaf, TreeMemoryPairing.liveFailureStore, TreeFactored.setPermissions,
    TreeFactored.overwrite, Permission.matchesProtector, Permission.isProt, Protected.yes]

def permissionResizeTree : TreeFactored.State :=
  { beforeTree with store := TreeFactored.setPermissions beforeTree.store [] [] }

def permissionResize : TreeFactoredMemory.State :=
  TreeFactoredMemory.setTree TreeMemoryPairing.liveFailure 0 permissionResizeTree

theorem permission_resize_not_sized : ¬ TreeFactoredMemory.WellSized permissionResize := by
  intro sized
  have uniform := sized 0 (TreeMemoryControls.block 1) permissionResizeTree rfl rfl
  have rootWidth := TreeValidated.uniform_root_width permissionResizeTree.topology []
    permissionResizeTree.store (TreeMemoryControls.block 1).size uniform
  simp [permissionResizeTree, beforeTree, TreeFactored.setPermissions,
    TreeFactored.overwrite, TreeMemoryControls.block] at rootWidth

def resizedAllocation : MiniRustReference.Allocation :=
  { TreeMemoryControls.block 1 with size := 0 }

def allocationResize : TreeFactoredMemory.State :=
  let resizedRaw := MiniRustReference.replace (TreeMemoryPairing.liveFailure.raw) 0 resizedAllocation
  { TreeMemoryPairing.liveFailure with raw := resizedRaw }

theorem allocation_resize_not_sized : ¬ TreeFactoredMemory.WellSized allocationResize := by
  intro sized
  have uniform := sized 0 resizedAllocation beforeTree rfl rfl
  have rootWidth := TreeValidated.uniform_root_width beforeTree.topology [] beforeTree.store
    resizedAllocation.size uniform
  simp [beforeTree, TreeMemoryPairing.liveFailureStore, resizedAllocation] at rootWidth

theorem resized_record_present_zero :
    TreeRawGeometry.sizeMap allocationResize.raw 0 = some 0 := rfl

/-- Absence and a present zero-sized allocation are different raw geometries. -/
theorem absent_not_present_zero :
    ¬ TreeRawGeometry.SameSizeMap MiniRustReference.empty allocationResize.raw := by
  intro same
  have impossible := same 0
  simp [TreeRawGeometry.sizeMap, MiniRustReference.empty, allocationResize,
    MiniRustReference.replace, resizedAllocation] at impossible

#print axioms converted_payloads
#print axioms actual_unprotect
#print axioms actual_traversal_UB
#print axioms actual_release_UB
#print axioms converted_geometry
#print axioms changed_sized
#print axioms actual_UB_residual_sized
#print axioms changed_state
#print axioms converted_kind_mismatch
#print axioms permission_resize_not_sized
#print axioms allocation_resize_not_sized
#print axioms resized_record_present_zero
#print axioms absent_not_present_zero

end AnnealResearch.TreeGeometryControls
