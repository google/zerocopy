import AnnealResearch.TreeMemoryOperations
import AnnealResearch.TreeMemoryReleaseAgreement
import AnnealResearch.TreeMemoryPairing

/-!
Paired operation controls reuse the universal correspondence at explicit complete
memory representatives. Equality observes the actual factored result through full
reification; it is not an independently executed factored reborrow history.
Direct validation controls expose ordering and zero-sized hook boundaries.
-/
namespace AnnealResearch.TreeMemoryCompositionControls

open TreePermissions

-- Earlier reference histories supply actual, checked construction equations.
theorem actual_strong_write :
    TreeFactoredMemory.translate (TreeFactoredMemory.store
      (TreeMemoryPairing.readState .strong) TreeMemoryControls.t [TreeMemoryControls.seven] 1) =
    .ok () (TreeMemoryControls.writeState .strong) := by
  rw [← TreeMemoryOperations.store_agrees _ _ _ _ (TreeMemoryPairing.read_sized .strong),
    TreeMemoryPairing.read_reify, TreeMemoryControls.actual_strong_write]

theorem actual_weak_write :
    TreeFactoredMemory.translate (TreeFactoredMemory.store
      (TreeMemoryPairing.readState .weak) TreeMemoryControls.t [TreeMemoryControls.seven] 1) =
    .ok () (TreeMemoryControls.writeState .weak) := by
  rw [← TreeMemoryOperations.store_agrees _ _ _ _ (TreeMemoryPairing.read_sized .weak),
    TreeMemoryPairing.read_reify, TreeMemoryControls.actual_weak_write]

theorem strong_grandchild_blocks_free :
    TreeFactoredMemory.translate (TreeFactoredMemory.deallocate
      (TreeMemoryPairing.writeState .strong) TreeMemoryControls.t .heap 1 1) =
    .ub .strongProtector (TreeMemoryControls.writeState .strong) := by
  rw [← TreeMemoryOperations.deallocate_agrees _ _ _ _ _ (TreeMemoryPairing.write_sized .strong),
    TreeMemoryPairing.write_reify, TreeMemoryControls.strong_grandchild_blocks_free]

theorem weak_used_grandchild_allows_free :
    TreeFactoredMemory.translate (TreeFactoredMemory.deallocate
      (TreeMemoryPairing.writeState .weak) TreeMemoryControls.t .heap 1 1) =
    .ok () (TreeMemoryControls.freed (TreeMemoryControls.writeState .weak)
      (TreeMemoryControls.treeWrite .weak) TreeMemoryControls.writtenBlock) := by
  rw [← TreeMemoryOperations.deallocate_agrees _ _ _ _ _ (TreeMemoryPairing.write_sized .weak),
    TreeMemoryPairing.write_reify, TreeMemoryControls.weak_used_grandchild_allows_free]

theorem live_release :
    TreeFactoredMemory.translate (TreeFactoredMemory.release
      (TreeMemoryPairing.writeState .strong) (0, [0, 0])) =
    .ok () TreeMemoryControls.releasedState := by
  rw [← TreeMemoryReleaseAgreement.release_agrees _ _ (TreeMemoryPairing.write_sized .strong),
    TreeMemoryPairing.write_reify, TreeMemoryControls.successful_live_release]

theorem dead_weak_release :
    TreeFactoredMemory.translate (TreeFactoredMemory.release TreeMemoryPairing.deadWeak
      (0, [0, 0])) = .ok () TreeMemoryControls.deadWeakReleased := by
  rw [← TreeMemoryReleaseAgreement.release_agrees _ _ TreeMemoryPairing.dead_weak_sized,
    TreeMemoryPairing.dead_weak_reify, TreeMemoryControls.successful_dead_weak_release]

theorem two_byte_public_store_rolls_back :
    TreeFactoredMemory.translate (TreeFactoredMemory.store TreeMemoryPairing.twoRead
      TreeMemoryControls.root [TreeMemoryControls.seven, TreeMemoryControls.seven] 1) =
    .ub (.tree .protectedForeignWriteReservedAfterLocalRead) TreeMemoryControls.twoRead := by
  rw [← TreeMemoryOperations.store_agrees _ _ _ _ TreeMemoryPairing.two_sized,
    TreeMemoryPairing.two_reify, TreeMemoryControls.two_byte_public_store_rolls_back]

/-- This input has explicit geometry but is not claimed program reachable. -/
theorem live_failed_release_commits_conversion :
    TreeFactoredMemory.translate (TreeFactoredMemory.release TreeMemoryPairing.liveFailure
      (0, [0])) = .ub (.tree .unprotectedLocalWriteFrozen)
      (TreeMemory.setTree TreeMemoryControls.liveFailure 0 TreeMemoryControls.liveFailureConverted) := by
  rw [← TreeMemoryReleaseAgreement.release_agrees _ _ TreeMemoryPairing.live_failure_sized,
    TreeMemoryPairing.live_failure_reify, TreeMemoryControls.live_failed_release_commits_conversion]

def missingTree (size : Nat) : TreeFactoredMemory.State :=
  { raw := (TreeMemoryControls.initial size).raw
    trees := fun _ => none
    currentFrame := [(99, [7])] }

def invalidPath : TreeMemory.Pointer := ⟨16, some (0, [99])⟩
def badBounds : TreeMemory.Pointer := ⟨18, some (0, [99])⟩
def misaligned : TreeMemory.Pointer := ⟨17, some (0, [99])⟩

theorem missing_tree_geometry (size : Nat) :
    TreeFactoredMemory.WellSized (missingTree size) := by
  intro id allocation tree allocated found
  simp [missingTree] at found

theorem metadata_dominates_missing_tree :
    TreeFactoredMemory.load (missingTree 1) badBounds 1 1 =
    .ub (.basic .bounds) (missingTree 1) := by
  simp [TreeFactoredMemory.load, MiniRustReference.load, MiniRustReference.checkPtr,
    TreeMemory.Pointer.basic, missingTree, TreeMemoryControls.initial,
    TreeMemoryControls.block, badBounds]

theorem valid_raw_missing_tree :
    TreeFactoredMemory.load (missingTree 1) invalidPath 1 1 =
    .unsupported .missingTree (missingTree 1) := by
  simp [TreeFactoredMemory.load, MiniRustReference.load, MiniRustReference.checkPtr,
    TreeFactoredMemory.hookTarget, TreeMemory.Pointer.basic, missingTree,
    TreeMemoryControls.initial, TreeMemoryControls.block, invalidPath]

theorem aligned_zero_load_skips_tree :
    TreeFactoredMemory.load (missingTree 1) invalidPath 0 8 = .ok [] (missingTree 1) := by
  simp [TreeFactoredMemory.load, MiniRustReference.load, MiniRustReference.checkPtr,
    TreeMemory.Pointer.basic, invalidPath]

theorem aligned_empty_store_skips_tree :
    TreeFactoredMemory.store (missingTree 1) invalidPath [] 8 = .ok () (missingTree 1) := by
  simp [TreeFactoredMemory.store, MiniRustReference.store, MiniRustReference.checkPtr,
    TreeMemory.Pointer.basic, invalidPath]

theorem misaligned_zero_load_fails_first :
    TreeFactoredMemory.load (missingTree 1) misaligned 0 8 =
    .ub (.basic .misalignedLoad) (missingTree 1) := by
  simp [TreeFactoredMemory.load, MiniRustReference.load, TreeMemory.Pointer.basic, misaligned]

theorem misaligned_empty_store_fails_first :
    TreeFactoredMemory.store (missingTree 1) misaligned [] 8 =
    .ub (.basic .misalignedStore) (missingTree 1) := by
  simp [TreeFactoredMemory.store, MiniRustReference.store, TreeMemory.Pointer.basic, misaligned]

theorem zero_free_checks_metadata :
    TreeFactoredMemory.deallocate (missingTree 0) invalidPath .heap 0 8 =
    .ub (.basic .freeAlign) (missingTree 0) := by
  simp [TreeFactoredMemory.deallocate, MiniRustReference.free, TreeMemory.Pointer.basic,
    missingTree, TreeMemoryControls.initial, TreeMemoryControls.block, invalidPath]

theorem zero_free_requires_tree :
    TreeFactoredMemory.deallocate (missingTree 0) invalidPath .heap 0 1 =
    .unsupported .missingTree (missingTree 0) := by
  simp [TreeFactoredMemory.deallocate, MiniRustReference.free, TreeMemory.Pointer.basic,
    TreeFactoredMemory.hookTarget, missingTree, TreeMemoryControls.initial,
    TreeMemoryControls.block, invalidPath]

def emptyTree : TreeFactored.State :=
  ⟨TreePairing.leaf, fun _ => ⟨[], .no⟩⟩
def emptyAllocation : TreeFactoredMemory.State :=
  TreeMemoryPairing.single (TreeMemoryControls.block 0) emptyTree []

theorem zero_free_checks_path :
    TreeFactoredMemory.deallocate emptyAllocation invalidPath .heap 0 1 =
    .unsupported (.tree .invalidPath) emptyAllocation := by
  simp [TreeFactoredMemory.deallocate, MiniRustReference.free, TreeMemory.Pointer.basic,
    TreeFactoredMemory.hookTarget, emptyAllocation, TreeMemoryPairing.single,
    TreeMemoryControls.block, invalidPath, TreeFactored.access, emptyTree,
    TreeFactored.findTopology, TreeFactored.Forest.get?, TreePairing.leaf,
    TreeCorrespondence.structuralToReference]

#print axioms actual_strong_write
#print axioms actual_weak_write
#print axioms strong_grandchild_blocks_free
#print axioms weak_used_grandchild_allows_free
#print axioms live_release
#print axioms dead_weak_release
#print axioms two_byte_public_store_rolls_back
#print axioms live_failed_release_commits_conversion
#print axioms missing_tree_geometry
#print axioms metadata_dominates_missing_tree
#print axioms valid_raw_missing_tree
#print axioms aligned_zero_load_skips_tree
#print axioms aligned_empty_store_skips_tree
#print axioms misaligned_zero_load_fails_first
#print axioms misaligned_empty_store_fails_first
#print axioms zero_free_checks_metadata
#print axioms zero_free_requires_tree
#print axioms zero_free_checks_path

end AnnealResearch.TreeMemoryCompositionControls
