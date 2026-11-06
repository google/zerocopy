import AnnealResearch.TreeLookup

/-!
Validated public operation correspondence on a structural uniform-array
domain. Paths and requested access ranges remain arbitrary: missing paths and
out-of-range accesses are compared as actual owned unsupported results. Scalar
UB is never an admission failure. No live/free-metadata, scalar-success, NoUB
or flag/kind matching premise is imposed.

This does not compare all malformed-input diagnostics. The frozen validators
order shape/path checks differently, and release also compares access-list
width with array width at different points.
-/

namespace AnnealResearch.TreeValidated

open TreePermissions
open TreeFactored (Path Topology Store State)
open TreeCorrespondence (reify Related)
open TreeAgreement (translate)

theorem uniform_root_width (topology : Topology) (here : Path) (store : Store) (width : Nat)
    (uniform : TreeFactored.arrayLengthsTree topology here store width = true) :
    (store here).permissions.length = width := by
  cases topology with
  | node children =>
    have parts : (store here).permissions.length = width ∧
        TreeFactored.arrayLengthsForest children here 0 store width = true := by
      simpa [TreeFactored.arrayLengthsTree] using uniform
    exact parts.1

theorem uniform_arrayLengths (state : State) (width : Nat)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true) :
    TreeFactored.arrayLengths state = true := by
  unfold TreeFactored.arrayLengths
  rw [uniform_root_width state.topology [] state.store width uniform]
  exact uniform

/-- Any path and any requested byte interval are allowed. Uniform arrays remove
the shape/path diagnostic-order discrepancy, while the checked wrappers retain
their actual missing-path and range rejection branches. -/
theorem access_agrees (state : State) (path : Path) (kind : AccessKind)
    (offset size width : Nat)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true) :
    TreeReference.access (reify state) (some path) kind offset size =
      translate reify (TreeFactored.access state path kind offset size) := by
  have rootWidth := uniform_root_width state.topology [] state.store width uniform
  have referenceWidth : (reify state).permissions.length = width := by
    simpa only [reify, TreeQueries.reifyTree_permissions] using rootWidth
  have factoredArrays := uniform_arrayLengths state width uniform
  have referenceArrays :
      TreeReference.arraysSized (reify state) (reify state).permissions.length = true := by
    rw [TreeQueries.arrayLengths_reify_root]
    exact factoredArrays
  have referenceArraysAtWidth : TreeReference.arraysSized (reify state) width = true := by
    rw [TreeQueries.arraysSized_reify]
    exact uniform
  cases found : TreeFactored.findTopology state.topology path with
  | none =>
    have absent : TreeReference.pathPresent (reify state) (some path) = false := by
      rw [TreeLookup.pathPresent_reify, found]
      rfl
    simp [TreeReference.access, referenceArrays, absent, TreeFactored.access, found,
      translate, TreeCorrespondence.structuralToReference]
  | some child =>
    have present := TreeLookup.validPath_present state path child found
    by_cases outOfRange : width < offset + size
    · simp [TreeReference.access, referenceArraysAtWidth, present, referenceWidth,
        TreeFactored.access, found, factoredArrays, rootWidth, outOfRange,
        translate, TreeCorrespondence.structuralToReference]
    · have within : offset + size ≤ width := by omega
      have raw := TreeAgreement.accessCore_agrees state (some path) kind offset size width
        uniform within
      simpa [TreeReference.access, referenceArraysAtWidth, present, referenceWidth,
        TreeFactored.access, found, factoredArrays, rootWidth, outOfRange] using raw

theorem access_resultRel (state : State) (path : Path) (kind : AccessKind)
    (offset size width : Nat)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true) :
    TreeCorrespondence.ResultRel Related
      (TreeReference.access (reify state) (some path) kind offset size)
      (TreeFactored.access state path kind offset size) := by
  rw [access_agrees state path kind offset size width uniform]
  exact TreeAgreement.translate_resultRel _ reify

theorem related_access {reference : TreeReference.Node} (state : State)
    (related : Related reference state) (path : Path) (kind : AccessKind)
    (offset size width : Nat)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true) :
    TreeCorrespondence.ResultRel Related
      (TreeReference.access reference (some path) kind offset size)
      (TreeFactored.access state path kind offset size) := by
  rw [related]
  exact access_resultRel state path kind offset size width uniform

/-- Release's end-access list has the allocation width. Paths remain arbitrary,
so missing paths are compared as unsupported rather than assumed away. -/
theorem releaseTraverse_agrees (state : State) (path : Path)
    (accesses : List (Option AccessKind))
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store accesses.length = true) :
    TreeReference.releaseTraverse (reify state) (some path) accesses =
      translate reify (TreeFactored.releaseTraverse state path accesses) := by
  have rootWidth := uniform_root_width state.topology [] state.store accesses.length uniform
  have factoredArrays := uniform_arrayLengths state accesses.length uniform
  have referenceArrays : TreeReference.arraysSized (reify state) accesses.length = true := by
    rw [TreeQueries.arraysSized_reify]
    exact uniform
  cases found : TreeFactored.findTopology state.topology path with
  | none =>
    have absent : TreeReference.pathPresent (reify state) (some path) = false := by
      rw [TreeLookup.pathPresent_reify, found]
      rfl
    simp [TreeReference.releaseTraverse, referenceArrays, absent,
      TreeFactored.releaseTraverse, found, translate, TreeCorrespondence.structuralToReference]
  | some child =>
    have present := TreeLookup.validPath_present state path child found
    have raw := TreeReleaseAgreement.releaseCore_agrees state (some path) accesses uniform
    simpa [TreeReference.releaseTraverse, referenceArrays, present,
      TreeFactored.releaseTraverse, found, factoredArrays, rootWidth] using raw

theorem releaseTraverse_resultRel (state : State) (path : Path)
    (accesses : List (Option AccessKind))
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store accesses.length = true) :
    TreeCorrespondence.ResultRel Related
      (TreeReference.releaseTraverse (reify state) (some path) accesses)
      (TreeFactored.releaseTraverse state path accesses) := by
  rw [releaseTraverse_agrees state path accesses uniform]
  exact TreeAgreement.translate_resultRel _ reify

/-- Interface for a memory domain stated at the actual allocation size. The
end-list equality is structural and can be obtained from atomic unprotection. -/
theorem releaseTraverse_at_width (state : State) (path : Path)
    (accesses : List (Option AccessKind)) (width : Nat)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true)
    (endWidth : accesses.length = width) :
    TreeReference.releaseTraverse (reify state) (some path) accesses =
      translate reify (TreeFactored.releaseTraverse state path accesses) := by
  apply releaseTraverse_agrees
  simpa only [endWidth] using uniform

theorem related_releaseTraverse {reference : TreeReference.Node} (state : State)
    (related : Related reference state) (path : Path)
    (accesses : List (Option AccessKind)) (width : Nat)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true)
    (endWidth : accesses.length = width) :
    TreeCorrespondence.ResultRel Related
      (TreeReference.releaseTraverse reference (some path) accesses)
      (TreeFactored.releaseTraverse state path accesses) := by
  rw [related, releaseTraverse_at_width state path accesses width uniform endWidth]
  exact TreeAgreement.translate_resultRel _ reify

#print axioms uniform_root_width
#print axioms uniform_arrayLengths
#print axioms access_agrees
#print axioms access_resultRel
#print axioms related_access
#print axioms releaseTraverse_agrees
#print axioms releaseTraverse_resultRel
#print axioms releaseTraverse_at_width
#print axioms related_releaseTraverse

end AnnealResearch.TreeValidated
