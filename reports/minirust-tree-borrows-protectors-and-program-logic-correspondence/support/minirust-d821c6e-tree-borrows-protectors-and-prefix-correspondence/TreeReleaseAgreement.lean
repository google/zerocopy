import AnnealResearch.TreeAgreement

/-!
Exact raw recursive Node.release_protector agreement. The selected node clears
its flag and prunes its descendants; other nodes perform the supplied end
accesses in byte order and then visit ordered children. Every ordinary UB
residual is retained. Uniform allocation-sized arrays are a structural domain
premise, independent of permission/protector matching or access success.

This does not bind Memory.release_protector's prior unprotect stage, live/dead
branch, outer mutation, frame obligations or validated public entry point.
-/

namespace AnnealResearch.TreeReleaseAgreement

open TreePermissions
open TreeFactored (Path Topology Forest Store State)
open TreeCorrespondence (reifyTree reifyForest reify)
open TreeAgreement (translate)

/-- Selected release is domain-free: it reads no array offsets or descendants,
does no assertion/unprotect conversion, and changes only the selected flag. -/
theorem releaseSelected_agrees (topology : Topology) (here : Path) (store : Store)
    (accesses : List (Option AccessKind)) :
    TreeReference.releaseCore (reifyTree topology here store) (some []) accesses =
      translate (reifyTree topology here)
        (TreeFactored.releaseTree topology here store (some []) accesses) := by
  cases topology with
  | node children =>
    change TreeReference.releaseCore
      (.mk (store here).permissions (store here).protection (reifyForest children here 0 store))
        (some []) accesses = _
    rw [TreeReference.release_selected_stops, TreeFactored.releaseTree_selected]
    simp only [translate]
    rw [TreeTraversal.reifyTree_setProtected]

mutual
  theorem releaseTree_agrees (topology : Topology) (here : Path) (store : Store)
      (path : Option Path) (accesses : List (Option AccessKind))
      (uniform : TreeFactored.arrayLengthsTree topology here store accesses.length = true) :
      TreeReference.releaseCore (reifyTree topology here store) path accesses =
        translate (reifyTree topology here)
          (TreeFactored.releaseTree topology here store path accesses) := by
    cases topology with
    | node children =>
      by_cases selected : path = some []
      · subst path
        exact releaseSelected_agrees (.node children) here store accesses
      · have parts : (store here).permissions.length = accesses.length ∧
            TreeFactored.arrayLengthsForest children here 0 store accesses.length = true := by
          simpa [TreeFactored.arrayLengthsTree] using uniform
        change TreeReference.releaseCore
          (.mk (store here).permissions (store here).protection (reifyForest children here 0 store))
            path accesses =
          translate (reifyTree (.node children) here)
            (TreeFactored.releaseTree (.node children) here store path accesses)
        rw [TreeReference.releaseCore, TreeFactored.releaseTree]
        all_goals try exact selected
        rw [TreeAgreement.nodeRelation_agrees,
          TreeOperations.releaseArray_agrees store here (TreeFactored.nodeRelation path)
            accesses parts.1]
        cases array : TreeReference.applyAccesses (store here).permissions accesses
            (TreeFactored.nodeRelation path) with
        | ok value permissions =>
          cases value
          simp only [TreeOperations.liftArray, List.nil_append, TreeFactored.Result.bind]
          let changed := TreeFactored.setPermissions store here permissions
          have unchanged : reifyForest children here 0 changed =
              reifyForest children here 0 store :=
            TreeAgreement.root_update_preserves_forest children here store permissions
          have nextUniform :
              TreeFactored.arrayLengthsForest children here 0 changed accesses.length = true := by
            rw [TreeAgreement.forestArrays_congr children here 0 changed store accesses.length
              unchanged]
            exact parts.2
          have next := releaseForest_agrees children here 0 changed path accesses nextUniform
          rw [← unchanged, next, TreeAgreement.translate_reference_map]
          apply TreeAgreement.translate_congr
          have parentFrame := TreeTraversal.releaseForest_preserves_outside children here 0
            changed path accesses here
            (TreeCorrespondence.parent_absent_from_child_forest children here 0)
          simp only [reifyTree]
          rw [parentFrame]
          simp [changed, TreeFactored.setPermissions, TreeFactored.overwrite]
        | ub fault permissions =>
          simp only [TreeOperations.liftArray, List.nil_append, TreeFactored.Result.bind,
            translate]
          rw [TreeTraversal.reifyTree_setPermissions]
        | unsupported reason permissions =>
          simp only [TreeOperations.liftArray, List.nil_append, TreeFactored.Result.bind,
            translate, TreeOperations.structural_roundtrip]
          rw [TreeTraversal.reifyTree_setPermissions]
  termination_by structural topology

  theorem releaseForest_agrees (children : Forest) (parent : Path) (index : Nat) (store : Store)
      (path : Option Path) (accesses : List (Option AccessKind))
      (uniform :
        TreeFactored.arrayLengthsForest children parent index store accesses.length = true) :
      TreeReference.releaseChildren (reifyForest children parent index store) path accesses index =
        translate (reifyForest children parent index)
          (TreeFactored.releaseForest children parent index store path accesses) := by
    cases children with
    | nil => simp only [reifyForest, TreeReference.releaseChildren, TreeFactored.releaseForest,
        translate]
    | cons child rest =>
      have parts :
          TreeFactored.arrayLengthsTree child (parent ++ [index]) store accesses.length = true ∧
          TreeFactored.arrayLengthsForest rest parent (index + 1) store accesses.length = true := by
        simpa [TreeFactored.arrayLengthsForest] using uniform
      change TreeReference.releaseChildren
        (reifyTree child (parent ++ [index]) store ::
          reifyForest rest parent (index + 1) store) path accesses index =
        translate (reifyForest (.cons child rest) parent index)
          (TreeFactored.releaseForest (.cons child rest) parent index store path accesses)
      rw [TreeReference.releaseChildren, TreeAgreement.childPath_agrees,
        releaseTree_agrees child (parent ++ [index]) store (TreeFactored.childPath path index)
          accesses parts.1, TreeFactored.releaseForest]
      cases childAnswer : TreeFactored.releaseTree child (parent ++ [index]) store
          (TreeFactored.childPath path index) accesses with
      | ok value changed =>
        cases value
        simp only [translate, TreeFactored.Result.bind]
        have unchanged := TreeTraversal.releaseChild_preserves_later child rest parent index store
          (TreeFactored.childPath path index) accesses
        simp only [childAnswer, TreeFactored.Result.residual] at unchanged
        have nextUniform :
            TreeFactored.arrayLengthsForest rest parent (index + 1) changed accesses.length =
              true := by
          rw [TreeAgreement.forestArrays_congr rest parent (index + 1) changed store accesses.length
            unchanged]
          exact parts.2
        have next := releaseForest_agrees rest parent (index + 1) changed path accesses nextUniform
        rw [← unchanged, next, TreeAgreement.translate_reference_map]
        apply TreeAgreement.translate_congr
        simp only [reifyForest]
        rw [TreeTraversal.releaseLater_preserves_child]
      | ub fault changed =>
        simp only [translate, TreeFactored.Result.bind, reifyForest]
        have unchanged := TreeTraversal.releaseChild_preserves_later child rest parent index store
          (TreeFactored.childPath path index) accesses
        simp only [childAnswer, TreeFactored.Result.residual] at unchanged
        rw [unchanged]
      | unsupported reason changed =>
        simp only [translate, TreeFactored.Result.bind, reifyForest]
        have unchanged := TreeTraversal.releaseChild_preserves_later child rest parent index store
          (TreeFactored.childPath path index) accesses
        simp only [childAnswer, TreeFactored.Result.residual] at unchanged
        rw [unchanged]
  termination_by structural children
end

theorem releaseCore_agrees (state : State) (path : Option Path)
    (accesses : List (Option AccessKind))
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store accesses.length = true) :
    TreeReference.releaseCore (reify state) path accesses =
      translate reify (TreeFactored.releaseCore state path accesses) := by
  simpa only [reify, TreeFactored.releaseCore, TreeAgreement.translate_factored_map] using
    releaseTree_agrees state.topology [] state.store path accesses uniform

theorem releaseCore_resultRel (state : State) (path : Option Path)
    (accesses : List (Option AccessKind))
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store accesses.length = true) :
    TreeCorrespondence.ResultRel TreeCorrespondence.Related
      (TreeReference.releaseCore (reify state) path accesses)
      (TreeFactored.releaseCore state path accesses) := by
  rw [releaseCore_agrees state path accesses uniform]
  exact TreeAgreement.translate_resultRel _ reify

#print axioms releaseSelected_agrees
#print axioms releaseTree_agrees
#print axioms releaseForest_agrees
#print axioms releaseCore_agrees
#print axioms releaseCore_resultRel

end AnnealResearch.TreeReleaseAgreement
