import AnnealResearch.TreeTraversal

/-!
Exact recursive operation agreement for the owned selected tree helpers.
The first stage covers access on every finite ordered topology. Structural
admission is uniform permission-array width and an in-range byte interval.
No scalar access-success, NoUB or protector-kind premise is imposed. All
ordinary UB residuals, child order, flags and permissions are compared.
-/

namespace AnnealResearch.TreeAgreement

open TreePermissions
open TreeFactored (Path Topology Forest Store State)
open TreeCorrespondence (reifyTree reifyForest reify)

/-- This is only a result/representation adapter, never an operation runner. -/
def translate (view : S → T) : TreeFactored.Result A S → TreeReference.Result A T
  | .ok value state => .ok value (view state)
  | .ub fault state => .ub fault (view state)
  | .unsupported reason state =>
      .unsupported (TreeCorrespondence.structuralToReference reason) (view state)

theorem translate_congr (answer : TreeFactored.Result A S) (first second : S → T)
    (same : first answer.residual = second answer.residual) :
    translate first answer = translate second answer := by
  cases answer <;> simp only [TreeFactored.Result.residual] at same <;>
    simp only [translate] <;> rw [same]

theorem translate_reference_map (answer : TreeFactored.Result A S)
    (view : S → T) (rebuild : T → U) :
    (translate view answer).mapState rebuild =
      translate (fun state => rebuild (view state)) answer := by
  cases answer <;> rfl

theorem translate_factored_map (answer : TreeFactored.Result A S)
    (changeState : S → T) (view : T → U) :
    translate view (answer.mapState changeState) =
      translate (fun state => view (changeState state)) answer := by
  cases answer <;> rfl

theorem translate_resultRel (answer : TreeFactored.Result A S) (view : S → T) :
    TreeCorrespondence.ResultRel (fun reference factored => reference = view factored)
      (translate view answer) answer := by
  cases answer <;> simp [translate, TreeCorrespondence.ResultRel]

theorem nodeRelation_agrees (path : Option Path) :
    TreeReference.nodeRelation path = TreeFactored.nodeRelation path := by
  cases path <;> rfl

theorem childPath_agrees (path : Option Path) (index : Nat) :
    TreeReference.childPath path index = TreeFactored.childPath path index := by
  cases path with
  | none => rfl
  | some relative => cases relative <;> rfl

/-- Query transport through an already proved equality of complete represented
forests; this is used only to carry the structural domain across framed work. -/
theorem forestArrays_congr (children : Forest) (parent : Path) (index : Nat)
    (first second : Store) (width : Nat)
    (same : reifyForest children parent index first = reifyForest children parent index second) :
    TreeFactored.arrayLengthsForest children parent index first width =
      TreeFactored.arrayLengthsForest children parent index second width := by
  calc
    _ = TreeReference.childrenSized (reifyForest children parent index first) width :=
      (TreeQueries.arraysSizedForest_reify children parent index first width).symm
    _ = TreeReference.childrenSized (reifyForest children parent index second) width :=
      congrArg (fun forest => TreeReference.childrenSized forest width) same
    _ = _ := TreeQueries.arraysSizedForest_reify children parent index second width

theorem root_update_preserves_forest (children : Forest) (here : Path) (store : Store)
    (permissions : List Permission) :
    reifyForest children here 0 (TreeFactored.setPermissions store here permissions) =
      reifyForest children here 0 store := by
  exact TreeTraversal.reifyForest_overwrite_parent children here 0 store
    { store here with permissions := permissions }

mutual
  theorem accessTree_agrees (topology : Topology) (here : Path) (store : Store)
      (path : Option Path) (kind : AccessKind) (offset size width : Nat)
      (uniform : TreeFactored.arrayLengthsTree topology here store width = true)
      (within : offset + size ≤ width) :
      TreeReference.accessCore (reifyTree topology here store) path kind offset size =
        translate (reifyTree topology here)
          (TreeFactored.accessTree topology here store path kind offset size) := by
    cases topology with
    | node children =>
      have parts : (store here).permissions.length = width ∧
          TreeFactored.arrayLengthsForest children here 0 store width = true := by
        simpa [TreeFactored.arrayLengthsTree] using uniform
      have startWithin : offset ≤ (store here).permissions.length := by omega
      change TreeReference.accessCore
        (.mk (store here).permissions (store here).protection (reifyForest children here 0 store))
          path kind offset size =
        translate (reifyTree (.node children) here)
          (TreeFactored.accessTree (.node children) here store path kind offset size)
      rw [TreeReference.accessCore, nodeRelation_agrees, TreeFactored.accessTree,
        TreeOperations.transitionRange_agrees store here kind (TreeFactored.nodeRelation path)
          offset size startWithin]
      cases array : TreeReference.transitionRange (store here).permissions offset size kind
          (TreeFactored.nodeRelation path) with
      | ok value permissions =>
        cases value
        simp only [TreeOperations.liftArray, List.nil_append, TreeFactored.Result.bind]
        let changed := TreeFactored.setPermissions store here permissions
        have unchanged : reifyForest children here 0 changed =
            reifyForest children here 0 store :=
          root_update_preserves_forest children here store permissions
        have nextUniform : TreeFactored.arrayLengthsForest children here 0 changed width = true := by
          rw [forestArrays_congr children here 0 changed store width unchanged]
          exact parts.2
        have next := accessForest_agrees children here 0 changed path kind offset size width
          nextUniform within
        rw [← unchanged, next, translate_reference_map]
        apply translate_congr
        have parentFrame := TreeTraversal.accessForest_preserves_outside children here 0 changed
          path kind offset size here
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

  theorem accessForest_agrees (children : Forest) (parent : Path) (index : Nat) (store : Store)
      (path : Option Path) (kind : AccessKind) (offset size width : Nat)
      (uniform : TreeFactored.arrayLengthsForest children parent index store width = true)
      (within : offset + size ≤ width) :
      TreeReference.accessChildren (reifyForest children parent index store) path kind
          offset size index =
        translate (reifyForest children parent index)
          (TreeFactored.accessForest children parent index store path kind offset size) := by
    cases children with
    | nil => simp only [reifyForest, TreeReference.accessChildren, TreeFactored.accessForest,
        translate]
    | cons child rest =>
      have parts : TreeFactored.arrayLengthsTree child (parent ++ [index]) store width = true ∧
          TreeFactored.arrayLengthsForest rest parent (index + 1) store width = true := by
        simpa [TreeFactored.arrayLengthsForest] using uniform
      change TreeReference.accessChildren
        (reifyTree child (parent ++ [index]) store ::
          reifyForest rest parent (index + 1) store) path kind offset size index =
        translate (reifyForest (.cons child rest) parent index)
          (TreeFactored.accessForest (.cons child rest) parent index store path kind offset size)
      rw [TreeReference.accessChildren, childPath_agrees,
        accessTree_agrees child (parent ++ [index]) store (TreeFactored.childPath path index)
          kind offset size width parts.1 within, TreeFactored.accessForest]
      cases childAnswer : TreeFactored.accessTree child (parent ++ [index]) store
          (TreeFactored.childPath path index) kind offset size with
      | ok value changed =>
        cases value
        simp only [translate, TreeFactored.Result.bind]
        have unchanged := TreeTraversal.accessChild_preserves_later child rest parent index store
          (TreeFactored.childPath path index) kind offset size
        simp only [childAnswer, TreeFactored.Result.residual] at unchanged
        have nextUniform :
            TreeFactored.arrayLengthsForest rest parent (index + 1) changed width = true := by
          rw [forestArrays_congr rest parent (index + 1) changed store width unchanged]
          exact parts.2
        have next := accessForest_agrees rest parent (index + 1) changed path kind offset size
          width nextUniform within
        rw [← unchanged, next, translate_reference_map]
        apply translate_congr
        simp only [reifyForest]
        rw [TreeTraversal.accessLater_preserves_child]
      | ub fault changed =>
        simp only [translate, TreeFactored.Result.bind, reifyForest]
        have unchanged := TreeTraversal.accessChild_preserves_later child rest parent index store
          (TreeFactored.childPath path index) kind offset size
        simp only [childAnswer, TreeFactored.Result.residual] at unchanged
        rw [unchanged]
      | unsupported reason changed =>
        simp only [translate, TreeFactored.Result.bind, reifyForest]
        have unchanged := TreeTraversal.accessChild_preserves_later child rest parent index store
          (TreeFactored.childPath path index) kind offset size
        simp only [childAnswer, TreeFactored.Result.residual] at unchanged
        rw [unchanged]
  termination_by structural children
end

theorem accessCore_agrees (state : State) (path : Option Path) (kind : AccessKind)
    (offset size width : Nat)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true)
    (within : offset + size ≤ width) :
    TreeReference.accessCore (reify state) path kind offset size =
      translate reify (TreeFactored.accessCore state path kind offset size) := by
  simpa only [reify, TreeFactored.accessCore, translate_factored_map] using
    accessTree_agrees state.topology [] state.store path kind offset size width uniform within

theorem accessCore_resultRel (state : State) (path : Option Path) (kind : AccessKind)
    (offset size width : Nat)
    (uniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true)
    (within : offset + size ≤ width) :
    TreeCorrespondence.ResultRel TreeCorrespondence.Related
      (TreeReference.accessCore (reify state) path kind offset size)
      (TreeFactored.accessCore state path kind offset size) := by
  rw [accessCore_agrees state path kind offset size width uniform within]
  exact translate_resultRel _ reify

#print axioms translate_congr
#print axioms translate_resultRel
#print axioms forestArrays_congr
#print axioms root_update_preserves_forest
#print axioms accessTree_agrees
#print axioms accessForest_agrees
#print axioms accessCore_agrees
#print axioms accessCore_resultRel

end AnnealResearch.TreeAgreement
