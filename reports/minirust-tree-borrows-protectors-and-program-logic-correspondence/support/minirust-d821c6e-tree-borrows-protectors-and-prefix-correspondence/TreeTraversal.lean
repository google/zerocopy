import AnnealResearch.TreeOperations
import AnnealResearch.TreeQueries

/-!
Recursive operation bridge, staged through exact store-support framing.
The support is every path represented by the full ordered recursive topology.
The frame theorems below include all raw worker results, including UB and
unsupported residual stores; they require no access success, NoUB, uniform
array size or protector-kind assumption. Operation agreement is added only
after this separation layer is checked.
-/

namespace AnnealResearch.TreeTraversal

open TreePermissions
open TreeFactored (Path Topology Forest Store Entry)
open TreeCorrespondence (representedTree representedForest reifyTree reifyForest)

theorem bind_preserves_at (before : Store) (answer : TreeFactored.Result A Store)
    (next : A → Store → TreeFactored.Result B Store) (query : Path)
    (firstFrame : answer.residual query = before query)
    (nextFrame : ∀ value changed, (next value changed).residual query = changed query) :
    (answer.bind next).residual query = before query := by
  cases answer with
  | ok value changed => exact (nextFrame value changed).trans firstFrame
  | ub fault changed => exact firstFrame
  | unsupported reason changed => exact firstFrame

theorem transitionAt_preserves_other (store : Store) (here query : Path)
    (kind : AccessKind) (relation : NodeRelation) (offset : Nat)
    (different : query ≠ here) :
    (TreeFactored.transitionAt store here kind relation offset).residual query = store query := by
  unfold TreeFactored.transitionAt
  cases found : TreeFactored.permissionAt (store here).permissions offset with
  | none => simp only [found, TreeFactored.Result.residual]
  | some permission =>
    simp only [found]
    cases step : permission.transition kind relation with
    | error fault => simp only [TreeFactored.Result.residual]
    | ok changed =>
      simp only [TreeFactored.Result.residual]
      exact TreeOperations.setPermissions_other store here query _ different

theorem transitionOffsets_preserves_other (store : Store) (here query : Path)
    (kind : AccessKind) (relation : NodeRelation) (offset count : Nat)
    (different : query ≠ here) :
    (TreeFactored.transitionOffsets store here kind relation offset count).residual query =
      store query := by
  induction count generalizing store offset with
  | zero => rfl
  | succ count ih =>
    rw [TreeFactored.transitionOffsets]
    exact bind_preserves_at store _ _ query
      (transitionAt_preserves_other store here query kind relation offset different)
      (fun _ changed => ih changed (offset + 1))

theorem releaseOffsets_preserves_other (store : Store) (here query : Path)
    (relation : NodeRelation) (offset : Nat) (accesses : List (Option AccessKind))
    (different : query ≠ here) :
    (TreeFactored.releaseOffsets store here relation offset accesses).residual query =
      store query := by
  induction accesses generalizing store offset with
  | nil => rfl
  | cons accessKind rest ih =>
    cases accessKind with
    | none => exact ih store (offset + 1)
    | some kind =>
      rw [TreeFactored.releaseOffsets]
      exact bind_preserves_at store _ _ query
        (transitionAt_preserves_other store here query kind relation offset different)
        (fun _ changed => ih changed (offset + 1))

theorem setProtected_preserves_other (store : Store) (here query : Path)
    (protection : Protected) (different : query ≠ here) :
    TreeFactored.setProtected store here protection query = store query := by
  simp [TreeFactored.setProtected, TreeFactored.overwrite, different]

mutual
  /-- All entries outside the actual recursive subtree are framed, even when a
  byte or later descendant returns UB after earlier trial updates. -/
  theorem accessTree_preserves_outside (topology : Topology) (here : Path) (store : Store)
      (path : Option Path) (kind : AccessKind) (offset size : Nat) (query : Path)
      (outside : ¬ representedTree topology here query) :
      (TreeFactored.accessTree topology here store path kind offset size).residual query =
        store query := by
    cases topology with
    | node children =>
      simp only [representedTree] at outside
      have different : query ≠ here := fun same => outside (Or.inl same)
      have outsideChildren : ¬ representedForest children here 0 query :=
        fun member => outside (Or.inr member)
      rw [TreeFactored.accessTree]
      exact bind_preserves_at store _ _ query
        (transitionOffsets_preserves_other store here query kind
          (TreeFactored.nodeRelation path) offset size different)
        (fun _ changed => accessForest_preserves_outside children here 0 changed path kind
          offset size query outsideChildren)
  termination_by structural topology

  theorem accessForest_preserves_outside (children : Forest) (parent : Path) (index : Nat)
      (store : Store) (path : Option Path) (kind : AccessKind) (offset size : Nat)
      (query : Path) (outside : ¬ representedForest children parent index query) :
      (TreeFactored.accessForest children parent index store path kind offset size).residual
        query = store query := by
    cases children with
    | nil => rfl
    | cons child rest =>
      simp only [representedForest] at outside
      rw [TreeFactored.accessForest]
      exact bind_preserves_at store _ _ query
        (accessTree_preserves_outside child (parent ++ [index]) store
          (TreeFactored.childPath path index) kind offset size query
          (fun member => outside (Or.inl member)))
        (fun _ changed => accessForest_preserves_outside rest parent (index + 1) changed path
          kind offset size query (fun member => outside (Or.inr member)))
  termination_by structural children
end

mutual
  theorem releaseTree_preserves_outside (topology : Topology) (here : Path) (store : Store)
      (path : Option Path) (accesses : List (Option AccessKind)) (query : Path)
      (outside : ¬ representedTree topology here query) :
      (TreeFactored.releaseTree topology here store path accesses).residual query =
        store query := by
    cases topology with
    | node children =>
      simp only [representedTree] at outside
      have different : query ≠ here := fun same => outside (Or.inl same)
      have outsideChildren : ¬ representedForest children here 0 query :=
        fun member => outside (Or.inr member)
      cases path with
      | none =>
        rw [TreeFactored.releaseTree]
        · exact bind_preserves_at store _ _ query
            (releaseOffsets_preserves_other store here query .foreignNode 0 accesses different)
            (fun _ changed => releaseForest_preserves_outside children here 0 changed none
              accesses query outsideChildren)
        · simp
      | some relative =>
        cases relative with
        | nil =>
          simp only [TreeFactored.releaseTree, TreeFactored.Result.residual]
          exact setProtected_preserves_other store here query .no different
        | cons first rest =>
          rw [TreeFactored.releaseTree]
          · exact bind_preserves_at store _ _ query
              (releaseOffsets_preserves_other store here query .localNode 0 accesses different)
              (fun _ changed => releaseForest_preserves_outside children here 0 changed
                (some (first :: rest)) accesses query outsideChildren)
          · simp
  termination_by structural topology

  theorem releaseForest_preserves_outside (children : Forest) (parent : Path) (index : Nat)
      (store : Store) (path : Option Path) (accesses : List (Option AccessKind))
      (query : Path) (outside : ¬ representedForest children parent index query) :
      (TreeFactored.releaseForest children parent index store path accesses).residual query =
        store query := by
    cases children with
    | nil => rfl
    | cons child rest =>
      simp only [representedForest] at outside
      rw [TreeFactored.releaseForest]
      exact bind_preserves_at store _ _ query
        (releaseTree_preserves_outside child (parent ++ [index]) store
          (TreeFactored.childPath path index) accesses query
          (fun member => outside (Or.inl member)))
        (fun _ changed => releaseForest_preserves_outside rest parent (index + 1) changed path
          accesses query (fun member => outside (Or.inr member)))
  termination_by structural children
end

mutual
  theorem representedTree_suffix (topology : Topology) (here query : Path)
      (member : representedTree topology here query) :
      ∃ suffix, query = here ++ suffix := by
    cases topology with
    | node children =>
      simp only [representedTree] at member
      rcases member with same | below
      · exact ⟨[], by simpa using same⟩
      · obtain ⟨index, _, suffix, shape⟩ := representedForest_branch children here 0 query below
        exact ⟨index :: suffix, shape⟩
  termination_by structural topology

  theorem representedForest_branch (children : Forest) (parent : Path) (index : Nat)
      (query : Path) (member : representedForest children parent index query) :
      ∃ childIndex, index ≤ childIndex ∧ ∃ suffix, query = parent ++ childIndex :: suffix := by
    cases children with
    | nil => simp only [representedForest] at member
    | cons child rest =>
      simp only [representedForest] at member
      rcases member with inChild | inRest
      · obtain ⟨suffix, shape⟩ := representedTree_suffix child (parent ++ [index]) query inChild
        exact ⟨index, Nat.le_refl _, suffix,
          by simpa only [List.append_assoc, List.singleton_append] using shape⟩
      · obtain ⟨later, lower, suffix, shape⟩ :=
          representedForest_branch rest parent (index + 1) query inRest
        exact ⟨later, by omega, suffix, shape⟩
  termination_by structural children
end

private theorem append_cons_head_eq (stem : Path) (first second : Nat) (left right : Path)
    (same : stem ++ first :: left = stem ++ second :: right) : first = second := by
  revert same
  induction stem with
  | nil => intro same; exact (List.cons.inj same).1
  | cons head rest ih => intro same; exact ih (List.cons.inj same).2

/-- A full recursive child subtree is disjoint from every later sibling subtree,
not just from the siblings' root cells. -/
theorem child_disjoint_later_forest (child : Topology) (rest : Forest) (parent : Path)
    (index : Nat) (query : Path)
    (inChild : representedTree child (parent ++ [index]) query) :
    ¬ representedForest rest parent (index + 1) query := by
  intro inLater
  obtain ⟨childSuffix, childShape⟩ :=
    representedTree_suffix child (parent ++ [index]) query inChild
  obtain ⟨laterIndex, lower, laterSuffix, laterShape⟩ :=
    representedForest_branch rest parent (index + 1) query inLater
  have same : parent ++ index :: childSuffix = parent ++ laterIndex :: laterSuffix := by
    simpa only [List.append_assoc, List.singleton_append] using childShape.symm.trans laterShape
  have heads := append_cons_head_eq parent index laterIndex childSuffix laterSuffix same
  omega

theorem reifyForest_overwrite_parent (children : Forest) (parent : Path) (index : Nat)
    (store : Store) (entry : Entry) :
    reifyForest children parent index (TreeFactored.overwrite store parent entry) =
      reifyForest children parent index store := by
  apply TreeCorrespondence.reifyForest_congr
  intro query member
  have different : query ≠ parent := by
    intro same
    subst query
    exact TreeCorrespondence.parent_absent_from_child_forest children parent index member
  exact TreeFactored.overwrite_other store parent query entry different

theorem reifyTree_setPermissions (children : Forest) (here : Path) (store : Store)
    (permissions : List Permission) :
    reifyTree (.node children) here (TreeFactored.setPermissions store here permissions) =
      .mk permissions (store here).protection (reifyForest children here 0 store) := by
  simp only [reifyTree, TreeFactored.setPermissions]
  rw [reifyForest_overwrite_parent]
  simp [TreeFactored.overwrite]

theorem reifyTree_setProtected (children : Forest) (here : Path) (store : Store)
    (protection : Protected) :
    reifyTree (.node children) here (TreeFactored.setProtected store here protection) =
      .mk (store here).permissions protection (reifyForest children here 0 store) := by
  simp only [reifyTree, TreeFactored.setProtected]
  rw [reifyForest_overwrite_parent]
  simp [TreeFactored.overwrite]

/-- Earlier-child access cannot change any later sibling's reconstructed tree,
on any result category, including a failure deep inside the earlier child. -/
theorem accessChild_preserves_later (child : Topology) (rest : Forest) (parent : Path)
    (index : Nat) (store : Store) (path : Option Path) (kind : AccessKind) (offset size : Nat) :
    reifyForest rest parent (index + 1)
      (TreeFactored.accessTree child (parent ++ [index]) store path kind offset size).residual =
      reifyForest rest parent (index + 1) store := by
  apply TreeCorrespondence.reifyForest_congr
  intro query inLater
  apply accessTree_preserves_outside child (parent ++ [index]) store path kind offset size query
  intro inChild
  exact child_disjoint_later_forest child rest parent index query inChild inLater

theorem accessLater_preserves_child (child : Topology) (rest : Forest) (parent : Path)
    (index : Nat) (store : Store) (path : Option Path) (kind : AccessKind) (offset size : Nat) :
    reifyTree child (parent ++ [index])
      (TreeFactored.accessForest rest parent (index + 1) store path kind offset size).residual =
      reifyTree child (parent ++ [index]) store := by
  apply TreeCorrespondence.reifyTree_congr
  intro query inChild
  exact accessForest_preserves_outside rest parent (index + 1) store path kind offset size query
    (child_disjoint_later_forest child rest parent index query inChild)

theorem releaseChild_preserves_later (child : Topology) (rest : Forest) (parent : Path)
    (index : Nat) (store : Store) (path : Option Path) (accesses : List (Option AccessKind)) :
    reifyForest rest parent (index + 1)
      (TreeFactored.releaseTree child (parent ++ [index]) store path accesses).residual =
      reifyForest rest parent (index + 1) store := by
  apply TreeCorrespondence.reifyForest_congr
  intro query inLater
  apply releaseTree_preserves_outside child (parent ++ [index]) store path accesses query
  intro inChild
  exact child_disjoint_later_forest child rest parent index query inChild inLater

theorem releaseLater_preserves_child (child : Topology) (rest : Forest) (parent : Path)
    (index : Nat) (store : Store) (path : Option Path) (accesses : List (Option AccessKind)) :
    reifyTree child (parent ++ [index])
      (TreeFactored.releaseForest rest parent (index + 1) store path accesses).residual =
      reifyTree child (parent ++ [index]) store := by
  apply TreeCorrespondence.reifyTree_congr
  intro query inChild
  exact releaseForest_preserves_outside rest parent (index + 1) store path accesses query
    (child_disjoint_later_forest child rest parent index query inChild)

#print axioms bind_preserves_at
#print axioms transitionAt_preserves_other
#print axioms transitionOffsets_preserves_other
#print axioms releaseOffsets_preserves_other
#print axioms setProtected_preserves_other
#print axioms accessTree_preserves_outside
#print axioms accessForest_preserves_outside
#print axioms releaseTree_preserves_outside
#print axioms releaseForest_preserves_outside
#print axioms representedTree_suffix
#print axioms representedForest_branch
#print axioms child_disjoint_later_forest
#print axioms reifyForest_overwrite_parent
#print axioms reifyTree_setPermissions
#print axioms reifyTree_setProtected
#print axioms accessChild_preserves_later
#print axioms accessLater_preserves_child
#print axioms releaseChild_preserves_later
#print axioms releaseLater_preserves_child

end AnnealResearch.TreeTraversal
