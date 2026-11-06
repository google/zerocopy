import AnnealResearch.TreeNodeUpdate
import AnnealResearch.TreeLookup

/-!
Generic selected-entry trial update on an arbitrary finite ordered tree.
Only topology-path validity is assumed. The callback preserves the selected
node's children by taking an Entry, but may return a changed Entry on success,
ordinary UB, or unsupported. Every such residual reconstructs all ancestors.
No array-width, scalar-success, NoUB or permission/flag matching premise occurs.
This is a representation theorem, not a source-helper adequacy theorem.
-/

namespace AnnealResearch.TreeNodePathUpdate

open TreeFactored (Path Topology Forest Entry Store State)
open TreeCorrespondence (reifyTree reifyForest reify)

private theorem append_cons_head_eq (stem : Path) (first second : Nat)
    (left right : Path)
    (same : stem ++ first :: left = stem ++ second :: right) : first = second := by
  revert same
  induction stem with
  | nil => intro same; exact (List.cons.inj same).1
  | cons head rest ih => intro same; exact ih (List.cons.inj same).2

/-- A write below one child cannot affect a different child's full subtree. -/
theorem reifyTree_overwrite_other_branch (child : Topology) (parent : Path)
    (index selected : Nat) (suffix : Path) (store : Store) (entry : Entry)
    (different : index ≠ selected) :
    reifyTree child (parent ++ [index])
        (TreeFactored.overwrite store (parent ++ selected :: suffix) entry) =
      reifyTree child (parent ++ [index]) store := by
  apply TreeCorrespondence.overwrite_absent_preserves_reify
  intro member
  obtain ⟨rest, shape⟩ := TreeTraversal.representedTree_suffix child
    (parent ++ [index]) (parent ++ selected :: suffix) member
  have heads : selected = index := append_cons_head_eq parent selected index suffix rest
    (by simpa only [List.append_assoc, List.singleton_append] using shape)
  exact different heads.symm

/-- A write under an earlier child cannot affect any later forest entry. -/
theorem reifyForest_overwrite_before (children : Forest) (parent : Path)
    (start selected : Nat) (suffix : Path) (store : Store) (entry : Entry)
    (earlier : selected < start) :
    reifyForest children parent start
        (TreeFactored.overwrite store (parent ++ selected :: suffix) entry) =
      reifyForest children parent start store := by
  apply TreeCorrespondence.reifyForest_congr
  intro query member
  by_cases same : query = parent ++ selected :: suffix
  · subst query
    obtain ⟨later, lower, rest, shape⟩ :=
      TreeTraversal.representedForest_branch children parent start
        (parent ++ selected :: suffix) member
    have heads : selected = later :=
      append_cons_head_eq parent selected later suffix rest shape
    omega
  · exact TreeFactored.overwrite_other store (parent ++ selected :: suffix) query entry same

/-- Replacing exactly one ordered child by its updated reification agrees with
one global selected-entry overwrite. The child's suffix can have any length. -/
theorem reifyForest_replace_descendant (children : Forest) (parent : Path)
    (start : Nat) (store : Store) (relative : Nat) (child : Topology)
    (suffix : Path) (entry : Entry)
    (found : children.get? relative = some child) :
    TreeReference.replaceNth (reifyForest children parent start store) relative
        (reifyTree child (parent ++ [start + relative])
          (TreeFactored.overwrite store (parent ++ (start + relative) :: suffix) entry)) =
      reifyForest children parent start
        (TreeFactored.overwrite store (parent ++ (start + relative) :: suffix) entry) := by
  induction relative generalizing children start with
  | zero =>
      cases children with
      | nil => cases found
      | cons first rest =>
          have same : first = child := by
            simpa only [TreeFactored.Forest.get?, Option.some.injEq] using found
          subst child
          simp only [Nat.add_zero, reifyForest, TreeReference.replaceNth]
          rw [reifyForest_overwrite_before rest parent (start + 1) start suffix store entry
            (by omega)]
  | succ relative ih =>
      cases children with
      | nil => cases found
      | cons first rest =>
          have below : rest.get? relative = some child := by
            simpa only [TreeFactored.Forest.get?] using found
          have increment : start + (relative + 1) = start + 1 + relative := by omega
          simp only [reifyForest, TreeReference.replaceNth]
          rw [increment]
          rw [reifyTree_overwrite_other_branch first parent start (start + 1 + relative)
            suffix store entry (by omega)]
          rw [ih rest (start + 1) below]

theorem reifyTree_modify_child (children : Forest) (here : Path) (store : Store)
    (index : Nat) (child : Topology) (suffix : Path) (entry : Entry)
    (found : children.get? index = some child) :
    reifyTree (.node children) here
        (TreeFactored.overwrite store (here ++ index :: suffix) entry) =
      TreeReference.Node.mk (store here).permissions (store here).protection
        (TreeReference.replaceNth (reifyForest children here 0 store) index
          (reifyTree child (here ++ [index])
            (TreeFactored.overwrite store (here ++ index :: suffix) entry))) := by
  have different : here ≠ here ++ index :: suffix := by
    intro same
    have lengths := congrArg List.length same
    simp only [List.length_append, List.length_cons] at lengths
    omega
  simp only [reifyTree]
  rw [TreeFactored.overwrite_other store (here ++ index :: suffix) here entry different]
  have replaced := reifyForest_replace_descendant children here 0 store index child suffix
    entry found
  simpa only [Nat.zero_add] using congrArg
    (fun list => TreeReference.Node.mk (store here).permissions (store here).protection list)
    replaced.symm

theorem entryCallback_translate {A : Type}
    (callback : Entry → TreeFactored.Result A Entry)
    (topology : Topology) (here : Path) (store : Store) :
    TreeNodeUpdate.entryCallback callback (reifyTree topology here store) =
      TreeAgreement.translate
        (fun entry => reifyTree topology here (TreeFactored.overwrite store here entry))
        (callback (store here)) := by
  unfold TreeNodeUpdate.entryCallback
  rw [TreeNodeUpdate.entryOf_reifyTree]
  cases callback (store here) <;> simp only [TreeAgreement.translate] <;>
    rw [TreeNodeUpdate.reifyTree_overwrite_current]

/-- Exact result equality includes ordinary-error reconstruction of changed
selected entries and every ancestor. Only valid topology paths are admitted. -/
theorem modifyAt_reifyTree {A : Type} (topology : Topology) (here : Path)
    (store : Store) (path : Path) (selected : Topology)
    (callback : Entry → TreeFactored.Result A Entry)
    (found : TreeFactored.findTopology topology path = some selected) :
    TreeReference.modifyAt (reifyTree topology here store) path
        (TreeNodeUpdate.entryCallback callback) =
      TreeAgreement.translate
        (fun entry => reifyTree topology here
          (TreeFactored.overwrite store (here ++ path) entry))
        (callback (store (here ++ path))) := by
  induction path generalizing topology here with
  | nil =>
      simpa only [TreeReference.modifyAt, List.append_nil] using
        entryCallback_translate callback topology here store
  | cons index rest ih =>
      cases topology with
      | node children =>
          cases childFound : children.get? index with
          | none =>
              simp only [TreeFactored.findTopology, childFound] at found
              cases found
          | some child =>
              have below : TreeFactored.findTopology child rest = some selected := by
                simpa only [TreeFactored.findTopology, childFound] using found
              conv => lhs; rw [reifyTree]
              rw [TreeReference.modifyAt]
              rw [TreeLookup.reifyForest_get?]
              simp only [Nat.zero_add, childFound, Option.map]
              have step := ih child (here ++ [index]) below
              simp only [List.append_assoc, List.singleton_append] at step
              rw [step, TreeAgreement.translate_reference_map]
              apply TreeAgreement.translate_congr
              exact (reifyTree_modify_child children here store index child rest _ childFound).symm

theorem modifyAt_agreement {A : Type} (state : State) (path : Path)
    (selected : Topology) (callback : Entry → TreeFactored.Result A Entry)
    (found : TreeFactored.findTopology state.topology path = some selected) :
    TreeCorrespondence.ResultRel TreeCorrespondence.Related
      (TreeReference.modifyAt (reify state) path (TreeNodeUpdate.entryCallback callback))
      (TreeNodeUpdate.updateEntryAt state path callback) := by
  change TreeCorrespondence.ResultRel TreeCorrespondence.Related
    (TreeReference.modifyAt (reifyTree state.topology [] state.store) path
      (TreeNodeUpdate.entryCallback callback)) _
  rw [modifyAt_reifyTree state.topology [] state.store path selected callback found]
  simp only [List.nil_append, TreeNodeUpdate.updateEntryAt, found]
  cases callback (state.store path) <;> exact ⟨rfl, rfl⟩

#print axioms reifyTree_overwrite_other_branch
#print axioms reifyForest_overwrite_before
#print axioms reifyForest_replace_descendant
#print axioms reifyTree_modify_child
#print axioms entryCallback_translate
#print axioms modifyAt_reifyTree
#print axioms modifyAt_agreement

end AnnealResearch.TreeNodePathUpdate
