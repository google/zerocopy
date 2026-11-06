import AnnealResearch.TreeTraversal

/-!
Selected-entry updates for the owned recursive / factored tree encodings.
The callback is explicitly restricted to an Entry, so it preserves the selected
node's ordered children. It may return success, ordinary UB, or unsupported,
and its changed entry is retained in every category. This is the trial-update
behavior of Node.modifyAt, not a copied-allocation commit policy.

This first checkpoint provides the callback interface and the arbitrary-root
reification equation. The arbitrary-path lifting theorem is a separate pending
obligation until the independently authored TreeLookup API is frozen.
-/

namespace AnnealResearch.TreeNodeUpdate


open TreePermissions

def entryOf (node : TreeReference.Node) : TreeFactored.Entry :=
  ⟨node.permissions, node.protection⟩

def withEntry (node : TreeReference.Node) (entry : TreeFactored.Entry) : TreeReference.Node :=
  .mk entry.permissions entry.protection node.children

/-- The same entry callback is lifted independently to the recursive node.
All returned states, including error states, reconstruct its original children. -/
def entryCallback {A : Type} (callback : TreeFactored.Entry → TreeFactored.Result A TreeFactored.Entry)
    (node : TreeReference.Node) : TreeReference.Result A TreeReference.Node :=
  match callback (entryOf node) with
  | .ok value entry => .ok value (withEntry node entry)
  | .ub fault entry => .ub fault (withEntry node entry)
  | .unsupported reason entry =>
      .unsupported (TreeCorrespondence.structuralToReference reason) (withEntry node entry)

/-- Factored selected-entry update: path validation precedes the callback;
only the selected global store entry changes, on every returned category. -/
def updateEntryAt {A : Type} (state : TreeFactored.State) (path : TreeFactored.Path)
    (callback : TreeFactored.Entry → TreeFactored.Result A TreeFactored.Entry) : TreeFactored.Result A TreeFactored.State :=
  match TreeFactored.findTopology state.topology path with
  | none => .unsupported .invalidPath state
  | some _ => (callback (state.store path)).mapState fun entry =>
      { state with store := TreeFactored.overwrite state.store path entry }

theorem overwrite_current (store : TreeFactored.Store) (path : TreeFactored.Path) :
    TreeFactored.overwrite store path (store path) = store := by
  funext query
  by_cases same : query = path
  · subst query; simp [TreeFactored.overwrite]
  · simp [TreeFactored.overwrite, same]

theorem entryOf_reifyTree (topology : TreeFactored.Topology) (here : TreeFactored.Path) (store : TreeFactored.Store) :
    entryOf (TreeCorrespondence.reifyTree topology here store) = store here := by
  cases topology with
  | node children =>
      simp only [entryOf, TreeCorrespondence.reifyTree,
        TreeReference.Node.permissions, TreeReference.Node.protection]

theorem reifyTree_overwrite_current (topology : TreeFactored.Topology) (here : TreeFactored.Path)
    (store : TreeFactored.Store) (entry : TreeFactored.Entry) :
    TreeCorrespondence.reifyTree topology here (TreeFactored.overwrite store here entry) =
      withEntry (TreeCorrespondence.reifyTree topology here store) entry := by
  cases topology with
  | node children =>
      simp only [TreeCorrespondence.reifyTree, withEntry, TreeReference.Node.children]
      rw [TreeTraversal.reifyForest_overwrite_parent]
      simp [TreeFactored.overwrite]

theorem entryCallback_children {A : Type} (callback : TreeFactored.Entry → TreeFactored.Result A TreeFactored.Entry)
    (node : TreeReference.Node) :
    (entryCallback callback node).state.children = node.children := by
  unfold entryCallback
  cases callback (entryOf node) <;> rfl

theorem entryCallback_reifyTree {A : Type} (callback : TreeFactored.Entry → TreeFactored.Result A TreeFactored.Entry)
    (topology : TreeFactored.Topology) (here : TreeFactored.Path) (store : TreeFactored.Store) :
    TreeCorrespondence.ResultRel (fun node changed => node = TreeCorrespondence.reifyTree topology here changed)
      (entryCallback callback (TreeCorrespondence.reifyTree topology here store))
      ((callback (store here)).mapState (TreeFactored.overwrite store here)) := by
  unfold entryCallback
  rw [entryOf_reifyTree]
  cases callback (store here) with
  | ok value entry =>
      exact ⟨rfl, (reifyTree_overwrite_current topology here store entry).symm⟩
  | ub fault entry =>
      exact ⟨rfl, (reifyTree_overwrite_current topology here store entry).symm⟩
  | unsupported reason entry =>
      exact ⟨rfl, (reifyTree_overwrite_current topology here store entry).symm⟩

theorem updateEntryAt_root {A : Type} (state : TreeFactored.State)
    (callback : TreeFactored.Entry → TreeFactored.Result A TreeFactored.Entry) :
    updateEntryAt state [] callback =
      (callback (state.store [])).mapState (fun entry =>
        { state with store := TreeFactored.overwrite state.store [] entry }) := by
  cases state with
  | mk topology store => cases topology <;> rfl

theorem modifyAt_root_agreement {A : Type} (state : TreeFactored.State)
    (callback : TreeFactored.Entry → TreeFactored.Result A TreeFactored.Entry) :
    TreeCorrespondence.ResultRel TreeCorrespondence.Related
      (TreeReference.modifyAt (TreeCorrespondence.reify state) [] (entryCallback callback))
      (updateEntryAt state [] callback) := by
  rw [updateEntryAt_root]
  cases answer : callback (state.store []) with
  | ok value entry =>
      simpa only [TreeReference.modifyAt, entryCallback, TreeCorrespondence.reify, entryOf_reifyTree,
        answer, TreeFactored.Result.mapState, TreeCorrespondence.ResultRel, TreeCorrespondence.Related] using
        And.intro (Eq.refl value)
          (reifyTree_overwrite_current state.topology [] state.store entry).symm
  | ub fault entry =>
      simpa only [TreeReference.modifyAt, entryCallback, TreeCorrespondence.reify, entryOf_reifyTree,
        answer, TreeFactored.Result.mapState, TreeCorrespondence.ResultRel, TreeCorrespondence.Related] using
        And.intro (Eq.refl fault)
          (reifyTree_overwrite_current state.topology [] state.store entry).symm
  | unsupported reason entry =>
      simpa only [TreeReference.modifyAt, entryCallback, TreeCorrespondence.reify, entryOf_reifyTree,
        answer, TreeFactored.Result.mapState, TreeCorrespondence.ResultRel, TreeCorrespondence.Related] using
        And.intro (Eq.refl (TreeCorrespondence.structuralToReference reason))
          (reifyTree_overwrite_current state.topology [] state.store entry).symm

#print axioms overwrite_current
#print axioms entryOf_reifyTree
#print axioms reifyTree_overwrite_current
#print axioms entryCallback_children
#print axioms entryCallback_reifyTree
#print axioms updateEntryAt_root
#print axioms modifyAt_root_agreement

end AnnealResearch.TreeNodeUpdate
