import AnnealResearch.TreeGraftPaths
import AnnealResearch.TreeUnprotectTotal

/-!
Actual arbitrary-parent insertion correspondence. The public theorem admits
only parent/child uniform arrays at a common width. Missing parent paths are
compared as owned invalidPath results. Every inserted descendant is taken from
the child store; old absent entries have no premise. Complete recursive result
equality includes ordered siblings, ancestor reconstruction and the exact fresh
returned path. No permission-kind, access-success, NoUB or history premise is
introduced. Width preservation and memory reborrow remain separate layers.
-/

namespace AnnealResearch.TreeInsertionAgreement

open TreeFactored (Path Topology Store State)
open TreeCorrespondence (reifyTree reifyForest reify)
open TreeGraftPaths (OutsideAgree)

theorem stripPrefix_compose (first second query : Path) :
    TreeFactored.stripPrefix (first ++ second) query =
      (TreeFactored.stripPrefix first query).bind
        (fun rest => TreeFactored.stripPrefix second rest) := by
  induction first generalizing query with
  | nil => rfl
  | cons head tail ih =>
      cases query with
      | nil => rfl
      | cons actual rest =>
          by_cases same : head = actual
          · simpa only [List.cons_append, TreeFactored.stripPrefix, same, ↓reduceIte,
              Option.bind] using ih rest
          · simp only [List.cons_append, TreeFactored.stripPrefix, same, ↓reduceIte, Option.bind]

theorem graft_below_frame (old child : Store) (parent tail : Path) :
    OutsideAgree parent old (TreeGraft.graft old (parent ++ tail) child) := by
  intro query missing
  apply TreeGraft.graft_outside
  rw [stripPrefix_compose, missing]
  rfl

theorem graft_parent_reify (children : TreeFactored.Forest) (parent : Path)
    (old : Store) (child : State) :
    reifyTree (.node (children.snoc child.topology)) parent
        (TreeGraft.graft old (parent ++ [children.length]) child.store) =
      TreeReference.Node.mk (old parent).permissions (old parent).protection
        (reifyForest children parent 0 old ++ [reify child]) := by
  have shifted :
      (fun query => TreeGraft.graft old (parent ++ [children.length]) child.store
        (parent ++ query)) =
      TreeGraft.graft (fun query => old (parent ++ query)) [children.length] child.store := by
    funext query
    simp only [TreeGraft.graft, TreeGraftPaths.stripPrefix_cancel]
  have localRoot := TreeGraft.graftRoot_reify children (fun query => old (parent ++ query)) child
  simp only [reify, TreeGraft.graftRoot] at localRoot
  rw [← shifted, TreeLookup.reifyTree_shift, TreeLookup.reifyForest_shift] at localRoot
  simpa only [List.append_nil, reify] using localRoot

/-- Structural lookup permits replacement of the update function by its actual
selected value. This equation does not assert a permission operation succeeds. -/
theorem modifyTopology_at_found (topology selected : Topology) (path : Path)
    (update : Topology → Topology)
    (found : TreeFactored.findTopology topology path = some selected) :
    TreeFactored.modifyTopology topology path update =
      TreeFactored.modifyTopology topology path (fun _ => update selected) := by
  induction path generalizing topology with
  | nil =>
      have same : topology = selected := Option.some.inj found
      subst topology
      rfl
  | cons index rest ih =>
      cases topology with
      | node children =>
          cases childFound : children.get? index with
          | none => simp only [TreeFactored.findTopology, childFound] at found; cases found
          | some child =>
              have below : TreeFactored.findTopology child rest = some selected := by
                simpa only [TreeFactored.findTopology, childFound] using found
              simp only [TreeFactored.modifyTopology, childFound]
              rw [ih child below]

theorem modifyTopology_exists (topology selected : Topology) (path : Path)
    (update : Topology → Topology)
    (found : TreeFactored.findTopology topology path = some selected) :
    ∃ changed, TreeFactored.modifyTopology topology path update = some changed := by
  induction path generalizing topology with
  | nil => exact ⟨update topology, rfl⟩
  | cons index rest ih =>
      cases topology with
      | node children =>
          cases childFound : children.get? index with
          | none => simp only [TreeFactored.findTopology, childFound] at found; cases found
          | some child =>
              have below : TreeFactored.findTopology child rest = some selected := by
                simpa only [TreeFactored.findTopology, childFound] using found
              obtain ⟨changed, equation⟩ := ih child below
              refine ⟨.node (children.replace index changed), ?_⟩
              simp only [TreeFactored.modifyTopology, childFound, equation]

theorem modifyAt_congr_found {A : Type} (node selected : TreeReference.Node) (path : Path)
    (first second : TreeReference.Node → TreeReference.Result A TreeReference.Node)
    (found : TreeReference.findNode node path = some selected)
    (same : first selected = second selected) :
    TreeReference.modifyAt node path first = TreeReference.modifyAt node path second := by
  induction path generalizing node with
  | nil =>
      have equal : node = selected := Option.some.inj found
      subst node
      exact same
  | cons index rest ih =>
      cases node with
      | mk permissions protection children =>
          cases childFound : children[index]? with
          | none =>
              simp only [TreeReference.findNode, TreeReference.Node.children, childFound] at found
              cases found
          | some child =>
              have below : TreeReference.findNode child rest = some selected := by
                simpa only [TreeReference.findNode, TreeReference.Node.children, childFound]
                  using found
              simp only [TreeReference.modifyAt, childFound]
              rw [ih child below]

def appendCallback (parent : Path) (child : TreeReference.Node) :
    TreeReference.Node → TreeReference.Result Path TreeReference.Node
  | .mk permissions protection children =>
      .ok (parent ++ [children.length]) (.mk permissions protection (children ++ [child]))

/-- A found-parent branch of actual insertion; the public theorem below
discharges these structural witnesses by inspecting the actual topology. -/
theorem insertion_found (state child : State) (parent : Path)
    (children : TreeFactored.Forest) (changed : Topology)
    (found : TreeFactored.findTopology state.topology parent = some (.node children))
    (shape : TreeFactored.modifyTopology state.topology parent
      (fun _ => .node (children.snoc child.topology)) = some changed) :
    TreeReference.modifyAt (reify state) parent (appendCallback parent (reify child)) =
      .ok (parent ++ [children.length])
        (reify ⟨changed, TreeGraft.graft state.store (parent ++ [children.length]) child.store⟩) := by
  let after := TreeGraft.graft state.store (parent ++ [children.length]) child.store
  have selected : TreeReference.findNode (reify state) parent =
      some (reifyTree (.node children) parent state.store) := by
    simpa only [List.nil_append, reify] using
      TreeLookup.findNode_found state.topology (.node children) [] state.store parent found
  have callbackSame :
      appendCallback parent (reify child) (reifyTree (.node children) parent state.store) =
        TreeReference.Result.ok (parent ++ [children.length])
          (reifyTree (.node (children.snoc child.topology)) parent after) := by
    change _ = TreeReference.Result.ok (parent ++ [children.length])
      (reifyTree (.node (children.snoc child.topology)) parent
        (TreeGraft.graft state.store (parent ++ [children.length]) child.store))
    rw [graft_parent_reify]
    simp only [reifyTree, appendCallback, TreeGraft.reifyForest_length]
  rw [modifyAt_congr_found (reify state)
    (reifyTree (.node children) parent state.store) parent
    (appendCallback parent (reify child))
    (fun _ => .ok (parent ++ [children.length])
      (reifyTree (.node (children.snoc child.topology)) parent after)) selected callbackSame]
  have frame : OutsideAgree ([] ++ parent) state.store after := by
    simpa only [List.nil_append] using
      graft_below_frame state.store child.store parent [children.length]
  simpa only [List.nil_append, reify] using
    TreeGraftPaths.modifyAt_replacement (parent ++ [children.length]) state.topology []
      state.store after parent (.node (children.snoc child.topology)) changed shape frame

/-- Only common uniform widths are external premises. Missing paths remain
owned rejection results; no successful lookup or permission result is assumed. -/
theorem addNode_agrees (state child : State) (parent : Path) (width : Nat)
    (parentUniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true)
    (childUniform : TreeFactored.arrayLengthsTree child.topology [] child.store width = true) :
    TreeReference.addNode (reify state) parent (reify child) =
      TreeAgreement.translate reify (TreeFactored.addNode state parent child) := by
  have rootWidth : (reify state).permissions.length = width := by
    simpa only [reify, TreeQueries.reifyTree_permissions] using
      TreeValidated.uniform_root_width state.topology [] state.store width parentUniform
  have parentArrays : TreeReference.arraysSized (reify state) width = true := by
    rw [TreeQueries.arraysSized_reify]
    exact parentUniform
  have childArrays : TreeReference.arraysSized (reify child) width = true := by
    rw [TreeQueries.arraysSized_reify]
    exact childUniform
  simp only [TreeReference.addNode, rootWidth, parentArrays, childArrays,
    Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  change TreeReference.modifyAt (reify state) parent (appendCallback parent (reify child)) = _
  cases found : TreeFactored.findTopology state.topology parent with
  | none =>
      have missing : TreeReference.findNode (reify state) parent = none :=
        (TreeLookup.findNode_missing_iff state.topology [] state.store parent).mpr found
      rw [TreeUnprotectTotal.modifyAt_missing _ _ _ missing]
      simp only [TreeFactored.addNode, found, TreeAgreement.translate,
        TreeCorrespondence.structuralToReference]
  | some selected =>
      cases selected with
      | node children =>
          let update : Topology → Topology := fun current =>
            match current with | .node old => .node (old.snoc child.topology)
          obtain ⟨changed, actualShape⟩ :=
            modifyTopology_exists state.topology (.node children) parent update found
          have constantShape : TreeFactored.modifyTopology state.topology parent
              (fun _ => .node (children.snoc child.topology)) = some changed := by
            rw [← modifyTopology_at_found state.topology (.node children) parent update found]
            exact actualShape
          rw [insertion_found state child parent children changed found constantShape]
          simp only [TreeFactored.addNode, found]
          change _ = TreeAgreement.translate reify
            (match TreeFactored.modifyTopology state.topology parent update with
            | none => .unsupported .invalidPath state
            | some topology => .ok (parent ++ [children.length])
                ⟨topology, TreeGraft.graft state.store (parent ++ [children.length]) child.store⟩)
          rw [actualShape]
          rfl

#print axioms stripPrefix_compose
#print axioms graft_below_frame
#print axioms graft_parent_reify
#print axioms modifyTopology_at_found
#print axioms modifyTopology_exists
#print axioms modifyAt_congr_found
#print axioms insertion_found
#print axioms addNode_agrees

end AnnealResearch.TreeInsertionAgreement
