import AnnealResearch.TreeGraft

/-!
Structural path reconstruction checkpoint for child-changing updates. Unlike
the earlier Entry-only callback bridge, replacement may change the complete
selected topology. A local actual modifyTopology equation supplies its purely
structural path case; outside-store framing rebuilds all ancestors and ordered
siblings. No width, kind, permission transition, NoUB or historical invariant
is used here. The final public addNode theorem, including missing paths, is a
later checkpoint and will discharge structural cases internally.
-/

namespace AnnealResearch.TreeGraftPaths

open TreeFactored (Path Topology Forest Store)
open TreeCorrespondence (reifyTree reifyForest)

def OutsideAgree (stem : Path) (old after : Store) : Prop :=
  ∀ query, TreeFactored.stripPrefix stem query = none → after query = old query

theorem stripPrefix_cancel (base stem query : Path) :
    TreeFactored.stripPrefix (base ++ stem) (base ++ query) =
      TreeFactored.stripPrefix stem query := by
  induction base with
  | nil => rfl
  | cons head tail ih =>
      change (if head = head then
        TreeFactored.stripPrefix (tail ++ stem) (tail ++ query) else none) = _
      rw [ite_eq_left rfl]
      exact ih

theorem reifyTree_outside_branch (topology : Topology) (parent : Path)
    (index selected : Nat) (suffix : Path) (old after : Store)
    (different : index ≠ selected)
    (frame : OutsideAgree (parent ++ selected :: suffix) old after) :
    reifyTree topology (parent ++ [index]) after =
      reifyTree topology (parent ++ [index]) old := by
  apply TreeCorrespondence.reifyTree_congr
  intro query member
  obtain ⟨rest, shape⟩ := TreeTraversal.representedTree_suffix topology
    (parent ++ [index]) query member
  have full : query = parent ++ index :: rest := by
    simpa only [List.append_assoc, List.singleton_append] using shape
  apply frame query
  rw [full, stripPrefix_cancel]
  simp [TreeFactored.stripPrefix, Ne.symm different]

theorem reifyForest_outside_later (children : Forest) (parent : Path)
    (start selected : Nat) (suffix : Path) (old after : Store)
    (later : selected < start)
    (frame : OutsideAgree (parent ++ selected :: suffix) old after) :
    reifyForest children parent start after = reifyForest children parent start old := by
  cases children with
  | nil => rfl
  | cons first rest =>
      simp only [reifyForest]
      rw [reifyTree_outside_branch first parent start selected suffix old after (by omega) frame,
        reifyForest_outside_later rest parent (start + 1) selected suffix old after
          (by omega) frame]
termination_by structural children

/-- Every ordered sibling outside the chosen child is rebuilt with its
unchanged represented entries. The replacement child can have any topology. -/
theorem reifyForest_replace (children : Forest) (parent : Path) (start relative : Nat)
    (original replacement : Topology) (suffix : Path) (old after : Store)
    (found : children.get? relative = some original)
    (frame : OutsideAgree (parent ++ (start + relative) :: suffix) old after) :
    reifyForest (children.replace relative replacement) parent start after =
      TreeReference.replaceNth (reifyForest children parent start old) relative
        (reifyTree replacement (parent ++ [start + relative]) after) := by
  induction relative generalizing children start with
  | zero =>
      cases children with
      | nil => cases found
      | cons first rest =>
          simp only [TreeFactored.Forest.replace, TreeReference.replaceNth,
            reifyForest, Nat.add_zero]
          have rootFrame : OutsideAgree (parent ++ start :: suffix) old after := by
            simpa only [Nat.add_zero] using frame
          rw [reifyForest_outside_later rest parent (start + 1) start suffix old after
            (by omega) rootFrame]
  | succ relative ih =>
      cases children with
      | nil => cases found
      | cons first rest =>
          have below : rest.get? relative = some original := by
            simpa only [TreeFactored.Forest.get?] using found
          have position : start + (relative + 1) = start + 1 + relative := by omega
          have nextFrame : OutsideAgree
              (parent ++ (start + 1 + relative) :: suffix) old after := by
            simpa only [position] using frame
          simp only [TreeFactored.Forest.replace, TreeReference.replaceNth, reifyForest]
          rw [position]
          rw [reifyTree_outside_branch first parent start (start + 1 + relative)
            suffix old after (by omega) nextFrame,
            ih rest (start + 1) below nextFrame]

/-- Full ancestor reconstruction for an arbitrary structural subtree update.
The callback ignores its input only because its complete chosen replacement is
provided explicitly. Final insertion will prove that replacement equals the
actual append callback, rather than execute one runner through the other. -/
theorem modifyAt_replacement {A : Type} (value : A) (topology : Topology)
    (here : Path) (old after : Store) (path : Path) (replacement changed : Topology)
    (shape : TreeFactored.modifyTopology topology path (fun _ => replacement) = some changed)
    (frame : OutsideAgree (here ++ path) old after) :
    TreeReference.modifyAt (reifyTree topology here old) path
        (fun _ => .ok value (reifyTree replacement (here ++ path) after)) =
      .ok value (reifyTree changed here after) := by
  induction path generalizing topology here changed with
  | nil =>
      have same : replacement = changed := by
        simpa only [TreeFactored.modifyTopology, Option.some.injEq] using shape
      subst changed
      simp only [TreeReference.modifyAt, List.append_nil]
  | cons index rest ih =>
      cases topology with
      | node children =>
          cases childFound : children.get? index with
          | none =>
              simp only [TreeFactored.modifyTopology, childFound] at shape
              cases shape
          | some child =>
              cases updated : TreeFactored.modifyTopology child rest (fun _ => replacement) with
              | none =>
                  simp only [TreeFactored.modifyTopology, childFound, updated] at shape
                  cases shape
              | some changedChild =>
                  have same : Topology.node (children.replace index changedChild) = changed := by
                    simpa only [TreeFactored.modifyTopology, childFound, updated,
                      Option.some.injEq] using shape
                  subst changed
                  have childFrame : OutsideAgree ((here ++ [index]) ++ rest) old after := by
                    simpa only [List.append_assoc, List.singleton_append] using frame
                  have step := ih child (here ++ [index]) changedChild updated childFrame
                  simp only [List.append_assoc, List.singleton_append] at step
                  have rootAbsent : TreeFactored.stripPrefix (here ++ index :: rest) here = none := by
                    have cancelled := stripPrefix_cancel here (index :: rest) []
                    simpa only [List.append_nil, TreeFactored.stripPrefix] using cancelled
                  have rootSame := frame here rootAbsent
                  have forestFrame : OutsideAgree (here ++ (0 + index) :: rest) old after := by
                    simpa only [Nat.zero_add] using frame
                  have forest := reifyForest_replace children here 0 index child changedChild
                    rest old after childFound forestFrame
                  simp only [Nat.zero_add] at forest
                  conv => lhs; rw [reifyTree]
                  rw [TreeReference.modifyAt, TreeLookup.reifyForest_get?]
                  simp only [Nat.zero_add, childFound, Option.map]
                  rw [step]
                  simp only [TreeReference.Result.mapState, reifyTree]
                  rw [rootSame, forest]

#print axioms stripPrefix_cancel
#print axioms reifyTree_outside_branch
#print axioms reifyForest_outside_later
#print axioms reifyForest_replace
#print axioms modifyAt_replacement

end AnnealResearch.TreeGraftPaths
