import AnnealResearch.TreeKindPreservation

/-!
First reusable release-kind layer. kindsAfterClear is a structural query: test
the selected node's existing permissions against No, retain its descendants,
and test every other node against its existing flag. It performs no permission
transition or conversion. Actual successful release traversal has exactly this
query, with no width/path/matching premise on the local success lemmas.

The next conversion obligation is to relate this query after actual unprotect
to the original tree's ordinary query. That is not assumed or proved here.
Ordinary all-residual release matching preservation is false; no such theorem
or public memory-operation success admission is introduced by this checkpoint.
-/

namespace AnnealResearch.TreeReleaseKinds

open TreePermissions

mutual
  def kindsAfterClear (node : TreeReference.Node) (path : Option TreeReference.Path) : Bool :=
    match node with
    | .mk permissions protection children =>
      if path = some [] then
        permissions.all (fun permission => permission.matchesProtector .no) &&
          TreeReference.childrenMatch children
      else
        permissions.all (fun permission => permission.matchesProtector protection) &&
          childrenAfterClear children path 0
  termination_by sizeOf node
  decreasing_by all_goals simp_wf <;> omega

  def childrenAfterClear (children : List TreeReference.Node) (path : Option TreeReference.Path)
      (index : Nat) : Bool :=
    match children with
    | [] => true
    | child :: rest =>
      kindsAfterClear child (TreeReference.childPath path index) &&
        childrenAfterClear rest path (index + 1)
  termination_by sizeOf children
  decreasing_by all_goals simp_wf <;> omega
end

mutual
  theorem kindsAfterClear_none (node : TreeReference.Node) :
      kindsAfterClear node none = TreeReference.kindsMatch node :=
    match node with
    | .mk permissions protection children => by
      simp [kindsAfterClear, TreeReference.kindsMatch]
      rw [childrenAfterClear_none children 0]
  termination_by sizeOf node
  decreasing_by all_goals simp_wf <;> omega

  theorem childrenAfterClear_none (children : List TreeReference.Node) (index : Nat) :
      childrenAfterClear children none index = TreeReference.childrenMatch children :=
    match children with
    | [] => by simp only [childrenAfterClear, TreeReference.childrenMatch]
    | child :: rest => by
      simp only [childrenAfterClear, TreeReference.childPath, TreeReference.childrenMatch]
      rw [kindsAfterClear_none child, childrenAfterClear_none rest (index + 1)]
  termination_by sizeOf children
  decreasing_by all_goals simp_wf <;> omega
end

theorem mapState_ok {A S T : Type} (answer : TreeReference.Result A S) (f : S → T)
    (value : A) (after : T) (success : answer.mapState f = .ok value after) :
    ∃ before, answer = .ok value before ∧ f before = after := by
  cases answer with
  | ok returned before =>
    change TreeReference.Result.ok returned (f before) = .ok value after at success
    obtain ⟨sameValue, sameState⟩ := TreeReference.Result.ok.inj success
    subst value
    exact ⟨before, rfl, sameState⟩
  | ub fault before =>
    simp only [TreeReference.Result.mapState] at success
    cases success
  | unsupported reason before =>
    simp only [TreeReference.Result.mapState] at success
    cases success

/-- A checked equation for the frozen Node runner, exposing its selected-node
branch as an if. This introduces no alternate runner or flag policy. -/
theorem releaseCore_node (permissions : List Permission) (protection : Protected)
    (children : List TreeReference.Node) (path : Option TreeReference.Path)
    (accesses : List (Option AccessKind)) :
    TreeReference.releaseCore (.mk permissions protection children) path accesses =
      if path = some [] then .ok () (.mk permissions .no children)
      else match TreeReference.applyAccesses permissions accesses (TreeReference.nodeRelation path) with
      | .ok () changed =>
        (TreeReference.releaseChildren children path accesses 0).mapState
          (fun nextChildren => .mk changed protection nextChildren)
      | .ub fault changed => .ub fault (.mk changed protection children)
      | .unsupported reason changed => .unsupported reason (.mk changed protection children) := by
  cases path with
  | none =>
    cases acted : TreeReference.applyAccesses permissions accesses
        (TreeReference.nodeRelation none) with
    | ok result changed => cases result; simp [TreeReference.releaseCore, acted]
    | ub fault changed => simp [TreeReference.releaseCore, acted]
    | unsupported reason changed => simp [TreeReference.releaseCore, acted]
  | some rest =>
    cases rest with
    | nil => simp [TreeReference.releaseCore]
    | cons first tail =>
      cases acted : TreeReference.applyAccesses permissions accesses
          (TreeReference.nodeRelation (some (first :: tail))) with
      | ok result changed => cases result; simp [TreeReference.releaseCore, acted]
      | ub fault changed => simp [TreeReference.releaseCore, acted]
      | unsupported reason changed => simp [TreeReference.releaseCore, acted]

mutual
  /-- The output equation is an actual local result observation. No public
  command boundary is restricted to success by this helper. -/
  theorem releaseCore_success_matching (node : TreeReference.Node)
      (path : Option TreeReference.Path) (accesses : List (Option AccessKind))
      (after : TreeReference.Node)
      (success : TreeReference.releaseCore node path accesses = .ok () after) :
      TreeReference.kindsMatch after = kindsAfterClear node path :=
    match node, success with
    | .mk permissions protection children, success => by
      rw [releaseCore_node] at success
      by_cases selected : path = some []
      · simp only [ite_eq_left selected] at success
        have same : TreeReference.Node.mk permissions .no children = after :=
          (TreeReference.Result.ok.inj success).2
        rw [← same]
        simp only [kindsAfterClear, ite_eq_left selected, TreeReference.kindsMatch]
      · simp only [ite_eq_right selected] at success
        cases acted : TreeReference.applyAccesses permissions accesses
            (TreeReference.nodeRelation path) with
        | ub fault changed =>
          simp only [acted] at success
          cases success
        | unsupported reason changed =>
          simp only [acted] at success
          cases success
        | ok result changed =>
          cases result
          simp only [acted] at success
          obtain ⟨nextChildren, childrenOK, same⟩ := mapState_ok
            (TreeReference.releaseChildren children path accesses 0)
            (fun found => TreeReference.Node.mk changed protection found) () after success
          have childQuery := releaseChildren_success_matching children path accesses 0
            nextChildren childrenOK
          have byteQuery := TreeKindPreservation.applyAccesses_matching permissions accesses
            (TreeReference.nodeRelation path) protection
          have currentQuery : changed.all (fun entry => entry.matchesProtector protection) =
              permissions.all (fun entry => entry.matchesProtector protection) := by
            simpa only [acted, TreeReference.Result.state] using byteQuery
          rw [← same]
          simp only [TreeReference.kindsMatch, kindsAfterClear, ite_eq_right selected]
          rw [currentQuery, childQuery]
  termination_by sizeOf node
  decreasing_by all_goals simp_wf <;> omega

  theorem releaseChildren_success_matching (children : List TreeReference.Node)
      (path : Option TreeReference.Path) (accesses : List (Option AccessKind)) (index : Nat)
      (after : List TreeReference.Node)
      (success : TreeReference.releaseChildren children path accesses index = .ok () after) :
      TreeReference.childrenMatch after = childrenAfterClear children path index :=
    match children, success with
    | [], success => by
      have expanded : TreeReference.Result.ok () ([] : List TreeReference.Node) =
          .ok () after := by
        simpa only [TreeReference.releaseChildren] using success
      have same : ([] : List TreeReference.Node) = after :=
        (TreeReference.Result.ok.inj expanded).2
      rw [← same]
      simp only [TreeReference.childrenMatch, childrenAfterClear]
    | child :: rest, success => by
      rw [TreeReference.releaseChildren] at success
      cases acted : TreeReference.releaseCore child (TreeReference.childPath path index) accesses with
      | ub fault changed =>
        simp only [acted] at success
        cases success
      | unsupported reason changed =>
        simp only [acted] at success
        cases success
      | ok result changed =>
        cases result
        simp only [acted] at success
        obtain ⟨nextRest, tailOK, same⟩ := mapState_ok
          (TreeReference.releaseChildren rest path accesses (index + 1))
          (changed :: ·) () after success
        have headQuery := releaseCore_success_matching child (TreeReference.childPath path index)
          accesses changed acted
        have tailQuery := releaseChildren_success_matching rest path accesses (index + 1)
          nextRest tailOK
        rw [← same]
        simp only [TreeReference.childrenMatch, childrenAfterClear]
        rw [headQuery, tailQuery]
  termination_by sizeOf children
  decreasing_by all_goals simp_wf <;> omega
end

theorem releaseTraverse_success_matching (node : TreeReference.Node)
    (path : Option TreeReference.Path) (accesses : List (Option AccessKind))
    (after : TreeReference.Node)
    (success : TreeReference.releaseTraverse node path accesses = .ok () after) :
    TreeReference.kindsMatch after = kindsAfterClear node path := by
  unfold TreeReference.releaseTraverse at success
  split at success
  · cases success
  · split at success
    · cases success
    · exact releaseCore_success_matching node path accesses after success

#print axioms kindsAfterClear_none
#print axioms childrenAfterClear_none
#print axioms mapState_ok
#print axioms releaseCore_node
#print axioms releaseCore_success_matching
#print axioms releaseChildren_success_matching
#print axioms releaseTraverse_success_matching

end AnnealResearch.TreeReleaseKinds
