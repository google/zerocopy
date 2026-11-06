import AnnealResearch.TreeLiveRelease

/-!
Actual recursive-reference reborrow preserves LiveKinds on every residual.
Ordered insertion preserves the exact existing matching Boolean when the new
child matches; its public width/path rejections retain the input tree. Actual
initialAccesses preserves that Boolean without an admission premise.

The memory theorem derives birth matching from its executed child-settings
guard. Input LiveKinds is its only premise: no WellSized, valid path, caller
settings compatibility, StateWF, successful access or NoUB assumption is added.
Raw memory is unchanged and frame registration changes no tree. This is an
owned selected-operation theorem, not a full type/layout or Rust adequacy claim.
-/

namespace AnnealResearch.TreeReborrowKinds

open TreePermissions
open TreeMemory (State Pointer Tree)
open TreeLiveKinds (LiveKinds)
open TreeLiveMemory (ResultLiveKinds)

/-- Exact replacement congruence for one represented ordered child. -/
theorem childrenMatch_replace (children : List TreeReference.Node) (index : Nat)
    (before after : TreeReference.Node) (found : children[index]? = some before)
    (same : TreeReference.kindsMatch after = TreeReference.kindsMatch before) :
    TreeReference.childrenMatch (TreeReference.replaceNth children index after) =
      TreeReference.childrenMatch children := by
  induction index generalizing children with
  | zero =>
    cases children with
    | nil => cases found
    | cons first rest =>
      have equal : first = before := Option.some.inj found
      subst before
      simp only [TreeReference.replaceNth, TreeReference.childrenMatch]
      rw [same]
  | succ index ih =>
    cases children with
    | nil => cases found
    | cons first rest =>
      have below : rest[index]? = some before := found
      simp only [TreeReference.replaceNth, TreeReference.childrenMatch]
      rw [ih rest below]

/-- Appending a matching child leaves the existing matching Boolean exact,
including when a different old node already mismatches. -/
theorem childrenMatch_append (children : List TreeReference.Node) (child : TreeReference.Node)
    (childMatching : TreeReference.kindsMatch child = true) :
    TreeReference.childrenMatch (children ++ [child]) = TreeReference.childrenMatch children := by
  induction children with
  | nil => simp [TreeReference.childrenMatch, childMatching]
  | cons first rest ih =>
    simp only [List.cons_append, TreeReference.childrenMatch]
    rw [ih]

/-- Callback query equality lifts through every actual modifyAt residual.
Missing paths keep their original tree; returned errors retain reconstructed
partial trial trees, with the original child order. -/
theorem modifyAt_matching (node : TreeReference.Node) (path : TreeReference.Path)
    (callback : TreeReference.Node → TreeReference.Result A TreeReference.Node)
    (preserves : ∀ selected,
      TreeReference.kindsMatch (callback selected).state = TreeReference.kindsMatch selected) :
    TreeReference.kindsMatch (TreeReference.modifyAt node path callback).state =
      TreeReference.kindsMatch node := by
  induction path generalizing node with
  | nil => exact preserves node
  | cons index rest ih =>
    cases node with
    | mk permissions protection children =>
      cases found : children[index]? with
      | none => simp only [TreeReference.modifyAt, found, TreeReference.Result.state]
      | some child =>
        simp only [TreeReference.modifyAt, found]
        rw [TreeKindPreservation.mapState_state]
        simp only [TreeReference.kindsMatch]
        rw [childrenMatch_replace children index child
          (TreeReference.modifyAt child rest callback).state found (ih child)]

/-- No width or valid-path premise: actual public insertion either rejects
with the input tree or executes the ordered matching-child append. -/
theorem addNode_matching (node : TreeReference.Node) (parent : TreeReference.Path)
    (child : TreeReference.Node) (childMatching : TreeReference.kindsMatch child = true) :
    TreeReference.kindsMatch (TreeReference.addNode node parent child).state =
      TreeReference.kindsMatch node := by
  unfold TreeReference.addNode
  try dsimp only
  split
  · rfl
  · apply modifyAt_matching
    intro selected
    cases selected with
    | mk permissions protection children =>
      simp only [TreeReference.Result.state, TreeReference.kindsMatch]
      rw [childrenMatch_append children child childMatching]

/-- Process the original inside-settings list. Every public access retains
its exact matching Boolean, including partial UB and structural rejection. -/
theorem initialAccesses_matching (node : TreeReference.Node) (path : TreeReference.Path)
    (offset : Nat) (inside : List Permission) :
    TreeReference.kindsMatch (TreeReference.initialAccesses node path offset inside).state =
      TreeReference.kindsMatch node := by
  induction inside generalizing node offset with
  | nil => rfl
  | cons permission rest ih =>
    cases initial : permission.initAccess with
    | none =>
      simpa only [TreeReference.initialAccesses, initial] using ih node (offset + 1)
    | some kind =>
      simp only [TreeReference.initialAccesses, initial]
      have same := TreeKindAccess.access_matching node (some path) kind offset 1
      cases acted : TreeReference.access node (some path) kind offset 1 with
      | ok result changed =>
        cases result
        simp only [TreeReference.Result.bind]
        rw [ih changed (offset + 1)]
        simpa only [acted, TreeReference.Result.state] using same
      | ub fault changed =>
        simpa only [TreeReference.Result.bind, TreeReference.Result.state, acted] using same
      | unsupported reason changed =>
        simpa only [TreeReference.Result.bind, TreeReference.Result.state, acted] using same

/-- Child birth matching comes from the executed whole-list guard, rather
than a caller-supplied settings or width condition. -/
theorem leaf_matching (permissions : List Permission) (protection : Protected)
    (accepted : permissions.all (fun permission => permission.matchesProtector protection) = true) :
    TreeReference.kindsMatch (.mk permissions protection []) = true := by
  simp only [TreeReference.kindsMatch, TreeReference.childrenMatch, accepted, Bool.and_self]

/-- All actual outcomes preserve live matching. Raw prechecks, geometry and
settings rejection are inspected internally. Insertion/initial-access failures
keep their exact committed partial tree and still satisfy the predicate. -/
theorem reborrow_preserves_all (state : State) (pointer : Pointer) (settings : TreeMemory.Settings)
    (matching : LiveKinds state) : ResultLiveKinds (TreeMemory.reborrow state pointer settings) := by
  unfold ResultLiveKinds TreeMemory.reborrow
  cases checked : MiniRustReference.checkPtr state.raw pointer.basic settings.inside.length with
  | ub fault => exact matching
  | unsupported => exact matching
  | noChoice => exact matching
  | ok maybeSpan =>
    cases origin : pointer.provenance with
    | none => exact matching
    | some provenance =>
      rcases provenance with ⟨id, parentPath⟩
      dsimp only
      cases rawFound : state.raw.allocations id with
      | none => exact matching
      | some allocation =>
        cases present : state.trees id with
        | none => exact matching
        | some tree =>
          dsimp only
          by_cases beforeBase : pointer.addr < allocation.base
          · simp only [ite_eq_left beforeBase, TreeLiveMemory.residual]
            exact matching
          · simp only [ite_eq_right beforeBase]
            by_cases beyond : allocation.size < pointer.addr - allocation.base + settings.inside.length
            · simp only [ite_eq_left beyond, TreeLiveMemory.residual]
              exact matching
            · simp only [ite_eq_right beyond]
              let permissions :=
                (List.replicate allocation.size settings.outside).take (pointer.addr - allocation.base) ++
                settings.inside ++ (List.replicate allocation.size settings.outside).drop
                  (pointer.addr - allocation.base + settings.inside.length)
              change LiveKinds (TreeLiveMemory.residual
                (if !permissions.all (fun permission => permission.matchesProtector settings.protection) then
                  TreeMemory.Result.unsupported .settings state
                else
                  match TreeReference.addNode tree parentPath
                      (.mk permissions settings.protection []) with
                  | .ub fault changed => .ub (.tree fault) (TreeMemory.setTree state id changed)
                  | .unsupported reason changed =>
                    .unsupported (.tree reason) (TreeMemory.setTree state id changed)
                  | .ok path added =>
                    match TreeReference.initialAccesses added path
                        (pointer.addr - allocation.base) settings.inside with
                    | .ub fault changed => .ub (.tree fault) (TreeMemory.setTree state id changed)
                    | .unsupported reason changed =>
                      .unsupported (.tree reason) (TreeMemory.setTree state id changed)
                    | .ok () changed =>
                      .ok { pointer with provenance := some (id, path) }
                        (if settings.protection.yes then
                          { TreeMemory.setTree state id changed with currentFrame :=
                              state.currentFrame ++ [(id, path)] }
                        else TreeMemory.setTree state id changed)))
              cases accepted : permissions.all
                  (fun permission => permission.matchesProtector settings.protection) with
              | false => exact matching
              | true =>
                have birth := leaf_matching permissions settings.protection accepted
                have insertion := addNode_matching tree parentPath
                  (.mk permissions settings.protection []) birth
                cases inserted : TreeReference.addNode tree parentPath
                    (.mk permissions settings.protection []) with
                | ub fault changed =>
                  have same : TreeReference.kindsMatch changed = TreeReference.kindsMatch tree := by
                    simpa only [inserted, TreeReference.Result.state] using insertion
                  exact TreeLiveKinds.liveKinds_replace_tree state id tree changed matching present same
                | unsupported reason changed =>
                  have same : TreeReference.kindsMatch changed = TreeReference.kindsMatch tree := by
                    simpa only [inserted, TreeReference.Result.state] using insertion
                  exact TreeLiveKinds.liveKinds_replace_tree state id tree changed matching present same
                | ok path added =>
                  have insertedSame : TreeReference.kindsMatch added = TreeReference.kindsMatch tree := by
                    simpa only [inserted, TreeReference.Result.state] using insertion
                  dsimp only
                  have accesses := initialAccesses_matching added path
                    (pointer.addr - allocation.base) settings.inside
                  cases started : TreeReference.initialAccesses added path
                      (pointer.addr - allocation.base) settings.inside with
                  | ub fault changed =>
                    have accessedSame : TreeReference.kindsMatch changed = TreeReference.kindsMatch added := by
                      simpa only [started, TreeReference.Result.state] using accesses
                    have same : TreeReference.kindsMatch changed = TreeReference.kindsMatch tree :=
                      accessedSame.trans insertedSame
                    exact TreeLiveKinds.liveKinds_replace_tree state id tree changed matching present same
                  | unsupported reason changed =>
                    have accessedSame : TreeReference.kindsMatch changed = TreeReference.kindsMatch added := by
                      simpa only [started, TreeReference.Result.state] using accesses
                    have same : TreeReference.kindsMatch changed = TreeReference.kindsMatch tree :=
                      accessedSame.trans insertedSame
                    exact TreeLiveKinds.liveKinds_replace_tree state id tree changed matching present same
                  | ok result changed =>
                    cases result
                    have accessedSame : TreeReference.kindsMatch changed = TreeReference.kindsMatch added := by
                      simpa only [started, TreeReference.Result.state] using accesses
                    have same : TreeReference.kindsMatch changed = TreeReference.kindsMatch tree :=
                      accessedSame.trans insertedSame
                    have updated := TreeLiveKinds.liveKinds_replace_tree state id tree changed matching present same
                    cases registered : settings.protection.yes with
                    | false => exact updated
                    | true =>
                      exact TreeLiveKinds.liveKinds_with_frame (TreeMemory.setTree state id changed)
                        (state.currentFrame ++ [(id, path)]) updated

/-- Requested stable-running corollary; the all-residual theorem above is
stronger for reborrow, unlike the separate release boundary. -/
theorem reborrow_preserves (state : State) (pointer : Pointer) (settings : TreeMemory.Settings)
    (matching : LiveKinds state) :
    TreeLiveRelease.RunningKinds (TreeMemory.reborrow state pointer settings) :=
  TreeLiveRelease.resultLiveKinds_implies_runningKinds _
    (reborrow_preserves_all state pointer settings matching)

#print axioms childrenMatch_replace
#print axioms childrenMatch_append
#print axioms modifyAt_matching
#print axioms addNode_matching
#print axioms initialAccesses_matching
#print axioms leaf_matching
#print axioms reborrow_preserves_all
#print axioms reborrow_preserves

end AnnealResearch.TreeReborrowKinds
