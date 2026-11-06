import AnnealResearch.TreeInsertionAgreement

/-!
Uniform-width preservation for every actual insertion residual. This proof
deliberately uses the recursive representation's list reconstruction and then
transports through the checked exact insertion equation and query bridge. It
is shared proof investment, not a second independent preservation proof.

The public all-outcome theorem has only common parent/child uniform-width
premises. Missing paths and every returned category remain present. No old
absent-store, kind, valid-path, permission-success, NoUB or history admission
is introduced. The separately named success-output corollary merely extracts
the uniformity of a supplied actual output; it does not restrict the main result.
-/

namespace AnnealResearch.TreeInsertionWidths

open TreeFactored (State)
open TreeCorrespondence (reify)

theorem childrenSized_get (nodes : List TreeReference.Node) (width index : Nat)
    (node : TreeReference.Node)
    (uniform : TreeReference.childrenSized nodes width = true)
    (found : nodes[index]? = some node) : TreeReference.arraysSized node width = true := by
  induction index generalizing nodes with
  | zero =>
      cases nodes with
      | nil => cases found
      | cons first rest =>
          change some first = some node at found
          have equal : first = node := Option.some.inj found
          subst node
          have parts : TreeReference.arraysSized first width = true ∧
              TreeReference.childrenSized rest width = true := by
            simpa only [TreeReference.childrenSized, Bool.and_eq_true] using uniform
          exact parts.1
  | succ index ih =>
      cases nodes with
      | nil => cases found
      | cons first rest =>
          have parts : TreeReference.arraysSized first width = true ∧
              TreeReference.childrenSized rest width = true := by
            simpa only [TreeReference.childrenSized, Bool.and_eq_true] using uniform
          apply ih rest parts.2
          exact found

theorem childrenSized_replaceNth (nodes : List TreeReference.Node) (index width : Nat)
    (replacement : TreeReference.Node)
    (uniform : TreeReference.childrenSized nodes width = true)
    (replacementUniform : TreeReference.arraysSized replacement width = true) :
    TreeReference.childrenSized (TreeReference.replaceNth nodes index replacement) width = true := by
  induction index generalizing nodes with
  | zero =>
      cases nodes with
      | nil => simp only [TreeReference.replaceNth, TreeReference.childrenSized]
      | cons first rest =>
          have parts : TreeReference.arraysSized first width = true ∧
              TreeReference.childrenSized rest width = true := by
            simpa only [TreeReference.childrenSized, Bool.and_eq_true] using uniform
          simp only [TreeReference.replaceNth, TreeReference.childrenSized,
            replacementUniform, parts.2, Bool.and_self]
  | succ index ih =>
      cases nodes with
      | nil => simp only [TreeReference.replaceNth, TreeReference.childrenSized]
      | cons first rest =>
          have parts : TreeReference.arraysSized first width = true ∧
              TreeReference.childrenSized rest width = true := by
            simpa only [TreeReference.childrenSized, Bool.and_eq_true] using uniform
          simp only [TreeReference.replaceNth, TreeReference.childrenSized,
            parts.1, ih rest parts.2, Bool.true_and]

theorem childrenSized_snoc (nodes : List TreeReference.Node) (child : TreeReference.Node)
    (width : Nat) (uniform : TreeReference.childrenSized nodes width = true)
    (childUniform : TreeReference.arraysSized child width = true) :
    TreeReference.childrenSized (nodes ++ [child]) width = true := by
  cases nodes with
  | nil => simp only [List.nil_append, TreeReference.childrenSized, childUniform, Bool.and_self]
  | cons first rest =>
      have parts : TreeReference.arraysSized first width = true ∧
          TreeReference.childrenSized rest width = true := by
        simpa only [TreeReference.childrenSized, Bool.and_eq_true] using uniform
      simp only [List.cons_append, TreeReference.childrenSized, parts.1,
        childrenSized_snoc rest child width parts.2 childUniform, Bool.true_and]
termination_by structural nodes

theorem state_mapState (answer : TreeReference.Result A S) (view : S → T) :
    (answer.mapState view).state = view answer.state := by
  cases answer <;> rfl

/-- Arbitrary callbacks may change the selected topology and may return any
category. Only their all-residual structural-width preservation is required. -/
theorem modifyAt_preserves_uniform (node : TreeReference.Node) (path : TreeReference.Path)
    (callback : TreeReference.Node → TreeReference.Result A TreeReference.Node) (width : Nat)
    (uniform : TreeReference.arraysSized node width = true)
    (preserves : ∀ selected, TreeReference.arraysSized selected width = true →
      TreeReference.arraysSized (callback selected).state width = true) :
    TreeReference.arraysSized (TreeReference.modifyAt node path callback).state width = true := by
  induction path generalizing node with
  | nil => exact preserves node uniform
  | cons index rest ih =>
      cases node with
      | mk permissions protection children =>
          have parts : (permissions.length == width) = true ∧
              TreeReference.childrenSized children width = true := by
            simpa only [TreeReference.arraysSized, Bool.and_eq_true] using uniform
          cases found : children[index]? with
          | none =>
              simpa only [TreeReference.modifyAt, found, TreeReference.Result.state] using uniform
          | some child =>
              have childWidth := childrenSized_get children width index child parts.2 found
              have changedWidth := ih child childWidth
              simp only [TreeReference.modifyAt, found]
              rw [state_mapState]
              simp only [TreeReference.arraysSized, parts.1,
                childrenSized_replaceNth children index width
                  (TreeReference.modifyAt child rest callback).state parts.2 changedWidth,
                Bool.and_self]

theorem appendCallback_preserves_uniform (parent : TreeReference.Path)
    (child node : TreeReference.Node) (width : Nat)
    (uniform : TreeReference.arraysSized node width = true)
    (childUniform : TreeReference.arraysSized child width = true) :
    TreeReference.arraysSized
      (TreeInsertionAgreement.appendCallback parent child node).state width = true := by
  cases node with
  | mk permissions protection children =>
      have parts : (permissions.length == width) = true ∧
          TreeReference.childrenSized children width = true := by
        simpa only [TreeReference.arraysSized, Bool.and_eq_true] using uniform
      simp only [TreeInsertionAgreement.appendCallback, TreeReference.Result.state,
        TreeReference.arraysSized, parts.1,
        childrenSized_snoc children child width parts.2 childUniform, Bool.and_self]

theorem reference_addNode_preserves_uniform (node child : TreeReference.Node)
    (parent : TreeReference.Path) (width : Nat)
    (uniform : TreeReference.arraysSized node width = true)
    (childUniform : TreeReference.arraysSized child width = true) :
    TreeReference.arraysSized (TreeReference.addNode node parent child).state width = true := by
  unfold TreeReference.addNode
  try dsimp only
  split
  · exact uniform
  · apply modifyAt_preserves_uniform node parent
      (TreeInsertionAgreement.appendCallback parent child) width uniform
    intro selected selectedWidth
    exact appendCallback_preserves_uniform parent child selected width selectedWidth childUniform

theorem translated_state (answer : TreeFactored.Result A State) :
    (TreeAgreement.translate reify answer).state = reify answer.residual := by
  cases answer <;> rfl

/-- Every actual residual, including missing-path unsupported, retains the
common width. The public premise contains no successful-result requirement. -/
theorem addNode_preserves_uniform (state child : State) (parent : TreeFactored.Path) (width : Nat)
    (parentUniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true)
    (childUniform : TreeFactored.arrayLengthsTree child.topology [] child.store width = true) :
    TreeFactored.arrayLengthsTree (TreeFactored.addNode state parent child).residual.topology []
      (TreeFactored.addNode state parent child).residual.store width = true := by
  have parentReference : TreeReference.arraysSized (reify state) width = true := by
    rw [TreeQueries.arraysSized_reify]
    exact parentUniform
  have childReference : TreeReference.arraysSized (reify child) width = true := by
    rw [TreeQueries.arraysSized_reify]
    exact childUniform
  have preserved := reference_addNode_preserves_uniform (reify state) (reify child)
    parent width parentReference childReference
  rw [TreeInsertionAgreement.addNode_agrees state child parent width parentUniform childUniform,
    translated_state, TreeQueries.arraysSized_reify] at preserved
  exact preserved

/-- Success-output extraction only. The preceding theorem already covers all
outcomes without this equation as an admission premise. -/
theorem addNode_success_uniform (state child changed : State)
    (parent returned : TreeFactored.Path) (width : Nat)
    (parentUniform : TreeFactored.arrayLengthsTree state.topology [] state.store width = true)
    (childUniform : TreeFactored.arrayLengthsTree child.topology [] child.store width = true)
    (success : TreeFactored.addNode state parent child = .ok returned changed) :
    TreeFactored.arrayLengthsTree changed.topology [] changed.store width = true := by
  have preserved := addNode_preserves_uniform state child parent width parentUniform childUniform
  simpa only [success, TreeFactored.Result.residual] using preserved

#print axioms childrenSized_get
#print axioms childrenSized_replaceNth
#print axioms childrenSized_snoc
#print axioms state_mapState
#print axioms modifyAt_preserves_uniform
#print axioms appendCallback_preserves_uniform
#print axioms reference_addNode_preserves_uniform
#print axioms translated_state
#print axioms addNode_preserves_uniform
#print axioms addNode_success_uniform

end AnnealResearch.TreeInsertionWidths
