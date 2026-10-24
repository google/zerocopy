import AnnealResearch.TreeFactoredReborrow

/-!
Every actual factored-memory reborrow residual preserves the existing WellSized
domain. Actual geometry derives child width; checked insertion and original-list
initial access preserve it on every category, including partial errors. Raw
memory is unchanged without any domain premise. Frame changes do not affect
array-width admission.

Private abbreviations below name the exact post-settings expression and a proof
conjunction. They do not change the frozen runner, add operational guards, or
extend the prefix observer. No LiveKinds, source reachability, valid path,
permission success or NoUB premise is added.
-/

namespace AnnealResearch.TreeReborrowDomain

open TreePermissions
open TreeFactoredMemory (State Pointer Tree)

private def Preserves (state : State) (answer : TreeFactoredMemory.Result A) : Prop :=
  answer.residual.raw = state.raw ∧
    (TreeFactoredMemory.WellSized state → TreeFactoredMemory.WellSized answer.residual)

/-- Syntactic proof abbreviation for the unchanged actual runner's tree phase. -/
private def treePhase (state : State) (pointer : Pointer) (settings : TreeMemory.Settings)
    (id : Nat) (parent : TreeFactored.Path) (tree : Tree) (permissions : List Permission)
    (offset : Nat) : TreeFactoredMemory.Result Pointer :=
  match TreeFactored.addNode tree parent
      (TreeFactoredMemory.reborrowChild permissions settings.protection) with
  | .ub fault changed => .ub (.tree fault) (TreeFactoredMemory.setTree state id changed)
  | .unsupported reason changed => .unsupported
      (.tree (TreeCorrespondence.structuralToReference reason))
      (TreeFactoredMemory.setTree state id changed)
  | .ok path added =>
    match TreeFactored.initialAccesses added path offset settings.inside with
    | .ub fault changed => .ub (.tree fault) (TreeFactoredMemory.setTree state id changed)
    | .unsupported reason changed => .unsupported
        (.tree (TreeCorrespondence.structuralToReference reason))
        (TreeFactoredMemory.setTree state id changed)
    | .ok () changed =>
      let updated := TreeFactoredMemory.setTree state id changed
      let registered := if settings.protection.yes then
        { updated with currentFrame := updated.currentFrame ++ [(id, path)] } else updated
      .ok { pointer with provenance := some (id, path) } registered

theorem setTree_preserves_at (state : State) (id : Nat)
    (allocation : MiniRustReference.Allocation) (tree : Tree)
    (sized : TreeFactoredMemory.WellSized state)
    (present : state.raw.allocations id = some allocation)
    (uniform : TreeFactored.arrayLengthsTree tree.topology [] tree.store allocation.size = true) :
    TreeFactoredMemory.WellSized (TreeFactoredMemory.setTree state id tree) := by
  apply TreeMemoryDomain.wellSized_setTree state id tree sized
  intro actual found
  have same : allocation = actual := Option.some.inj (present.symm.trans found)
  subst actual
  exact uniform

theorem treePhase_raw (state : State) (pointer : Pointer) (settings : TreeMemory.Settings)
    (id : Nat) (parent : TreeFactored.Path) (tree : Tree) (permissions : List Permission)
    (offset : Nat) :
    (treePhase state pointer settings id parent tree permissions offset).residual.raw = state.raw := by
  unfold treePhase
  cases TreeFactored.addNode tree parent
      (TreeFactoredMemory.reborrowChild permissions settings.protection) with
  | ub fault changed => rfl
  | unsupported reason changed => rfl
  | ok path added =>
      simp only
      cases TreeFactored.initialAccesses added path offset settings.inside with
      | ub fault changed => rfl
      | unsupported reason changed => rfl
      | ok value changed =>
          cases value
          cases settings.protection.yes <;> rfl

theorem treePhase_preserves (state : State) (pointer : Pointer) (settings : TreeMemory.Settings)
    (id : Nat) (parent : TreeFactored.Path) (tree : Tree) (permissions : List Permission)
    (offset : Nat) (allocation : MiniRustReference.Allocation)
    (sized : TreeFactoredMemory.WellSized state)
    (rawFound : state.raw.allocations id = some allocation)
    (treeFound : state.trees id = some tree)
    (childUniform : TreeFactored.arrayLengthsTree
      (TreeFactoredMemory.reborrowChild permissions settings.protection).topology []
      (TreeFactoredMemory.reborrowChild permissions settings.protection).store allocation.size = true) :
    TreeFactoredMemory.WellSized
      (treePhase state pointer settings id parent tree permissions offset).residual := by
  have uniform := sized id allocation tree rawFound treeFound
  have insertionWidth := TreeInsertionWidths.addNode_preserves_uniform tree
    (TreeFactoredMemory.reborrowChild permissions settings.protection) parent
    allocation.size uniform childUniform
  unfold treePhase
  cases inserted : TreeFactored.addNode tree parent
      (TreeFactoredMemory.reborrowChild permissions settings.protection) with
  | ub fault changed =>
      have changedWidth :
          TreeFactored.arrayLengthsTree changed.topology [] changed.store allocation.size = true := by
        simpa only [inserted, TreeFactored.Result.residual] using insertionWidth
      exact setTree_preserves_at state id allocation changed sized rawFound changedWidth
  | unsupported reason changed =>
      have changedWidth :
          TreeFactored.arrayLengthsTree changed.topology [] changed.store allocation.size = true := by
        simpa only [inserted, TreeFactored.Result.residual] using insertionWidth
      exact setTree_preserves_at state id allocation changed sized rawFound changedWidth
  | ok path added =>
      simp only
      have addedWidth : TreeFactored.arrayLengthsTree added.topology [] added.store allocation.size = true := by
        simpa only [inserted, TreeFactored.Result.residual] using insertionWidth
      have initialWidth := TreeInitialAgreement.initialAccesses_preserves_uniform added path
        offset settings.inside allocation.size addedWidth
      cases initial : TreeFactored.initialAccesses added path offset settings.inside with
      | ub fault changed =>
          have changedWidth :
              TreeFactored.arrayLengthsTree changed.topology [] changed.store allocation.size = true := by
            simpa only [initial, TreeFactored.Result.residual] using initialWidth
          exact setTree_preserves_at state id allocation changed sized rawFound changedWidth
      | unsupported reason changed =>
          have changedWidth :
              TreeFactored.arrayLengthsTree changed.topology [] changed.store allocation.size = true := by
            simpa only [initial, TreeFactored.Result.residual] using initialWidth
          exact setTree_preserves_at state id allocation changed sized rawFound changedWidth
      | ok value changed =>
          cases value
          have changedWidth :
              TreeFactored.arrayLengthsTree changed.topology [] changed.store allocation.size = true := by
            simpa only [initial, TreeFactored.Result.residual] using initialWidth
          have committed := setTree_preserves_at state id allocation changed sized rawFound changedWidth
          cases guarded : settings.protection.yes with
          | false => exact committed
          | true =>
              exact TreeMemoryDomain.wellSized_with_frame (TreeFactoredMemory.setTree state id changed)
                ((TreeFactoredMemory.setTree state id changed).currentFrame ++ [(id, path)]) committed

/-- Raw equality has no admission; the structural-domain implication retains
all outcomes. No bad or unsupported residual is replaced by its input state. -/
theorem reborrow_raw_and_domain (state : State) (pointer : Pointer) (settings : TreeMemory.Settings) :
    Preserves state (TreeFactoredMemory.reborrow state pointer settings) := by
  unfold TreeFactoredMemory.reborrow
  cases checked : MiniRustReference.checkPtr state.raw pointer.basic settings.inside.length with
  | ub fault => exact ⟨rfl, fun sized => sized⟩
  | unsupported => exact ⟨rfl, fun sized => sized⟩
  | noChoice => exact ⟨rfl, fun sized => sized⟩
  | ok span =>
      simp only
      cases provenance : pointer.provenance with
      | none => exact ⟨rfl, fun sized => sized⟩
      | some origin =>
          rcases origin with ⟨id, parent⟩
          simp only
          cases rawFound : state.raw.allocations id with
          | none => exact ⟨rfl, fun sized => sized⟩
          | some allocation =>
              cases treeFound : state.trees id with
              | none => exact ⟨rfl, fun sized => sized⟩
              | some tree =>
                  simp only
                  by_cases below : pointer.addr < allocation.base
                  · simp only [below, ↓reduceIte]
                    exact ⟨rfl, fun sized => sized⟩
                  · simp only [below, ↓reduceIte]
                    by_cases beyond : allocation.size <
                        pointer.addr - allocation.base + settings.inside.length
                    · simp only [beyond, ↓reduceIte]
                      exact ⟨rfl, fun sized => sized⟩
                    · simp only [beyond, ↓reduceIte]
                      let offset := pointer.addr - allocation.base
                      let permissions := TreeFactoredMemory.reborrowPermissions allocation.size offset settings
                      have within : offset + settings.inside.length ≤ allocation.size := by
                        dsimp only [offset]
                        omega
                      have childUniform := TreeFactoredReborrow.assembled_child_uniform
                        allocation.size offset settings within
                      by_cases accepted : permissions.all
                          (fun permission => permission.matchesProtector settings.protection) = true
                      · have matching := accepted
                        simp only [permissions, offset] at matching
                        simp only [matching, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                        refine ⟨?_, ?_⟩
                        · exact treePhase_raw state pointer settings id parent tree permissions offset
                        · intro sized
                          exact treePhase_preserves state pointer settings id parent tree permissions offset
                            allocation sized rawFound treeFound childUniform
                      · have matching : permissions.all
                            (fun permission => permission.matchesProtector settings.protection) = false := by
                          cases result : permissions.all
                              (fun permission => permission.matchesProtector settings.protection) with
                          | false => rfl
                          | true => exact False.elim (accepted result)
                        simp only [permissions, offset] at matching
                        simp only [matching, Bool.not_false, ↓reduceIte]
                        exact ⟨rfl, fun sized => sized⟩

theorem reborrow_preserves (state : State) (pointer : Pointer) (settings : TreeMemory.Settings)
    (sized : TreeFactoredMemory.WellSized state) :
    TreeMemoryDomain.ResultWellSized (TreeFactoredMemory.reborrow state pointer settings) :=
  (reborrow_raw_and_domain state pointer settings).2 sized

theorem reborrow_raw (state : State) (pointer : Pointer) (settings : TreeMemory.Settings) :
    (TreeFactoredMemory.reborrow state pointer settings).residual.raw = state.raw :=
  (reborrow_raw_and_domain state pointer settings).1

#print axioms setTree_preserves_at
#print axioms treePhase_raw
#print axioms treePhase_preserves
#print axioms reborrow_raw_and_domain
#print axioms reborrow_preserves
#print axioms reborrow_raw

end AnnealResearch.TreeReborrowDomain
