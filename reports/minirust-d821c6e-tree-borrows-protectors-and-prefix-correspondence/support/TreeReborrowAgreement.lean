import AnnealResearch.TreeFactoredReborrow

/-!
Exact actual memory-reborrow correspondence under only input WellSized.
Shared raw checks, supplied settings and commit skeleton are explicit. Actual
tree execution uses the independent F insertion and initial-access runners,
with their checked equations and all-outcome width preservation.

The proof follows executed geometry/settings branches internally. It retains
missing records/paths, raw and tree errors, partial changed trees, unchanged raw
memory and the exact frame append order. No settings compatibility, valid path,
permission success, NoUB or history premise is added to the public theorem.
The four-command prefix observer, frame consumption and Rust/source-helper
adequacy remain separate.
-/

namespace AnnealResearch.TreeReborrowAgreement

open TreePermissions
open TreeFactoredMemory (State Pointer Tree)

private theorem reify_raw (state : State) :
    (TreeFactoredMemory.reify state).raw = state.raw := rfl

private theorem reify_trees (state : State) (id : Nat) :
    (TreeFactoredMemory.reify state).trees id =
      (state.trees id).map TreeCorrespondence.reify := rfl

/-- A result/commit equation for the actual post-settings tree phase. Width
premises are local facts derived inside the public wrapper proof below. -/
theorem tree_phase_agrees (state : State) (pointer : Pointer) (settings : TreeMemory.Settings)
    (id : Nat) (parent : TreeFactored.Path) (tree : Tree) (permissions : List Permission)
    (offset width : Nat)
    (uniform : TreeFactored.arrayLengthsTree tree.topology [] tree.store width = true)
    (childUniform : TreeFactored.arrayLengthsTree
      (TreeFactoredMemory.reborrowChild permissions settings.protection).topology []
      (TreeFactoredMemory.reborrowChild permissions settings.protection).store width = true) :
    (match TreeReference.addNode (TreeCorrespondence.reify tree) parent
        (TreeCorrespondence.reify (TreeFactoredMemory.reborrowChild permissions settings.protection)) with
    | .ub fault changed => TreeMemory.Result.ub (.tree fault)
        (TreeMemory.setTree (TreeFactoredMemory.reify state) id changed)
    | .unsupported reason changed => .unsupported (.tree reason)
        (TreeMemory.setTree (TreeFactoredMemory.reify state) id changed)
    | .ok path added =>
      match TreeReference.initialAccesses added path offset settings.inside with
      | .ub fault changed => .ub (.tree fault)
          (TreeMemory.setTree (TreeFactoredMemory.reify state) id changed)
      | .unsupported reason changed => .unsupported (.tree reason)
          (TreeMemory.setTree (TreeFactoredMemory.reify state) id changed)
      | .ok () changed =>
        let updated := TreeMemory.setTree (TreeFactoredMemory.reify state) id changed
        let registered := if settings.protection.yes then
          { updated with currentFrame := updated.currentFrame ++ [(id, path)] } else updated
        .ok { pointer with provenance := some (id, path) } registered) =
      TreeFactoredMemory.translate
        (match TreeFactored.addNode tree parent
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
            .ok { pointer with provenance := some (id, path) } registered) := by
  rw [TreeInsertionAgreement.addNode_agrees tree
    (TreeFactoredMemory.reborrowChild permissions settings.protection) parent width uniform childUniform]
  cases inserted : TreeFactored.addNode tree parent
      (TreeFactoredMemory.reborrowChild permissions settings.protection) with
  | ub fault changed =>
      simp only [TreeAgreement.translate, TreeFactoredMemory.translate,
        TreeFactoredMemory.reify_setTree]
  | unsupported reason changed =>
      simp only [TreeAgreement.translate, TreeFactoredMemory.translate,
        TreeFactoredMemory.reify_setTree]
  | ok path added =>
      have addedUniform := TreeInsertionWidths.addNode_success_uniform tree
        (TreeFactoredMemory.reborrowChild permissions settings.protection) added
        parent path width uniform childUniform inserted
      simp only [TreeAgreement.translate]
      rw [TreeInitialAgreement.initialAccesses_agrees added path offset settings.inside width addedUniform]
      cases initial : TreeFactored.initialAccesses added path offset settings.inside with
      | ub fault changed =>
          simp only [TreeAgreement.translate, TreeFactoredMemory.translate,
            TreeFactoredMemory.reify_setTree]
      | unsupported reason changed =>
          simp only [TreeAgreement.translate, TreeFactoredMemory.translate,
            TreeFactoredMemory.reify_setTree]
      | ok value changed =>
          cases value
          simp only [TreeAgreement.translate]
          cases guarded : settings.protection.yes <;>
            simp only [Bool.false_eq_true, ↓reduceIte, TreeFactoredMemory.translate,
              TreeFactoredMemory.reify_with_frame, TreeFactoredMemory.reify_setTree] <;> rfl

/-- Sole input admission is the existing allocation-sized array domain.
Operands/settings and parent paths are arbitrary, including owned rejection
cases and all partial ordinary errors. Full raw/tree/frame states are compared. -/
theorem reborrow_agrees (state : State) (pointer : Pointer) (settings : TreeMemory.Settings)
    (sized : TreeFactoredMemory.WellSized state) :
    TreeMemory.reborrow (TreeFactoredMemory.reify state) pointer settings =
      TreeFactoredMemory.translate (TreeFactoredMemory.reborrow state pointer settings) := by
  unfold TreeMemory.reborrow TreeFactoredMemory.reborrow
  simp only [reify_raw]
  cases checked : MiniRustReference.checkPtr state.raw pointer.basic settings.inside.length with
  | ub fault => rfl
  | unsupported => rfl
  | noChoice => rfl
  | ok span =>
      cases provenance : pointer.provenance with
      | none => rfl
      | some origin =>
          rcases origin with ⟨id, parent⟩
          cases allocationFound : state.raw.allocations id with
          | none => simp only [allocationFound, TreeFactoredMemory.translate]
          | some allocation =>
              cases treeFound : state.trees id with
              | none =>
                  simp only [allocationFound, reify_trees, treeFound, Option.map_none,
                    TreeFactoredMemory.translate]
              | some tree =>
                  have uniform := sized id allocation tree allocationFound treeFound
                  simp only [allocationFound, reify_trees, treeFound, Option.map_some]
                  by_cases below : pointer.addr < allocation.base
                  · simp only [below, ↓reduceIte, TreeFactoredMemory.translate]
                  · simp only [below, ↓reduceIte]
                    by_cases beyond : allocation.size <
                        pointer.addr - allocation.base + settings.inside.length
                    · simp only [beyond, ↓reduceIte, TreeFactoredMemory.translate]
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
                        simp only [permissions, offset, TreeFactoredMemory.reborrowPermissions] at matching
                        simp only [TreeFactoredMemory.reborrowPermissions, matching, Bool.not_true,
                          Bool.false_eq_true, ↓reduceIte]
                        rw [← TreeFactoredReborrow.child_reify]
                        exact tree_phase_agrees state pointer settings id parent tree permissions offset
                          allocation.size uniform childUniform
                      · have matching : permissions.all
                            (fun permission => permission.matchesProtector settings.protection) = false := by
                          cases result : permissions.all
                              (fun permission => permission.matchesProtector settings.protection) with
                          | false => rfl
                          | true => exact False.elim (accepted result)
                        simp only [permissions, offset, TreeFactoredMemory.reborrowPermissions] at matching
                        simp only [TreeFactoredMemory.reborrowPermissions, matching, Bool.not_false,
                          ↓reduceIte, TreeFactoredMemory.translate]

theorem related_reborrow (reference : TreeMemory.State) (state : State) (pointer : Pointer)
    (settings : TreeMemory.Settings) (related : TreeFactoredMemory.Related reference state)
    (sized : TreeFactoredMemory.WellSized state) :
    TreeMemory.reborrow reference pointer settings =
      TreeFactoredMemory.translate (TreeFactoredMemory.reborrow state pointer settings) := by
  rw [related]
  exact reborrow_agrees state pointer settings sized

#print axioms tree_phase_agrees
#print axioms reborrow_agrees
#print axioms related_reborrow

end AnnealResearch.TreeReborrowAgreement
