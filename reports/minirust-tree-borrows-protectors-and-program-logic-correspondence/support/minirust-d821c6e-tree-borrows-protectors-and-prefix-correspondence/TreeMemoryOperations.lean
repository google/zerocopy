import AnnealResearch.TreeMemoryAgreement

/-!
Actual raw-load/store/free composition with the independent factored tree
runner. Only WellSized is an input-domain premise. Raw kernels and the memory
commit skeleton are shared openly; tree agreement is supplied by the checked
independent-operation bridge. All result categories and full reified residual
states are retained, including rollback after scalar or Strong-guard UB.
-/

namespace AnnealResearch.TreeMemoryOperations

open TreePermissions
open TreeFactoredMemory (State Pointer Path Tree)

private theorem reify_raw (state : State) :
    (TreeFactoredMemory.reify state).raw = state.raw := rfl

/-- Generic theorem about the existing hook-result commit cases, not another
operation runner. Failed tree trials are discarded by both public wrappers. -/
theorem access_commit_agrees (state : State) (id : Nat) (path : Path) (tree : Tree)
    (raw : MiniRustReference.State) (value : A) (kind : AccessKind) (offset size width : Nat)
    (uniform : TreeFactored.arrayLengthsTree tree.topology [] tree.store width = true) :
    (match TreeReference.access (TreeCorrespondence.reify tree) (some path) kind offset size with
    | .ok () changed => TreeMemory.Result.ok value
        { TreeMemory.setTree (TreeFactoredMemory.reify state) id changed with raw }
    | .ub fault _ => .ub (.tree fault) (TreeFactoredMemory.reify state)
    | .unsupported reason _ => .unsupported (.tree reason) (TreeFactoredMemory.reify state)) =
      TreeFactoredMemory.translate
        (match TreeFactored.access tree path kind offset size with
        | .ok () changed => .ok value { TreeFactoredMemory.setTree state id changed with raw }
        | .ub fault _ => .ub (.tree fault) state
        | .unsupported reason _ => .unsupported
            (.tree (TreeCorrespondence.structuralToReference reason)) state) := by
  rw [TreeValidated.access_agrees tree path kind offset size width uniform]
  cases answer : TreeFactored.access tree path kind offset size with
  | ok result changed =>
    cases result
    simp only [TreeAgreement.translate, TreeFactoredMemory.translate]
    rw [TreeMemoryAgreement.reify_commit]
  | ub fault changed => rfl
  | unsupported reason changed => rfl

/-- The full recursive Strong query participates after actual successful tree
Write; no absence-of-Strong premise is imposed, and rejection rolls back. -/
theorem deallocate_commit_agrees (state : State) (id : Nat) (path : Path) (tree : Tree)
    (raw : MiniRustReference.State) (size width : Nat)
    (uniform : TreeFactored.arrayLengthsTree tree.topology [] tree.store width = true) :
    (match TreeReference.access (TreeCorrespondence.reify tree) (some path) .write 0 size with
    | .ok () changed =>
      if TreeReference.containsStrong changed then
        TreeMemory.Result.ub .strongProtector (TreeFactoredMemory.reify state)
      else .ok () { TreeMemory.setTree (TreeFactoredMemory.reify state) id changed with raw }
    | .ub fault _ => .ub (.tree fault) (TreeFactoredMemory.reify state)
    | .unsupported reason _ => .unsupported (.tree reason) (TreeFactoredMemory.reify state)) =
      TreeFactoredMemory.translate
        (match TreeFactored.access tree path .write 0 size with
        | .ok () changed =>
          if TreeFactored.containsStrong changed then .ub .strongProtector state
          else .ok () { TreeFactoredMemory.setTree state id changed with raw }
        | .ub fault _ => .ub (.tree fault) state
        | .unsupported reason _ => .unsupported
            (.tree (TreeCorrespondence.structuralToReference reason)) state) := by
  rw [TreeValidated.access_agrees tree path .write 0 size width uniform]
  cases answer : TreeFactored.access tree path .write 0 size with
  | ok result changed =>
    cases result
    simp only [TreeAgreement.translate]
    rw [TreeQueries.containsStrong_reify]
    cases blocked : TreeFactored.containsStrong changed with
    | false =>
      change TreeMemory.Result.ok ()
        { TreeMemory.setTree (TreeFactoredMemory.reify state) id (TreeCorrespondence.reify changed)
          with raw } =
        TreeMemory.Result.ok ()
          (TreeFactoredMemory.reify { TreeFactoredMemory.setTree state id changed with raw })
      rw [TreeMemoryAgreement.reify_commit]
    | true => rfl
  | ub fault changed => rfl
  | unsupported reason changed => rfl

theorem load_agrees (state : State) (pointer : Pointer) (size align : Nat)
    (sized : TreeFactoredMemory.WellSized state) :
    TreeMemory.load (TreeFactoredMemory.reify state) pointer size align =
      TreeFactoredMemory.translate (TreeFactoredMemory.load state pointer size align) := by
  unfold TreeMemory.load TreeFactoredMemory.load
  simp only [reify_raw]
  cases loaded : MiniRustReference.load state.raw pointer.basic size align with
  | ub fault => rfl
  | unsupported => rfl
  | noChoice => rfl
  | ok proposed =>
    rcases proposed with ⟨bytes, raw⟩
    by_cases zero : size = 0
    · simp only [ite_eq_left zero, TreeFactoredMemory.translate]
      rw [TreeFactoredMemory.reify_with_raw]
      rfl
    · simp only [ite_eq_right zero]
      cases checked : MiniRustReference.checkPtr state.raw pointer.basic size with
      | ub fault => rfl
      | unsupported => rfl
      | noChoice => rfl
      | ok maybeSpan =>
        cases maybeSpan with
        | none => rfl
        | some span =>
          rw [TreeMemoryAgreement.hookTarget_reify]
          cases target : TreeFactoredMemory.hookTarget state pointer with
          | none => rfl
          | some selected =>
            rcases selected with ⟨id, path, tree⟩
            obtain ⟨allocation, _, uniform⟩ :=
              TreeMemoryAgreement.checked_hook_uniform state pointer size span id path tree
                sized checked target
            exact access_commit_agrees state id path tree raw bytes .read span.offset size
              allocation.size uniform

theorem store_agrees (state : State) (pointer : Pointer) (bytes : List MiniRustReference.Byte)
    (align : Nat) (sized : TreeFactoredMemory.WellSized state) :
    TreeMemory.store (TreeFactoredMemory.reify state) pointer bytes align =
      TreeFactoredMemory.translate (TreeFactoredMemory.store state pointer bytes align) := by
  unfold TreeMemory.store TreeFactoredMemory.store
  simp only [reify_raw]
  cases proposed : MiniRustReference.store state.raw pointer.basic bytes align with
  | ub fault => rfl
  | unsupported => rfl
  | noChoice => rfl
  | ok raw =>
    by_cases zero : bytes.length = 0
    · simp only [ite_eq_left zero, TreeFactoredMemory.translate]
      rw [TreeFactoredMemory.reify_with_raw]
      rfl
    · simp only [ite_eq_right zero]
      cases checked : MiniRustReference.checkPtr state.raw pointer.basic bytes.length with
      | ub fault => rfl
      | unsupported => rfl
      | noChoice => rfl
      | ok maybeSpan =>
        cases maybeSpan with
        | none => rfl
        | some span =>
          rw [TreeMemoryAgreement.hookTarget_reify]
          cases target : TreeFactoredMemory.hookTarget state pointer with
          | none => rfl
          | some selected =>
            rcases selected with ⟨id, path, tree⟩
            obtain ⟨allocation, _, uniform⟩ :=
              TreeMemoryAgreement.checked_hook_uniform state pointer bytes.length span id path tree
                sized checked target
            exact access_commit_agrees state id path tree raw () .write span.offset bytes.length
              allocation.size uniform

theorem deallocate_agrees (state : State) (pointer : Pointer) (kind : MiniRustReference.Kind)
    (size align : Nat) (sized : TreeFactoredMemory.WellSized state) :
    TreeMemory.deallocate (TreeFactoredMemory.reify state) pointer kind size align =
      TreeFactoredMemory.translate
        (TreeFactoredMemory.deallocate state pointer kind size align) := by
  unfold TreeMemory.deallocate TreeMemory.freeWith TreeFactoredMemory.deallocate
  simp only [reify_raw]
  cases freed : MiniRustReference.free state.raw pointer.basic kind size align with
  | ub fault => rfl
  | unsupported => rfl
  | noChoice => rfl
  | ok raw =>
    rw [TreeMemoryAgreement.hookTarget_reify]
    cases target : TreeFactoredMemory.hookTarget state pointer with
    | none => rfl
    | some selected =>
      rcases selected with ⟨id, path, tree⟩
      obtain ⟨allocation, _, uniform⟩ :=
        TreeMemoryAgreement.freed_hook_uniform state pointer kind size align raw id path tree
          sized freed target
      exact deallocate_commit_agrees state id path tree raw size allocation.size uniform

#print axioms access_commit_agrees
#print axioms deallocate_commit_agrees
#print axioms load_agrees
#print axioms store_agrees
#print axioms deallocate_agrees

end AnnealResearch.TreeMemoryOperations
