import AnnealResearch.TreeFactoredMemory

/-!
Memory-composition agreement, staged through actual precheck consequences.
The raw MiniRustReference kernel and commit skeleton are shared explicitly;
the factored tree operations execute their independent validated runners.
No raw state/liveness/free-metadata/scalar-success/NoUB admission is added to
TreeFactoredMemory.WellSized. Missing extra trees remain owned unsupported.
-/

namespace AnnealResearch.TreeMemoryAgreement

open TreeFactoredMemory (State Pointer Path Tree)

theorem hookTarget_reify (state : State) (pointer : Pointer) :
    TreeMemory.hookTarget (TreeFactoredMemory.reify state) pointer =
      (TreeFactoredMemory.hookTarget state pointer).map
        (fun target => (target.1, target.2.1, TreeCorrespondence.reify target.2.2)) := by
  cases provenance : pointer.provenance with
  | none =>
    simp [TreeMemory.hookTarget, TreeFactoredMemory.hookTarget, provenance]
  | some origin =>
    rcases origin with ⟨id, path⟩
    cases treeFound : state.trees id <;>
      simp [TreeMemory.hookTarget, TreeFactoredMemory.hookTarget, TreeFactoredMemory.reify,
        provenance, treeFound]

/-- The hook's allocation ID/path comes from the actual pointer provenance,
and its extra tree is the entry at that ID, rather than an independent key. -/
theorem hookTarget_fields (state : State) (pointer : Pointer) (id : Nat) (path : Path)
    (tree : Tree)
    (target : TreeFactoredMemory.hookTarget state pointer = some (id, path, tree)) :
    pointer.provenance = some (id, path) ∧ state.trees id = some tree := by
  cases provenance : pointer.provenance with
  | none => simp [TreeFactoredMemory.hookTarget, provenance] at target
  | some origin =>
    rcases origin with ⟨originId, originPath⟩
    cases treeFound : state.trees originId with
    | none => simp [TreeFactoredMemory.hookTarget, provenance, treeFound] at target
    | some originTree =>
      have expanded : some (originId, originPath, originTree) = some (id, path, tree) := by
        simpa only [TreeFactoredMemory.hookTarget, provenance, treeFound, Option.map_some] using target
      have tupleEq := Option.some.inj expanded
      have sameId : originId = id := congrArg Prod.fst tupleEq
      have samePath : originPath = path :=
        congrArg (fun triple : Nat × Path × Tree => triple.2.1) tupleEq
      have sameTree : originTree = tree :=
        congrArg (fun triple : Nat × Path × Tree => triple.2.2) tupleEq
      subst id
      subst path
      subst tree
      exact ⟨rfl, by first | rfl | exact treeFound⟩

/-- Allocation presence is derived from an actual successful nonempty span
result, including the zero-length-first rule; it is not a caller premise. -/
theorem checkPtr_ok_allocation_at (raw : MiniRustReference.State)
    (pointer : MiniRustReference.Ptr) (id size : Nat) (span : MiniRustReference.CheckedSpan)
    (provenance : pointer.provenance = some id)
    (checked : MiniRustReference.checkPtr raw pointer size = .ok (some span)) :
    ∃ allocation, raw.allocations id = some allocation := by
  by_cases zero : size = 0
  · simp [MiniRustReference.checkPtr, zero] at checked
  · cases found : raw.allocations id with
    | none => simp [MiniRustReference.checkPtr, zero, provenance, found] at checked
    | some allocation => exact ⟨allocation, rfl⟩

/-- Free's actual success branch implies a present record at the provenance ID.
No liveness, kind, base, size or alignment condition is assumed in advance. -/
theorem free_ok_allocation_at (raw : MiniRustReference.State) (pointer : MiniRustReference.Ptr)
    (id : Nat) (kind : MiniRustReference.Kind) (size align : Nat)
    (proposed : MiniRustReference.State) (provenance : pointer.provenance = some id)
    (freed : MiniRustReference.free raw pointer kind size align = .ok proposed) :
    ∃ allocation, raw.allocations id = some allocation := by
  cases found : raw.allocations id with
  | none => simp [MiniRustReference.free, provenance, found] at freed
  | some allocation => exact ⟨allocation, rfl⟩

theorem checked_hook_uniform (state : State) (pointer : Pointer) (size : Nat)
    (span : MiniRustReference.CheckedSpan) (id : Nat) (path : Path) (tree : Tree)
    (sized : TreeFactoredMemory.WellSized state)
    (checked : MiniRustReference.checkPtr state.raw pointer.basic size = .ok (some span))
    (target : TreeFactoredMemory.hookTarget state pointer = some (id, path, tree)) :
    ∃ allocation, state.raw.allocations id = some allocation ∧
      TreeFactored.arrayLengthsTree tree.topology [] tree.store allocation.size = true := by
  have fields := hookTarget_fields state pointer id path tree target
  have basicProvenance : pointer.basic.provenance = some id := by
    simp [TreeMemory.Pointer.basic, fields.1]
  obtain ⟨allocation, found⟩ :=
    checkPtr_ok_allocation_at state.raw pointer.basic id size span basicProvenance checked
  exact ⟨allocation, found, sized id allocation tree found fields.2⟩

theorem freed_hook_uniform (state : State) (pointer : Pointer) (kind : MiniRustReference.Kind)
    (size align : Nat) (proposed : MiniRustReference.State) (id : Nat) (path : Path) (tree : Tree)
    (sized : TreeFactoredMemory.WellSized state)
    (freed : MiniRustReference.free state.raw pointer.basic kind size align = .ok proposed)
    (target : TreeFactoredMemory.hookTarget state pointer = some (id, path, tree)) :
    ∃ allocation, state.raw.allocations id = some allocation ∧
      TreeFactored.arrayLengthsTree tree.topology [] tree.store allocation.size = true := by
  have fields := hookTarget_fields state pointer id path tree target
  have basicProvenance : pointer.basic.provenance = some id := by
    simp [TreeMemory.Pointer.basic, fields.1]
  obtain ⟨allocation, found⟩ :=
    free_ok_allocation_at state.raw pointer.basic id kind size align proposed basicProvenance freed
  exact ⟨allocation, found, sized id allocation tree found fields.2⟩

theorem reify_commit (state : State) (id : Nat) (tree : Tree) (raw : MiniRustReference.State) :
    TreeFactoredMemory.reify { TreeFactoredMemory.setTree state id tree with raw } =
      { TreeMemory.setTree (TreeFactoredMemory.reify state) id (TreeCorrespondence.reify tree)
        with raw } := by
  rw [TreeFactoredMemory.reify_with_raw, TreeFactoredMemory.reify_setTree]

#print axioms hookTarget_reify
#print axioms hookTarget_fields
#print axioms checkPtr_ok_allocation_at
#print axioms free_ok_allocation_at
#print axioms checked_hook_uniform
#print axioms freed_hook_uniform
#print axioms reify_commit

end AnnealResearch.TreeMemoryAgreement
