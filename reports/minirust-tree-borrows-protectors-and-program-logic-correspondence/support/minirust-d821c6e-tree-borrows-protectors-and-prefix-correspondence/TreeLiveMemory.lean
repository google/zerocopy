import AnnealResearch.TreeLiveKinds

/-!
All-residual LiveKinds preservation for the unchanged recursive-reference
load/store/deallocate wrappers. Only LiveKinds input is assumed. Actual raw
successes derive NoNewLive; actual tree successes use exact matching equality;
the existing copied-trial error branches retain the original wrapper state.

The residual observer covers ok, UB, unsupported and noChoice explicitly.
No StateWF, valid path, liveness, correct free operand, byte validity, successful
access, width or NoUB admission is added. Release remains a separate boundary:
its known terminal conversion mismatch refutes all-residual preservation.
-/

namespace AnnealResearch.TreeLiveMemory

open TreePermissions
open TreeMemory (State Pointer Path Tree)
open TreeLiveKinds (LiveKinds NoNewLive)

def residual : TreeMemory.Result A → State
  | .ok _ state => state
  | .ub _ state => state
  | .unsupported _ state => state
  | .noChoice state => state

def ResultLiveKinds (answer : TreeMemory.Result A) : Prop := LiveKinds (residual answer)

/-- Actual hook lookup supplies the stored tree at its pointer-derived ID.
No independent path/ID or permission premise is supplied by the caller. -/
theorem hookTarget_tree (state : State) (pointer : Pointer) (id : Nat) (path : Path)
    (tree : Tree) (target : TreeMemory.hookTarget state pointer = some (id, path, tree)) :
    state.trees id = some tree := by
  cases provenance : pointer.provenance with
  | none => simp [TreeMemory.hookTarget, provenance] at target
  | some origin =>
    rcases origin with ⟨originId, originPath⟩
    cases treeFound : state.trees originId with
    | none => simp [TreeMemory.hookTarget, provenance, treeFound] at target
    | some originTree =>
      have expanded : some (originId, originPath, originTree) = some (id, path, tree) := by
        simpa only [TreeMemory.hookTarget, provenance, treeFound, Option.map_some] using target
      have tupleEq := Option.some.inj expanded
      have sameId : originId = id := congrArg Prod.fst tupleEq
      have sameTree : originTree = tree :=
        congrArg (fun triple : Nat × Path × Tree => triple.2.2) tupleEq
      subst id
      subst tree
      first | rfl | exact treeFound

/-- Proof of the existing successful-commit/error-rollback alternatives, not
another hook runner. Every scalar UB and structural failure is retained. -/
theorem access_commit_preserves (state : State) (id : Nat) (path : Path) (tree : Tree)
    (raw : MiniRustReference.State) (value : A) (kind : AccessKind) (offset size : Nat)
    (matching : LiveKinds state) (present : state.trees id = some tree)
    (noNew : NoNewLive state.raw raw) :
    ResultLiveKinds
      (match TreeReference.access tree (some path) kind offset size with
      | .ok () changed => TreeMemory.Result.ok value { TreeMemory.setTree state id changed with raw }
      | .ub fault _ => .ub (.tree fault) state
      | .unsupported reason _ => .unsupported (.tree reason) state) := by
  have query := TreeKindAccess.access_matching tree (some path) kind offset size
  unfold ResultLiveKinds
  cases acted : TreeReference.access tree (some path) kind offset size with
  | ok result changed =>
    cases result
    dsimp only [residual]
    have preserved : TreeReference.kindsMatch changed = TreeReference.kindsMatch tree := by
      simpa only [acted, TreeReference.Result.state] using query
    exact TreeLiveKinds.liveKinds_commit state id tree changed raw matching present preserved noNew
  | ub fault changed => exact matching
  | unsupported reason changed => exact matching

theorem load_preserves (state : State) (pointer : Pointer) (size align : Nat)
    (matching : LiveKinds state) : ResultLiveKinds (TreeMemory.load state pointer size align) := by
  unfold ResultLiveKinds TreeMemory.load
  cases loaded : MiniRustReference.load state.raw pointer.basic size align with
  | ub fault => exact matching
  | unsupported => exact matching
  | noChoice => exact matching
  | ok proposed =>
    rcases proposed with ⟨bytes, raw⟩
    have noNew := TreeLiveKinds.load_noNewLive loaded
    by_cases zero : size = 0
    · simp only [ite_eq_left zero, residual]
      exact TreeLiveKinds.liveKinds_with_raw state raw matching noNew
    · simp only [ite_eq_right zero]
      cases checked : MiniRustReference.checkPtr state.raw pointer.basic size with
      | ub fault => exact matching
      | unsupported => exact matching
      | noChoice => exact matching
      | ok maybeSpan =>
        cases maybeSpan with
        | none => exact matching
        | some span =>
          cases target : TreeMemory.hookTarget state pointer with
          | none => exact matching
          | some selected =>
            rcases selected with ⟨id, path, tree⟩
            dsimp only
            have present := hookTarget_tree state pointer id path tree target
            exact access_commit_preserves state id path tree raw bytes .read span.offset size
              matching present noNew

theorem store_preserves (state : State) (pointer : Pointer) (bytes : List MiniRustReference.Byte)
    (align : Nat) (matching : LiveKinds state) :
    ResultLiveKinds (TreeMemory.store state pointer bytes align) := by
  unfold ResultLiveKinds TreeMemory.store
  cases proposed : MiniRustReference.store state.raw pointer.basic bytes align with
  | ub fault => exact matching
  | unsupported => exact matching
  | noChoice => exact matching
  | ok raw =>
    have noNew := TreeLiveKinds.store_noNewLive proposed
    by_cases zero : bytes.length = 0
    · simp only [ite_eq_left zero, residual]
      exact TreeLiveKinds.liveKinds_with_raw state raw matching noNew
    · simp only [ite_eq_right zero]
      cases checked : MiniRustReference.checkPtr state.raw pointer.basic bytes.length with
      | ub fault => exact matching
      | unsupported => exact matching
      | noChoice => exact matching
      | ok maybeSpan =>
        cases maybeSpan with
        | none => exact matching
        | some span =>
          cases target : TreeMemory.hookTarget state pointer with
          | none => exact matching
          | some selected =>
            rcases selected with ⟨id, path, tree⟩
            dsimp only
            have present := hookTarget_tree state pointer id path tree target
            exact access_commit_preserves state id path tree raw () .write span.offset bytes.length
              matching present noNew

theorem deallocate_preserves (state : State) (pointer : Pointer) (kind : MiniRustReference.Kind)
    (size align : Nat) (matching : LiveKinds state) :
    ResultLiveKinds (TreeMemory.deallocate state pointer kind size align) := by
  unfold ResultLiveKinds TreeMemory.deallocate TreeMemory.freeWith
  cases freed : MiniRustReference.free state.raw pointer.basic kind size align with
  | ub fault => exact matching
  | unsupported => exact matching
  | noChoice => exact matching
  | ok raw =>
    have noNew := TreeLiveKinds.free_noNewLive freed
    cases target : TreeMemory.hookTarget state pointer with
    | none => exact matching
    | some selected =>
      rcases selected with ⟨id, path, tree⟩
      dsimp only
      have present := hookTarget_tree state pointer id path tree target
      have query := TreeKindAccess.access_matching tree (some path) .write 0 size
      cases acted : TreeReference.access tree (some path) .write 0 size with
      | ub fault changed => exact matching
      | unsupported reason changed => exact matching
      | ok result changed =>
        cases result
        dsimp only
        have preserved : TreeReference.kindsMatch changed = TreeReference.kindsMatch tree := by
          simpa only [acted, TreeReference.Result.state] using query
        cases TreeReference.containsStrong changed with
        | false =>
          exact TreeLiveKinds.liveKinds_commit state id tree changed raw matching present preserved noNew
        | true => exact matching

#print axioms residual
#print axioms hookTarget_tree
#print axioms access_commit_preserves
#print axioms load_preserves
#print axioms store_preserves
#print axioms deallocate_preserves

end AnnealResearch.TreeLiveMemory
