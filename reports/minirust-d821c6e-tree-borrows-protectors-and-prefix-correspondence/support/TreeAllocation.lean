import AnnealResearch.TreeFactoredMemory
import AnnealResearch.TreeQueries

/-!
Selected allocation birth over the unchanged shared MiniRustReference allocator.
R and F construct allocation-sized Unprot.Unique / No / leaf roots directly.
Both convert the actual raw returned pointer by adding the empty root path;
F never executes R or constructs a tree by reifying reference execution.

Only raw success installs a whole new optional tree at old raw.next and commits
the actual returned raw state. Every raw error/noChoice keeps the original
complete state, and allocation never changes the current frame. Branch agreement
is unconditional over owned maps and Nat operands. It is not source admission,
allocator fairness/progress, whole-Rust adequacy, or a choice-aware client proof.
-/

namespace AnnealResearch.TreeAllocation

open TreePermissions

def rootPermissions (size : Nat) : List Permission := List.replicate size (.unprot .unique)

def referenceRoot (size : Nat) : TreeReference.Node := .mk (rootPermissions size) .no []

/-- Direct factored leaf. Only [] is represented; other constant-store cells
are irrelevant to this topology and are not an absent-store admission. -/
def factoredRoot (size : Nat) : TreeFactored.State :=
  ⟨.node .nil, fun _ => ⟨rootPermissions size, .no⟩⟩

/-- Shared conversion of the actual raw pointer, not a fresh-ID assumption. -/
def rootPointer (pointer : MiniRustReference.Ptr) : TreeMemory.Pointer :=
  { addr := pointer.addr
    provenance := pointer.provenance.map fun id => (id, []) }

end AnnealResearch.TreeAllocation

namespace AnnealResearch.TreeMemory

/-- One actual raw candidate. Invalid candidates remain noChoice; allocation
UB/unsupported retain the whole input state. No new runtime guard is inserted. -/
def allocateAt (state : State) (kind : MiniRustReference.Kind) (size align address : Nat) :
    Result Pointer :=
  match MiniRustReference.allocateAt state.raw kind size align address with
  | .ub fault => .ub (.basic fault) state
  | .unsupported => .unsupported .basicRepresentation state
  | .noChoice => .noChoice state
  | .ok (pointer, raw) =>
    .ok (TreeAllocation.rootPointer pointer)
      { setTree state state.raw.next (TreeAllocation.referenceRoot size) with raw }

end AnnealResearch.TreeMemory

namespace AnnealResearch.TreeFactoredMemory

/-- Same raw allocator and request/pointer conversion, direct F tree birth.
Install the entire new leaf even if an old stray tree occupied the selected ID. -/
def allocateAt (state : State) (kind : MiniRustReference.Kind) (size align address : Nat) :
    Result Pointer :=
  match MiniRustReference.allocateAt state.raw kind size align address with
  | .ub fault => .ub (.basic fault) state
  | .unsupported => .unsupported .basicRepresentation state
  | .noChoice => .noChoice state
  | .ok (pointer, raw) =>
    .ok (TreeAllocation.rootPointer pointer)
      { setTree state state.raw.next (TreeAllocation.factoredRoot size) with raw }

end AnnealResearch.TreeFactoredMemory

namespace AnnealResearch.TreeAllocation

open TreePermissions

theorem rootPointer_basic (pointer : MiniRustReference.Ptr) :
    (rootPointer pointer).basic = pointer := by
  cases pointer with
  | mk address provenance => cases provenance <;> rfl

theorem rootPermissions_length (size : Nat) : (rootPermissions size).length = size := by
  simp only [rootPermissions, List.length_replicate]

theorem referenceRoot_matching (size : Nat) : TreeReference.kindsMatch (referenceRoot size) = true := by
  have permissionsMatch :
      (rootPermissions size).all (fun permission => permission.matchesProtector .no) = true := by
    induction size with
    | zero => rfl
    | succ size ih =>
      change (true && (rootPermissions size).all
        (fun permission => permission.matchesProtector .no)) = true
      exact ih
  simp only [referenceRoot, TreeReference.kindsMatch, TreeReference.childrenMatch,
    permissionsMatch, Bool.and_self]

theorem referenceRoot_width (size : Nat) :
    TreeReference.arraysSized (referenceRoot size) size = true := by
  simp [referenceRoot, rootPermissions, TreeReference.arraysSized, TreeReference.childrenSized]

theorem factoredRoot_reify (size : Nat) :
    TreeCorrespondence.reify (factoredRoot size) = referenceRoot size := by
  simp only [factoredRoot, referenceRoot, TreeCorrespondence.reify,
    TreeCorrespondence.reifyTree, TreeCorrespondence.reifyForest]

theorem factoredRoot_width (size : Nat) :
    TreeFactored.arrayLengthsTree (factoredRoot size).topology []
      (factoredRoot size).store size = true := by
  have query := TreeQueries.arraysSized_reify (factoredRoot size) size
  rw [factoredRoot_reify, referenceRoot_width] at query
  exact query.symm

theorem factoredRoot_matching (size : Nat) :
    TreeFactored.matchesProtectors (factoredRoot size) = true := by
  have query := TreeQueries.kindsMatch_reify (factoredRoot size)
  rw [factoredRoot_reify, referenceRoot_matching] at query
  exact query.symm

private theorem reify_raw (state : TreeFactoredMemory.State) :
    (TreeFactoredMemory.reify state).raw = state.raw := rfl

/-- Every branch and full residual agrees, without width, StateWF, candidate,
success, liveness, settings, permission or NoUB admission. The raw kernel and
pointer conversion are shared; root tree representations are direct R/F data. -/
theorem allocateAt_agrees (state : TreeFactoredMemory.State) (kind : MiniRustReference.Kind)
    (size align address : Nat) :
    TreeMemory.allocateAt (TreeFactoredMemory.reify state) kind size align address =
      TreeFactoredMemory.translate (TreeFactoredMemory.allocateAt state kind size align address) := by
  unfold TreeMemory.allocateAt TreeFactoredMemory.allocateAt
  simp only [reify_raw]
  cases chosen : MiniRustReference.allocateAt state.raw kind size align address with
  | ub fault => rfl
  | unsupported => rfl
  | noChoice => rfl
  | ok created =>
    rcases created with ⟨pointer, raw⟩
    simp only [TreeFactoredMemory.translate]
    have treeUpdate := TreeFactoredMemory.reify_setTree state state.raw.next (factoredRoot size)
    rw [factoredRoot_reify] at treeUpdate
    have rawUpdate := congrArg (fun before : TreeMemory.State => { before with raw }) treeUpdate
    exact congrArg (TreeMemory.Result.ok (rootPointer pointer)) rawUpdate.symm

/-- Actual raw result on every category. No success premise or raw-WF claim. -/
theorem reference_raw (state : TreeMemory.State) (kind : MiniRustReference.Kind)
    (size align address : Nat) :
    (match TreeMemory.allocateAt state kind size align address with
    | .ok _ changed | .ub _ changed | .unsupported _ changed | .noChoice changed => changed.raw) =
      (match MiniRustReference.allocateAt state.raw kind size align address with
      | .ok (_, raw) => raw
      | .ub _ | .unsupported | .noChoice => state.raw) := by
  unfold TreeMemory.allocateAt
  cases MiniRustReference.allocateAt state.raw kind size align address with
  | ok created => rcases created with ⟨pointer, raw⟩; rfl
  | ub fault => rfl
  | unsupported => rfl
  | noChoice => rfl

theorem factored_raw (state : TreeFactoredMemory.State) (kind : MiniRustReference.Kind)
    (size align address : Nat) :
    (match TreeFactoredMemory.allocateAt state kind size align address with
    | .ok _ changed | .ub _ changed | .unsupported _ changed | .noChoice changed => changed.raw) =
      (match MiniRustReference.allocateAt state.raw kind size align address with
      | .ok (_, raw) => raw
      | .ub _ | .unsupported | .noChoice => state.raw) := by
  unfold TreeFactoredMemory.allocateAt
  cases MiniRustReference.allocateAt state.raw kind size align address with
  | ok created => rcases created with ⟨pointer, raw⟩; rfl
  | ub fault => rfl
  | unsupported => rfl
  | noChoice => rfl

theorem reference_frame (state : TreeMemory.State) (kind : MiniRustReference.Kind)
    (size align address : Nat) :
    (match TreeMemory.allocateAt state kind size align address with
    | .ok _ changed | .ub _ changed | .unsupported _ changed | .noChoice changed =>
      changed.currentFrame) = state.currentFrame := by
  unfold TreeMemory.allocateAt
  cases MiniRustReference.allocateAt state.raw kind size align address with
  | ok created => rcases created with ⟨pointer, raw⟩; rfl
  | ub fault => rfl
  | unsupported => rfl
  | noChoice => rfl

theorem factored_frame (state : TreeFactoredMemory.State) (kind : MiniRustReference.Kind)
    (size align address : Nat) :
    (match TreeFactoredMemory.allocateAt state kind size align address with
    | .ok _ changed | .ub _ changed | .unsupported _ changed | .noChoice changed =>
      changed.currentFrame) = state.currentFrame := by
  unfold TreeFactoredMemory.allocateAt
  cases MiniRustReference.allocateAt state.raw kind size align address with
  | ok created => rcases created with ⟨pointer, raw⟩; rfl
  | ub fault => rfl
  | unsupported => rfl
  | noChoice => rfl

#print axioms rootPointer_basic
#print axioms rootPermissions_length
#print axioms referenceRoot_matching
#print axioms referenceRoot_width
#print axioms factoredRoot_reify
#print axioms factoredRoot_width
#print axioms factoredRoot_matching
#print axioms allocateAt_agrees
#print axioms reference_raw
#print axioms factored_raw
#print axioms reference_frame
#print axioms factored_frame

end AnnealResearch.TreeAllocation
