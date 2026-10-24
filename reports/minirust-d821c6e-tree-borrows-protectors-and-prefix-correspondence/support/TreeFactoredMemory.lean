import AnnealResearch.TreeMemory
import AnnealResearch.TreeValidated

/-!
Factored-tree version of the frozen TreeMemory commit skeleton. Raw prechecks
and payload operations are the SAME MiniRustReference functions; tree operations
execute TreeFactored's independent runners, never the reference through reify.
Fault/unsupported categories and pointer operands are shared explicitly.

This layer defines load/store/free/release, their full-state reifier and structural
array domain. Operation agreement is a separate proof, not a property inferred
from these definitions. Reborrow/exit, pointer-fragment paths and type/layout
settings are not added. The prior manual helper/source-adequacy limits remain.
-/
namespace AnnealResearch.TreeFactoredMemory

open TreePermissions

abbrev Pointer := TreeMemory.Pointer
abbrev Provenance := TreeMemory.Provenance
abbrev Path := TreeFactored.Path
abbrev Tree := TreeFactored.State
abbrev Fault := TreeMemory.Fault
abbrev Unsupported := TreeMemory.Unsupported

structure State where
  raw : MiniRustReference.State
  trees : Nat → Option Tree
  currentFrame : List Provenance

inductive Result (A : Type) where
  | ok (value : A) (state : State)
  | ub (fault : Fault) (state : State)
  | unsupported (reason : Unsupported) (state : State)
  | noChoice (state : State)

def reify (state : State) : TreeMemory.State :=
  { raw := state.raw
    trees := fun id => (state.trees id).map TreeCorrespondence.reify
    currentFrame := state.currentFrame }

def Related (reference : TreeMemory.State) (factored : State) : Prop :=
  reference = reify factored

/-- Uniform width is tied to actual allocation metadata, including dead records.
Paired absent trees remain allowed; no liveness, free-operand, permission-success,
constructor-kind, Strong-blocker, frame-flag or NoUB condition is asserted. -/
def WellSized (state : State) : Prop :=
  ∀ id allocation tree, state.raw.allocations id = some allocation →
    state.trees id = some tree →
    TreeFactored.arrayLengthsTree tree.topology [] tree.store allocation.size = true

def translate : Result A → TreeMemory.Result A
  | .ok value state => .ok value (reify state)
  | .ub fault state => .ub fault (reify state)
  | .unsupported reason state => .unsupported reason (reify state)
  | .noChoice state => .noChoice (reify state)

def setTree (state : State) (id : Nat) (tree : Tree) : State :=
  { state with trees := fun selected => if selected = id then some tree else state.trees selected }

def hookTarget (state : State) (pointer : Pointer) : Option (Nat × Path × Tree) :=
  match pointer.provenance with
  | none => none
  | some (id, path) => (state.trees id).map fun tree => (id, path, tree)

def load (state : State) (pointer : Pointer) (size align : Nat) :
    Result (List MiniRustReference.Byte) :=
  match MiniRustReference.load state.raw pointer.basic size align with
  | .ub fault => .ub (.basic fault) state
  | .unsupported => .unsupported .basicRepresentation state
  | .noChoice => .noChoice state
  | .ok (bytes, raw) =>
    if size = 0 then .ok bytes { state with raw }
    else match MiniRustReference.checkPtr state.raw pointer.basic size with
    | .ub fault => .ub (.basic fault) state
    | .unsupported => .unsupported .basicRepresentation state
    | .noChoice => .noChoice state
    | .ok none => .unsupported .basicRepresentation state
    | .ok (some span) =>
      match hookTarget state pointer with
      | none => .unsupported .missingTree state
      | some (id, path, tree) =>
        match TreeFactored.access tree path .read span.offset size with
        | .ok () changed => .ok bytes { setTree state id changed with raw }
        | .ub fault _ => .ub (.tree fault) state
        | .unsupported reason _ => .unsupported
            (.tree (TreeCorrespondence.structuralToReference reason)) state

def store (state : State) (pointer : Pointer)
    (bytes : List MiniRustReference.Byte) (align : Nat) : Result Unit :=
  match MiniRustReference.store state.raw pointer.basic bytes align with
  | .ub fault => .ub (.basic fault) state
  | .unsupported => .unsupported .basicRepresentation state
  | .noChoice => .noChoice state
  | .ok raw =>
    if bytes.length = 0 then .ok () { state with raw }
    else match MiniRustReference.checkPtr state.raw pointer.basic bytes.length with
    | .ub fault => .ub (.basic fault) state
    | .unsupported => .unsupported .basicRepresentation state
    | .noChoice => .noChoice state
    | .ok none => .unsupported .basicRepresentation state
    | .ok (some span) =>
      match hookTarget state pointer with
      | none => .unsupported .missingTree state
      | some (id, path, tree) =>
        match TreeFactored.access tree path .write span.offset bytes.length with
        | .ok () changed => .ok () { setTree state id changed with raw }
        | .ub fault _ => .ub (.tree fault) state
        | .unsupported reason _ => .unsupported
            (.tree (TreeCorrespondence.structuralToReference reason)) state

def deallocate (state : State) (pointer : Pointer) (kind : MiniRustReference.Kind)
    (size align : Nat) : Result Unit :=
  match MiniRustReference.free state.raw pointer.basic kind size align with
  | .ub fault => .ub (.basic fault) state
  | .unsupported => .unsupported .basicRepresentation state
  | .noChoice => .noChoice state
  | .ok raw =>
    match hookTarget state pointer with
    | none => .unsupported .missingTree state
    | some (id, path, tree) =>
      match TreeFactored.access tree path .write 0 size with
      | .ok () changed =>
        if TreeFactored.containsStrong changed then .ub .strongProtector state
        else .ok () { setTree state id changed with raw }
      | .ub fault _ => .ub (.tree fault) state
      | .unsupported reason _ => .unsupported
          (.tree (TreeCorrespondence.structuralToReference reason)) state

def release (state : State) (provenance : Provenance) : Result Unit :=
  let (id, path) := provenance
  match state.raw.allocations id, state.trees id with
  | none, _ => .unsupported .basicRepresentation state
  | _, none => .unsupported .missingTree state
  | some allocation, some tree =>
    match TreeFactored.unprotectAt tree path with
    | .ub fault changed => .ub (.tree fault) (setTree state id changed)
    | .unsupported reason changed => .unsupported
        (.tree (TreeCorrespondence.structuralToReference reason)) (setTree state id changed)
    | .ok accesses converted =>
      if !allocation.live then .ok () (setTree state id converted)
      else match TreeFactored.releaseTraverse converted path accesses with
      | .ok () changed => .ok () (setTree state id changed)
      | .ub fault changed => .ub (.tree fault) (setTree state id changed)
      | .unsupported reason changed => .unsupported
          (.tree (TreeCorrespondence.structuralToReference reason)) (setTree state id changed)

theorem reify_setTree (state : State) (id : Nat) (tree : Tree) :
    reify (setTree state id tree) =
      TreeMemory.setTree (reify state) id (TreeCorrespondence.reify tree) := by
  unfold reify setTree TreeMemory.setTree
  congr 1
  funext selected
  by_cases same : selected = id <;> simp [same]

theorem reify_with_raw (state : State) (raw : MiniRustReference.State) :
    reify { state with raw } = { reify state with raw } := rfl

theorem reify_with_frame (state : State) (frame : List Provenance) :
    reify { state with currentFrame := frame } = { reify state with currentFrame := frame } := rfl

theorem reified_related (state : State) : Related (reify state) state := rfl

#print axioms reify_setTree
#print axioms reify_with_raw
#print axioms reify_with_frame
#print axioms reified_related

end AnnealResearch.TreeFactoredMemory
