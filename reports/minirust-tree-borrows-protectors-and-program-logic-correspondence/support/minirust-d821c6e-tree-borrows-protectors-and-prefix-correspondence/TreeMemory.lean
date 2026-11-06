import AnnealResearch.MiniRustReference
import AnnealResearch.TreeReference

/-!
Selected recursive-tree hooks composed with unchanged raw BasicMemory checks.
The proposed raw result is held privately until the hook succeeds. Reborrow
and release instead commit ordinary returned partial tree changes. This is a
manual source-equation experiment, not a full Tree Borrows/Rust interpretation.

Raw payload controls use numeric/uninitialized bytes without pointer fragments;
MiniRustReference.Byte does not encode the additional Tree Borrows path of a
pointer fragment. Settings below are explicitly supplied selected specializations,
not the source's type/layout computation. Geometry outside nonnegative in-bounds
offsets is unsupported. No allocator, Return machine or whole-program NoUB claim.
-/
namespace AnnealResearch.TreeMemory

open TreePermissions

abbrev Path := TreeReference.Path
abbrev Tree := TreeReference.Node
abbrev Provenance := Nat × Path

structure Pointer where
  addr : Nat
  provenance : Option Provenance
  deriving DecidableEq, Repr

def Pointer.basic (pointer : Pointer) : MiniRustReference.Ptr :=
  ⟨pointer.addr, pointer.provenance.map Prod.fst⟩

structure State where
  raw : MiniRustReference.State
  trees : Nat → Option Tree
  currentFrame : List Provenance

inductive Fault where
  | basic (reason : MiniRustReference.UB)
  | tree (reason : TreePermissions.Fault)
  | strongProtector
  deriving DecidableEq, Repr

inductive Unsupported where
  | basicRepresentation | missingTree
  | tree (reason : TreeReference.Structural)
  | settings | geometry
  deriving DecidableEq, Repr

inductive Result (A : Type) where
  | ok (value : A) (state : State)
  | ub (fault : Fault) (state : State)
  | unsupported (reason : Unsupported) (state : State)
  | noChoice (state : State)

def setTree (state : State) (id : Nat) (tree : Tree) : State :=
  { state with trees := fun selected => if selected = id then some tree else state.trees selected }

/-- Resolve the hook's actual allocation ID/path from pointer provenance, after
the raw precheck succeeded. No caller-supplied independent spatial key exists. -/
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
        match TreeReference.access tree (some path) .read span.offset size with
        | .ok () changed => .ok bytes { setTree state id changed with raw }
        | .ub fault _ => .ub (.tree fault) state
        | .unsupported reason _ => .unsupported (.tree reason) state

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
        match TreeReference.access tree (some path) .write span.offset bytes.length with
        | .ok () changed => .ok () { setTree state id changed with raw }
        | .ub fault _ => .ub (.tree fault) state
        | .unsupported reason _ => .unsupported (.tree reason) state

/-- The selector argument exists only to challenge omitted-recursion mutants.
The actual deallocate operation below always uses the complete recursive search. -/
def freeWith (blocks : Tree → Bool) (eagerCommit : Bool) (state : State)
    (pointer : Pointer) (kind : MiniRustReference.Kind) (size align : Nat) : Result Unit :=
  match MiniRustReference.free state.raw pointer.basic kind size align with
  | .ub fault => .ub (.basic fault) state
  | .unsupported => .unsupported .basicRepresentation state
  | .noChoice => .noChoice state
  | .ok raw =>
    match hookTarget state pointer with
    | none => .unsupported .missingTree state
    | some (id, path, tree) =>
      match TreeReference.access tree (some path) .write 0 size with
      | .ok () changed =>
        if blocks changed then
          .ub .strongProtector (if eagerCommit then setTree state id changed else state)
        else .ok () { setTree state id changed with raw }
      | .ub fault _ => .ub (.tree fault) state
      | .unsupported reason _ => .unsupported (.tree reason) state

def deallocate := freeWith TreeReference.containsStrong false

/-- Memory.release_protector first converts the selected node, then branches
on liveness. Outer allocation mutation commits changes on ordinary returned UB. -/
def release (state : State) (provenance : Provenance) : Result Unit :=
  let (id, path) := provenance
  match state.raw.allocations id, state.trees id with
  | none, _ => .unsupported .basicRepresentation state
  | _, none => .unsupported .missingTree state
  | some allocation, some tree =>
    match TreeReference.unprotectAt tree path with
    | .ub fault changed => .ub (.tree fault) (setTree state id changed)
    | .unsupported reason changed => .unsupported (.tree reason) (setTree state id changed)
    | .ok accesses converted =>
      if !allocation.live then .ok () (setTree state id converted)
      else match TreeReference.releaseTraverse converted (some path) accesses with
      | .ok () changed => .ok () (setTree state id changed)
      | .ub fault changed => .ub (.tree fault) (setTree state id changed)
      | .unsupported reason changed => .unsupported (.tree reason) (setTree state id changed)

structure Settings where
  inside : List Permission
  outside : Permission
  protection : Protected

/-- Selected reborrow kernel, including actual initial accesses and registration
only after success. Mismatching child settings model source assertion input as
unsupported; existing-node compatibility is never used as an execution guard. -/
def reborrow (state : State) (pointer : Pointer) (settings : Settings) : Result Pointer :=
  match MiniRustReference.checkPtr state.raw pointer.basic settings.inside.length with
  | .ub fault => .ub (.basic fault) state
  | .unsupported => .unsupported .basicRepresentation state
  | .noChoice => .noChoice state
  | .ok _ =>
    match pointer.provenance with
    | none => .ok pointer state
    | some (id, parentPath) =>
      match state.raw.allocations id, state.trees id with
      | none, _ => .unsupported .basicRepresentation state
      | _, none => .unsupported .missingTree state
      | some allocation, some tree =>
        if pointer.addr < allocation.base then .unsupported .geometry state
        else
          let offset := pointer.addr - allocation.base
          if allocation.size < offset + settings.inside.length then
            .unsupported .geometry state
          else
            let outside := List.replicate allocation.size settings.outside
            let permissions := outside.take offset ++ settings.inside ++
              outside.drop (offset + settings.inside.length)
            if !permissions.all (·.matchesProtector settings.protection) then
              .unsupported .settings state
            else
              let child := TreeReference.Node.mk permissions settings.protection []
              match TreeReference.addNode tree parentPath child with
              | .ub fault changed => .ub (.tree fault) (setTree state id changed)
              | .unsupported reason changed =>
                  .unsupported (.tree reason) (setTree state id changed)
              | .ok path added =>
                match TreeReference.initialAccesses added path offset settings.inside with
                | .ub fault changed => .ub (.tree fault) (setTree state id changed)
                | .unsupported reason changed =>
                    .unsupported (.tree reason) (setTree state id changed)
                | .ok () changed =>
                  let updated := setTree state id changed
                  let registered := if settings.protection.yes then
                    { updated with currentFrame := updated.currentFrame ++ [(id, path)] }
                    else updated
                  .ok { pointer with provenance := some (id, path) } registered

theorem zero_load_has_no_tree_hook (state : State) (pointer : Pointer) (align : Nat)
    (positive : align ≠ 0) (aligned : pointer.addr % align = 0) :
    load state pointer 0 align = .ok [] state := by
  simp [load, MiniRustReference.load, positive, aligned, Pointer.basic,
    MiniRustReference.checkPtr]

theorem release_does_not_consume_frame (state : State) (provenance : Provenance) :
    (match release state provenance with
    | .ok _ changed | .ub _ changed | .unsupported _ changed | .noChoice changed =>
      changed.currentFrame) = state.currentFrame := by
  rcases provenance with ⟨id, path⟩
  cases allocationFound : state.raw.allocations id <;>
    cases treeFound : state.trees id
  all_goals simp only [release, allocationFound, treeFound]
  all_goals try rfl
  rename_i allocation tree
  cases converted : TreeReference.unprotectAt tree path with
  | ub fault changed => rfl
  | unsupported reason changed => rfl
  | ok accesses changed =>
    cases live : allocation.live <;> simp only [Bool.not_false, Bool.not_true,
      ite_true, Bool.false_eq_true, ite_false]
    · rfl
    · cases TreeReference.releaseTraverse changed (some path) accesses with
      | ok value next => cases value; rfl
      | ub fault next => rfl
      | unsupported reason next => rfl

#print axioms zero_load_has_no_tree_hook
#print axioms release_does_not_consume_frame

end AnnealResearch.TreeMemory
