import AnnealResearch.TreeInitialAgreement
import AnnealResearch.TreeMemoryAgreement
import AnnealResearch.TreeMemoryDomain

/-!
New owned factored-memory reborrow, retaining the frozen recursive wrapper's
raw checks, explicit geometry/settings validation, partial-error commit, and
successful protector registration order. Settings and pointers are shared
supplied types; type/layout settings computation is not implemented here.

The child is constructed directly as an F leaf, not by running the recursive
model or encoding its execution. A constant total store supplies the root;
absent entries are irrelevant to reification. Tree execution uses actual
F.addNode and F.initialAccesses. This checkpoint defines the operation and
reusable geometry/constructor equations. Full R/F wrapper agreement is still
pending and must expose only the existing input WellSized domain.
-/

namespace AnnealResearch.TreeFactoredMemory

open TreePermissions

def reborrowPermissions (size offset : Nat) (settings : TreeMemory.Settings) : List Permission :=
  let outside := List.replicate size settings.outside
  outside.take offset ++ settings.inside ++ outside.drop (offset + settings.inside.length)

def reborrowChild (permissions : List Permission) (protection : Protected) : Tree :=
  ⟨.node .nil, fun _ => ⟨permissions, protection⟩⟩

def reborrow (state : State) (pointer : Pointer) (settings : TreeMemory.Settings) : Result Pointer :=
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
            let permissions := reborrowPermissions allocation.size offset settings
            if !permissions.all (·.matchesProtector settings.protection) then
              .unsupported .settings state
            else
              let child := reborrowChild permissions settings.protection
              match TreeFactored.addNode tree parentPath child with
              | .ub fault changed => .ub (.tree fault) (setTree state id changed)
              | .unsupported reason changed => .unsupported
                  (.tree (TreeCorrespondence.structuralToReference reason)) (setTree state id changed)
              | .ok path added =>
                match TreeFactored.initialAccesses added path offset settings.inside with
                | .ub fault changed => .ub (.tree fault) (setTree state id changed)
                | .unsupported reason changed => .unsupported
                    (.tree (TreeCorrespondence.structuralToReference reason)) (setTree state id changed)
                | .ok () changed =>
                  let updated := setTree state id changed
                  let registered := if settings.protection.yes then
                    { updated with currentFrame := updated.currentFrame ++ [(id, path)] }
                    else updated
                  .ok { pointer with provenance := some (id, path) } registered

end AnnealResearch.TreeFactoredMemory

namespace AnnealResearch.TreeFactoredReborrow

open TreePermissions
open TreeFactoredMemory (State Pointer reborrow reborrowPermissions reborrowChild)

/-- The input inequality is exactly the successful executed geometry branch.
It is a local constructor fact, not admission for future wrapper agreement. -/
theorem permissions_length (size offset : Nat) (settings : TreeMemory.Settings)
    (within : offset + settings.inside.length ≤ size) :
    (reborrowPermissions size offset settings).length = size := by
  have offsetBound : offset ≤ size := by omega
  simp only [reborrowPermissions, List.length_append, List.length_take,
    List.length_replicate, List.length_drop, Nat.min_eq_left offsetBound]
  omega

theorem child_reify (permissions : List Permission) (protection : Protected) :
    TreeCorrespondence.reify (reborrowChild permissions protection) =
      TreeReference.Node.mk permissions protection [] := by
  simp only [reborrowChild, TreeCorrespondence.reify, TreeCorrespondence.reifyTree,
    TreeCorrespondence.reifyForest]

theorem child_uniform (permissions : List Permission) (protection : Protected) (width : Nat)
    (length : permissions.length = width) :
    TreeFactored.arrayLengthsTree (reborrowChild permissions protection).topology []
      (reborrowChild permissions protection).store width = true := by
  simp [reborrowChild, TreeFactored.arrayLengthsTree, TreeFactored.arrayLengthsForest, length]

theorem assembled_child_uniform (size offset : Nat) (settings : TreeMemory.Settings)
    (within : offset + settings.inside.length ≤ size) :
    TreeFactored.arrayLengthsTree
      (reborrowChild (reborrowPermissions size offset settings) settings.protection).topology []
      (reborrowChild (reborrowPermissions size offset settings) settings.protection).store size = true :=
  child_uniform _ _ _ (permissions_length size offset settings within)

/-- Matching remains the actual executed settings guard, not an input-domain
assumption imposed on existing trees or on supplied settings. -/
theorem child_matching (permissions : List Permission) (protection : Protected) :
    TreeFactored.matchesProtectors (reborrowChild permissions protection) =
      permissions.all (fun permission => permission.matchesProtector protection) := by
  simp only [reborrowChild, TreeFactored.matchesProtectors, TreeFactored.matchingTree,
    TreeFactored.matchingForest, Bool.and_true]

theorem reborrow_basic_ub (state : State) (pointer : Pointer) (settings : TreeMemory.Settings)
    (fault : MiniRustReference.UB)
    (checked : MiniRustReference.checkPtr state.raw pointer.basic settings.inside.length = .ub fault) :
    reborrow state pointer settings = .ub (.basic fault) state := by
  simp only [reborrow, checked]

theorem reborrow_no_provenance (state : State) (pointer : Pointer)
    (settings : TreeMemory.Settings) (span : Option MiniRustReference.CheckedSpan)
    (checked : MiniRustReference.checkPtr state.raw pointer.basic settings.inside.length = .ok span)
    (provenance : pointer.provenance = none) :
    reborrow state pointer settings = .ok pointer state := by
  simp only [reborrow, checked, provenance]

/-- An actual width-free zero-size branch; no allocation, tree or frame entry
is consulted when the pointer has no provenance. -/
theorem zero_no_provenance (state : State) (pointer : Pointer) (outside : Permission)
    (protection : Protected) (provenance : pointer.provenance = none) :
    reborrow state pointer ⟨[], outside, protection⟩ = .ok pointer state := by
  simp only [reborrow, MiniRustReference.checkPtr, List.length_nil, ↓reduceIte, provenance]

#print axioms permissions_length
#print axioms child_reify
#print axioms child_uniform
#print axioms assembled_child_uniform
#print axioms child_matching
#print axioms reborrow_basic_ub
#print axioms reborrow_no_provenance
#print axioms zero_no_provenance

end AnnealResearch.TreeFactoredReborrow
