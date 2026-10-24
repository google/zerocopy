import AnnealResearch.TreeTraversalGeometry

/-!
Unconditional geometry preservation through the unchanged independent recursive
traversals and public validated access/release entry points. Every success, UB
and unsupported residual participates, including prior partial permission
updates. Array/range/path validation failures retain their actual outcomes.

Geometry preserves the complete ordered topology and each total-store cell's
permission-list length. Permission values and protector flags may change. No
width, valid-path, scalar-success, kind-matching or NoUB premise is introduced.
-/

namespace AnnealResearch.TreeTraversalGeometry

open TreePermissions
open TreeFactored (Path Topology Forest Store State)

mutual
  theorem accessTree_sameLengths (topology : Topology) (here : Path) (store : Store)
      (path : Option Path) (kind : AccessKind) (offset size : Nat) :
      SameLengths store (TreeFactored.accessTree topology here store path kind offset size).residual := by
    cases topology with
    | node children =>
        rw [TreeFactored.accessTree]
        exact bind_sameLengths store _ _
          (transitionOffsets_sameLengths store here kind (TreeFactored.nodeRelation path) offset size)
          (fun _ changed => accessForest_sameLengths children here 0 changed path kind offset size)
  termination_by structural topology

  theorem accessForest_sameLengths (children : Forest) (parent : Path) (index : Nat)
      (store : Store) (path : Option Path) (kind : AccessKind) (offset size : Nat) :
      SameLengths store
        (TreeFactored.accessForest children parent index store path kind offset size).residual := by
    cases children with
    | nil => exact sameLengths_refl store
    | cons child rest =>
        rw [TreeFactored.accessForest]
        exact bind_sameLengths store _ _
          (accessTree_sameLengths child (parent ++ [index]) store
            (TreeFactored.childPath path index) kind offset size)
          (fun _ changed => accessForest_sameLengths rest parent (index + 1) changed path kind offset size)
  termination_by structural children
end

mutual
  theorem releaseTree_sameLengths (topology : Topology) (here : Path) (store : Store)
      (path : Option Path) (accesses : List (Option AccessKind)) :
      SameLengths store (TreeFactored.releaseTree topology here store path accesses).residual := by
    cases topology with
    | node children =>
        by_cases stopped : path = some []
        · subst path
          simpa only [TreeFactored.releaseTree, TreeFactored.Result.residual] using
            setProtected_sameLengths store here .no
        · simpa only [TreeFactored.releaseTree, stopped] using
            bind_sameLengths store _ _
              (releaseOffsets_sameLengths store here (TreeFactored.nodeRelation path) 0 accesses)
              (fun _ changed => releaseForest_sameLengths children here 0 changed path accesses)
  termination_by structural topology

  theorem releaseForest_sameLengths (children : Forest) (parent : Path) (index : Nat)
      (store : Store) (path : Option Path) (accesses : List (Option AccessKind)) :
      SameLengths store
        (TreeFactored.releaseForest children parent index store path accesses).residual := by
    cases children with
    | nil => exact sameLengths_refl store
    | cons child rest =>
        rw [TreeFactored.releaseForest]
        exact bind_sameLengths store _ _
          (releaseTree_sameLengths child (parent ++ [index]) store
            (TreeFactored.childPath path index) accesses)
          (fun _ changed => releaseForest_sameLengths rest parent (index + 1) changed path accesses)
  termination_by structural children
end

theorem accessCore_geometry (state : State) (path : Option Path) (kind : AccessKind)
    (offset size : Nat) :
    Geometry state (TreeFactored.accessCore state path kind offset size).residual := by
  unfold TreeFactored.accessCore
  exact mapStore_geometry state _
    (accessTree_sameLengths state.topology [] state.store path kind offset size)

theorem releaseCore_geometry (state : State) (path : Option Path)
    (accesses : List (Option AccessKind)) :
    Geometry state (TreeFactored.releaseCore state path accesses).residual := by
  unfold TreeFactored.releaseCore
  exact mapStore_geometry state _
    (releaseTree_sameLengths state.topology [] state.store path accesses)

/-- All structural validation failures and every raw worker result preserve
geometry; no validation condition is imposed on the caller. -/
theorem access_geometry (state : State) (path : Path) (kind : AccessKind)
    (offset size : Nat) :
    Geometry state (TreeFactored.access state path kind offset size).residual := by
  unfold TreeFactored.access
  cases TreeFactored.findTopology state.topology path with
  | none => exact geometry_refl state
  | some selected =>
      dsimp only
      cases TreeFactored.arrayLengths state with
      | false => exact geometry_refl state
      | true =>
          by_cases beyond : (state.store []).permissions.length < offset + size
          · simpa only [beyond, ↓reduceIte, TreeFactored.Result.residual] using geometry_refl state
          · simpa only [beyond, ↓reduceIte] using
              accessCore_geometry state (some path) kind offset size

theorem releaseTraverse_geometry (state : State) (path : Path)
    (accesses : List (Option AccessKind)) :
    Geometry state (TreeFactored.releaseTraverse state path accesses).residual := by
  unfold TreeFactored.releaseTraverse
  cases TreeFactored.findTopology state.topology path with
  | none => exact geometry_refl state
  | some selected =>
      dsimp only
      cases TreeFactored.arrayLengths state with
      | false => exact geometry_refl state
      | true =>
          by_cases same : accesses.length = (state.store []).permissions.length
          · simpa only [same, ↓reduceIte] using releaseCore_geometry state (some path) accesses
          · simpa only [same, ↓reduceIte, TreeFactored.Result.residual] using geometry_refl state

/-- Exact Bool query preservation also covers initially malformed widths. -/
theorem access_arrayLengths (state : State) (path : Path) (kind : AccessKind)
    (offset size width : Nat) :
    TreeFactored.arrayLengthsTree (TreeFactored.access state path kind offset size).residual.topology []
        (TreeFactored.access state path kind offset size).residual.store width =
      TreeFactored.arrayLengthsTree state.topology [] state.store width :=
  geometry_arrayLengths state _ width (access_geometry state path kind offset size)

theorem releaseTraverse_arrayLengths (state : State) (path : Path)
    (accesses : List (Option AccessKind)) (width : Nat) :
    TreeFactored.arrayLengthsTree (TreeFactored.releaseTraverse state path accesses).residual.topology []
        (TreeFactored.releaseTraverse state path accesses).residual.store width =
      TreeFactored.arrayLengthsTree state.topology [] state.store width :=
  geometry_arrayLengths state _ width (releaseTraverse_geometry state path accesses)

#print axioms accessTree_sameLengths
#print axioms accessForest_sameLengths
#print axioms releaseTree_sameLengths
#print axioms releaseForest_sameLengths
#print axioms accessCore_geometry
#print axioms releaseCore_geometry
#print axioms access_geometry
#print axioms releaseTraverse_geometry
#print axioms access_arrayLengths
#print axioms releaseTraverse_arrayLengths

end AnnealResearch.TreeTraversalGeometry
