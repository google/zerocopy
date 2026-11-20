import Miri.TreeBorrows.LocationState

/-!
Finite tree-visitor schedule from pinned Miri
tree_borrows/tree_visitor.rs. This models the normal-tree visitation order
and the precise local/foreign relation used at each node. A tree is assumed to
be a valid finite rooted tree, as it is at Miri's visitor call sites.
Allocation ranges, wildcard subtrees, exposed caches, and diagnostics are
outside this traversal schedule.
-/

namespace Miri.TreeBorrows

namespace Tree

/-- Whether to visit the accessed node's direct children. -/
inductive ChildrenVisitMode where
  | VisitChildrenOfAccessed
  | SkipChildrenOfAccessed
  deriving DecidableEq, Repr, Inhabited

/-- Ordered parent/child links used by Miri's normal tree visitor. -/
structure TraversalNode where
  parent : Option Nat
  children : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- A finite tree indexed by its node positions. -/
structure TraversalTree where
  nodes : Array TraversalNode
  deriving DecidableEq, Repr, Inhabited

/-- One node visit and the access relation passed to the location transition. -/
structure TraversalEvent where
  node : Nat
  relatedness : AccessRelatedness
  deriving DecidableEq, Repr

namespace TraversalTree

private def nodeAt (tree : TraversalTree) (index : Nat) : TraversalNode :=
  tree.nodes[index]?.getD ⟨none, []⟩

/-- The start node followed by its successive parents, through the root. -/
private def ancestorPathAux (tree : TraversalTree) : Nat → Nat → List Nat
  | 0, current => [current]
  | fuel + 1, current =>
      match (nodeAt tree current).parent with
      | none => [current]
      | some parent => current :: ancestorPathAux tree fuel parent

def ancestorPath (tree : TraversalTree) (start : Nat) : List Nat :=
  ancestorPathAux tree tree.nodes.size start

private theorem ancestorPathAux_head (tree : TraversalTree) (fuel : Nat)
    (current : Nat) :
    (ancestorPathAux tree fuel current).head? = some current := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases h : (nodeAt tree current).parent <;> simp [ancestorPathAux, h]

theorem ancestorPath_head (tree : TraversalTree) (start : Nat) :
    (ancestorPath tree start).head? = some start := by
  exact ancestorPathAux_head tree tree.nodes.size start

/-- Initial foreign roots are pushed in the same order as the source visitor:
first the accessed node's children in reverse order, then sibling subtrees
of each successive parent. -/
private def initialForeignRoots (tree : TraversalTree)
    (path : List Nat) (mode : ChildrenVisitMode) : List Nat :=
  go path none true
where
  go (remaining : List Nat) (previous : Option Nat) (isStart : Bool) : List Nat :=
    match remaining with
    | [] => []
    | current :: rest =>
        let shouldVisitChildren := !isStart || mode == .VisitChildrenOfAccessed
        let siblings :=
          if shouldVisitChildren then
            ((nodeAt tree current).children.reverse).filter
              (fun child => previous != some child)
          else []
        siblings ++ go rest (some current) false

/-- Bottom-up foreign subtree events. The finite fuel corresponds to the
height bound of a valid rooted tree; a skipped node prunes itself and all
descendants, matching the source SkipSelfAndChildren result. -/
private def foreignPostorder (tree : TraversalTree) (skipNodes : List Nat) :
    Nat → Nat → List TraversalEvent
  | 0, _ => []
  | fuel + 1, index =>
      if skipNodes.contains index then []
      else
        let children := (nodeAt tree index).children.reverse
        children.flatMap (foreignPostorder tree skipNodes fuel) ++
          [⟨index, .ForeignAccess⟩]

/-- Schedule a normal access: access the start and its ancestors first, then
visit deferred cousin/child subtrees bottom-up. skipNodes models the source's
foreign-only continue callback. -/
def traverse (tree : TraversalTree) (start : Nat)
    (mode : ChildrenVisitMode) (skipNodes : List Nat) :
    Nat × List TraversalEvent :=
  let path := ancestorPath tree start
  let root := path.getLast!
  let localEvents := path.map (fun index => ⟨index, .LocalAccess⟩)
  let foreignRoots := initialForeignRoots tree path mode
  let foreignEvents :=
    foreignRoots.flatMap (foreignPostorder tree skipNodes tree.nodes.size)
  (root, localEvents ++ foreignEvents)

/-- The source visitor always propagates at the accessed node first. -/
theorem traverse_starts_at_accessed_node (tree : TraversalTree) (start : Nat)
    (mode : ChildrenVisitMode) (skipNodes : List Nat) :
    (traverse tree start mode skipNodes).2.head? =
      some ⟨start, .LocalAccess⟩ := by
  simp [traverse, ancestorPath_head]

end TraversalTree

end Tree

end Miri.TreeBorrows
