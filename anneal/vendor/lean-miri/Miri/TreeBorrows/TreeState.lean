import Lean
import Init.Internal.Order.While
import Miri.TreeBorrows.UniMap
import Miri.TreeBorrows.LocationState
import Miri.TreeBorrows.NormalTree
import Miri.TreeBorrows.GlobalState
import Miri.DataStructures.DedupRangeMap
import Miri.ABI.Size
import Miri.Memory.Identity

/-!
The allocation-local state layout from Miri's `tree_borrows/tree.rs`:
tag-to-index map, indexed nodes, per-range location data, and ordered roots.
The first constructor is the exact `Tree::new` root state. Diagnostic-only
node history is intentionally omitted. Child insertion and access traversal
are separate operations.
-/

namespace Miri.TreeBorrows

open Miri.ABI
open Miri.DataStructures

/-- Per-node information consumed by tree traversal and permission defaults.
The source's `NodeDebugInfo` name is retained because `miri_pointer_name` and
`miri_print_borrow_state` expose it. Access history is diagnostic-only and is
not needed to print the current tree.
-/
structure TreeNode where
  tag : Miri.Memory.BorTag
  parent : Option UniIndex
  children : Array UniIndex := #[]
  defaultInitialPermission : Permission
  defaultInitialSifa : IdempotentForeignAccess
  isExposed : Bool := false
  debugName : Option String := none
  deriving DecidableEq, Repr

namespace TreeNode

def defaultLocationState (node : TreeNode) : Tree.LocationState :=
  ⟨node.defaultInitialPermission, false, node.defaultInitialSifa⟩

end TreeNode

/-- Willard-cache counters for one node at one homogeneous byte range.
Counters keep the source's `u16` width.
-/
structure ExposedCacheNode where
  localWrites : UInt16 := 0
  localReads : UInt16 := 0
  deriving DecidableEq, Repr, Inhabited

inductive WildcardAccessRelatedness where
  | LocalAccess
  | ForeignAccess
  | EitherAccess
  deriving DecidableEq, Repr, Inhabited

/-- Wildcard-relatedness cache for one location range. -/
structure ExposedCache where
  nodes : UniValMap ExposedCacheNode := {}
  deriving DecidableEq, Repr, Inhabited

inductive ExposedCacheError where
  | MissingNode (index : UniIndex)
  | InvalidIndex (index : Nat)
  | ParentCycle (index : UniIndex)
  deriving DecidableEq, Repr

structure ExposedCacheUpdate where
  cache : ExposedCache
  outcome : Except ExposedCacheError Unit
  deriving DecidableEq, Repr

namespace ExposedCache

def accessRelatedness (cache : ExposedCache) (root id : UniIndex)
    (kind : AccessKind) (isWildcardTree onlyForeign : Bool) :
    Option WildcardAccessRelatedness := Id.run do
  let rootState := cache.nodes.get root |>.getD {}
  let nodeState := cache.nodes.get id |>.getD {}
  let (total, localCount) := match kind with
    | .Read => (rootState.localReads.toNat, nodeState.localReads.toNat)
    | .Write => (rootState.localWrites.toNat, nodeState.localWrites.toNat)
  let total := total + (if isWildcardTree then 1 else 0)
  let relatedness :=
    if total == 0 then none
    else if total == localCount then some .LocalAccess
    else if localCount == 0 then some .ForeignAccess
    else some .EitherAccess
  if onlyForeign then
    match relatedness with
    | some .LocalAccess | none => return none
    | some .ForeignAccess | some .EitherAccess => return some .ForeignAccess
  else
    return relatedness

private def hasReadExposure : WildcardAccessLevel → Bool
  | .None => false
  | .Read | .Write => true

private def hasWriteExposure : WildcardAccessLevel → Bool
  | .Write => true
  | .None | .Read => false

/-- Source `ExposedCache::update_exposure`: update the node's counters and
propagate the same exposure delta through each ancestor. On malformed node
indices/cycles, preserve all earlier counter mutations in the returned cache.
-/
def updateExposure (cache : ExposedCache) (nodes : UniValMap TreeNode)
    (id : UniIndex) (oldLevel newLevel : WildcardAccessLevel) : ExposedCacheUpdate := Id.run do
  if oldLevel == newLevel then return { cache, outcome := .ok () }
  let mut current := cache
  let mut next := some id
  let mut steps := 0
  let mut outcome : Except ExposedCacheError Unit := .ok ()
  let mut active := true
  while active do
    if steps > nodes.size then
      outcome := .error (.ParentCycle (next.getD id))
      active := false
    else
      match next with
      | none => active := false
      | some index =>
          match nodes.get index with
          | none =>
              outcome := .error (.MissingNode index)
              active := false
          | some node =>
              let old := current.nodes.get index |>.getD {}
              let incrementWrites := !hasWriteExposure oldLevel && hasWriteExposure newLevel
              let decrementWrites := hasWriteExposure oldLevel && !hasWriteExposure newLevel
              let incrementReads := !hasReadExposure oldLevel && hasReadExposure newLevel
              let decrementReads := hasReadExposure oldLevel && !hasReadExposure newLevel
              let updated := {
                localWrites :=
                  if incrementWrites then old.localWrites + 1
                  else if decrementWrites then old.localWrites - 1
                  else old.localWrites
                localReads :=
                  if incrementReads then old.localReads + 1
                  else if decrementReads then old.localReads - 1
                  else old.localReads
              }
              current := { current with nodes := current.nodes.insert index updated }
              next := node.parent
              steps := steps + 1
              if next.isNone then active := false
  return { cache := current, outcome }

def remove (cache : ExposedCache) (idx : UniIndex) : ExposedCache :=
  { cache with nodes := cache.nodes.remove idx }

end ExposedCache

/-- The source's `LocationTree`: lazily stored permission state and one
exposed-node cache per homogeneous range. -/
structure LocationTree where
  perms : UniValMap Tree.LocationState := {}
  exposedCache : ExposedCache := {}
  deriving DecidableEq, Repr, Inhabited

/-- Allocation-local tree state. `roots` begins with the allocation's unique
root and may later contain ordered wildcard roots.
-/
structure BorrowTree where
  tagMapping : UniKeyMap Miri.Memory.BorTag
  nodes : UniValMap TreeNode
  locations : DedupRangeMap LocationTree
  roots : Array UniIndex
  deriving DecidableEq, Repr

inductive DebugNameError where
  | missingTag (tag : Miri.Memory.BorTag)
  | missingNode (index : UniIndex)
  | missingParent (tag : Miri.Memory.BorTag) (distance : Nat)
  deriving DecidableEq, Repr

namespace BorrowTree

/-- Source `Tree::nth_parent`, with malformed/exhausted ancestry retained as a
checked machine error by diagnostic callers instead of an unchecked unwrap. -/
def nthParent (tree : BorrowTree) (tag : Miri.Memory.BorTag) (distance : Nat) :
    Except DebugNameError Miri.Memory.BorTag := do
  let some index := tree.tagMapping.get tag
    | throw (.missingTag tag)
  let mut current := index
  for step in [:distance] do
    let some node := tree.nodes.get current
      | throw (.missingNode current)
    let some parent := node.parent
      | throw (.missingParent tag (step + 1))
    current := parent
  let some node := tree.nodes.get current
    | throw (.missingNode current)
  return node.tag

/-- Source `NodeDebugInfo::add_name`: several names for one tag are joined
with `", "` in their insertion order. -/
def addDebugName (tree : BorrowTree) (tag : Miri.Memory.BorTag)
    (name : String) : Except DebugNameError BorrowTree := do
  let some index := tree.tagMapping.get tag
    | throw (.missingTag tag)
  let some node := tree.nodes.get index
    | throw (.missingNode index)
  let debugName := match node.debugName with
    | none => name
    | some previous => previous ++ ", " ++ name
  return {tree with nodes := tree.nodes.insert index {node with debugName := some debugName}}

/-- Source `Tree::give_pointer_debug_name`, including ancestor selection. -/
def givePointerDebugName (tree : BorrowTree) (tag : Miri.Memory.BorTag)
    (distance : Nat) (name : String) : Except DebugNameError BorrowTree := do
  let ancestor ← tree.nthParent tag distance
  tree.addDebugName ancestor name

private def trimLocationForRangeEquality (location : LocationTree) : LocationTree :=
  { location with
    perms := location.perms.trimTrailingNone
    exposedCache := { nodes := location.exposedCache.nodes.trimTrailingNone } }

private def rootIndex : UniIndex := ⟨0⟩

/-- Source `Tree::new`: disabled default at out-of-bounds/uninitialized
locations, one non-exposed root, and an accessed Unique permission throughout
the allocation's in-bounds bytes.
-/
def new (rootTag : Miri.Memory.BorTag) (size : Size) : BorrowTree := Id.run do
  let root := rootIndex
  let rootDefault := Permission.newDisabled
  let mapping : UniKeyMap Miri.Memory.BorTag :=
    { mapping := #[(rootTag, root)], deassigned := #[] }
  let rootNode : TreeNode := {
    tag := rootTag
    parent := none
    children := #[]
    defaultInitialPermission := rootDefault
    defaultInitialSifa := .None
    isExposed := false
  }
  let mut perms : UniValMap Tree.LocationState := {}
  perms := perms.insert root ⟨Permission.newUnique, true, .None⟩
  let initialLocation : LocationTree := { perms, exposedCache := {} }
  let locations := DedupRangeMap.new size initialLocation
  let mut nodes : UniValMap TreeNode := {}
  nodes := nodes.insert root rootNode
  return {
    tagMapping := mapping
    nodes
    locations
    roots := #[root]
  }

def indexOfTag (tree : BorrowTree) (tag : Miri.Memory.BorTag) : Option UniIndex :=
  tree.tagMapping.get tag

def nodeAt (tree : BorrowTree) (idx : UniIndex) : Option TreeNode :=
  tree.nodes.get idx

/-- Current or lazily initialized per-location state for a node. -/
def locationStateAt (tree : BorrowTree) (location : LocationTree) (idx : UniIndex) :
    Option Tree.LocationState := do
  let node ← tree.nodeAt idx
  return (location.perms.get idx).getD node.defaultLocationState

private def traversalProjection (tree : BorrowTree) : Tree.TraversalTree :=
  ⟨tree.nodes.data.map fun entry =>
    match entry with
    | none => ⟨none, []⟩
    | some node =>
        ⟨node.parent.map UniIndex.toNat, node.children.toList.map UniIndex.toNat⟩⟩

/-- Source LocationTree::get_min_exposed_child. This deliberately scans node
topology rather than relying on enabled-only cache counts.
-/
private def minExposedChild (tree : BorrowTree) (start : UniIndex) : Option Miri.Memory.BorTag :=
  Id.run do
    let mut stack := #[start]
    let mut steps := 0
    let mut minimum : Option Miri.Memory.BorTag := none
    while !stack.isEmpty && steps ≤ tree.nodes.size do
      steps := steps + 1
      let some index := stack.back? | return minimum
      stack := stack.pop
      match tree.nodes.get index with
      | none => pure ()
      | some node =>
          let alreadySmaller := minimum.any fun tag => tag.value < node.tag.value
          if !alreadySmaller then
            for child in node.children do
              stack := stack.push child
            if node.isExposed &&
                (minimum.isNone || minimum.any (fun tag => node.tag.value < tag.value)) then
              minimum := some node.tag
    return minimum

private def normalProjection (tree : BorrowTree) (location : LocationTree)
    (protectedTags : ProtectedTags) : Tree.NormalTreeState :=
  let defaults := tree.nodes.data.map fun entry =>
    match entry with
    | some node => node.defaultLocationState
    | none => ⟨.Disabled, false, .None⟩
  let locationStates := tree.nodes.data.mapIdx fun position _ =>
    match UniIndex.ofNat? position with
    | none => none
    | some index => location.perms.get index
  let protectedNodes := tree.nodes.entries.toList.filterMap fun (index, node) =>
    if protectedTags.contains node.tag then some index.toNat else none
  {
    topology := traversalProjection tree
    defaultStates := defaults
    protectedNodes
    locationStates
  }

structure NormalLocationAccessResult where
  location : LocationTree
  access : Tree.NormalAccessResult
  outcome : Except ExposedCacheError Unit
  deriving DecidableEq, Repr

inductive TreeMutationError where
  | MissingTag (tag : Miri.Memory.BorTag)
  | MissingNode (index : UniIndex)
  | ExposedCache (error : ExposedCacheError)
  | RangeMap (error : DedupRangeMapError)
  deriving DecidableEq, Repr

structure TreeMutationResult where
  tree : BorrowTree
  outcome : Except TreeMutationError Unit
  deriving DecidableEq, Repr

inductive ChildInsertError where
  | DuplicateTag (tag : Miri.Memory.BorTag)
  | TagIndexExhausted (active : Nat)
  | MissingParentTag (tag : Miri.Memory.BorTag)
  | OutsidePermissionNotInitial (permission : Permission)
  | OutsideUniquePermission
  | ProtectedReservedIM
  | InsidePermissionNotInitial (permission : Permission)
  | InsideSifaMismatch (permission : Permission)
  | InsidePermissionInvariant (permission : Permission)
  | SizeError (error : SizeError)
  | RangeMapError (error : DedupRangeMapError)
  | MissingNode (index : UniIndex)
  | ParentCycle (index : UniIndex)
  deriving DecidableEq, Repr

structure ChildInsertResult where
  tree : BorrowTree
  outcome : Except ChildInsertError Unit
  deriving DecidableEq, Repr

inductive TreeGcError where
  | MissingNode (index : UniIndex)
  | MissingChildPosition (parent : UniIndex) (position : Nat)
  | MissingReplacementChild (index : UniIndex)
  | EmptyTraversalStack (root : UniIndex)
  | ParentCycle (root : UniIndex)
  | RangeMerge (error : DedupRangeMapError)
  deriving DecidableEq, Repr

structure TreeGcResult where
  tree : BorrowTree
  outcome : Except TreeGcError Unit
  deriving DecidableEq, Repr

private def failingNode? : Tree.NormalAccessStatus → Option Nat
  | .Completed => none
  | .TransitionError node _
  | .RecordDebugAssertion node
  | .PermissionInvariantFailure node
  | .TransitionApplicationInvariantFailure node
  | .PossibleInvariantFailure node
  | .MissingLocationState node => some node

inductive WildcardAccessStatus where
  | Completed
  | EmptyTraversalStack (root : UniIndex)
  | NoValidExposedReferences (root : UniIndex) (node : Option UniIndex)
  | MissingNode (index : UniIndex)
  | RecordDebugAssertion (index : UniIndex)
  | TransitionError (index : UniIndex) (error : Diagnostics.TransitionError)
  | CacheFailure (error : ExposedCacheError)
  | PermissionInvariantFailure (index : UniIndex)
  | TransitionApplicationInvariantFailure (index : UniIndex)
  | PossibleInvariantFailure (index : UniIndex)
  | ParentCycle (root : UniIndex)
  deriving DecidableEq, Repr

structure WildcardLocationAccessResult where
  location : LocationTree
  status : WildcardAccessStatus
  deriving DecidableEq, Repr

private def wildcardRelatedness (cache : ExposedCache) (root index : UniIndex)
    (kind : AccessKind) (isWildcardTree onlyForeign : Bool) :
    Option WildcardAccessRelatedness :=
  cache.accessRelatedness root index kind isWildcardTree onlyForeign

private def exactRelatedness? : WildcardAccessRelatedness → Option AccessRelatedness
  | .LocalAccess => some .LocalAccess
  | .ForeignAccess => some .ForeignAccess
  | .EitherAccess => none

/-- Source `LocationTree::perform_wildcard_access`. The stack implements the
source visitor's child-first, postorder traversal. Relatedness and SIFA skip
decisions are recomputed against the cache as child transitions change it.
-/
def performWildcardAccessAt (tree : BorrowTree) (initialLocation : LocationTree)
    (root : UniIndex) (maxLocalTag : Option Miri.Memory.BorTag)
    (kind : AccessKind) (protectedTags : ProtectedTags) (isWildcardTree : Bool) :
    WildcardLocationAccessResult := Id.run do
  let mut location := initialLocation
  let mut hasValidExposed := false
  let mut status := WildcardAccessStatus.Completed
  let mut stack : Array (UniIndex × Bool) := #[(root, false)]
  let mut steps := 0
  while !stack.isEmpty && status == .Completed do
    steps := steps + 1
    if steps > tree.nodes.size * 2 + 1 then
      status := .ParentCycle root
    else
      let some (index, afterChildren) := stack.back?
        | status := .EmptyTraversalStack root
          continue
      if !afterChildren then
        let some node := tree.nodes.get index
          | status := .MissingNode index
            continue
        let onlyForeign := match maxLocalTag with
          | some maximum => maximum.value < node.tag.value
          | none => false
        let relatedness := wildcardRelatedness location.exposedCache root index kind
          isWildcardTree onlyForeign
        let state := location.perms.get index |>.getD node.defaultLocationState
        let skip := match relatedness.bind exactRelatedness? with
          | some rel =>
              match state.skipIfKnownNoop kind rel with
              | .SkipSelfAndChildren => true
              | .Recurse => false
          | none => false
        if skip then
          stack := stack.pop
        else
          stack := stack.pop.push (index, true)
          for child in node.children do
            stack := stack.push (child, false)
      else
        stack := stack.pop
        let some node := tree.nodes.get index
          | status := .MissingNode index
            continue
        let onlyForeign := match maxLocalTag with
          | some maximum => maximum.value < node.tag.value
          | none => false
        let relatedness := wildcardRelatedness location.exposedCache root index kind
          isWildcardTree onlyForeign
        match relatedness with
        | none =>
            status := .NoValidExposedReferences root (some index)
        | some related =>
            let isProtected := protectedTags.contains node.tag
            let oldState := location.perms.get index |>.getD node.defaultLocationState
            if node.isExposed &&
                (oldState.permission.strongestAllowedLocalAccess isProtected).allows kind &&
                (maxLocalTag.isNone || maxLocalTag.any
                  (fun maximum => maximum.value >= node.tag.value)) then
              hasValidExposed := true
            let (withState, state) := location.perms.orInsert index node.defaultLocationState
            location := { location with perms := withState }
            match exactRelatedness? related with
            | none => pure ()
            | some rel =>
                match state.recordNewAccess kind rel with
                | .DebugAssertion => status := .RecordDebugAssertion index
                | .Recorded recorded =>
                    location := { location with perms := location.perms.insert index recorded }
                    let access := recorded.performAccess kind rel isProtected
                    let updatedState := access.resultingState
                    location := { location with perms := location.perms.insert index updatedState }
                    match access with
                    | .Success _ transition =>
                        if node.isExposed && !transition.isNoop then
                          let oldLevel := oldState.permission.strongestAllowedLocalAccess isProtected
                          let newLevel := updatedState.permission.strongestAllowedLocalAccess isProtected
                          let update := location.exposedCache.updateExposure tree.nodes index
                            oldLevel newLevel
                          location := { location with exposedCache := update.cache }
                          match update.outcome with
                          | .error error => status := .CacheFailure error
                          | .ok _ => pure ()
                    | .Error _ error => status := .TransitionError index error
                    | .PermissionInvariantFailure _ => status := .PermissionInvariantFailure index
                    | .TransitionApplicationInvariantFailure _ =>
                        status := .TransitionApplicationInvariantFailure index
                    | .PossibleInvariantFailure _ => status := .PossibleInvariantFailure index
  if status == .Completed && !hasValidExposed && !isWildcardTree then
    status := .NoValidExposedReferences root none
  return { location, status }

/-- Perform the source normal-tree component at one actual tree location.
Permission transitions are delegated to `NormalTreeState`; this operation
projects the source `UniValMap` topology and lazy defaults, writes state back
to the real maps, and applies exposed-cache deltas in visit order. Additional
wildcard roots are handled by the separate wildcard-access component.
-/
def performNormalAccessAt (tree : BorrowTree) (location : LocationTree)
    (start : UniIndex) (kind : AccessKind) (protectedTags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) : NormalLocationAccessResult := Id.run do
  let access := Tree.NormalTreeState.performAccess
    (normalProjection tree location protectedTags) start.toNat kind mode
  let mut nextLocation := location
  for position in [:access.tree.locationStates.size] do
    match access.tree.locationStates[position]? with
    | some (some state) =>
        match UniIndex.ofNat? position with
        | some index =>
            nextLocation := { nextLocation with perms := nextLocation.perms.insert index state }
        | none => pure ()
    | _ => pure ()
  let mut cacheOutcome : Except ExposedCacheError Unit := .ok ()
  for event in access.visited do
    if cacheOutcome matches .ok _ then
      match UniIndex.ofNat? event.node with
      | none => cacheOutcome := .error (.InvalidIndex event.node)
      | some index =>
        match tree.nodeAt index with
        | none => cacheOutcome := .error (.MissingNode index)
        | some node =>
          if node.isExposed && failingNode? access.status != some event.node then
            match tree.locationStateAt location index, access.tree.stateAt event.node with
            | some oldState, some newState =>
                match performAccessTransition kind event.relatedness oldState.permission
                    (protectedTags.contains node.tag) with
                | .Transition transition =>
                    if !transition.isNoop then
                      let oldLevel := oldState.permission.strongestAllowedLocalAccess
                        (protectedTags.contains node.tag)
                      let newLevel := newState.permission.strongestAllowedLocalAccess
                        (protectedTags.contains node.tag)
                      let update := nextLocation.exposedCache.updateExposure tree.nodes index
                        oldLevel newLevel
                      nextLocation := { nextLocation with exposedCache := update.cache }
                      cacheOutcome := update.outcome
                | .UndefinedBehavior | .ImpossibleProtectedReservedIM => pure ()
            | _, _ => cacheOutcome := .error (.MissingNode index)
  return { location := nextLocation, access, outcome := cacheOutcome }

private def updateEveryLocation (tree : BorrowTree)
    (update : LocationTree → LocationTree × Except TreeMutationError Unit) :
    TreeMutationResult := Id.run do
  let mut current := tree
  for position in [:tree.locations.entries.size] do
    match current.locations.index position with
    | .error error =>
        return { tree := current, outcome := .error (.RangeMap error) }
    | .ok segment =>
        let (nextLocation, outcome) := update segment.data
        let mutation := current.locations.setAtPos position nextLocation
        current := { current with locations := mutation.state }
        match outcome, mutation.outcome with
        | .error error, _ => return { tree := current, outcome := .error error }
        | .ok (), .error error =>
            return { tree := current, outcome := .error (.RangeMap error) }
        | .ok (), .ok () => pure ()
  return { tree := current, outcome := .ok () }

/-- Source `Tree::expose_tag`, including the per-range Willard-cache update.
The global protected-tag table determines which local accesses remain valid
through this exposed tag.
-/
def exposeTag (tree : BorrowTree) (protectedTags : ProtectedTags)
    (tag : Miri.Memory.BorTag) : TreeMutationResult := Id.run do
  let some index := tree.indexOfTag tag
    | return { tree, outcome := .error (.MissingTag tag) }
  let some node := tree.nodeAt index
    | return { tree, outcome := .error (.MissingNode index) }
  if node.isExposed then return { tree, outcome := .ok () }
  let exposedTree := { tree with nodes := tree.nodes.insert index { node with isExposed := true } }
  let update := updateEveryLocation exposedTree fun location =>
    let state := location.perms.get index |>.getD node.defaultLocationState
    let accessLevel := state.permission.strongestAllowedLocalAccess
      (protectedTags.contains tag)
    let cacheUpdate := location.exposedCache.updateExposure exposedTree.nodes index
      .None accessLevel
    let nextLocation := { location with exposedCache := cacheUpdate.cache }
    let outcome := cacheUpdate.outcome.mapError TreeMutationError.ExposedCache
    (nextLocation, outcome)
  return update

/-- Source `update_exposure_for_protector_release`: exposed nodes retain their
exposure, while the cache counters change from protected to unprotected local
permission strength.
-/
def updateExposureForProtectorRelease (tree : BorrowTree)
    (tag : Miri.Memory.BorTag) : TreeMutationResult := Id.run do
  let some index := tree.indexOfTag tag
    | return { tree, outcome := .error (.MissingTag tag) }
  let some node := tree.nodeAt index
    | return { tree, outcome := .error (.MissingNode index) }
  if !node.isExposed then return { tree, outcome := .ok () }
  return updateEveryLocation tree fun location =>
    let state := location.perms.get index |>.getD node.defaultLocationState
    let wasAllowed := state.permission.strongestAllowedLocalAccess true
    let nowAllowed := state.permission.strongestAllowedLocalAccess false
    let cacheUpdate := location.exposedCache.updateExposure tree.nodes index
      wasAllowed nowAllowed
    let nextLocation := { location with exposedCache := cacheUpdate.cache }
    let outcome := cacheUpdate.outcome.mapError TreeMutationError.ExposedCache
    (nextLocation, outcome)

private def weakerSifa (left right : IdempotentForeignAccess) : IdempotentForeignAccess :=
  if left.rank ≤ right.rank then left else right

/-- Restore the source parent-weaker/child-stronger SIFA invariant after a
retag, including lazy defaults and all already materialized location states.
-/
private def updateSifaAfterRetag (tree : BorrowTree) (start : UniIndex)
    (strongestAllowed : IdempotentForeignAccess) :
    BorrowTree × Except ChildInsertError Unit := Id.run do
  if strongestAllowed == .Write then return (tree, .ok ())
  let mut current := tree
  let mut cursor := some start
  let mut steps := 0
  let mut active := true
  while active do
    if steps > current.nodes.size then
      return (current, .error (.ParentCycle (cursor.getD start)))
    match cursor with
    | none => active := false
    | some index =>
        let some node := current.nodes.get index
          | return (current, .error (.MissingNode index))
        let (defaultSifa, defaultChanged) :=
          node.defaultInitialSifa.ensureNoStrongerThan strongestAllowed
        let mut anyChanged := defaultChanged
        for segment in current.locations.iterAll do
          if let some locationState := segment.data.perms.get index then
            let (_, changed) := locationState.idempotentForeignAccess
              |>.ensureNoStrongerThan strongestAllowed
            anyChanged := anyChanged || changed
        let locations := current.locations.modifyAll fun _ location =>
          match location.perms.get index with
          | none => location
          | some locationState =>
              let (sifa, _) := locationState.idempotentForeignAccess
                |>.ensureNoStrongerThan strongestAllowed
              let updatedState := { locationState with idempotentForeignAccess := sifa }
              { location with perms := location.perms.insert index updatedState }
        current := {
          current with
          locations
          nodes := current.nodes.insert index
            ({ node with defaultInitialSifa := defaultSifa })
        }
        if anyChanged then
          cursor := node.parent
          steps := steps + 1
        else
          active := false
  return (current, .ok ())

/-- Source `Tree::new_child`: allocate the tag index, attach a concrete child
or ordered wildcard root, store lazy defaults, materialize inside-range
permissions, and weaken ancestor SIFAs until the retag invariant is restored.
Mutation and invariant failures retain earlier source-ordered state changes.
-/
def newChild (tree : BorrowTree) (baseOffset : Size)
    (parentProvenance : Miri.Memory.ProvenanceExtra)
    (newTag : Miri.Memory.BorTag) (insidePermissions : DedupRangeMap Tree.LocationState)
    (outsidePermission : Permission) (isProtected : Bool) : ChildInsertResult := Id.run do
  let (mapping, newIndex, duplicate) := match tree.tagMapping.insert newTag with
    | .Inserted mapping index => (mapping, some index, false)
    | .DuplicateKeyAfterReplacement mapping index => (mapping, some index, true)
    | .Error mapping _ => (mapping, none, false)
  let mut current := { tree with tagMapping := mapping }
  if duplicate then return { tree := current, outcome := .error (.DuplicateTag newTag) }
  let some newIndex := newIndex
    | return { tree := current, outcome := .error (.TagIndexExhausted mapping.size) }
  let parentIndex := match parentProvenance with
    | .wildcard => some none
    | .concrete parentTag => (tree.tagMapping.get parentTag).map some
  let some parentIndex := parentIndex
    | return { tree := current, outcome := .error (.MissingParentTag (match parentProvenance with
        | .concrete tag => tag
        | .wildcard => newTag)) }
  if !outsidePermission.isInitial then
    return { tree := current, outcome := .error (.OutsidePermissionNotInitial outsidePermission) }
  if outsidePermission.isUnique then
    return { tree := current, outcome := .error .OutsideUniquePermission }
  let defaultSifa := match outsidePermission.strongestIdempotentForeignAccess isProtected with
    | .Access sifa => some sifa
    | .ImpossibleProtectedReservedIM => none
  let some defaultSifa := defaultSifa
    | return { tree := current, outcome := .error .ProtectedReservedIM }
  let node : TreeNode := {
    tag := newTag
    parent := parentIndex
    children := #[]
    defaultInitialPermission := outsidePermission
    defaultInitialSifa := defaultSifa
    isExposed := false
  }
  current := { current with nodes := current.nodes.insert newIndex node }
  match parentIndex with
  | none => current := { current with roots := current.roots.push newIndex }
  | some parent =>
      match current.nodes.get parent with
      | none => return { tree := current, outcome := .error (.MissingNode parent) }
      | some parentNode =>
          let updatedParent := { parentNode with children := parentNode.children.push newIndex }
          current := { current with nodes := current.nodes.insert parent updatedParent }
  let mut minimumSifa := defaultSifa
  for segment in insidePermissions.iterAll do
    let initial := segment.data.permission
    if !initial.isInitial then
      return { tree := current, outcome := .error (.InsidePermissionNotInitial initial) }
    let expectedSifa := match initial.strongestIdempotentForeignAccess isProtected with
      | .Access sifa => some sifa
      | .ImpossibleProtectedReservedIM => none
    let some expectedSifa := expectedSifa
      | return { tree := current, outcome := .error (.InsidePermissionInvariant initial) }
    if segment.data.idempotentForeignAccess != expectedSifa then
      return { tree := current, outcome := .error (.InsideSifaMismatch initial) }
    minimumSifa := weakerSifa minimumSifa segment.data.idempotentForeignAccess
    let start ← match Size.add (Size.ofBytes segment.range.start) baseOffset with
      | .ok start => pure start
      | .error error =>
          return { tree := current, outcome := .error (.SizeError error) }
    let rangeUpdate := current.locations.modifyRange start
      (Size.ofBytes (segment.range.stop - segment.range.start)) fun _ location =>
        { location with perms := location.perms.insert newIndex segment.data }
    current := { current with locations := rangeUpdate.state }
    match rangeUpdate.outcome with
    | .error error => return { tree := current, outcome := .error (.RangeMapError error) }
    | .ok () => pure ()
  match parentIndex with
  | none => return { tree := current, outcome := .ok () }
  | some parent =>
      let (updated, outcome) := updateSifaAfterRetag current parent minimumSifa
      return { tree := updated, outcome }

private def nodeIsUseless (tree : BorrowTree) (index : UniIndex)
    (liveTags : Array Miri.Memory.BorTag) : Bool :=
  match tree.nodes.get index with
  | none => false
  | some node => node.children.isEmpty && !liveTags.contains node.tag

/-- Source `Tree::can_be_replaced_by_single_child`: dead non-root nodes with
one child may be collapsed only when the parent's and child's permissions are
compatible at every represented byte range. -/
private def replacementChild? (tree : BorrowTree) (index : UniIndex)
    (liveTags : Array Miri.Memory.BorTag) : Option UniIndex := Id.run do
  let some node := tree.nodes.get index | return none
  if liveTags.contains node.tag || node.parent.isNone || node.children.size != 1 then
    return none
  let some childIndex := node.children[0]? | return none
  let some child := tree.nodes.get childIndex | return none
  let mut compatible := true
  for segment in tree.locations.iterAll do
    let parentPermission := (segment.data.perms.get index).map Tree.LocationState.permission
      |>.getD node.defaultInitialPermission
    let childPermission := (segment.data.perms.get childIndex).map Tree.LocationState.permission
      |>.getD child.defaultInitialPermission
    if !Permission.canBeReplacedByChild parentPermission childPermission then
      compatible := false
  if compatible then return some childIndex else return none

/-- Source `Tree::remove_useless_node`, removing the index from the node map,
every range's permission and exposure maps, then the reusable tag map. -/
private def removeUselessNode (tree : BorrowTree) (index : UniIndex) :
    BorrowTree × Except TreeGcError Unit := Id.run do
  let some node := tree.nodes.get index
    | return (tree, .error (.MissingNode index))
  let nodes := tree.nodes.remove index
  let locations := tree.locations.modifyAll fun _ location => {
    location with
    perms := location.perms.remove index
    exposedCache := location.exposedCache.remove index
  }
  let tagMapping := tree.tagMapping.remove node.tag
  return ({ tree with nodes, locations, tagMapping }, .ok ())

/-- Iterative postorder counterpart of `Tree::remove_useless_children`. The
explicit stack avoids Lean recursion limits and retains source child order.
Malformed indexes/cycles become results, preserving prior mutations. -/
private def removeUselessChildren (tree : BorrowTree) (root : UniIndex)
    (liveTags : Array Miri.Memory.BorTag) : TreeGcResult := Id.run do
  let mut current := tree
  let mut stack : Array (UniIndex × Nat) := #[(root, 0)]
  let mut steps := 0
  while !stack.isEmpty do
    steps := steps + 1
    if steps > current.nodes.size * 2 + 1 then
      return { tree := current, outcome := .error (.ParentCycle root) }
    let some (index, nthChild) := stack.back?
      | return { tree := current, outcome := .error (.EmptyTraversalStack root) }
    let some node := current.nodes.get index
      | return { tree := current, outcome := .error (.MissingNode index) }
    if nthChild < node.children.size then
      let some child := node.children[nthChild]?
        | return { tree := current, outcome := .error (.MissingChildPosition index nthChild) }
      let rest := stack.pop.push (index, nthChild + 1)
      stack := rest.push (child, 0)
    else
      let originalChildren := node.children
      let mut keptChildren : Array UniIndex := #[]
      for childIndex in originalChildren do
        if nodeIsUseless current childIndex liveTags then
          let (next, outcome) := removeUselessNode current childIndex
          current := next
          match outcome with
          | .error error => return { tree := current, outcome := .error error }
          | .ok () => pure ()
        else
          match replacementChild? current childIndex liveTags with
          | none => keptChildren := keptChildren.push childIndex
          | some replacement =>
              let (next, outcome) := removeUselessNode current childIndex
              current := next
              match outcome with
              | .error error => return { tree := current, outcome := .error error }
              | .ok () => pure ()
              let some replacementNode := current.nodes.get replacement
                | return { tree := current, outcome := .error (.MissingReplacementChild replacement) }
              let replacementNode := { replacementNode with parent := some index }
              let updatedNodes := current.nodes.insert replacement replacementNode
              current := { current with nodes := updatedNodes }
              keptChildren := keptChildren.push replacement
      let some currentNode := current.nodes.get index
        | return { tree := current, outcome := .error (.MissingNode index) }
      let currentNode := { currentNode with children := keptChildren }
      let updatedNodes := current.nodes.insert index currentNode
      current := { current with nodes := updatedNodes }
      stack := stack.pop
  return { tree := current, outcome := .ok () }

/-- Tags reported by source `VisitProvenance for Tree`: all roots and every
exposed node whose provenance may still permit an access. -/
def provenanceTags (tree : BorrowTree) : Array Miri.Memory.BorTag := Id.run do
  let mut tags := #[]
  for root in tree.roots do
    if let some node := tree.nodes.get root then tags := tags.push node.tag
  for (_, node) in tree.nodes.entries do
    if node.isExposed then tags := tags.push node.tag
  return tags

/-- Source `Tree::remove_unreachable_tags`: process each ordered root with
postorder leaf removal and safe single-child collapse, then thoroughly merge
adjacent equal location ranges. -/
def removeUnreachableTags (tree : BorrowTree)
    (liveTags : Array Miri.Memory.BorTag) : TreeGcResult := Id.run do
  let mut current := tree
  for root in tree.roots do
    let result := removeUselessChildren current root liveTags
    current := result.tree
    match result.outcome with
    | .error error => return { tree := current, outcome := .error error }
    | .ok () => pure ()
  -- Rust's `UniValMap::PartialEq` ignores trailing `None` values. Canonicalize
  -- the nested maps before the range map's structural equality check.
  current := { current with locations := current.locations.modifyAll fun _ loc =>
    trimLocationForRangeEquality loc }
  let merged := current.locations.mergeAdjacentThorough
  current := { current with locations := merged.state }
  match merged.outcome with
  | .error error => return { tree := current, outcome := .error (.RangeMerge error) }
  | .ok () => return { tree := current, outcome := .ok () }

structure BorrowTreeLocationResult where
  range : ByteRange
  normalAccess : Option Tree.NormalAccessResult
  deriving DecidableEq, Repr

inductive BorrowTreeAccessStatus where
  | Completed
  | MissingTag (tag : Miri.Memory.BorTag)
  | MultipleRoots (count : Nat)
  | RangeMapFailure (error : DedupRangeMapError)
  | LocationMapFailure (range : ByteRange) (error : DedupRangeMapError)
  | CacheFailure (range : ByteRange) (error : ExposedCacheError)
  | AccessFailure (range : ByteRange) (status : Tree.NormalAccessStatus)
  | WildcardFailure (range : ByteRange) (status : WildcardAccessStatus)
  deriving DecidableEq, Repr

structure BorrowTreeAccessResult where
  tree : BorrowTree
  locations : Array BorrowTreeLocationResult
  status : BorrowTreeAccessStatus
  deriving DecidableEq, Repr

inductive BorrowTreeDeallocStatus where
  | Deallocated
  | AccessFailure (status : BorrowTreeAccessStatus)
  | MultipleRoots (count : Nat)
  | MissingTag (tag : Miri.Memory.BorTag)
  | RangeMapFailure (error : DedupRangeMapError)
  | ProtectedDealloc (range : ByteRange) (node : UniIndex)
  deriving DecidableEq, Repr

structure BorrowTreeDeallocResult where
  tree : BorrowTree
  status : BorrowTreeDeallocStatus
  deriving DecidableEq, Repr

private structure TreeLocationAccessAtResult where
  location : LocationTree
  normalAccess : Option Tree.NormalAccessResult
  status : Option BorrowTreeAccessStatus

/-- Apply the source LocationTree::perform_access order: first the concrete
source tree, then each other root as a wildcard subtree. None provenance
starts with wildcard accesses on all roots.
-/
private def performTreeAccessAt (tree : BorrowTree) (location : LocationTree)
    (source? : Option UniIndex) (kind : AccessKind) (protectedTags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (range : ByteRange) : TreeLocationAccessAtResult := Id.run do
  let mut currentLocation := location
  let mut normalAccess : Option Tree.NormalAccessResult := none
  let mut accessedRoot? : Option UniIndex := none
  let mut status : Option BorrowTreeAccessStatus := none
  if let some source := source? then
    let normal := tree.performNormalAccessAt currentLocation source kind protectedTags mode
    currentLocation := normal.location
    normalAccess := some normal.access
    match normal.outcome with
    | .error error =>
        return ⟨currentLocation, normalAccess, some (.CacheFailure range error)⟩
    | .ok () =>
        if normal.access.status != .Completed then
          return ⟨currentLocation, normalAccess,
            some (.AccessFailure range normal.access.status)⟩
        match UniIndex.ofNat? normal.access.root with
        | none =>
            return ⟨currentLocation, normalAccess,
              some (.AccessFailure range (.MissingLocationState normal.access.root))⟩
        | some root => accessedRoot? := some root
  let maxLocalTag := accessedRoot?.bind fun root => (tree.nodes.get root).map TreeNode.tag
  let minExposed := if mode == .SkipChildrenOfAccessed then
      source?.bind (minExposedChild tree)
    else none
  let mut stopOtherRoots := false
  for rootPosition in [:tree.roots.size] do
    if status.isNone && !stopOtherRoots then
      match tree.roots[rootPosition]? with
      | none => pure ()
      | some root =>
          let rootTag := (tree.nodes.get root).map TreeNode.tag
          let pastMinExposed := match rootTag, minExposed with
            | some tag, some minimum => tag.value > minimum.value
            | _, _ => false
          if mode == .SkipChildrenOfAccessed && pastMinExposed then
            stopOtherRoots := true
          else if accessedRoot? != some root then
            let wildcard := tree.performWildcardAccessAt currentLocation root
              maxLocalTag kind protectedTags (rootPosition != 0)
            currentLocation := wildcard.location
            if wildcard.status != .Completed then
              status := some (.WildcardFailure range wildcard.status)
  return ⟨currentLocation, normalAccess, status⟩

/-- Ranged access for concrete or wildcard provenance. Tree state and
Willard-cache updates are threaded across homogeneous range segments and all
ordered roots.
-/
def performBorrowAccessRange (tree : BorrowTree)
    (provenance : Miri.Memory.ProvenanceExtra) (offset length : Size)
    (kind : AccessKind) (protectedTags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) : BorrowTreeAccessResult := Id.run do
  let source? := match provenance with
    | .concrete tag => tree.indexOfTag tag
    | .wildcard => none
  match provenance with
  | .concrete tag =>
      if source?.isNone then
        return { tree, locations := #[], status := .MissingTag tag }
  | .wildcard => pure ()
  let prepared := tree.locations.iterMut offset length
  let mut currentMap := prepared.state
  let mut currentTree := tree
  let mut visited : Array BorrowTreeLocationResult := #[]
  let mut status := BorrowTreeAccessStatus.Completed
  match prepared.outcome with
  | .error error => status := .RangeMapFailure error
  | .ok _ =>
      for cursor in [:prepared.positions.size] do
        if status == .Completed then
          match prepared.positions[cursor]?, prepared.segments[cursor]? with
          | some position, some segment =>
              let access := currentTree.performTreeAccessAt segment.data source? kind
                protectedTags mode segment.range
              let mutation := currentMap.setAtPos position access.location
              currentMap := mutation.state
              visited := visited.push ⟨segment.range, access.normalAccess⟩
              match mutation.outcome with
              | .error error => status := .LocationMapFailure segment.range error
              | .ok () =>
                  match access.status with
                  | some failure => status := failure
                  | none => pure ()
          | _, _ =>
              status := .RangeMapFailure
                (.indexOutOfBounds cursor prepared.positions.size)
  currentTree := { currentTree with locations := currentMap }
  return { tree := currentTree, locations := visited, status }

/-- Concrete-tag convenience wrapper over the full source-root access path. -/
def performNormalAccessRange (tree : BorrowTree) (tag : Miri.Memory.BorTag)
    (offset length : Size) (kind : AccessKind) (protectedTags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) : BorrowTreeAccessResult :=
  tree.performBorrowAccessRange (.concrete tag) offset length kind protectedTags mode

inductive ProtectorReleaseStatus where
  | Released
  | MissingTag (tag : Miri.Memory.BorTag)
  | RangeMapFailure (error : DedupRangeMapError)
  | LocationMapFailure (error : DedupRangeMapError)
  | AccessFailure (range : ByteRange) (status : BorrowTreeAccessStatus)
  | ExposureUpdateFailure (error : TreeMutationError)
  deriving DecidableEq, Repr

structure ProtectorReleaseResult where
  tree : BorrowTree
  status : ProtectorReleaseStatus
  deriving DecidableEq, Repr

/-- Source Tree::perform_protector_end_access followed by
update_exposure_for_protector_release. The tag remains protected during its
implicit accessed-location read/write, and the caller removes the global
protector only after this operation succeeds.
-/
def releaseProtector (tree : BorrowTree) (tag : Miri.Memory.BorTag)
    (protectedTags : ProtectedTags) : ProtectorReleaseResult := Id.run do
  let some source := tree.indexOfTag tag
    | return { tree, status := .MissingTag tag }
  let mut currentTree := tree
  for position in [:tree.locations.entries.size] do
    match currentTree.locations.index position with
    | .error error =>
        return { tree := currentTree, status := .RangeMapFailure error }
    | .ok segment =>
        match segment.data.perms.get source with
        | none => pure ()
        | some state =>
            match state.permission.associatedAccess with
            | none => pure ()
            | some kind =>
                if state.accessed then
                  let access := currentTree.performTreeAccessAt segment.data (some source) kind
                    protectedTags .SkipChildrenOfAccessed segment.range
                  let mutation := currentTree.locations.setAtPos position access.location
                  currentTree := { currentTree with locations := mutation.state }
                  match mutation.outcome with
                  | .error error =>
                      return { tree := currentTree, status := .LocationMapFailure error }
                  | .ok () =>
                      match access.status with
                      | some status =>
                          return ⟨currentTree, .AccessFailure segment.range status⟩
                      | none => pure ()
  let exposure := currentTree.updateExposureForProtectorRelease tag
  match exposure.outcome with
  | .error error =>
      return { tree := exposure.tree, status := .ExposureUpdateFailure error }
  | .ok () => return { tree := exposure.tree, status := .Released }

/-- Source `Tree::dealloc` for a single concrete root: first perform the write
through the supplied tag, then inspect visited nodes in source tree-visitor
order for accessed strong protectors. Cell permissions are exempt. Weak
protectors are handled by the initial write transition itself.
-/
def deallocateBorrowRange (tree : BorrowTree)
    (provenance : Miri.Memory.ProvenanceExtra)
    (offset length : Size) (protectedTags : ProtectedTags) : BorrowTreeDeallocResult := Id.run do
  let accessed := tree.performBorrowAccessRange provenance offset length .Write protectedTags
    .VisitChildrenOfAccessed
  if accessed.status != .Completed then
    return { tree := accessed.tree, status := .AccessFailure accessed.status }
  -- `Tree::dealloc` checks the concrete provenance tag itself first. The
  -- normal access result's root is deliberately not used here: starting at
  -- the root changes the visitor's local-access prefix and protector error
  -- precedence when the provenance tag is an interior node.
  let startIndex? := match provenance with
    | .concrete tag => accessed.tree.indexOfTag tag
    | .wildcard => none
  if let .concrete tag := provenance then
    if startIndex?.isNone then
      return { tree := accessed.tree, status := .MissingTag tag }
  let prepared := accessed.tree.locations.iterMut offset length
  let mut currentMap := prepared.state
  match prepared.outcome with
  | .error error =>
      let updatedTree := { accessed.tree with locations := currentMap }
      return { tree := updatedTree, status := .RangeMapFailure error }
  | .ok () =>
      for cursor in [:prepared.positions.size] do
        match prepared.positions[cursor]?, prepared.segments[cursor]? with
        | some position, some segment =>
            let topology := traversalProjection accessed.tree
            let mut foundProtected : Option UniIndex := none
            let mut accessedRoot? : Option UniIndex := none
            -- The source visitor first traverses the concrete tag and its
            -- ancestors, then deferred descendants/cousins. Its returned
            -- root is the one excluded from the subsequent reverse-root pass.
            if let some startIndex := startIndex? then
              let traversal := Tree.TraversalTree.traverse topology startIndex.toNat
                .VisitChildrenOfAccessed []
              accessedRoot? := UniIndex.ofNat? traversal.1
              for event in traversal.2 do
                if foundProtected.isNone then
                  match UniIndex.ofNat? event.node with
                  | none => pure ()
                  | some index =>
                      match accessed.tree.nodeAt index with
                      | none => pure ()
                      | some node =>
                          let permission := segment.data.perms.get index
                            |>.getD node.defaultLocationState
                          if protectedTags.get node.tag == some .StrongProtector &&
                              !permission.permission.isCell && permission.accessed then
                            foundProtected := some index
            for root in accessed.tree.roots.reverse do
              if accessedRoot? != some root && foundProtected.isNone then
                let events := (Tree.TraversalTree.traverse topology root.toNat
                  .VisitChildrenOfAccessed []).2
                for event in events do
                  if foundProtected.isNone then
                    match UniIndex.ofNat? event.node with
                    | none => pure ()
                    | some index =>
                        match accessed.tree.nodeAt index with
                        | none => pure ()
                        | some node =>
                            let permission := segment.data.perms.get index
                              |>.getD node.defaultLocationState
                            if protectedTags.get node.tag == some .StrongProtector &&
                                !permission.permission.isCell && permission.accessed then
                              foundProtected := some index
            if let some index := foundProtected then
              let updatedTree := { accessed.tree with locations := currentMap }
              return ⟨updatedTree, .ProtectedDealloc segment.range index⟩
            match currentMap.index position with
            | .error error =>
                let updatedTree := { accessed.tree with locations := currentMap }
                return { tree := updatedTree, status := .RangeMapFailure error }
            | .ok _ => pure ()
        | _, _ =>
            let updatedTree := { accessed.tree with locations := currentMap }
            return ⟨updatedTree,
              .RangeMapFailure (.indexOutOfBounds cursor prepared.positions.size)⟩
  let updatedTree := { accessed.tree with locations := currentMap }
  return { tree := updatedTree, status := .Deallocated }

/-- Concrete-tag convenience wrapper for source Tree::dealloc. -/
def deallocateRange (tree : BorrowTree) (tag : Miri.Memory.BorTag)
    (offset length : Size) (protectedTags : ProtectedTags) : BorrowTreeDeallocResult :=
  tree.deallocateBorrowRange (.concrete tag) offset length protectedTags

@[simp] theorem new_root_node (rootTag : Miri.Memory.BorTag) (size : Size) :
    (BorrowTree.new rootTag size).nodes.get ⟨0⟩ = some {
      tag := rootTag
      parent := none
      children := #[]
      defaultInitialPermission := .newDisabled
      defaultInitialSifa := .None
      isExposed := false
    } := by
  simp [BorrowTree.new, rootIndex, UniValMap.insert, UniValMap.extendTo,
    UniValMap.get, UniIndex.toNat]

@[simp] theorem new_root_is_only_tree_root (rootTag : Miri.Memory.BorTag)
    (size : Size) : (BorrowTree.new rootTag size).roots = #[⟨0⟩] := by
  rfl

theorem new_one_byte_root_is_accessed_unique :
    (((BorrowTree.new Miri.Memory.BorTag.one (Size.ofBytes 1)).locations.iterAll[0]?).map
      fun segment => segment.data.perms.get ⟨0⟩) = some (some ⟨.Unique, true, .None⟩) := by
  decide


/-! Zero-byte protected child construction from finite graph and allocator
invariants. These proof-only declarations do not change the interpreter.
The rank and loop lemmas are adapted from PR35/38 generic Tree Borrows proofs. -/

namespace ZeroProtection
open Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
open Lean Elab Tactic in
elab "name_ancestor_loop" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun expr => expr.isAppOf ``Lean.Loop.forIn)
      | throwError "no Loop.forIn found"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (← Lean.Meta.inferType body) body
    let (scan, goal) ← goal.intro1P
    let target ← goal.getType
    let target := target.replace fun expr =>
      if expr == body then some (mkFVar scan) else none
    return [← goal.change target]
/-- A source while-loop invariant with a well-founded data measure. -/
theorem loop_invariant {β : Type} (scan : Unit → β → Id (ForInStep β))
    (measure : β → Nat) (property : β → Prop)
    (step : ∀ state, property state →
      (∃ final, scan () state = .done final ∧ property final) ∨
      ∃ next, scan () state = .yield next ∧ property next ∧ measure next < measure state)
    (initial : β) (valid : property initial) :
    property (Lean.Loop.forIn {} initial scan) := by
  have sound : ∀ bound state, measure state = bound → property state →
      property (Lean.Loop.forIn {} state scan) := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
      intro state measured valid
      rw [Lean.Loop.forIn_eq_of_monadTail]
      rcases step state valid with done | more
      · obtain ⟨final,actual,preserved⟩ := done
        simpa only [actual,bind,pure] using preserved
      · obtain ⟨next,actual,preserved,smaller⟩ := more
        simp only [actual,bind]
        exact ih (measure next) (by omega) next rfl preserved
  exact sound (measure initial) initial rfl valid
structure ParentDepth (nodes : UniValMap TreeNode) where
  depth : UniIndex → Nat
  bounded : ∀ index node, nodes.get index = some node → depth index ≤ nodes.size
  parent : ∀ index node, nodes.get index = some node → ∀ before, node.parent = some before →
    ∃ earlier, nodes.get before = some earlier ∧ depth before < depth index
theorem index_injective (left right : UniIndex) (same : left.toNat = right.toNat) : left = right := by
  cases left with
  | mk left =>
    cases right with
    | mk right =>
      exact congrArg UniIndex.mk (UInt32.toNat_inj.mp same)

theorem lookup_valid {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
    (present : nodes.get index = some value) : index.toNat < nodes.data.size := by
  unfold UniValMap.get at present
  cases source : nodes.data[index.toNat]? with
  | none => simp [source] at present
  | some old => exact (Array.getElem?_eq_some_iff.mp source).1

theorem insert_existing {α : Type} (nodes : UniValMap α) (index : UniIndex) (old next : α)
    (present : nodes.get index = some old) :
    (nodes.insert index next).data = nodes.data.set index.toNat (some next) (lookup_valid nodes index old present) := by
  have valid := lookup_valid nodes index old present
  have noExtra : index.toNat + 1 - nodes.data.size = 0 := by omega
  simp [UniValMap.insert,UniValMap.extendTo,noExtra,valid,Id.run,pure]

theorem insert_existing_get_same {α : Type} (nodes : UniValMap α) (index : UniIndex) (old next : α)
    (present : nodes.get index = some old) : (nodes.insert index next).get index = some next := by
  unfold UniValMap.get
  rw [insert_existing nodes index old next present]
  simp

theorem insert_existing_get_other {α : Type} (nodes : UniValMap α) (index query : UniIndex) (old next : α)
    (present : nodes.get index = some old) (different : query ≠ index) :
    (nodes.insert index next).get query = nodes.get query := by
  have differentNat : query.toNat ≠ index.toNat := fun same => different (index_injective query index same)
  unfold UniValMap.get
  rw [insert_existing nodes index old next present]
  simp [Ne.symm differentNat]

theorem insert_existing_size {α : Type} (nodes : UniValMap α) (index : UniIndex) (old next : α)
    (present : nodes.get index = some old) : (nodes.insert index next).size = nodes.size := by
  unfold UniValMap.size
  rw [insert_existing nodes index old next present]
  simp

/-- Changing non-parent node metadata preserves the real exposed-cache
ancestor certificate and its depth function. -/
def update_depth (nodes : UniValMap TreeNode) (depth : ParentDepth nodes) (index : UniIndex)
    (old next : TreeNode) (present : nodes.get index = some old) (sameParent : next.parent = old.parent) :
    ParentDepth (nodes.insert index next) where
  depth := depth.depth
  bounded := by
    intro query node lookup
    rw [insert_existing_size nodes index old next present]
    by_cases same : query = index
    · subst query
      rw [insert_existing_get_same nodes index old next present] at lookup
      cases lookup
      exact depth.bounded index old present
    · rw [insert_existing_get_other nodes index query old next present same] at lookup
      exact depth.bounded query node lookup
  parent := by
    intro query node lookup before parentEq
    have original : ∃ original, nodes.get query = some original ∧ original.parent = node.parent := by
      by_cases same : query = index
      · subst query
        rw [insert_existing_get_same nodes index old next present] at lookup
        cases lookup
        exact ⟨old,present,sameParent.symm⟩
      · rw [insert_existing_get_other nodes index query old next present same] at lookup
        exact ⟨node,lookup,rfl⟩
    obtain ⟨original,originalLookup,parentSame⟩ := original
    obtain ⟨ancestor,ancestorLookup,smaller⟩ := depth.parent query original originalLookup before (parentSame.trans parentEq)
    by_cases same : before = index
    · subst before
      exact ⟨next,insert_existing_get_same nodes index old next present,smaller⟩
    · exact ⟨ancestor,(insert_existing_get_other nodes index before old next present same).trans ancestorLookup,smaller⟩
abbrev LoopState := Option (BorrowTree × Except BorrowTree.ChildInsertError Unit) × BorrowTree × Option UniIndex × Nat × Bool

def weakened (tree : BorrowTree) (index : UniIndex) (node : TreeNode) (strongest : IdempotentForeignAccess) : BorrowTree :=
  {tree with
    locations := (tree.locations.modifyAll fun _ location =>
      match location.perms.get index with
      | none => location
      | some state => {location with perms := location.perms.insert index ({state with idempotentForeignAccess := (state.idempotentForeignAccess.ensureNoStrongerThan strongest).1})})
    nodes := tree.nodes.insert index
      ({node with defaultInitialSifa := (node.defaultInitialSifa.ensureNoStrongerThan strongest).1})}

def changed (tree : BorrowTree) (index : UniIndex) (node : TreeNode) (strongest : IdempotentForeignAccess) : Bool := Id.run do
  let mut result := (node.defaultInitialSifa.ensureNoStrongerThan strongest).2
  for segment in tree.locations.iterAll do
    if let some state := segment.data.perms.get index then
      result := result || (state.idempotentForeignAccess.ensureNoStrongerThan strongest).2
  return result

def Good (depth : UniIndex → Nat) (state : LoopState) : Prop :=
  state.1 = none ∧ ∃ certificate : ParentDepth state.2.1.nodes,
    certificate.depth = depth ∧ state.2.2.2.1 ≤ state.2.1.nodes.size ∧
      (state.2.2.2.2 = true → ∀ index, state.2.2.1 = some index → ∃ node,
        state.2.1.nodes.get index = some node ∧ state.2.2.2.1 + depth index < state.2.1.nodes.size)

def Measure (depth : UniIndex → Nat) (state : LoopState) : Nat :=
  if state.2.2.2.2 then (state.2.2.1.map (fun index => depth index + 2)).getD 1 else 0

theorem succeeds (tree : BorrowTree) (depth : ParentDepth tree.nodes) (start : UniIndex)
    (node : TreeNode) (present : tree.nodes.get start = some node)
    (strict : depth.depth start < tree.nodes.size) (strongest : IdempotentForeignAccess) :
    (updateSifaAfterRetag tree start strongest).2 = .ok () := by
  unfold updateSifaAfterRetag
  split
  · rfl
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_ancestor_loop
    have step : ∀ state, Good depth.depth state →
        (∃ final, scan () state = .done final ∧ Good depth.depth final) ∨
        ∃ next, scan () state = .yield next ∧ Good depth.depth next ∧ Measure depth.depth next < Measure depth.depth state := by
      intro state good
      rcases state with ⟨returned,current,cursor,steps,active⟩
      rcases good with ⟨returnedEq,certificate,depthEq,stepsBound,live⟩
      dsimp only at returnedEq stepsBound
      subst returned
      cases active with
      | false => exact .inl ⟨_,rfl,⟨rfl,certificate,depthEq,stepsBound,by simp⟩⟩
      | true =>
        have notPast : ¬ steps > current.nodes.size := by omega
        cases cursor with
        | none =>
          refine .inr ⟨(none,current,none,steps,false),?_,⟨rfl,certificate,depthEq,stepsBound,by simp⟩,?_⟩
          · simp [scan,notPast]
          · simp [Measure]
        | some index =>
          obtain ⟨currentNode,lookup,strictBound⟩ := live rfl index rfl
          dsimp only at strictBound
          let nextNode := {currentNode with defaultInitialSifa := (currentNode.defaultInitialSifa.ensureNoStrongerThan strongest).1}
          let nextTree := weakened current index currentNode strongest
          let nextCertificate := update_depth current.nodes certificate index currentNode nextNode lookup rfl
          have nextDepth : nextCertificate.depth = depth.depth := depthEq
          have sameSize : nextTree.nodes.size = current.nodes.size := insert_existing_size current.nodes index currentNode nextNode lookup
          have parentPresent : ∀ before, currentNode.parent = some before → ∃ earlier,
              nextTree.nodes.get before = some earlier ∧ depth.depth before < depth.depth index := by
            intro before edge
            obtain ⟨earlier,earlierLookup,smaller⟩ := nextCertificate.parent index nextNode
              (insert_existing_get_same current.nodes index currentNode nextNode lookup) before edge
            rw [nextDepth] at smaller
            exact ⟨earlier,earlierLookup,smaller⟩
          cases actualChanged : changed current index currentNode strongest with
          | false =>
            have actual : scan () (none,current,some index,steps,true) = .yield (none,nextTree,some index,steps,false) := by
              simp only [scan,ite_eq_left rfl,ite_eq_right notPast,lookup]
              change (if changed current index currentNode strongest then _ else _) = _
              rw [actualChanged]
              rfl
            refine .inr ⟨_,actual,⟨rfl,nextCertificate,nextDepth,?_,by simp⟩,?_⟩
            · rw [sameSize]; exact stepsBound
            · simp [Measure]
          | true =>
            have actual : scan () (none,current,some index,steps,true) = .yield (none,nextTree,currentNode.parent,steps+1,true) := by
              simp only [scan,ite_eq_left rfl,ite_eq_right notPast,lookup]
              change (if changed current index currentNode strongest then _ else _) = _
              rw [actualChanged]
              rfl
            refine .inr ⟨_,actual,⟨rfl,nextCertificate,nextDepth,?_,?_⟩,?_⟩
            · dsimp only; rw [sameSize]; omega
            · intro active before edge
              obtain ⟨earlier,earlierLookup,smaller⟩ := parentPresent before edge
              exact ⟨earlier,earlierLookup,by dsimp; rw [sameSize]; omega⟩
            · cases parentEq : currentNode.parent with
              | none => simp [Measure]
              | some before =>
                have smaller := (parentPresent before parentEq).choose_spec.2
                simp only [Measure,↓reduceIte,Option.map_some,Option.getD_some]
                omega
    have initial : Good depth.depth (none,tree,some start,0,true) := by
      refine ⟨rfl,depth,rfl,by simp,?_⟩
      intro active index same
      have indexEq : index = start := Option.some.inj same.symm
      subst index
      exact ⟨node,present,by simpa using strict⟩
    have maintained := loop_invariant scan (Measure depth.depth) (Good depth.depth) step _ initial
    rw [maintained.1]

namespace Append
/-- The append-index branch of the actual newChild node insertion. Existing
node data and parent depth are arbitrary; free-index reuse is a separate case. -/
theorem insert_append {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
 (atEnd : index.toNat = nodes.data.size) :
 (nodes.insert index value).data = nodes.data.push (some value) := by
 simp [UniValMap.insert,UniValMap.extendTo,atEnd,Id.run,pure,Array.set_push]
theorem append_size {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
 (atEnd : index.toNat = nodes.data.size) : (nodes.insert index value).size = nodes.size+1 := by
 unfold UniValMap.size
 rw [insert_append nodes index value atEnd]
 simp
theorem append_get_same {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
 (atEnd : index.toNat = nodes.data.size) : (nodes.insert index value).get index = some value := by
 unfold UniValMap.get
 rw [insert_append nodes index value atEnd]
 simp [atEnd]
theorem append_get_other {α : Type} (nodes : UniValMap α) (index query : UniIndex) (value : α)
 (atEnd : index.toNat = nodes.data.size) (different : query ≠ index) :
 (nodes.insert index value).get query = nodes.get query := by
 have notEnd : query.toNat ≠ nodes.data.size := fun same => different (index_injective query index (same.trans atEnd.symm))
 unfold UniValMap.get
 rw [insert_append nodes index value atEnd]
 by_cases valid : query.toNat < nodes.data.size
 · simp [Array.getElem?_push,valid,notEnd]
 · simp [Array.getElem?_push,valid,notEnd]
def append_depth (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
 (index parent : UniIndex) (parentNode newNode : TreeNode)
 (atEnd : index.toNat = nodes.data.size)
 (parentPresent : nodes.get parent = some parentNode) (childParent : newNode.parent = some parent) :
 ParentDepth (nodes.insert index newNode) where
 depth := fun query => if query = index then before.depth parent + 1 else before.depth query
 bounded := by
   intro query node lookup
   rw [append_size nodes index newNode atEnd]
   by_cases same : query = index
   · subst query
     simp only [ite_true]
     have bound := before.bounded parent parentNode parentPresent
     omega
   · simp only [same,ite_false]
     rw [append_get_other nodes index query newNode atEnd same] at lookup
     have bound := before.bounded query node lookup
     omega
 parent := by
   intro query node lookup earlier edge
   have parentNotNew : parent ≠ index := by
     intro same
     have bound := lookup_valid nodes parent parentNode parentPresent
     rw [same,atEnd] at bound
     omega
   by_cases same : query = index
   · subst query
     rw [append_get_same nodes index newNode atEnd] at lookup
     cases lookup
     have earlierEq : earlier = parent := Option.some.inj (edge.symm.trans childParent)
     subst earlier
     refine ⟨parentNode,(append_get_other nodes index parent newNode atEnd parentNotNew).trans parentPresent,?_⟩
     simp only [parentNotNew,ite_false,ite_true]
     omega
   · rw [append_get_other nodes index query newNode atEnd same] at lookup
     obtain ⟨ancestor,present,smaller⟩ := before.parent query node lookup earlier edge
     have earlierNotNew : earlier ≠ index := by
       intro equal
       have bound := lookup_valid nodes earlier ancestor present
       rw [equal,atEnd] at bound
       omega
     refine ⟨ancestor,(append_get_other nodes index earlier newNode atEnd earlierNotNew).trans present,?_⟩
     simpa only [earlierNotNew,same,ite_false] using smaller


/-- The second source-ordered node insertion in newChild attaches the new
index to its parent's children, without changing either node's parent link. -/
def attachedNodes (nodes : UniValMap TreeNode) (index parent : UniIndex)
    (parentNode newNode : TreeNode) : UniValMap TreeNode :=
  (nodes.insert index newNode).insert parent {parentNode with children := parentNode.children.push index}

theorem parent_not_fresh (nodes : UniValMap TreeNode) (index parent : UniIndex) (parentNode : TreeNode)
    (atEnd : index.toNat = nodes.data.size) (parentPresent : nodes.get parent = some parentNode) : parent ≠ index := by
  intro same
  have valid := lookup_valid nodes parent parentNode parentPresent
  rw [same,atEnd] at valid
  omega

def attached_depth (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = nodes.data.size) (parentPresent : nodes.get parent = some parentNode)
    (childParent : newNode.parent = some parent) : ParentDepth (attachedNodes nodes index parent parentNode newNode) :=
  update_depth (nodes.insert index newNode)
    (append_depth nodes before index parent parentNode newNode atEnd parentPresent childParent)
    parent parentNode {parentNode with children := parentNode.children.push index}
    ((append_get_other nodes index parent newNode atEnd (parent_not_fresh nodes index parent parentNode atEnd parentPresent)).trans parentPresent) rfl

theorem attached_parent_strict (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = nodes.data.size) (parentPresent : nodes.get parent = some parentNode)
    (childParent : newNode.parent = some parent) :
    (attached_depth nodes before index parent parentNode newNode atEnd parentPresent childParent).depth parent <
      (attachedNodes nodes index parent parentNode newNode).size := by
  have different := parent_not_fresh nodes index parent parentNode atEnd parentPresent
  have lookup := (append_get_other nodes index parent newNode atEnd different).trans parentPresent
  change (if parent = index then before.depth parent+1 else before.depth parent) < _
  simp only [different,ite_false]
  unfold attachedNodes
  rw [insert_existing_size (nodes.insert index newNode) parent parentNode _ lookup,
    append_size nodes index newNode atEnd]
  have bound := before.bounded parent parentNode parentPresent
  omega

/-- The real ancestor-SIFA stage invoked by newChild succeeds after its two
actual node insertions. The new index and original parent's presence are data
conditions; no successful child insertion or SIFA update is a premise. -/
theorem sifa_after_attach (tree : BorrowTree) (before : ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodes.get parent = some parentNode)
    (childParent : newNode.parent = some parent) (strongest : IdempotentForeignAccess) :
    (updateSifaAfterRetag
      {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode} parent strongest).2 = .ok () := by
  let nodes := tree.nodes.insert index newNode
  let updatedParent := {parentNode with children := parentNode.children.push index}
  have lookup : nodes.get parent = some parentNode :=
    (append_get_other tree.nodes index parent newNode atEnd
      (parent_not_fresh tree.nodes index parent parentNode atEnd parentPresent)).trans parentPresent
  let current : BorrowTree := {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
  let certificate : ParentDepth current.nodes := by
    dsimp only [current]
    exact attached_depth tree.nodes before index parent parentNode newNode atEnd parentPresent childParent
  have present : current.nodes.get parent = some updatedParent := by
    dsimp only [current,attachedNodes,updatedParent]
    exact insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode
      {parentNode with children := parentNode.children.push index} lookup
  have strict : certificate.depth parent < current.nodes.size := by
    dsimp only [certificate,current]
    exact attached_parent_strict tree.nodes before index parent parentNode newNode atEnd parentPresent childParent
  change (updateSifaAfterRetag current parent strongest).2 = .ok ()
  exact ZeroProtection.succeeds current certificate parent updatedParent present strict strongest

end Append

namespace Sparse
/-- Extending a sparse location map with absent entries preserves every lookup,
including queries beyond both its old and new extents. -/
theorem extend_get {α : Type} (map : UniValMap α) (length : Nat) (index : UniIndex) :
    (⟨UniValMap.extendTo map.data length⟩ : UniValMap α).get index = map.get index := by
  unfold UniValMap.get UniValMap.extendTo
  rw [Array.getElem?_append]
  by_cases valid : index.toNat < map.data.size
  · simp only [valid,↓reduceIte]
  · have absent : map.data[index.toNat]? = none := Array.getElem?_eq_none (by omega)
    simp only [valid,↓reduceIte,absent,Array.getElem?_replicate]
    by_cases inside : index.toNat-map.data.size < length-map.data.size <;> simp only [inside,↓reduceIte]

private theorem extended_bound {α : Type} (map : UniValMap α) (index : UniIndex) :
    index.toNat < (UniValMap.extendTo map.data (index.toNat+1)).size := by
  simp only [UniValMap.extendTo,Array.size_append,Array.size_replicate]
  omega

private theorem inserted_data {α : Type} (map : UniValMap α) (index : UniIndex) (value : α) :
    (map.insert index value).data =
      (UniValMap.extendTo map.data (index.toNat+1)).set index.toNat (some value) (extended_bound map index) := by
  simp only [UniValMap.insert,extended_bound map index,↓reduceDIte,Id.run,pure]

/-- The actual sparse-map insertion stores the new child's materialized state. -/
theorem get_same {α : Type} (map : UniValMap α) (index : UniIndex) (value : α) :
    (map.insert index value).get index = some value := by
  unfold UniValMap.get
  rw [inserted_data]
  simp

/-- Inserting the new child state preserves every other node's state even
when the per-location sparse array has a different length from the node table. -/
theorem get_other {α : Type} (map : UniValMap α) (index query : UniIndex) (value : α) (different : query ≠ index) :
    (map.insert index value).get query = map.get query := by
  have differentNat : query.toNat ≠ index.toNat := fun equal => different (index_injective query index equal)
  unfold UniValMap.get
  rw [inserted_data]
  simp only [Array.getElem?_set,Ne.symm differentNat,↓reduceIte]
  exact extend_get map (index.toNat+1) query


end Sparse

namespace Reuse
/-- Insertion at a bounded sparse slot retains the table length. Vacancy is a
separate caller condition: this operation itself also permits overwriting. -/
theorem insert_bounded {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
    (valid : index.toNat < nodes.data.size) :
    (nodes.insert index value).data = nodes.data.set index.toNat (some value) valid := by
  have noExtra : index.toNat+1-nodes.data.size = 0 := by omega
  simp [UniValMap.insert,UniValMap.extendTo,noExtra,valid,Id.run,pure]

theorem bounded_size {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
    (valid : index.toNat < nodes.data.size) : (nodes.insert index value).size = nodes.size := by
  unfold UniValMap.size
  rw [insert_bounded nodes index value valid]
  simp

theorem parent_not_vacant (nodes : UniValMap TreeNode) (index parent : UniIndex) (parentNode : TreeNode)
    (vacant : nodes.get index = none) (parentPresent : nodes.get parent = some parentNode) : parent ≠ index := by
  intro same
  rw [same,vacant] at parentPresent
  cases parentPresent

/-- A bounded vacant slot can hold a fresh child. The explicit rank slack
ensures the child's parent-rank-plus-one fits without enlarging the table.
Every old parent edge remains valid; none can point to the vacant slot. -/
def vacant_depth (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < nodes.data.size) (vacant : nodes.get index = none)
    (parentPresent : nodes.get parent = some parentNode) (childParent : newNode.parent = some parent)
    (parentSlack : before.depth parent < nodes.size) : ParentDepth (nodes.insert index newNode) where
  depth := fun query => if query = index then before.depth parent+1 else before.depth query
  bounded := by
    intro query node lookup
    rw [bounded_size nodes index newNode valid]
    by_cases same : query = index
    · subst query
      simp only [ite_true]
      omega
    · simp only [same,ite_false]
      rw [Sparse.get_other nodes index query newNode same] at lookup
      exact before.bounded query node lookup
  parent := by
    intro query node lookup earlier edge
    have parentNotNew := parent_not_vacant nodes index parent parentNode vacant parentPresent
    by_cases same : query = index
    · subst query
      rw [Sparse.get_same] at lookup
      cases lookup
      have earlierEq : earlier = parent := Option.some.inj (edge.symm.trans childParent)
      subst earlier
      refine ⟨parentNode,(Sparse.get_other nodes index parent newNode parentNotNew).trans parentPresent,?_⟩
      simp only [parentNotNew,ite_false,ite_true]
      omega
    · rw [Sparse.get_other nodes index query newNode same] at lookup
      obtain ⟨ancestor,present,smaller⟩ := before.parent query node lookup earlier edge
      have earlierNotNew : earlier ≠ index := by
        intro equal
        rw [equal,vacant] at present
        cases present
      refine ⟨ancestor,(Sparse.get_other nodes index earlier newNode earlierNotNew).trans present,?_⟩
      simpa only [earlierNotNew,same,ite_false] using smaller

/-- Both source node insertions preserve the depth certificate on a reusable
slot. No absence of per-location permissions is inferred from node vacancy. -/
def attached_depth (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < nodes.data.size) (vacant : nodes.get index = none)
    (parentPresent : nodes.get parent = some parentNode) (childParent : newNode.parent = some parent)
    (parentSlack : before.depth parent < nodes.size) :
    ParentDepth (Append.attachedNodes nodes index parent parentNode newNode) :=
  update_depth (nodes.insert index newNode)
    (vacant_depth nodes before index parent parentNode newNode valid vacant parentPresent childParent parentSlack)
    parent parentNode {parentNode with children := parentNode.children.push index}
    ((Sparse.get_other nodes index parent newNode
      (parent_not_vacant nodes index parent parentNode vacant parentPresent)).trans parentPresent) rfl

theorem attached_parent_strict (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < nodes.data.size) (vacant : nodes.get index = none)
    (parentPresent : nodes.get parent = some parentNode) (childParent : newNode.parent = some parent)
    (parentSlack : before.depth parent < nodes.size) :
    (attached_depth nodes before index parent parentNode newNode valid vacant parentPresent childParent parentSlack).depth parent <
      (Append.attachedNodes nodes index parent parentNode newNode).size := by
  have different := parent_not_vacant nodes index parent parentNode vacant parentPresent
  have lookup := (Sparse.get_other nodes index parent newNode different).trans parentPresent
  change (if parent = index then before.depth parent+1 else before.depth parent) < _
  simp only [different,ite_false]
  unfold Append.attachedNodes
  rw [insert_existing_size (nodes.insert index newNode) parent parentNode _ lookup,bounded_size nodes index newNode valid]
  exact parentSlack

theorem sifa_after_attach (tree : BorrowTree) (before : ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (parentPresent : tree.nodes.get parent = some parentNode) (childParent : newNode.parent = some parent)
    (parentSlack : before.depth parent < tree.nodes.size) (strongest : IdempotentForeignAccess) :
    (updateSifaAfterRetag {tree with nodes := Append.attachedNodes tree.nodes index parent parentNode newNode}
      parent strongest).2 = .ok () := by
  let current : BorrowTree := {tree with nodes := Append.attachedNodes tree.nodes index parent parentNode newNode}
  let updatedParent := {parentNode with children := parentNode.children.push index}
  let certificate : ParentDepth current.nodes := by
    dsimp only [current]
    exact attached_depth tree.nodes before index parent parentNode newNode valid vacant parentPresent childParent parentSlack
  have lookup := (Sparse.get_other tree.nodes index parent newNode
    (parent_not_vacant tree.nodes index parent parentNode vacant parentPresent)).trans parentPresent
  have present : current.nodes.get parent = some updatedParent := by
    dsimp only [current,Append.attachedNodes,updatedParent]
    exact insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode _ lookup
  have strict : certificate.depth parent < current.nodes.size := by
    dsimp only [certificate,current]
    exact attached_parent_strict tree.nodes before index parent parentNode newNode valid vacant parentPresent childParent parentSlack
  exact ZeroProtection.succeeds current certificate parent updatedParent present strict strongest

end Reuse

/-- Both concrete allocation branches of a zero-byte protected child complete
from raw parent, allocator and acyclic-graph facts. -/
theorem concrete_child (tree : BorrowTree) (depth : ParentDepth tree.nodes)
    (parentTag tag : Miri.Memory.BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.tagMapping.get parentTag = some parent)
    (present : tree.nodes.get parent = some parentNode)
    (fresh : tree.tagMapping.get tag = none)
    (room : tree.tagMapping.mapping.size ≤ 4294967295)
    (appendAligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.size)
    (reuseValid : ∀ index, tree.tagMapping.deassigned.back? = some index →
      index.toNat < tree.nodes.size ∧ tree.nodes.get index = none)
    (rank : depth.depth parent < tree.nodes.size)
    (offset : Size) (initial : Tree.LocationState) :
    ∃ after, tree.newChild offset (.concrete parentTag) tag
      (DedupRangeMap.new Size.ZERO initial) (.ReservedFrz false) true = ⟨after, .ok ()⟩ := by
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let mapping : UniKeyMap Miri.Memory.BorTag := {
      mapping := (tree.tagMapping.mapping.filter fun row => row.1 != tag).push (tag,index)
      deassigned := tree.tagMapping.deassigned }
    have inserted : tree.tagMapping.insert tag = .Inserted mapping index := by
      simp [UniKeyMap.insert, available, UniIndex.ofNat?, room, fresh, mapping, index]
    have atEnd : index.toNat = tree.nodes.data.size := by
      simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact appendAligned available
    let node : TreeNode := {
      tag := tag, parent := some parent, children := #[]
      defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None, isExposed := false }
    have success := Append.sifa_after_attach {tree with tagMapping := mapping} depth index parent parentNode node
      atEnd present rfl .None
    have different := Append.parent_not_fresh tree.nodes index parent parentNode atEnd present
    have lookup := (Append.append_get_other tree.nodes index parent node atEnd different).trans present
    unfold BorrowTree.newChild
    rw [inserted]
    simp only [tagged,Option.map_some,Bool.false_eq_true,↓reduceIte]
    simp only [Permission.isInitial,Permission.isUnique,Permission.strongestIdempotentForeignAccess,
      Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
    simp only [node] at lookup
    rw [lookup]
    simp only [DedupRangeMap.new, DedupRangeMap.iterAll, Size.ZERO, Size.ofBytes,
      beq_self_eq_true, ↓reduceIte, ← Array.forIn_toList, List.forIn_nil, pure]
    change ∃ after, (let result := (updateSifaAfterRetag
      {tree with tagMapping := mapping, nodes := Append.attachedNodes tree.nodes index parent parentNode node}
      parent .None); (⟨result.1,result.2⟩ : ChildInsertResult)) = ⟨after,.ok ()⟩
    exact ⟨_, congrArg (fun outcome => (⟨_,outcome⟩ : ChildInsertResult)) success⟩
  | some index =>
    let mapping : UniKeyMap Miri.Memory.BorTag := {
      mapping := (tree.tagMapping.mapping.filter fun row => row.1 != tag).push (tag,index)
      deassigned := tree.tagMapping.deassigned.pop }
    have inserted : tree.tagMapping.insert tag = .Inserted mapping index := by
      simp [UniKeyMap.insert, available, fresh, mapping]
    obtain ⟨bounded,vacant⟩ := reuseValid index available
    let node : TreeNode := {
      tag := tag, parent := some parent, children := #[]
      defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None, isExposed := false }
    have success := Reuse.sifa_after_attach {tree with tagMapping := mapping} depth index parent parentNode node
      bounded vacant present rfl rank .None
    have different := Reuse.parent_not_vacant tree.nodes index parent parentNode vacant present
    have lookup := (Sparse.get_other tree.nodes index parent node different).trans present
    unfold BorrowTree.newChild
    rw [inserted]
    simp only [tagged,Option.map_some,Bool.false_eq_true,↓reduceIte]
    simp only [Permission.isInitial,Permission.isUnique,Permission.strongestIdempotentForeignAccess,
      Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
    simp only [node] at lookup
    rw [lookup]
    simp only [DedupRangeMap.new, DedupRangeMap.iterAll, Size.ZERO, Size.ofBytes,
      beq_self_eq_true, ↓reduceIte, ← Array.forIn_toList, List.forIn_nil, pure]
    change ∃ after, (let result := (updateSifaAfterRetag
      {tree with tagMapping := mapping, nodes := Append.attachedNodes tree.nodes index parent parentNode node}
      parent .None); (⟨result.1,result.2⟩ : ChildInsertResult)) = ⟨after,.ok ()⟩
    exact ⟨_, congrArg (fun outcome => (⟨_,outcome⟩ : ChildInsertResult)) success⟩

namespace View
open Miri.Memory
abbrev StateShape := Permission × Bool
abbrev NodeShape := BorTag × Option UniIndex × Array UniIndex × Permission × Bool

def stateShape (state : LocationState) : StateShape := (state.permission,state.accessed)
def nodeShape (node : TreeNode) : NodeShape := (node.tag,node.parent,node.children,node.defaultInitialPermission,node.isExposed)
def locationShape (location : LocationTree) : Array (Option StateShape) := location.perms.data.map (Option.map stateShape)
def treeShape (tree : BorrowTree) :=
  (tree.tagMapping,tree.nodes.data.map (Option.map nodeShape),
    tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)),tree.roots)

theorem insert_existing_shape {α β : Type} (shape : α → β) (nodes : UniValMap α)
    (index : UniIndex) (old next : α) (present : nodes.get index = some old) (same : shape next = shape old) :
    (nodes.insert index next).data.map (Option.map shape) = nodes.data.map (Option.map shape) := by
  have valid := lookup_valid nodes index old present
  have slot : nodes.data[index.toNat] = some old := by
    simpa only [UniValMap.get,Array.getElem?_eq_getElem valid] using present
  rw [insert_existing nodes index old next present]
  apply Array.ext
  · simp
  · intro position left right
    simp only [Array.getElem_map,Array.getElem_set]
    by_cases equal : index.toNat = position
    · subst position
      simp [slot,same]
    · simp [equal]

def weakenLocation (location : LocationTree) (index : UniIndex) (strongest : IdempotentForeignAccess) : LocationTree :=
  match location.perms.get index with
  | none => location
  | some state => {location with perms := location.perms.insert index ({state with idempotentForeignAccess := (state.idempotentForeignAccess.ensureNoStrongerThan strongest).1})}

theorem weaken_location_shape (location : LocationTree) (index : UniIndex) (strongest : IdempotentForeignAccess) :
    locationShape (weakenLocation location index strongest) = locationShape location := by
  unfold weakenLocation
  cases present : location.perms.get index with
  | none => rfl
  | some state => exact insert_existing_shape stateShape location.perms index state _ present rfl

theorem weakened_tree_shape (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (strongest : IdempotentForeignAccess) :
    treeShape (weakened tree index node strongest) = treeShape tree := by
  have nodeEq := insert_existing_shape nodeShape tree.nodes index node
    {node with defaultInitialSifa := (node.defaultInitialSifa.ensureNoStrongerThan strongest).1} present rfl
  have locationsEq : ((weakened tree index node strongest).locations.entries.map
      (fun segment => (segment.range,locationShape segment.data))) =
      tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) := by
    apply Array.ext
    · simp [weakened,DedupRangeMap.modifyAll]
    · intro position left right
      have valid : position < tree.locations.entries.size := by simpa only [Array.size_map] using right
      simp only [weakened,DedupRangeMap.modifyAll,Array.getElem_map]
      exact congrArg (fun value => ((tree.locations.entries[position]'valid).range,value))
        (weaken_location_shape (tree.locations.entries[position]'valid).data index strongest)
  have actualNodeEq : (weakened tree index node strongest).nodes.data.map (Option.map nodeShape) =
      tree.nodes.data.map (Option.map nodeShape) := nodeEq
  change (tree.tagMapping,(weakened tree index node strongest).nodes.data.map (Option.map nodeShape),
    (weakened tree index node strongest).locations.entries.map
      (fun segment => (segment.range,locationShape segment.data)),tree.roots) =
    (tree.tagMapping,tree.nodes.data.map (Option.map nodeShape),
      tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)),tree.roots)
  rw [actualNodeEq,locationsEq]
def Preserves (before : BorrowTree) (state : LoopState) : Prop :=
  treeShape state.2.1 = treeShape before ∧
    ∀ returned, state.1 = some returned → treeShape returned.1 = treeShape before

def Measure (state : LoopState) : Nat :=
  if state.2.2.2.2 then (state.2.1.nodes.size+1-state.2.2.2.1)+1 else 0

/-- Even an error result changes no tag/topology/permission/accessed data in
this SIFA-only stage. This metadata fact is not an assertion of safe execution. -/
theorem preserves (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess) :
    treeShape (updateSifaAfterRetag tree start strongest).1 = treeShape tree := by
  unfold updateSifaAfterRetag
  split
  · rfl
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_ancestor_loop
    have step : ∀ state, Preserves tree state →
        (∃ final, scan () state = .done final ∧ Preserves tree final) ∨
        ∃ next, scan () state = .yield next ∧ Preserves tree next ∧ Measure next < Measure state := by
      intro state preserved
      rcases state with ⟨returned,current,cursor,steps,active⟩
      have currentShape : treeShape current = treeShape tree := preserved.1
      cases active with
      | false => exact .inl ⟨_,rfl,⟨currentShape,by simp⟩⟩
      | true =>
        by_cases past : steps > current.nodes.size
        · refine .inl ⟨(some (current,.error (.ParentCycle (cursor.getD start))),current,cursor,steps,true),?_,?_⟩
          · simp [scan,past]
          · exact ⟨currentShape,fun returned same => by cases same; exact currentShape⟩
        · cases cursor with
          | none =>
            refine .inr ⟨(none,current,none,steps,false),?_,⟨currentShape,by simp⟩,?_⟩
            · simp [scan,past]
            · simp [Measure]
          | some index =>
            cases lookup : current.nodes.get index with
            | none =>
              refine .inl ⟨(some (current,.error (.MissingNode index)),current,some index,steps,true),?_,?_⟩
              · simp [scan,past,lookup]
              · exact ⟨currentShape,fun returned same => by cases same; exact currentShape⟩
            | some node =>
              let nextTree := weakened current index node strongest
              have nextShape : treeShape nextTree = treeShape tree :=
                (weakened_tree_shape current index node lookup strongest).trans currentShape
              have sameSize : nextTree.nodes.size = current.nodes.size := insert_existing_size current.nodes index node _ lookup
              cases actualChanged : changed current index node strongest with
              | false =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,some index,steps,false) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node strongest then _ else _) = _
                  rw [actualChanged]
                  rfl
                refine .inr ⟨_,actual,⟨nextShape,by simp⟩,?_⟩
                simp [Measure]
              | true =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,node.parent,steps+1,true) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node strongest then _ else _) = _
                  rw [actualChanged]
                  rfl
                refine .inr ⟨_,actual,⟨nextShape,by simp⟩,?_⟩
                simp only [Measure,↓reduceIte]
                rw [sameSize]
                omega
    have initial : Preserves tree (none,tree,some start,0,true) := ⟨rfl,by simp⟩
    have maintained := loop_invariant scan Measure (Preserves tree) step _ initial
    cases actual : (Lean.Loop.forIn {} (none,tree,some start,0,true) scan).1 with
    | none => exact maintained.1
    | some returned => exact maintained.2 returned actual

/-- Sparse lookup commutes with the observable metadata projection. -/
theorem mapped_lookup {A B : Type} (shape : A → B) (nodes : UniValMap A) (index : UniIndex) :
    ((nodes.data.map (Option.map shape))[index.toNat]?).getD none =
      (nodes.get index).map shape := by
  simp only [Array.getElem?_map, UniValMap.get]
  cases nodes.data[index.toNat]? <;> rfl

/-- In particular, SIFA weakening preserves any fresh node's tag and exposure. -/
theorem node_fields (before after : BorrowTree) (same : treeShape after = treeShape before)
    (index : UniIndex) (node : TreeNode) (present : before.nodes.get index = some node) :
    ∃ result, after.nodes.get index = some result ∧ result.tag = node.tag ∧ result.isExposed = node.isExposed := by
  have nodesEq := congrArg (fun shape => shape.2.1) same
  change after.nodes.data.map (Option.map nodeShape) = before.nodes.data.map (Option.map nodeShape) at nodesEq
  have observed := congrArg (fun data => (data[index.toNat]?).getD none) nodesEq
  rw [mapped_lookup, mapped_lookup, present] at observed
  cases found : after.nodes.get index with
  | none => simp [found] at observed
  | some result =>
    have shapeEq : nodeShape result = nodeShape node := by simpa [found] using observed
    exact ⟨result, rfl, congrArg (fun value => value.1) shapeEq,
      congrArg (fun value => value.2.2.2.2) shapeEq⟩

/-- An index absent from every location remains absent after SIFA weakening;
we do not assume that physical node vacancy alone implies permission vacancy. -/
theorem absent_permissions (before after : BorrowTree) (same : treeShape after = treeShape before)
    (index : UniIndex)
    (absent : ∀ position (valid : position < before.locations.entries.size),
      before.locations.entries[position].data.perms.get index = none) :
    ∀ position (valid : position < after.locations.entries.size),
      after.locations.entries[position].data.perms.get index = none := by
  have locationsEq := congrArg (fun shape => shape.2.2.1) same
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at locationsEq
  have countEq := congrArg Array.size locationsEq
  simp only [Array.size_map] at countEq
  intro position valid
  have beforeValid : position < before.locations.entries.size := by omega
  have observed := congrArg (fun entries => entries[position]?) locationsEq
  simp only [Array.getElem?_map, Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem beforeValid, Option.map_some] at observed
  have permissionsEq := congrArg Prod.snd (Option.some.inj observed)
  have lookup := congrArg (fun data => (data[index.toNat]?).getD none) permissionsEq
  change ((after.locations.entries[position].data.perms.data.map (Option.map stateShape))[index.toNat]?).getD none =
    ((before.locations.entries[position].data.perms.data.map (Option.map stateShape))[index.toNat]?).getD none at lookup
  rw [mapped_lookup, mapped_lookup, absent position beforeValid] at lookup
  cases result : after.locations.entries[position].data.perms.get index with
  | none => rfl
  | some state => simp [result] at lookup

end View

namespace Release
open Lean Elab Tactic
open Miri.Memory

/-- An in-range raw range-map index always supplies its actual stored segment. -/
theorem index_exact {A : Type} (map : DedupRangeMap A) (position : Nat)
    (valid : position < map.entries.size) : map.index position = .ok map.entries[position] := by
  unfold DedupRangeMap.index
  change (match (if h : position < map.entries.size then some map.entries[position] else none) with
    | some segment => Except.ok segment
    | none => Except.error (DedupRangeMapError.indexOutOfBounds position map.entries.size)) = _
  simp [valid]

theorem list_tail {α β : Type} (items : List α) (scan : α → β → Id (ForInStep β))
    (property : List α → β → Prop) (initial : β) (good : property items initial) (distinct : items.Nodup)
    (step : ∀ item rest, item ∉ rest → ∀ state, property (item::rest) state →
      ∃ next, scan item state = .yield next ∧ property rest next) :
    property [] (forIn items initial scan) := by
  induction items generalizing initial with
  | nil => exact good
  | cons item rest ih =>
    obtain ⟨notMember,restDistinct⟩ := List.nodup_cons.mp distinct
    obtain ⟨next,actual,preserved⟩ := step item rest notMember initial good
    simpa only [List.forIn_cons,actual,bind,pure] using ih next preserved restDistinct

elab "name_fresh_release_scan" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun expr => expr.isAppOf ``ForIn.forIn)
      | throwError "no actual protector release loop"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (←Lean.Meta.inferType body) body
    let (scan,goal) ← goal.intro1P
    let target ← goal.getType
    return [←goal.change (target.replace fun expr => if expr == body then some (mkFVar scan) else none)]

/-- Releasing an unexposed zero-sized reservation with no materialized states
really scans all allocation locations, skips each absent permission, and returns
Released. Existing roots, ranges and exposure caches are preserved. -/
theorem release (tree : BorrowTree) (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node)
    (unexposed : node.isExposed = false)
    (absent : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none)
    (protections : ProtectedTags) :
    tree.releaseProtector tag protections = ⟨tree,.Released⟩ := by
  have exposure : tree.updateExposureForProtectorRelease tag = ⟨tree,.ok ()⟩ := by
    unfold BorrowTree.updateExposureForProtectorRelease
    simp [tagged,present,unexposed,Id.run,pure]
  unfold BorrowTree.releaseProtector
  rw [tagged]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let property := fun (remaining : List Nat) (state : Option BorrowTree.ProtectorReleaseResult × BorrowTree) =>
    state = (none,tree) ∧ ∀ position ∈ remaining, position < tree.locations.entries.size
  have step : ∀ position rest, position ∉ rest → ∀ state, property (position::rest) state →
      ∃ next, scan position state = .yield next ∧ property rest next := by
    intro position rest notMember state good
    rcases good with ⟨equal,bounded⟩
    subst state
    have valid := bounded position (by simp)
    refine ⟨(none,tree),?_,rfl,?_⟩
    · simp only [scan,index_exact tree.locations position valid,absent position valid]
    · intro query member
      exact bounded query (by simp [member])
  have finished := list_tail (List.range tree.locations.entries.size) scan property (none,tree)
    ⟨rfl,by intro position member;exact List.mem_range.mp member⟩ (List.nodup_range) step
  simp only [List.range_eq_range'] at finished
  rw [finished.1]
  simp only [exposure]


/-- The ancestor SIFA stage preserves the exact facts needed to release a
fresh, lazy, unexposed child, including on every existing byte partition. -/
theorem after_sifa (tree : BorrowTree) (tag : BorTag) (index start : UniIndex)
    (node : TreeNode) (strongest : IdempotentForeignAccess)
    (tagged : tree.indexOfTag tag = some index)
    (present : tree.nodes.get index = some node) (unexposed : node.isExposed = false)
    (absent : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none)
    (protections : ProtectedTags) :
    let after := (updateSifaAfterRetag tree start strongest).1
    after.releaseProtector tag protections = ⟨after,.Released⟩ := by
  dsimp only
  let after := (updateSifaAfterRetag tree start strongest).1
  have shape : View.treeShape after = View.treeShape tree := View.preserves tree start strongest
  have maps := congrArg (fun view => view.1) shape
  change after.tagMapping = tree.tagMapping at maps
  have selected : after.indexOfTag tag = some index := by
    unfold indexOfTag
    rw [maps]
    exact tagged
  obtain ⟨next,found,_,sameExposure⟩ := View.node_fields tree after shape index node present
  exact release after tag index next selected found (sameExposure.trans unexposed)
    (View.absent_permissions tree after shape index absent) protections

attribute [local irreducible] updateSifaAfterRetag UniValMap.insert
set_option maxHeartbeats 100000

/-- Implementation-facing source equation for a concrete zero child. The
insertion equation is discharged from raw freshness/pool data by clients. -/
theorem concrete_zero_eq (tree : BorrowTree) (parentTag tag : BorTag) (index parent : UniIndex)
    (parentNode : TreeNode) (mapping : UniKeyMap BorTag)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (tagged : tree.tagMapping.get parentTag = some parent)
    (present : tree.nodes.get parent = some parentNode) (vacant : tree.nodes.get index = none)
    (offset : Size) (initial : LocationState) :
    let node : TreeNode := {
      tag := tag, parent := some parent, children := #[]
      defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None, isExposed := false }
    let staged : BorrowTree := {tree with
      tagMapping := mapping
      nodes := Append.attachedNodes tree.nodes index parent parentNode node}
    let result := updateSifaAfterRetag staged parent .None
    tree.newChild offset (.concrete parentTag) tag (DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true = ⟨result.1,result.2⟩ := by
  dsimp only
  have different := Reuse.parent_not_vacant tree.nodes index parent parentNode vacant present
  have lookup := (Sparse.get_other tree.nodes index parent
    ({
      tag := tag, parent := some parent, children := #[], defaultInitialPermission := .ReservedFrz false
      defaultInitialSifa := .None, isExposed := false} : TreeNode) different).trans present
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [tagged,Option.map_some,Bool.false_eq_true,↓reduceIte]
  simp only [Permission.isInitial,Permission.isUnique,Permission.strongestIdempotentForeignAccess,
    Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
  rw [lookup]
  simp only [DedupRangeMap.new,DedupRangeMap.iterAll,Size.ZERO,Size.ofBytes,
    beq_self_eq_true,↓reduceIte,←Array.forIn_toList,List.forIn_nil,pure]
  rfl

/-- The freshly inserted concrete zero child can be released without changing
its post-constructor tree. Initial node vacancy and permission vacancy are
separate facts; no release or byte-access success is assumed. -/
theorem concrete_zero_release (tree : BorrowTree) (parentTag tag : BorTag) (index parent : UniIndex)
    (parentNode : TreeNode) (mapping : UniKeyMap BorTag)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (tagged : tree.tagMapping.get parentTag = some parent)
    (present : tree.nodes.get parent = some parentNode) (vacant : tree.nodes.get index = none)
    (newTag : mapping.get tag = some index)
    (absent : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none)
    (offset : Size) (initial : LocationState) (protections : ProtectedTags) :
    let after := (tree.newChild offset (.concrete parentTag) tag (DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true).tree
    after.releaseProtector tag protections = ⟨after,.Released⟩ := by
  rw [concrete_zero_eq tree parentTag tag index parent parentNode mapping inserted tagged present vacant]
  dsimp only
  let node : TreeNode := {
    tag := tag, parent := some parent, children := #[]
    defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None, isExposed := false }
  let staged : BorrowTree := {tree with
    tagMapping := mapping
    nodes := Append.attachedNodes tree.nodes index parent parentNode node}
  have different := Reuse.parent_not_vacant tree.nodes index parent parentNode vacant present
  have newPresent : staged.nodes.get index = some node := by
    change ((tree.nodes.insert index node).insert parent
      {parentNode with children := parentNode.children.push index}).get index = some node
    rw [Sparse.get_other _ parent index _ (Ne.symm different),Sparse.get_same]
  exact after_sifa staged tag index parent node .None newTag newPresent rfl absent protections

/-- Exact lazy-root result for the wildcard zero-size source constructor. -/
theorem wildcard_zero_eq (tree : BorrowTree) (tag : BorTag) (index : UniIndex)
    (mapping : UniKeyMap BorTag)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (offset : Size) (initial : LocationState) :
    tree.newChild offset .wildcard tag (DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true =
      ⟨{tree with
        tagMapping := mapping
        nodes := tree.nodes.insert index {
          tag := tag, parent := none, children := #[]
          defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None, isExposed := false }
        roots := tree.roots.push index}, .ok ()⟩ := by
  simp [BorrowTree.newChild, inserted, DedupRangeMap.new, DedupRangeMap.iterAll,
    Permission.isInitial, Permission.isUnique, Permission.strongestIdempotentForeignAccess,Size.ZERO,Size.ofBytes]

/-- Ending the fresh wildcard-root protector leaves its zero-size constructor
result unchanged. Node vacancy and permission vacancy are kept independent. -/
theorem wildcard_zero_release (tree : BorrowTree) (tag : BorTag) (index : UniIndex)
    (mapping : UniKeyMap BorTag)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index)
    (newTag : mapping.get tag = some index)
    (absent : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none)
    (offset : Size) (initial : LocationState) (protections : ProtectedTags) :
    let after := (tree.newChild offset .wildcard tag (DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true).tree
    after.releaseProtector tag protections = ⟨after,.Released⟩ := by
  rw [wildcard_zero_eq tree tag index mapping inserted]
  dsimp only
  apply release
  · exact newTag
  · exact Sparse.get_same _ _ _
  · rfl
  · exact absent

end Release

end ZeroProtection

end BorrowTree

end Miri.TreeBorrows

namespace Miri.TreeBorrows.BorrowTree
open Miri.ABI Miri.Memory Miri.DataStructures
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private def freshLocation : LocationTree :=
  ⟨⟨#[some ⟨.Unique,true,.None⟩]⟩,{}⟩
private def freshNormal (held : Bool) : Tree.NormalTreeState :=
  ⟨⟨#[⟨none,[]⟩]⟩,#[⟨.Disabled,false,.None⟩],if held then [0] else [],#[some ⟨.Unique,true,.None⟩]⟩
private theorem fresh_normal (held : Bool) :
    Tree.NormalTreeState.performAccess (freshNormal held) 0 .Write .VisitChildrenOfAccessed =
      ⟨freshNormal held,0,[⟨0,.LocalAccess⟩],.Completed⟩ := by
  cases held <;> decide

private theorem fresh_projection (tag : BorTag) (size : Size) (protectedTags : ProtectedTags) :
    normalProjection (BorrowTree.new tag size) freshLocation protectedTags =
      freshNormal (protectedTags.contains tag) := by
  simp [normalProjection,BorrowTree.new,freshLocation,freshNormal,rootIndex,
    traversalProjection,UniValMap.entries,UniValMap.insert,UniValMap.get,TreeNode.defaultLocationState,
    UniIndex.ofNat?,UniIndex.toNat,Id.run,bind,Bind.bind,pure,Pure.pure,
    UniValMap.extendTo,Permission.newDisabled,Permission.newUnique]
  cases held : protectedTags.contains tag <;> simp [List.filterMap,held]

private theorem fresh_normal_at (tag : BorTag) (size : Size) (protectedTags : ProtectedTags) :
    (BorrowTree.new tag size).performNormalAccessAt freshLocation rootIndex .Write protectedTags .VisitChildrenOfAccessed =
      ⟨freshLocation,⟨freshNormal (protectedTags.contains tag),0,[⟨0,.LocalAccess⟩],.Completed⟩,.ok ()⟩ := by
  unfold performNormalAccessAt
  rw [fresh_projection]
  simp only [rootIndex,UniIndex.toNat,UInt32.toNat_zero,fresh_normal]
  simp [freshNormal,freshLocation,BorrowTree.new,rootIndex,nodeAt,UniIndex.ofNat?,UniIndex.toNat,
    UniValMap.insert,UniValMap.get,UniValMap.extendTo,Id.run,bind,Bind.bind,pure,Pure.pure,
    ←Array.forIn_toList]

private theorem fresh_tree_at (tag : BorTag) (size : Size) (protectedTags : ProtectedTags) (range : ByteRange) :
    (BorrowTree.new tag size).performTreeAccessAt freshLocation (some rootIndex) .Write protectedTags
      .VisitChildrenOfAccessed range =
      ⟨freshLocation,some ⟨freshNormal (protectedTags.contains tag),0,[⟨0,.LocalAccess⟩],.Completed⟩,none⟩ := by
  unfold performTreeAccessAt
  dsimp only [Id.run]
  rw [fresh_normal_at]
  simp [BorrowTree.new,rootIndex,nodeAt,UniIndex.ofNat?,UniIndex.toNat,
    UniValMap.insert,UniValMap.get,UniValMap.extendTo,Id.run,bind,Bind.bind,pure,Pure.pure,
    ←Array.forIn_toList]

/-- The actual first full-range write on fresh allocation-owned provenance.
The existing global protector map is arbitrary. -/
theorem fresh_root_full_write (tag : BorTag) (size : Size) (protectedTags : ProtectedTags) :
    let result := (BorrowTree.new tag size).performBorrowAccessRange (.concrete tag)
      Size.ZERO size .Write protectedTags .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = BorrowTree.new tag size := by
  have source : (BorrowTree.new tag size).indexOfTag tag = some rootIndex := by
    simp [BorrowTree.indexOfTag,BorrowTree.new,rootIndex,UniKeyMap.get,Id.run,
      bind,Bind.bind,pure,Pure.pure]
  have locations : (BorrowTree.new tag size).locations = DedupRangeMap.new size freshLocation := rfl
  dsimp only
  unfold performBorrowAccessRange
  dsimp only [Id.run]
  rw [source]
  rw [locations]
  by_cases zero : size.bytes = 0
  · simp [DedupRangeMap.iterMut,DedupRangeMap.iterMutWithClone,zero,
      Id.run,bind,Bind.bind,pure,Pure.pure]
    rfl
  · rw [DedupRangeMap.iterMut_new_full size freshLocation zero]
    simp only [Id.run,bind,Bind.bind,pure,Pure.pure]
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Array.size_singleton,
      Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    simp only [List.range',List.forIn_cons,List.forIn_nil,bind,Bind.bind,pure,Pure.pure]
    simp only [Option.isNone_some,beq_self_eq_true,Bool.false_eq_true,↓reduceIte,Array.getElem?_singleton]
    rw [fresh_tree_at]
    simp only [bind,Bind.bind,pure,Pure.pure]
    have same : (DedupRangeMap.new size freshLocation).setAtPos 0 freshLocation =
        ⟨DedupRangeMap.new size freshLocation,.ok ()⟩ := by
      simp only [DedupRangeMap.new,zero,beq_iff_eq,↓reduceIte]
      rfl
    rw [same]
    simp [locations,Id.run,bind,Bind.bind,pure,Pure.pure]
    rfl

end Miri.TreeBorrows.BorrowTree
