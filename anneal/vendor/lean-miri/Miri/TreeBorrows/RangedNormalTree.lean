import Miri.TreeBorrows.NormalTree
import Miri.DataStructures.DedupRangeMap

/-!
Allocation-range iteration for the normal one-root Tree Borrows slice. Each
deduplicated range stores the lazily materialized per-node states for one
location, and each selected range gets the normal-tree visitor transition.
Wildcard roots, exposed-pointer state, diagnostics, and protector lifecycle
remain outside this model.
-/

namespace Miri.TreeBorrows

namespace Tree

open Miri.ABI
open Miri.DataStructures

/-- Normal-tree state partitioned over allocation byte ranges. Each range's
payload contains one optional state per tree node, matching lazy
`LocationTree.perms` initialization at that location. -/
structure RangedNormalTreeState where
  topology : TraversalTree
  defaultStates : Array LocationState
  protectedNodes : List Nat
  locations : DedupRangeMap (Array (Option LocationState))
  deriving DecidableEq, Repr

namespace RangedNormalTreeState

def new (size : Size) (topology : TraversalTree)
    (defaultStates : Array LocationState) (protectedNodes : List Nat)
    (initialStates : Array (Option LocationState)) : RangedNormalTreeState := {
  topology := topology
  defaultStates := defaultStates
  protectedNodes := protectedNodes
  locations := DedupRangeMap.new size initialStates
}

/-- One-byte, one-node Cell state used for a small end-to-end ranged access
contract. -/
def singletonCell : RangedNormalTreeState :=
  new (Size.ofBytes 1) ⟨#[⟨none, []⟩]⟩ #[⟨.Cell, false, .None⟩] [] #[none]

end RangedNormalTreeState

/-- One tree access result for one deduplicated location interval. -/
structure RangedLocationResult where
  range : ByteRange
  result : NormalAccessResult
  deriving DecidableEq, Repr

/-- Status from mutating the selected range partition and applying each
per-location tree transition in source order. -/
inductive RangedAccessStatus where
  | Completed
  | RangeMapFailure (error : DedupRangeMapError)
  | LocationMapFailure (range : ByteRange) (error : DedupRangeMapError)
  | AccessFailure (range : ByteRange) (status : NormalAccessStatus)
  deriving DecidableEq, Repr

/-- Updated partition, visited location intervals (including a failing one),
and first failure. -/
structure RangedAccessResult where
  state : RangedNormalTreeState
  locations : Array RangedLocationResult
  status : RangedAccessStatus
  deriving DecidableEq, Repr

namespace RangedNormalTreeState

private def locationTree (state : RangedNormalTreeState)
    (locationStates : Array (Option LocationState)) : NormalTreeState := {
  topology := state.topology
  defaultStates := state.defaultStates
  protectedNodes := state.protectedNodes
  locationStates := locationStates
}

/-- Apply one normal-tree access to every deduplicated range in the requested
byte interval. The range map performs its eager split/merge preparation first;
then each selected payload is updated in order. A per-location error retains
that interval's partial tree changes and stops the remaining range loop. -/
def performAccessRange (state : RangedNormalTreeState) (offset length : Size)
    (start : Nat) (kind : AccessKind) (mode : ChildrenVisitMode) :
    RangedAccessResult := Id.run do
  let prepared := state.locations.iterMut offset length
  let mut currentMap := prepared.state
  let mut visited : Array RangedLocationResult := #[]
  let mut status := RangedAccessStatus.Completed
  match prepared.outcome with
  | .error error =>
      status := .RangeMapFailure error
  | .ok _ =>
      for cursor in [:prepared.positions.size] do
        if status == .Completed then
          match prepared.positions[cursor]?, prepared.segments[cursor]? with
          | some position, some segment =>
              let tree := locationTree state segment.data
              let result := NormalTreeState.performAccess tree start kind mode
              let mutation := currentMap.setAtPos position result.tree.locationStates
              currentMap := mutation.state
              visited := visited.push ⟨segment.range, result⟩
              match mutation.outcome with
              | .error error => status := .LocationMapFailure segment.range error
              | .ok _ =>
                  if result.status != .Completed then
                    status := .AccessFailure segment.range result.status
          | _, _ =>
              status := .RangeMapFailure (.indexOutOfBounds cursor prepared.positions.size)
  return {
    state := { state with locations := currentMap }
    locations := visited
    status := status
  }

end RangedNormalTreeState

end Tree

end Miri.TreeBorrows
