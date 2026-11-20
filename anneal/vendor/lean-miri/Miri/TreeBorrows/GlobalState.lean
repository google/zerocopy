import Miri.Memory.Identity

/-!
Global pointer-tag and protector bookkeeping from Miri's
`borrow_tracker::GlobalStateInner`, `FrameState`, and `ProtectorKind`.

This is the borrow-tracker bookkeeping layer only. Allocation tree mutations,
protector-triggered reads on stack pop, and memory accesses live in separate
Tree Borrows operations.
-/

namespace Miri.TreeBorrows

open Miri.Memory

/-- Miri's two protector strengths. -/
inductive ProtectorKind where
  | WeakProtector
  | StrongProtector
  deriving DecidableEq, Repr, Inhabited

/-- Finite map from source `BorTag` to `ProtectorKind`.

The source uses an FxHashMap, whose iteration order is not semantic here.
This representation preserves the observable map operations (insert replaces,
remove deletes, lookup returns the current kind).
-/
structure ProtectedTags where
  entries : Array (BorTag × ProtectorKind) := #[]
  deriving DecidableEq, Repr, Inhabited

namespace ProtectedTags

def get (map : ProtectedTags) (tag : BorTag) : Option ProtectorKind :=
  (map.entries.find? fun entry => entry.1 == tag).map Prod.snd

def contains (map : ProtectedTags) (tag : BorTag) : Bool :=
  (map.get tag).isSome

def insert (map : ProtectedTags) (tag : BorTag) (kind : ProtectorKind) : ProtectedTags :=
  ⟨(map.entries.filter fun entry => entry.1 != tag).push (tag, kind)⟩

def remove (map : ProtectedTags) (tag : BorTag) : ProtectedTags :=
  ⟨map.entries.filter fun entry => entry.1 != tag⟩

def size (map : ProtectedTags) : Nat := map.entries.size

@[simp] theorem get_insert_same (map : ProtectedTags) (tag : BorTag)
    (kind : ProtectorKind) : (map.insert tag kind).get tag = some kind := by
  simp [get, insert]

@[simp] theorem get_remove_same (map : ProtectedTags) (tag : BorTag) :
    (map.remove tag).get tag = none := by
  simp [get, remove]

end ProtectedTags

/-- Tags protected by one call frame, paired with the allocation whose
Tree Borrows state must receive its release operation before the frame ends.
-/
structure FrameState where
  protectedTags : Array (AllocId × BorTag) := #[]
  deriving DecidableEq, Repr, Inhabited

namespace FrameState

def addProtector (frame : FrameState) (allocId : AllocId) (tag : BorTag) : FrameState :=
  { frame with protectedTags := frame.protectedTags.push (allocId, tag) }

/-- Provenance pairs visited by the source `VisitProvenance` implementation.
The global protected-tag table is intentionally not separately traced.
-/
def liveBorrowTags (frame : FrameState) : Array (AllocId × BorTag) :=
  frame.protectedTags

end FrameState

inductive GlobalStateError where
  | pointerTagOverflow (tag : BorTag)
  deriving DecidableEq, Repr

/-- The semantic fields from Miri's `GlobalStateInner` that govern pointer
tag allocation and protector bookkeeping. Root allocation IDs and tracked
tag IDs use arrays as finite maps/sets; their insertion and lookup behavior
matches the source's map/set API.
-/
structure GlobalState where
  nextPointerTag : BorTag := BorTag.one
  rootPointerTags : Array (AllocId × BorTag) := #[]
  protectedTags : ProtectedTags := {}
  trackedPointerTags : Array BorTag := #[]
  deriving DecidableEq, Repr, Inhabited

namespace GlobalState

def new (trackedPointerTags : Array BorTag := #[]) : GlobalState :=
  { nextPointerTag := BorTag.one, rootPointerTags := #[],
    protectedTags := {}, trackedPointerTags := trackedPointerTags }

def isTrackedPointerTag (state : GlobalState) (tag : BorTag) : Bool :=
  state.trackedPointerTags.contains tag

def rootTag? (state : GlobalState) (allocId : AllocId) : Option BorTag :=
  (state.rootPointerTags.find? fun entry => entry.1 == allocId).map Prod.snd

/-- Source `GlobalStateInner::new_ptr`: return the current tag and advance the
counter with checked `BorTag::succ`. Miri unwraps overflow; this port retains
it as an explicit error.
-/
def newPointerTag (state : GlobalState) : Except GlobalStateError (GlobalState × BorTag) :=
  match BorTag.succ state.nextPointerTag with
  | none => .error (.pointerTagOverflow state.nextPointerTag)
  | some next => .ok ({ state with nextPointerTag := next }, state.nextPointerTag)

/-- Source `root_ptr_tag`: return the stable per-allocation root tag, creating
one with `new_ptr` when absent.
-/
def rootPointerTag (state : GlobalState) (allocId : AllocId) :
    Except GlobalStateError (GlobalState × BorTag) := do
  match rootTag? state allocId with
  | some tag => pure (state, tag)
  | none =>
      let (next, tag) ← state.newPointerTag
      pure ({ next with rootPointerTags := next.rootPointerTags.push (allocId, tag) }, tag)

/-- Source `remove_unreachable_allocs`, where `liveAllocIds` is the set passed
by the allocation collector.
-/
def removeUnreachableAllocs (state : GlobalState) (liveAllocIds : Array AllocId) : GlobalState :=
  { state with rootPointerTags := state.rootPointerTags.filter fun entry =>
      liveAllocIds.contains entry.1 }

/-- Add the two source-side records created when a reborrow installs a
protector: one frame-owned (allocation, tag) pair and one global tag-to-kind
entry used by access transitions.
-/
def addProtector (state : GlobalState) (frame : FrameState) (allocId : AllocId)
    (tag : BorTag) (kind : ProtectorKind) : GlobalState × FrameState :=
  ({ state with protectedTags := state.protectedTags.insert tag kind },
   frame.addProtector allocId tag)

/-- Source `end_call`: remove every tag listed by the frame from the global
protected-tag map. Tree Borrows' release operation is performed before this
bookkeeping step by `on_stack_pop`.
-/
def endCall (state : GlobalState) (frame : FrameState) : GlobalState :=
  { state with protectedTags :=
      (frame.protectedTags.foldl (fun tags pair => tags.remove pair.2) state.protectedTags) }

/-- The global map is only a lookup index; protected tags remain live through
their frame-owned provenance records.
-/
def liveBorrowTags (frames : Array FrameState) : Array (AllocId × BorTag) :=
  frames.foldl (fun live frame => live ++ frame.liveBorrowTags) #[]

@[simp] theorem newPointerTag_returns_one :
    (new (#[] : Array BorTag)).newPointerTag =
      .ok ({ new (#[] : Array BorTag) with nextPointerTag := ⟨2, by decide⟩ }, BorTag.one) := by
  rfl

@[simp] theorem rootPointerTag_existing (state : GlobalState) (allocId : AllocId)
    (tag : BorTag) (h : state.rootTag? allocId = some tag) :
    state.rootPointerTag allocId = .ok (state, tag) := by
  unfold rootPointerTag
  rw [h]
  rfl

@[simp] theorem endCall_empty (state : GlobalState) :
    state.endCall {} = state := by
  cases state
  rfl

@[simp] theorem addProtector_global_lookup (state : GlobalState) (frame : FrameState)
    (allocId : AllocId) (tag : BorTag) (kind : ProtectorKind) :
    (state.addProtector frame allocId tag kind).1.protectedTags.get tag = some kind := by
  simp [addProtector]

end GlobalState

end Miri.TreeBorrows
