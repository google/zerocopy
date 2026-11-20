import Miri.Memory.AllocRange

/-! A checked Lean port of Miri's allocation-object range map. -/

namespace Miri.DataStructures
open Miri.ABI Miri.Memory

abbrev Position := Nat

/-- The half-open vector interval returned by an imperfect access classification. -/
structure PositionRange where
  start : Position
  stop : Position
  deriving DecidableEq, Repr, Inhabited

/-- The three classifications returned by `RangeObjectMap::access_type`. -/
inductive AccessType where
  | perfectlyOverlapping (position : Position)
  | empty (position : Position)
  | imperfectlyOverlapping (positions : PositionRange)
  deriving DecidableEq, Repr

/-- A binary-search result: either the containing object or its insertion slot. -/
inductive OffsetSearch where
  | found (position : Position)
  | insertionPoint (position : Position)
  deriving DecidableEq, Repr

/-- Explicit forms of the panics and invalid vector operations in the Rust API. -/
inductive RangeObjectMapError where
  | memory (error : MemoryError)
  | positionOutOfBounds (position length : Nat)
  | positionRangeReversed (start stop : Nat)
  | positionRangeOutOfBounds (start stop length : Nat)
  | previousObjectOverlaps (position : Position) (previousEnd newStart : Size)
  | nextObjectOverlaps (position : Position) (newEnd nextStart : Size)
  | internalIndexOutOfBounds (position length : Nat)
  deriving DecidableEq, Repr

instance : ToString RangeObjectMapError where
  toString
    | .memory error => toString error
    | .positionOutOfBounds position length =>
        s!"RangeObjectMap position {position} is outside {length} objects"
    | .positionRangeReversed start stop =>
        s!"RangeObjectMap drain range {start}..{stop} is reversed"
    | .positionRangeOutOfBounds start stop length =>
        s!"RangeObjectMap drain range {start}..{stop} exceeds {length} objects"
    | .previousObjectOverlaps _ _ _ =>
        "RangeObjectMap insertion overlaps the previous object"
    | .nextObjectOverlaps _ _ _ =>
        "RangeObjectMap insertion overlaps the next object"
    | .internalIndexOutOfBounds position length =>
        s!"RangeObjectMap internal index {position} is outside {length} objects"

/-- One entry in the source `Vec<Elem<T>>`. -/
structure RangeObject (α : Type) where
  range : AllocRange
  data : α
  deriving DecidableEq, Repr

/-- The map keeps the source's sorted vector representation. -/
structure RangeObjectMap (α : Type) where
  objects : Array (RangeObject α) := #[]
  deriving DecidableEq, Repr, Inhabited

/-- Mutating Rust methods may panic after changing the vector. Keep that state
alongside an explicit error so Lean callers can observe the exact partial effect. -/
structure MutationResult (α : Type) where
  state : α
  outcome : Except RangeObjectMapError Unit

namespace RangeObjectMap

def new : RangeObjectMap α := ⟨#[]⟩

@[inline] def length (map : RangeObjectMap α) : Nat := map.objects.size

@[inline] def isEmpty (map : RangeObjectMap α) : Bool := map.objects.isEmpty

@[inline] def ranges (map : RangeObjectMap α) : Array AllocRange :=
  map.objects.map RangeObject.range

/-- Checked read corresponding to Rust indexing. -/
def index (map : RangeObjectMap α) (position : Position) : Except RangeObjectMapError α := do
  if h : position < map.objects.size then
    return map.objects[position].data
  else
    throw (.positionOutOfBounds position map.objects.size)

/-- Checked replacement corresponding to Rust `IndexMut`. Invalid indices leave
the map unchanged. -/
def setAtPos (map : RangeObjectMap α) (position : Position) (data : α) :
    MutationResult (RangeObjectMap α) :=
  if h : position < map.objects.size then
    let old := map.objects[position]
    let next := { old with data := data }
    { state := { map with objects := map.objects.set position next h }, outcome := .ok () }
  else
    { state := map, outcome := .error (.positionOutOfBounds position map.objects.size) }

/-- Checked in-place data update corresponding to a borrow through `IndexMut`. -/
def modifyAtPos (map : RangeObjectMap α) (position : Position) (modify : α → α) :
    MutationResult (RangeObjectMap α) :=
  if h : position < map.objects.size then
    let old := map.objects[position]
    let next := { old with data := modify old.data }
    { state := { map with objects := map.objects.set position next h }, outcome := .ok () }
  else
    { state := map, outcome := .error (.positionOutOfBounds position map.objects.size) }

/-- Source `iter()` order, materialized as an array for the pure Lean API. -/
def iter (map : RangeObjectMap α) : Array α := map.objects.map RangeObject.data

private def objectAt? (objects : Array (RangeObject α)) (position : Nat) :
    Option (RangeObject α) :=
  if h : position < objects.size then some objects[position] else none

private def checkedEnd (range : AllocRange) : Except RangeObjectMapError Size :=
  range.endExclusive.mapError RangeObjectMapError.memory

private def lastIncludedOffset (range : AllocRange) : Except RangeObjectMapError Size := do
  let finish ← checkedEnd range
  (Size.sub finish (Size.ofBytes 1)).mapError (fun error => .memory (.sizeError error))

/-- Mirror `Vec::binary_search_by`: lower offsets compare Greater, offsets at
or beyond an object's exclusive end compare Less. The midpoint and branches
match Rust's binary-search result, including its insertion point. -/
private def findOffsetAux (objects : Array (RangeObject α)) (offset : Size)
    (low high : Nat) : Except RangeObjectMapError OffsetSearch := do
  if high ≤ low then
    return .insertionPoint low
  let middle := low + (high - low) / 2
  let object ← match objectAt? objects middle with
    | some object => pure object
    | none => throw (.internalIndexOutOfBounds middle objects.size)
  let finish ← checkedEnd object.range
  if offset.bytes < object.range.start.bytes then
    findOffsetAux objects offset low middle
  else if offset.bytes ≥ finish.bytes then
    findOffsetAux objects offset (middle + 1) high
  else
    return .found middle
termination_by high - low
decreasing_by all_goals omega

/-- Finds the object containing an offset, or the vector insertion position. -/
def findOffset (map : RangeObjectMap α) (offset : Size) :
    Except RangeObjectMapError OffsetSearch :=
  findOffsetAux map.objects offset 0 map.objects.size

/-- Classify a byte access exactly as Miri does. In particular the end byte is
computed as `range.end() - 1`; empty accesses can therefore produce the same
underflow error as the source instead of receiving special treatment. -/
def accessType (map : RangeObjectMap α) (range : AllocRange) :
    Except RangeObjectMapError AccessType := do
  match ← map.findOffset range.start with
  | .found position =>
      let object ← match objectAt? map.objects position with
        | some object => pure object
        | none => throw (.internalIndexOutOfBounds position map.objects.size)
      if object.range.start == range.start && object.range.size == range.size then
        return .perfectlyOverlapping position
      else
        let last ← lastIncludedOffset range
        let endPosition ← match ← map.findOffset last with
          | .found inclusivePosition => pure (inclusivePosition + 1)
          | .insertionPoint exclusivePosition => pure exclusivePosition
        return .imperfectlyOverlapping ⟨position, endPosition⟩
  | .insertionPoint position =>
      let last ← lastIncludedOffset range
      match ← map.findOffset last with
      | .insertionPoint endPosition =>
          if position == endPosition then
            return .empty position
          else
            return .imperfectlyOverlapping ⟨position, endPosition⟩
      | .found endPosition =>
          return .imperfectlyOverlapping ⟨position, endPosition + 1⟩

/-- Insert before checking adjacency, as in Rust. The returned state therefore
contains the inserted element when a subsequent size check or assertion fails. -/
def insertAtPos (map : RangeObjectMap α) (position : Position)
    (range : AllocRange) (data : α) : MutationResult (RangeObjectMap α) := Id.run do
  if h : position ≤ map.objects.size then
    let inserted := map.objects.insertIdx position ⟨range, data⟩ h
    let nextMap : RangeObjectMap α := { map with objects := inserted }
    if position > 0 then
      let previousPosition := position - 1
      match objectAt? inserted previousPosition with
      | none =>
          return ({ state := nextMap, outcome := .error (.internalIndexOutOfBounds previousPosition inserted.size) } : MutationResult (RangeObjectMap α))
      | some previous =>
          match checkedEnd previous.range with
          | .error error => return { state := nextMap, outcome := .error error }
          | .ok previousEnd =>
              if previousEnd.bytes > range.start.bytes then
                return ({ state := nextMap, outcome := .error (.previousObjectOverlaps position previousEnd range.start) } : MutationResult (RangeObjectMap α))
    if position < map.objects.size then
      let nextPosition := position + 1
      match checkedEnd range with
      | .error error =>
          return ({ state := nextMap, outcome := .error error } : MutationResult (RangeObjectMap α))
      | .ok rangeEnd =>
          match objectAt? inserted nextPosition with
          | none =>
              return ({ state := nextMap, outcome := .error (.internalIndexOutOfBounds nextPosition inserted.size) } : MutationResult (RangeObjectMap α))
          | some next =>
              if rangeEnd.bytes > next.range.start.bytes then
                return ({ state := nextMap, outcome := .error (.nextObjectOverlaps position rangeEnd next.range.start) } : MutationResult (RangeObjectMap α))
    return { state := nextMap, outcome := .ok () }
  else
    return ({ state := map, outcome := .error (.positionOutOfBounds position map.objects.size) } : MutationResult (RangeObjectMap α))

/-- Remove a vector interval, corresponding to `Vec::drain(start..stop)`. -/
def removePosRange (map : RangeObjectMap α) (start stop : Position) :
    MutationResult (RangeObjectMap α) :=
  if start > stop then
    { state := map, outcome := .error (.positionRangeReversed start stop) }
  else if stop > map.objects.size then
    { state := map,
      outcome := .error (.positionRangeOutOfBounds start stop map.objects.size) }
  else
    let objects := map.objects.extract 0 start ++ map.objects.extract stop map.objects.size
    { state := { map with objects := objects }, outcome := .ok () }

/-- Remove one position, corresponding to `Vec::remove`. -/
def removeFromPos (map : RangeObjectMap α) (position : Position) :
    MutationResult (RangeObjectMap α) :=
  if h : position < map.objects.size then
    { state := { map with objects := map.objects.eraseIdx position h }, outcome := .ok () }
  else
    { state := map,
      outcome := .error (.positionOutOfBounds position map.objects.size) }

/-- Sorted, non-overlapping ranges, stated using checked exclusive endpoints. -/
def WellFormed (map : RangeObjectMap α) : Prop :=
  ∀ (i j : Nat) (hi : i < map.objects.size) (hj : j < map.objects.size),
    i < j → ∃ finish : Size,
      map.objects[i].range.endExclusive = .ok finish ∧
      finish.bytes ≤ map.objects[j].range.start.bytes

theorem new_wellFormed : WellFormed (new : RangeObjectMap α) := by
  intro i j hi _ _
  simp [new] at hi

theorem setAtPos_preserves_ranges (map : RangeObjectMap α) (position : Position)
    (data : α) (inBounds : position < map.objects.size) :
    (map.setAtPos position data).state.ranges = map.ranges := by
  simp only [setAtPos, dite_eq_left inBounds, ranges]
  rw [Array.map_set]
  have dataRange :
      ({ map.objects[position] with data := data } : RangeObject α).range =
        map.objects[position].range := rfl
  rw [dataRange]
  apply Array.ext
  · simp
  · intro i leftBound rightBound
    by_cases samePosition : position = i
    · subst i
      simp
    · simp [Array.getElem_set, samePosition]

end RangeObjectMap
end Miri.DataStructures
