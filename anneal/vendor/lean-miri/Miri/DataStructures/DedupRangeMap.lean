import Lean
import Miri.ABI.Size

/-! A checked port of Miri's `DedupRangeMap<T>` range partition. -/

namespace Miri.DataStructures
open Miri.ABI

/-- A half-open byte interval, matching `ops::Range<u64>`. -/
structure ByteRange where
  start : UInt64
  stop : UInt64
  deriving DecidableEq, Repr, Inhabited

/-- One range and its associated value. -/
structure RangeMapSegment (α : Type) where
  range : ByteRange
  data : α
  deriving DecidableEq, Repr

/-- Explicit equivalents of the source's checked-size failures and panics. -/
inductive DedupRangeMapError where
  | sizeError (error : SizeError)
  | offsetNotCovered (offset mapSize : UInt64)
  | iterationPastMap (endOffset mapSize : UInt64)
  | indexOutOfBounds (index length : Nat)
  | splitOutsideSegment (index : Nat) (offset start stop : UInt64)
  | mergeRequiresAdjacent (previousEnd nextStart : UInt64)
  deriving DecidableEq, Repr

instance : ToString DedupRangeMapError where
  toString
    | .sizeError error => toString error
    | .offsetNotCovered offset mapSize =>
        s!"DedupRangeMap offset {offset} is not covered by map of size {mapSize}"
    | .iterationPastMap endOffset mapSize =>
        s!"DedupRangeMap iteration ends at {endOffset}, beyond map size {mapSize}"
    | .indexOutOfBounds index length =>
        s!"DedupRangeMap index {index} is outside {length} segments"
    | .splitOutsideSegment index offset start stop =>
        s!"DedupRangeMap split at {offset} is outside segment {index} [{start}..{stop})"
    | .mergeRequiresAdjacent previousEnd nextStart =>
        s!"DedupRangeMap cannot merge nonadjacent segments ending at {previousEnd} and starting at {nextStart}"

/-- The source's ordered vector of half-open intervals. -/
structure DedupRangeMap (α : Type) where
  entries : Array (RangeMapSegment α) := #[]
  deriving DecidableEq, Repr, Inhabited

/-- Mutations carry state even on failure, preserving operations performed before
the corresponding Rust panic. -/
structure DedupMutationResult (α : Type) where
  state : α
  outcome : Except DedupRangeMapError Unit

/-- Result of preparing a source `iter_mut` call. The map already contains the
source's start/end splits and opportunistic merges; positions identify exactly
the entries borrowed by the returned Rust iterator. -/
structure IterMutResult (α : Type) where
  state : DedupRangeMap α
  positions : Array Nat
  segments : Array (RangeMapSegment α)
  outcome : Except DedupRangeMapError Unit

namespace DedupRangeMap

private def segmentAt? (entries : Array (RangeMapSegment α)) (index : Nat) :
    Option (RangeMapSegment α) :=
  if h : index < entries.size then some entries[index] else none

private def updateAt (entries : Array (RangeMapSegment α)) (index : Nat)
    (segment : RangeMapSegment α) : Except DedupRangeMapError (Array (RangeMapSegment α)) :=
  if h : index < entries.size then
    return entries.set index segment h
  else
    throw (.indexOutOfBounds index entries.size)

private def checkedEnd (offset length : UInt64) : Except DedupRangeMapError UInt64 := do
  let finish ← (Size.add (.ofBytes offset) (.ofBytes length)).mapError DedupRangeMapError.sizeError
  return finish.bytes

def new (size : Size) (initial : α) : DedupRangeMap α :=
  if size.bytes == 0 then
    ⟨#[]⟩
  else
    ⟨#[⟨⟨0, size.bytes⟩, initial⟩]⟩

/-- The source reports the last interval's end, or zero for an empty map. -/
def size (map : DedupRangeMap α) : Size :=
  match map.entries.back? with
  | none => Size.ZERO
  | some segment => Size.ofBytes segment.range.stop

def isEmpty (map : DedupRangeMap α) : Bool := map.entries.isEmpty

def length (map : DedupRangeMap α) : Nat := map.entries.size

/-- Binary search using the source's ordering comparator; unlike
`RangeObjectMap.findOffset`, the source unwraps the result and panics if the
offset is not covered. -/
private def findOffset (map : DedupRangeMap α) (offset : UInt64) :
    Except DedupRangeMapError Nat := Id.run do
  let mut low := 0
  let mut high := map.entries.size
  let mut answer : Option (Except DedupRangeMapError Nat) := none
  while low < high && answer.isNone do
    let middle := low + (high - low) / 2
    match segmentAt? map.entries middle with
    | none => answer := some (.error (.indexOutOfBounds middle map.entries.size))
    | some segment =>
        if offset < segment.range.start then
          high := middle
        else if offset ≥ segment.range.stop then
          low := middle + 1
        else
          answer := some (.ok middle)
  match answer with
  | some result => return result
  | none => return .error (.offsetNotCovered offset map.size.bytes)

/-- Read-only iteration returns complete stored segments intersecting the
requested interval; edge segments are not split or clipped. -/
def iter (map : DedupRangeMap α) (offset len : Size) :
    Except DedupRangeMapError (Array (RangeMapSegment α)) := do
  let offsetBytes := offset.bytes
  let lenBytes := len.bytes
  let first ←
    if lenBytes == 0 then pure 0 else findOffset map offsetBytes
  let finish ← checkedEnd offsetBytes lenBytes
  if finish > (map.size).bytes then
    throw (.iterationPastMap finish (map.size).bytes)
  if lenBytes == 0 then
    return #[]
  let mut selected := #[]
  let mut index := first
  let mut running := true
  while running do
    match segmentAt? map.entries index with
    | none => running := false
    | some segment =>
        if segment.range.start < finish then
          selected := selected.push segment
          index := index + 1
        else
          running := false
  return selected

def iterAll (map : DedupRangeMap α) : Array (RangeMapSegment α) := map.entries

/-- Read a stored segment by vector position. -/
def index (map : DedupRangeMap α) (position : Nat) :
    Except DedupRangeMapError (RangeMapSegment α) := do
  match segmentAt? map.entries position with
  | some segment => pure segment
  | none => throw (.indexOutOfBounds position map.entries.size)

/-- Replace a stored segment's value, corresponding to mutation through a
returned mutable iterator reference. -/
def setAtPos (map : DedupRangeMap α) (position : Nat) (data : α) :
    DedupMutationResult (DedupRangeMap α) := Id.run do
  match segmentAt? map.entries position with
  | none => return { state := map, outcome := .error (.indexOutOfBounds position map.entries.size) }
  | some segment =>
      match updateAt map.entries position { segment with data := data } with
      | .error error => return { state := map, outcome := .error error }
      | .ok entries => return { state := { map with entries }, outcome := .ok () }

/-- Split one segment at an interior byte offset. -/
private def splitIndex (entries : Array (RangeMapSegment α)) (index : Nat)
    (splitOffset : UInt64) (cloneData : α → α) :
    Except DedupRangeMapError (Array (RangeMapSegment α) × Bool) := do
  if h : index < entries.size then
    let segment := entries[index]
    if splitOffset == segment.range.start || splitOffset == segment.range.stop then
      return (entries, false)
    if splitOffset < segment.range.start || splitOffset ≥ segment.range.stop then
      throw (.splitOutsideSegment index splitOffset segment.range.start segment.range.stop)
    let first := { segment with range := { segment.range with stop := splitOffset } }
    let second := { segment with
      range := { segment.range with start := splitOffset }
      data := cloneData segment.data }
    let updated := entries.set index first h
    have insertBound : index + 1 ≤ updated.size := by
      change index + 1 ≤ (entries.set index first h).size
      rw [Array.size_set h]
      omega
    return (updated.insertIdx (index + 1) second insertBound, true)
  else
    throw (.indexOutOfBounds index entries.size)

private def removeInterval (entries : Array α) (first stop : Nat) : Array α :=
  entries.extract 0 first ++ entries.extract stop entries.size

/-- Merge an equal run `[first, stop)` into its first entry, preserving the
source's original data value and interval endpoints. -/
private def mergeRun (entries : Array (RangeMapSegment α)) (first stop : Nat) :
    Except DedupRangeMapError (Array (RangeMapSegment α)) := do
  let initial ← match segmentAt? entries first with
    | some segment => pure segment
    | none => throw (.indexOutOfBounds first entries.size)
  let last ← match segmentAt? entries (stop - 1) with
    | some segment => pure segment
    | none => throw (.indexOutOfBounds (stop - 1) entries.size)
  let initial := { initial with range := { initial.range with stop := last.range.stop } }
  let entries ← updateAt entries first initial
  return removeInterval entries (first + 1) stop

private def selectedSlice (entries : Array (RangeMapSegment α)) (first stop : Nat) :
    Except DedupRangeMapError (Array (RangeMapSegment α)) := do
  if first > stop || stop > entries.size then
    throw (.indexOutOfBounds stop entries.size)
  return entries.extract first stop

/-- Perform source `iter_mut`'s eager start split, bounded duplicate merge
scan, and end split. The returned position list represents the mutable slice;
callers can update those entries using `setAtPos`. -/
def iterMutWithClone (map : DedupRangeMap α) (offset len : Size)
    [DecidableEq α] (cloneData : α → α) :
    IterMutResult α := Id.run do
  let offsetBytes := offset.bytes
  let lenBytes := len.bytes
  if lenBytes == 0 then
    return { state := map, positions := #[], segments := #[], outcome := .ok () }
  let firstSearch := findOffset map offsetBytes
  let mut firstIndex ← match firstSearch with
    | .ok index => pure index
    | .error error =>
        return { state := map, positions := #[], segments := #[], outcome := .error error }
  let mut current := map
  match splitIndex current.entries firstIndex offsetBytes cloneData with
  | .error sourceError =>
      return { state := current, positions := #[], segments := #[], outcome := .error sourceError }
  | .ok (entries, didSplit) =>
      current := { current with entries }
      if didSplit then firstIndex := firstIndex + 1
  let finish ← match checkedEnd offsetBytes lenBytes with
    | .ok finish => pure finish
    | .error error =>
        return { state := current, positions := #[], segments := #[], outcome := .error error }
  let mut equalSinceIndex := firstIndex
  let mut successfulMergeCount := 3
  let mut endIndex := firstIndex
  let mut done := false
  let mut failure : Option DedupRangeMapError := none
  while !done && failure.isNone do
    match segmentAt? current.entries endIndex with
    | none =>
        failure := some (.indexOutOfBounds endIndex current.entries.size)
    | some segment =>
        let complete := segment.range.stop ≥ finish
        endIndex := endIndex + 1
        if !complete && endIndex ≥ current.entries.size then
          failure := some (.iterationPastMap finish current.size.bytes)
        else
          if successfulMergeCount > 0 then
            let shouldMerge ←
              if complete then pure true
              else
                match segmentAt? current.entries endIndex with
                | none =>
                    failure := some (.indexOutOfBounds endIndex current.entries.size)
                    pure false
                | some next =>
                    match segmentAt? current.entries equalSinceIndex with
                    | none =>
                        failure := some (.indexOutOfBounds equalSinceIndex current.entries.size)
                        pure false
                    | some firstEqual => pure (next.data != firstEqual.data)
            if shouldMerge && failure.isNone then
              let removedCount := endIndex - equalSinceIndex - 1
              if removedCount > 0 then
                match mergeRun current.entries equalSinceIndex endIndex with
                | .error error => failure := some error
                | .ok entries =>
                    current := { current with entries }
                    endIndex := endIndex - removedCount
                    successfulMergeCount := successfulMergeCount + removedCount
              else
                successfulMergeCount := successfulMergeCount - 1
              equalSinceIndex := endIndex
          if complete && failure.isNone then done := true
  match failure with
  | some error =>
      return { state := current, positions := #[], segments := #[], outcome := .error error }
  | none =>
      let lastIndex := endIndex - 1
      match splitIndex current.entries lastIndex finish cloneData with
      | .error error =>
          return { state := current, positions := #[], segments := #[], outcome := .error error }
      | .ok (entries, _) =>
          current := { current with entries }
          let selectedStop := lastIndex + 1
          match selectedSlice current.entries firstIndex selectedStop with
          | .error error =>
              return { state := current, positions := #[], segments := #[], outcome := .error error }
          | .ok segments =>
              let positions := (List.range (selectedStop - firstIndex)).toArray.map (· + firstIndex)
              return { state := current, positions, segments, outcome := .ok () }

/-- Prepare a mutable range using value-preserving copies on splits. This is the
usual instance for value-like Lean state and is exact when the Rust `Clone`
implementation returns the same value. Use `iterMutWithClone` when a modeled
clone operation produces a different value. -/
def iterMut (map : DedupRangeMap α) (offset len : Size) [DecidableEq α] :
    IterMutResult α :=
  map.iterMutWithClone offset len id

/-- Apply one pure update to every segment selected by `iter_mut`. Splitting and
merging happen first, before the callback updates values, as in Rust. -/
def modifyRangeWithClone (map : DedupRangeMap α) (offset len : Size)
    [DecidableEq α] (cloneData : α → α) (modify : ByteRange → α → α) :
    IterMutResult α := Id.run do
  let prepared := map.iterMutWithClone offset len cloneData
  match prepared.outcome with
  | .error _ => return prepared
  | .ok _ =>
      let mut current := prepared.state
      let mut segments := #[]
      for position in prepared.positions do
        match segmentAt? current.entries position with
        | none =>
            return ({ state := current, positions := prepared.positions, segments := segments, outcome := .error (.indexOutOfBounds position current.entries.size) } : IterMutResult α)
        | some segment =>
            let updated := { segment with data := modify segment.range segment.data }
            match updateAt current.entries position updated with
            | .error error =>
                return ({ state := current, positions := prepared.positions, segments := segments, outcome := .error error } : IterMutResult α)
            | .ok entries =>
                current := { current with entries }
                segments := segments.push updated
      return { state := current, positions := prepared.positions, segments, outcome := .ok () }

/-- Apply a pure update after source `iter_mut` splitting and merging. The
default split copy preserves the immutable Lean value. -/
def modifyRange (map : DedupRangeMap α) (offset len : Size)
    [DecidableEq α] (modify : ByteRange → α → α) : IterMutResult α :=
  map.modifyRangeWithClone offset len id modify

/-- Apply an update to every element without splitting or merging, matching
`iter_mut_all`. -/
def modifyAll (map : DedupRangeMap α) (modify : ByteRange → α → α) : DedupRangeMap α :=
  { map with entries := map.entries.map fun segment =>
      { segment with data := modify segment.range segment.data } }

/-- Coalesce every adjacent equal run, with the same adjacency assertion as the
source. On a failed assertion the vector contains only the already-built prefix. -/
def mergeAdjacentThorough (map : DedupRangeMap α) [DecidableEq α] :
    DedupMutationResult (DedupRangeMap α) := Id.run do
  let mut accumulated : Array (RangeMapSegment α) := #[]
  for segment in map.entries do
    match accumulated.back? with
    | none => accumulated := accumulated.push segment
    | some previous =>
        if previous.data = segment.data then
          if previous.range.stop != segment.range.start then
            return ({ state := { map with entries := accumulated }, outcome := .error (.mergeRequiresAdjacent previous.range.stop segment.range.start) } : DedupMutationResult (DedupRangeMap α))
          let position := accumulated.size - 1
          match segmentAt? accumulated position with
          | none =>
              return ({ state := { map with entries := accumulated }, outcome := .error (.indexOutOfBounds position accumulated.size) } : DedupMutationResult (DedupRangeMap α))
          | some first =>
              match updateAt accumulated position
                  { first with range := { first.range with stop := segment.range.stop } } with
              | .error error =>
                  return { state := { map with entries := accumulated }, outcome := .error error }
              | .ok next => accumulated := next
        else
          accumulated := accumulated.push segment
  return { state := { map with entries := accumulated }, outcome := .ok () }

/-- Sorted, gapless, nonempty intervals beginning at zero. -/
def WellFormed (map : DedupRangeMap α) : Prop :=
  if h : map.entries.size = 0 then True
  else
    map.entries[0].range.start = 0 ∧
    (∀ i (hi : i < map.entries.size), map.entries[i].range.start < map.entries[i].range.stop) ∧
    (∀ i (hi : i + 1 < map.entries.size),
      map.entries[i].range.stop = map.entries[i + 1].range.start)

theorem new_wellFormed (size : Size) (initial : α) :
    (new size initial).WellFormed := by
  unfold WellFormed new
  by_cases h : size.bytes = 0
  · simp [h]
  · have hpos : 0 < size.bytes := by
      apply UInt64.lt_iff_toNat_lt.mpr
      have hne : size.bytes.toNat ≠ 0 := by
        intro hzero
        have hzero' : size.bytes.toNat = (0 : UInt64).toNat := by simpa using hzero
        have hbits : size.bytes = 0 := UInt64.toNat_inj.mp hzero'
        exact h hbits
      exact Nat.pos_of_ne_zero hne
    simp [h, hpos]

end DedupRangeMap
end Miri.DataStructures

namespace Miri.DataStructures.DedupRangeMap
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
variable {A : Type} [DecidableEq A]
private theorem findOffset_new_zero (size : Size) (value : A) (positive : size.bytes ≠ 0) :
    findOffset (new size value) 0 = .ok 0 := by
  unfold findOffset new
  simp only [positive,beq_iff_eq,↓reduceIte,Size.ofBytes,Id.run,bind,Bind.bind,pure,Pure.pure,ForIn.forIn]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [segmentAt?,positive,bind,Bind.bind,pure,Pure.pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [bind,Bind.bind,pure,Pure.pure]

open Lean Elab Meta Tactic in
elab "name_full_range_scan" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun e => e.isAppOf ``Lean.Loop.forIn)
      | throwError "missing full-range source loop"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (← inferType body) body
    let (scan,goal) ← goal.intro1P
    return [← goal.change (target.replace fun e => if e == body then some (mkFVar scan) else none)]

theorem iterMut_new_full (size : Size) (value : A) (positive : size.bytes ≠ 0) :
    (new size value).iterMut Size.ZERO size =
      ⟨new size value,#[0],#[⟨⟨0,size.bytes⟩,value⟩],.ok ()⟩ := by
  have splitZero : splitIndex (new size value).entries 0 0 id =
      .ok ((new size value).entries,false) := by
    simp [new,positive,splitIndex,segmentAt?,Id.run,pure,Pure.pure,Except.pure]
  have finish : checkedEnd 0 size.bytes = .ok size.bytes := by
    simp [checkedEnd,Size.ZERO,Size.ofBytes,Size.add,Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  unfold iterMut iterMutWithClone
  simp only [Size.ZERO,Size.ofBytes,positive,beq_iff_eq,↓reduceIte]
  rw [findOffset_new_zero size value positive]
  dsimp only [Id.run,bind,Bind.bind,pure,Pure.pure]
  rw [splitZero]
  dsimp only [bind,Bind.bind,pure,Pure.pure]
  rw [finish]
  dsimp only [bind,Bind.bind,pure,Pure.pure]
  simp only [ForIn.forIn]
  name_full_range_scan
  have computed : Lean.Loop.forIn {} ((new size value),0,3,0,false,(none : Option DedupRangeMapError)) scan =
      ((new size value),1,2,1,true,(none : Option DedupRangeMapError)) := by
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp [scan,new,positive,segmentAt?,bind,Bind.bind,pure,Pure.pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp [scan,new,positive,segmentAt?,bind,Bind.bind,pure,Pure.pure]
  rw [computed]
  simp [new,positive,splitIndex,segmentAt?,selectedSlice,Id.run,
    bind,Bind.bind,pure,Pure.pure,Except.bind,Except.pure]
end Miri.DataStructures.DedupRangeMap
