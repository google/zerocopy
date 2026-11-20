/-!
# Miri's vector-clock value operations

This module ports the timestamp and vector-clock operations from the pinned
`upstream/miri-source/src/concurrency/vector_clock.rs` (Miri revision
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`, blob
`723dfd29651525198b7590553f1ef5e72b952eba`). The stored representation keeps
the complete packed 32-bit timestamp word, including the low read/retag bit.
Clock comparisons and timestamp equality intentionally inspect time only, as
the Rust `PartialEq`/`Ord` implementations do.

The source's `Span` field is omitted. In this file it affects debug output and
diagnostic attribution only: increment copies a non-dummy span, join and
`set_at_index` choose a non-dummy span, and none of those span choices affects
timestamp time, read type, ordering, clock equality, or update success. The
surrounding data-race detector uses spans when rendering diagnostics, which is
outside this value-operation port. `SmallVec`'s inline capacity is likewise a
storage optimization; this module preserves the logical vector length and
trailing-zero invariant, not allocation strategy.

This does not model thread scheduling, synchronization, data-race reports,
atomic operations, memory, or full Miri concurrency semantics.
-/

namespace Miri.Concurrency

/-- The non-atomic read category packed into a vector timestamp. -/
inductive NaReadType where
  | Read
  | Retag
  deriving DecidableEq, Repr, Inhabited

/-- Errors corresponding to Rust conversion failures, checked timestamp overflow,
and assertions/panics in the selected value operations. -/
inductive ClockError where
  | timestampOverflow
  | vectorIndexOverflow
  | setAtIndexWouldDecrease
  | mutableIndexOutOfBounds
  deriving DecidableEq, Repr, Inhabited

/-- A clock index is exactly a Rust `u32` value. -/
structure VectorIdx where
  private mk ::
  value : Fin 4294967296
  deriving DecidableEq, Repr

namespace VectorIdx

/-- Construct the index associated with a Rust `u32`. -/
def ofU32 (value : Nat) (h : value < 4294967296) : VectorIdx := ⟨⟨value, h⟩⟩

/-- Model `Idx::new`: converting a host index above `u32::MAX` panics upstream. -/
def ofNat (value : Nat) : Except ClockError VectorIdx :=
  if h : value < 4294967296 then .ok ⟨⟨value, h⟩⟩ else .error .vectorIndexOverflow

/-- Convert the index to its mathematical value. -/
def toNat (index : VectorIdx) : Nat := index.value.val

@[simp] theorem toNat_ofU32 (value : Nat) (h : value < 4294967296) :
    (ofU32 value h).toNat = value := rfl

end VectorIdx

/-- The largest time encodable above a one-bit read type in a packed `u32`. -/
def maxTimestamp : Nat := 2147483647

/-- A timestamp stores the exact unsigned 32-bit word `2 * time + readBit`.

The `Fin` bound models the raw u32 range without truncating or dropping its
retag bit. Rust equality and ordering compare `time`, not this whole word. -/
structure VTimestamp where
  private mk ::
  packed : Fin 4294967296
  deriving Repr

namespace VTimestamp

/-- The all-zero timestamp. -/
def ZERO : VTimestamp := ⟨⟨0, by decide⟩⟩

/-- The raw packed `u32` value as a natural number. -/
def packedValue (timestamp : VTimestamp) : Nat := timestamp.packed.val

/-- Decode the timestamp by shifting away the low read-type bit. -/
def time (timestamp : VTimestamp) : Nat := timestamp.packed.val / 2

/-- Decode the low bit as a regular read or retag read. -/
def readType (timestamp : VTimestamp) : NaReadType :=
  if timestamp.packed.val % 2 = 0 then .Read else .Retag

/-- Encode time and read type, preserving the source's checked-multiply overflow. -/
def encode (time : Nat) (readType : NaReadType) : Except ClockError VTimestamp :=
  if h : time ≤ maxTimestamp then
    match readType with
    | .Read => .ok ⟨⟨2 * time, by unfold maxTimestamp at h; omega⟩⟩
    | .Retag => .ok ⟨⟨2 * time + 1, by unfold maxTimestamp at h; omega⟩⟩
  else
    .error .timestampOverflow

/-- Encode a timestamp, returning overflow instead of wrapping its packed word. -/
def ofTime (time : Nat) : Except ClockError VTimestamp := encode time .Read

/-- The packed-word constructor, useful for faithful decoding of existing u32 values. -/
def ofPacked (packed : Nat) (h : packed < 4294967296) : VTimestamp := ⟨⟨packed, h⟩⟩

/-- Equality corresponding to Rust `PartialEq`: the packed read/retag bit is ignored. -/
def sameTime (left right : VTimestamp) : Bool := left.time == right.time

/-- Ordering corresponding to Rust `Ord`: only the decoded timestamp is compared. -/
def compare (left right : VTimestamp) : Ordering :=
  if left.time < right.time then .lt
  else if left.time > right.time then .gt
  else .eq

/-- Preserve the read type while replacing time; encoding overflow is an upstream panic. -/
def setTime (timestamp : VTimestamp) (time : Nat) : Except ClockError VTimestamp :=
  encode time timestamp.readType

/-- Preserve time while replacing the packed read/retag bit. -/
def setReadType (timestamp : VTimestamp) (readType : NaReadType) : VTimestamp :=
  match readType with
  | .Read => ⟨⟨2 * timestamp.time, by
      have hraw := timestamp.packed.isLt
      change 2 * (timestamp.packed.val / 2) < 4294967296
      omega⟩⟩
  | .Retag => ⟨⟨2 * timestamp.time + 1, by
      have hraw := timestamp.packed.isLt
      change 2 * (timestamp.packed.val / 2) + 1 < 4294967296
      omega⟩⟩

/-- Rust `r.max(l)`: the receiver is the other clock's timestamp, and Rust's
`Ord::max` returns its second argument on ties, so the left/self timestamp wins. -/
def maxForJoin (left right : VTimestamp) : VTimestamp :=
  if right.time ≤ left.time then left else right

@[simp] theorem maxForJoin_left_on_time_tie (left right : VTimestamp)
    (sameTime : left.time = right.time) :
    maxForJoin left right = left := by
  simp [maxForJoin, sameTime]

@[simp] theorem time_setReadType (timestamp : VTimestamp) (readType : NaReadType) :
    (timestamp.setReadType readType).time = timestamp.time := by
  cases readType <;> simp [setReadType, time] <;> omega

@[simp] theorem sameTime_refl (timestamp : VTimestamp) : timestamp.sameTime timestamp = true := by
  simp [sameTime]

end VTimestamp

instance : BEq VTimestamp where
  beq := VTimestamp.sameTime

/-- A vector clock is either empty or ends in a timestamp whose time is nonzero.

Its prefix may contain zero timestamps, including timestamp-zero retag reads.
This representation enforces Miri's unique trailing-zero-free clock shape. -/
inductive VClock where
  /-- The all-zero vector is represented only by the empty clock. -/
  | zero
  /-- A canonical clock with arbitrary prefix and a nonzero final time. -/
  | nonzero (earlier : List VTimestamp) (last : VTimestamp) (last_time_nonzero : last.time ≠ 0)
  deriving Repr, Inhabited

namespace VClock

/-- The logical timestamp slice corresponding to the internal vector. -/
def asList : VClock → List VTimestamp
  | .zero => []
  | .nonzero earlier last _ => earlier ++ [last]

/-- The logical number of stored entries. -/
def length (clock : VClock) : Nat := clock.asList.length

/-- The all-zero vector clock. -/
def default : VClock := .zero

/-- Remove trailing entries whose decoded time is zero, exactly as constructors and
updates must do to maintain the internal invariant. -/
private def ofReversedList : List VTimestamp → VClock
  | [] => .zero
  | last :: priorRev =>
      if h : last.time = 0 then ofReversedList priorRev
      else .nonzero priorRev.reverse last h
termination_by values => values.length
decreasing_by simp_wf

/-- Build a clock from a logical timestamp list, removing trailing time-zero values. -/
def ofList (values : List VTimestamp) : VClock := ofReversedList values.reverse

private def listIndex? : List α → Nat → Option α
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, index + 1 => listIndex? rest index
termination_by _values index => index
decreasing_by omega

private def listReplace : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, index + 1, value => do
      let updated ← listReplace rest index value
      pure (head :: updated)
termination_by values _index _value => values.length
decreasing_by simp_wf

/-- The last stored timestamp, when the clock is nonempty. -/
def last? : VClock → Option VTimestamp
  | .zero => none
  | .nonzero _ last _ => some last

/-- The canonical last-entry invariant follows from the representation. -/
theorem last_time_nonzero (clock : VClock) :
    match clock.last? with
    | none => True
    | some timestamp => timestamp.time ≠ 0 := by
  cases clock with
  | zero => trivial
  | nonzero _ _ h => exact h

/-- Read a clock entry; absent vector indices denote `VTimestamp::ZERO`. -/
def index (clock : VClock) (index : VectorIdx) : VTimestamp :=
  (listIndex? clock.asList index.toNat).getD VTimestamp.ZERO

/-- Construct a clock containing only the supplied timestamp at one index.
As upstream, any timestamp whose time is zero produces the empty vector, even a retag read. -/
def newWithIndex (index : VectorIdx) (timestamp : VTimestamp) : VClock :=
  if timestamp.time = 0 then .zero
  else ofList (List.replicate index.toNat VTimestamp.ZERO ++ [timestamp])

private def padTo (values : List VTimestamp) (minLength : Nat) : List VTimestamp :=
  values ++ List.replicate (minLength - values.length) VTimestamp.ZERO

/-- Increment the timestamp at a known vector index.
Packed-time overflow is returned explicitly instead of wrapping. -/
def incrementIndex (clock : VClock) (index : VectorIdx) : Except ClockError VClock := do
  let previous := clock.index index
  let incremented ← previous.setTime (previous.time + 1)
  let padded := padTo clock.asList (index.toNat + 1)
  match listReplace padded index.toNat incremented with
  | some updated => pure (ofList updated)
  | none => .error .mutableIndexOutOfBounds

private def joinLists : List VTimestamp → List VTimestamp → List VTimestamp
  | [], [] => []
  | left :: leftRest, right :: rightRest =>
      VTimestamp.maxForJoin left right :: joinLists leftRest rightRest
  | left :: leftRest, [] =>
      VTimestamp.maxForJoin left VTimestamp.ZERO :: joinLists leftRest []
  | [], right :: rightRest =>
      VTimestamp.maxForJoin VTimestamp.ZERO right :: joinLists [] rightRest

/-- Pointwise join, with the source's left/self raw timestamp chosen on equal times. -/
def join (left right : VClock) : VClock :=
  ofList (joinLists left.asList right.asList)

/-- Replace one coordinate by the corresponding timestamp of `other`.
This models the source assertion that the coordinate may only increase; the
assertion failure is represented explicitly as `setAtIndexWouldDecrease`. -/
def setAtIndex (clock other : VClock) (index : VectorIdx) : Except ClockError VClock := do
  let newTimestamp := other.index index
  if _hZero : newTimestamp.time = 0 then
    if index.toNat ≥ clock.length then pure clock
    else
      let padded := padTo clock.asList (index.toNat + 1)
      match listIndex? padded index.toNat with
      | none => .error .mutableIndexOutOfBounds
      | some oldTimestamp =>
        if oldTimestamp.time > newTimestamp.time then
          .error .setAtIndexWouldDecrease
        else
          match listReplace padded index.toNat newTimestamp with
          | some updated => pure (ofList updated)
          | none => .error .mutableIndexOutOfBounds
  else
    let padded := padTo clock.asList (index.toNat + 1)
    match listIndex? padded index.toNat with
    | none => .error .mutableIndexOutOfBounds
    | some oldTimestamp =>
      if oldTimestamp.time > newTimestamp.time then
        .error .setAtIndexWouldDecrease
      else
        match listReplace padded index.toNat newTimestamp with
        | some updated => pure (ofList updated)
        | none => .error .mutableIndexOutOfBounds

/-- Clear all clock entries. -/
def setZeroVector (_clock : VClock) : VClock := .zero

/-- Read the packed read type at an existing coordinate and preserve its time. -/
def applyReadType (clock : VClock) (index : VectorIdx) (readType : NaReadType) :
    Except ClockError VClock :=
  if _h : index.toNat < clock.length then
    let values := clock.asList
    match listIndex? values index.toNat with
    | none => .error .mutableIndexOutOfBounds
    | some oldTimestamp =>
      match listReplace values index.toNat (oldTimestamp.setReadType readType) with
      | some updated => .ok (ofList updated)
      | none => .error .mutableIndexOutOfBounds
  else
    .error .mutableIndexOutOfBounds

/-- Clone a clock, including every raw read-type bit. -/
def clone (clock : VClock) : VClock := clock

/-- Clone-from has the same logical behavior as replacing the value. -/
def cloneFrom (_clock : VClock) (source : VClock) : VClock := source

/-- Clock equality corresponding to Rust's derived `VClock` equality and timestamp `PartialEq`:
length and every decoded time must agree; read/retag bits are ignored. -/
def equalLists : List VTimestamp → List VTimestamp → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      left.sameTime right && equalLists leftRest rightRest
  | _, _ => false

/-- Compare the common vector prefix using Miri's partial-order accumulation rule. -/
def compareCommon (order : Ordering) : List VTimestamp → List VTimestamp → Option Ordering
  | left :: leftRest, right :: rightRest =>
      match order, VTimestamp.compare left right with
      | .eq, next => compareCommon next leftRest rightRest
      | .lt, .gt => none
      | .lt, _ => compareCommon .lt leftRest rightRest
      | .gt, .lt => none
      | .gt, _ => compareCommon .gt leftRest rightRest
  | _, _ => some order
termination_by left _right => left.length
decreasing_by
  all_goals simp_wf

/-- Partial componentwise vector-clock comparison. -/
def partialCompare (left right : VClock) : Option Ordering :=
  match compareCommon .eq left.asList right.asList with
  | none => none
  | some order =>
    match compare left.length right.length with
    | .eq => some order
    | .lt =>
      match order with
      | .lt | .eq => some .lt
      | .gt => none
    | .gt =>
      match order with
      | .gt | .eq => some .gt
      | .lt => none

private def allLE : List VTimestamp → List VTimestamp → Bool
  | [], _ => true
  | _, [] => true
  | left :: leftRest, right :: rightRest =>
      decide (left.time ≤ right.time) && allLE leftRest rightRest

private def allGE : List VTimestamp → List VTimestamp → Bool
  | [], _ => true
  | _, [] => true
  | left :: leftRest, right :: rightRest =>
      decide (left.time ≥ right.time) && allGE leftRest rightRest

/-- Rust's optimized strict-less-than comparison. -/
def lt (left right : VClock) : Bool :=
  left.length ≤ right.length && allLE left.asList right.asList &&
    !(left.length = right.length && equalLists left.asList right.asList)

/-- Rust's optimized less-than-or-equal comparison. -/
def le (left right : VClock) : Bool :=
  left.length ≤ right.length && allLE left.asList right.asList

/-- Rust's optimized strict-greater-than comparison. -/
def gt (left right : VClock) : Bool :=
  left.length ≥ right.length && allGE left.asList right.asList &&
    !(left.length = right.length && equalLists left.asList right.asList)

/-- Rust's optimized greater-than-or-equal comparison. -/
def ge (left right : VClock) : Bool :=
  left.length ≥ right.length && allGE left.asList right.asList

/-- Build a read-only clock from timestamps, canonicalizing only trailing time-zero entries. -/
def fromTimestamps (timestamps : List VTimestamp) : VClock := ofList timestamps

@[simp] theorem length_zero : (default : VClock).length = 0 := rfl

theorem increment_keeps_canonical (clock : VClock) (index : VectorIdx)
    (next : VClock) (_h : clock.incrementIndex index = .ok next) :
    match next.last? with
    | none => True
    | some timestamp => timestamp.time ≠ 0 := next.last_time_nonzero

theorem join_keeps_canonical (left right : VClock) :
    match (left.join right).last? with
    | none => True
    | some timestamp => timestamp.time ≠ 0 := (left.join right).last_time_nonzero

end VClock

instance : BEq VClock where
  beq left right := VClock.equalLists left.asList right.asList

end Miri.Concurrency
