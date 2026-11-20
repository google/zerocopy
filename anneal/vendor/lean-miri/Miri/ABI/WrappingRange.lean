import Miri.ABI.Size

/-!
The inclusive wrapping ranges used by `rustc_abi::WrappingRange`.

Range endpoints are machine-width `u128` values (`BitVec 128` in Lean). Values
are compared as unsigned integers except in `noSignedWraparound`, which applies
the source `Size.sign_extend` interpretation. Operations which call a panicking
Size helper propagate that failure explicitly.
-/

namespace Miri.ABI

structure WrappingRange where
  start : U128
  «end» : U128
  deriving DecidableEq, Repr

inductive WrappingRangeError where
  | sizeFailure (error : SizeError)
  | valueOutOfRange (value maxValue : U128)
  | zeroWidthRange
  deriving Repr, DecidableEq

inductive WrapStatus where
  | nonWrapping
  | wrapping
  | full
  deriving DecidableEq, Repr

namespace WrappingRange

private def unsignedMax (size : Size) : Except WrappingRangeError U128 :=
  (Size.unsignedIntMax size).mapError .sizeFailure

@[inline] def full (size : Size) : Except WrappingRangeError WrappingRange := do
  return ⟨0, ← unsignedMax size⟩

@[inline] def contains (range : WrappingRange) (value : U128) : Bool :=
  if range.start.toNat ≤ range.end.toNat then
    range.start.toNat ≤ value.toNat && value.toNat ≤ range.end.toNat
  else
    range.start.toNat ≤ value.toNat || value.toNat ≤ range.end.toNat

private def validEndpoints (range : WrappingRange) (size : Size) :
    Except WrappingRangeError U128 := do
  let maximum ← unsignedMax size
  if range.start.toNat > maximum.toNat then
    throw (.valueOutOfRange range.start maximum)
  if range.end.toNat > maximum.toNat then
    throw (.valueOutOfRange range.end maximum)
  return maximum

@[inline] def isFullFor (range : WrappingRange) (size : Size) :
    Except WrappingRangeError Bool := do
  let maximum ← validEndpoints range size
  let next ← (Size.truncate size (range.end + 1)).mapError .sizeFailure
  let _ := maximum
  return range.start == next

@[inline] def containsRange (range other : WrappingRange) (size : Size) :
    Except WrappingRangeError Bool := do
  if ← range.isFullFor size then return true
  let truncate (value : U128) : Except WrappingRangeError U128 :=
    (Size.truncate size value).mapError .sizeFailure
  let delta := range.start
  let maximum ← truncate (range.end - delta)
  let otherStart ← truncate (other.start - delta)
  let otherEnd ← truncate (other.end - delta)
  return otherStart.toNat ≤ otherEnd.toNat && otherEnd.toNat ≤ maximum.toNat

@[inline] def withStart (range : WrappingRange) (start : U128) : WrappingRange :=
  ⟨start, range.end⟩

@[inline] def withEnd (range : WrappingRange) (endValue : U128) : WrappingRange :=
  ⟨range.start, endValue⟩

private def width (range : WrappingRange) (size : Size) :
    Except WrappingRangeError U128 :=
  (Size.truncate size (range.end - range.start)).mapError .sizeFailure

@[inline] def noUnsignedWraparound (range : WrappingRange) (size : Size) :
    Except WrappingRangeError WrapStatus := do
  if ← range.isFullFor size then return .full
  return if range.start.toNat ≤ range.end.toNat then .nonWrapping else .wrapping

@[inline] def noSignedWraparound (range : WrappingRange) (size : Size) :
    Except WrappingRangeError WrapStatus := do
  if ← range.isFullFor size then return .full
  let start ← (Size.signExtend size range.start).mapError .sizeFailure
  let endValue ← (Size.signExtend size range.end).mapError .sizeFailure
  return if start ≤ endValue then .nonWrapping else .wrapping

private def adjacentPairs : List U128 → List (U128 × U128)
  | first :: second :: rest => (first, second) :: adjacentPairs (second :: rest)
  | _ => []

private def insertSorted (value : U128) : List U128 → List U128
  | [] => [value]
  | head :: rest =>
      if value.toNat ≤ head.toNat then value :: head :: rest
      else head :: insertSorted value rest

private def sortValues : List U128 → List U128
  | [] => []
  | value :: rest => insertSorted value (sortValues rest)

private def chooseMinimumWidth (values : List WrappingRange) (size : Size)
    (best : WrappingRange) (bestWidth : U128) : Except WrappingRangeError WrappingRange := do
  match values with
  | [] => return best
  | candidate :: rest =>
      let candidateWidth ← width candidate size
      if candidateWidth.toNat < bestWidth.toNat then
        chooseMinimumWidth rest size candidate candidateWidth
      else
        chooseMinimumWidth rest size best bestWidth

/-! Match the upstream algorithm: use the obvious interval if it is no larger
than any wraparound candidate; otherwise examine intervals between adjacent
sorted values and keep the first minimum-width range. -/
def smallestRangeContaining (values : List U128) (size : Size) :
    Except WrappingRangeError (Option WrappingRange) := do
  match values with
  | [] => return none
  | first :: rest =>
      let minimum := rest.foldl
        (fun current value => if value.toNat < current.toNat then value else current)
        first
      let maximum := rest.foldl
        (fun current value => if value.toNat > current.toNat then value else current)
        first
      let valueMaximum ← unsignedMax size
      if maximum.toNat > valueMaximum.toNat then
        throw (.valueOutOfRange maximum valueMaximum)
      let bitCount ← (Size.bits size).mapError .sizeFailure
      if bitCount == 0 then throw .zeroWidthRange
      let halfRange := BitVec.ofNat 128 (2 ^ (bitCount.toNat - 1))
      let obvious : WrappingRange := ⟨minimum, maximum⟩
      if (maximum - minimum).toNat ≤ halfRange.toNat then
        return some obvious
      let sorted := sortValues values
      let wrapCandidates := (adjacentPairs sorted).filterMap fun (endValue, startValue) =>
        if startValue == endValue then none else some ⟨startValue, endValue⟩
      let obviousWidth ← width obvious size
      return some (← chooseMinimumWidth wrapCandidates size obvious obviousWidth)

end WrappingRange

end Miri.ABI
