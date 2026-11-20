import Miri.ABI.Align
import Miri.Concurrency.VectorClock

/-! A checked value port of Miri's size/alignment/thread keyed address reuse
pool. RNG outputs are explicit legal-choice arguments; no seed or PRNG stream
is introduced. -/

namespace Miri.Memory.AllocAddresses

open Miri.ABI Miri.Concurrency

def maxReusePoolSize : Nat := 64

/-- Only this distinction from rustc `MemoryKind` affects reuse-pool behavior:
stack allocations are never remembered or reused. All other kinds follow the
same pool policy. -/
inductive AddressMemoryKind where
  | stack
  | other
  deriving DecidableEq, Repr

/-- The source thread index is an ordered `u32`. -/
abbrev AddressThreadId := UInt32

structure AddressReuseConfig where
  addressReuseRate : Float
  addressReuseCrossThreadRate : Float
  deriving DecidableEq, Repr

structure ReusableAddress where
  address : UInt64
  size : Size
  thread : AddressThreadId
  clock : VClock
  deriving Repr

structure ReusePool where
  addressReuseRate : Float
  addressReuseCrossThreadRate : Float
  /-- The outer index is the alignment's log2, like source `subpool`. -/
  pool : Array (Array ReusableAddress) := #[]
  deriving Repr

inductive ReusePoolError where
  | invalidRate (rate : Float)
  | illegalBernoulliChoice (rate : Float) (choice : Bool)
  | invalidAlignment (error : AlignError)
  | invalidRangeChoice (choice begin stop : Nat)
  | malformedPoolIndex (index : Nat) (length : Nat)
  | malformedChoiceIndex (index : Nat) (length : Nat)
  | reusedAddressMisaligned (address alignment : UInt64)
  deriving Repr

instance : ToString ReusePoolError where
  toString
    | .invalidRate rate => s!"address reuse probability {rate} is outside [0, 1]"
    | .illegalBernoulliChoice rate choice =>
        s!"random_bool({rate}) cannot choose {choice}"
    | .invalidAlignment error => toString error
    | .invalidRangeChoice choice begin stop =>
        s!"random_range selected {choice}, outside {begin}..{stop}"
    | .malformedPoolIndex index length =>
        s!"reuse-pool index {index} is outside {length} subpools"
    | .malformedChoiceIndex index length =>
        s!"reuse-pool selection index {index} is outside {length} entries"
    | .reusedAddressMisaligned address alignment =>
        s!"reused address {address} is not aligned to {alignment} bytes"

structure ReusePoolResult (α : Type) where
  state : ReusePool
  outcome : Except ReusePoolError α

structure ReusedAddress where
  address : UInt64
  /-- A cross-thread address carries the donor clock for an acquire hook. -/
  clockToAcquire : Option VClock
  deriving Repr

namespace ReusePool

private def validRate (rate : Float) : Bool :=
  Float.le 0.0 rate && Float.le rate 1.0

/-- The support of a source `rng.random_bool(rate)` result. For interior rates
both results are possible; endpoints permit only the corresponding result. -/
def bernoulliChoiceAllowed (rate : Float) (choice : Bool) : Bool :=
  if !validRate rate then false
  else if choice then Float.lt 0.0 rate else Float.lt rate 1.0

def new (config : AddressReuseConfig) : Except ReusePoolError ReusePool := do
  if !validRate config.addressReuseRate then
    throw (.invalidRate config.addressReuseRate)
  if !validRate config.addressReuseCrossThreadRate then
    throw (.invalidRate config.addressReuseCrossThreadRate)
  return ⟨config.addressReuseRate, config.addressReuseCrossThreadRate, #[]⟩

def addressSpaceShortage (pool : ReusePool) : ReusePool :=
  if Float.lt 0.0 pool.addressReuseRate then
    { pool with addressReuseRate := 1.0 }
  else pool

private def checkedPoolIndex (align : Align) : Except ReusePoolError Nat := do
  let bytes ← (Align.bytes align).mapError ReusePoolError.invalidAlignment
  let normalized ← (Align.fromBytes bytes).mapError ReusePoolError.invalidAlignment
  if normalized != align then throw (.invalidAlignment (.tooLarge bytes))
  return align.pow2

private def getSubpool? (pool : ReusePool) (index : Nat) : Option (Array ReusableAddress) :=
  pool.pool[index]?

private def ensureSubpool (pool : ReusePool) (index : Nat) : ReusePool := Id.run do
  let mut subpools := pool.pool
  while subpools.size ≤ index do
    subpools := subpools.push #[]
  return { pool with pool := subpools }

private def updateSubpool (pool : ReusePool) (index : Nat)
    (subpool : Array ReusableAddress) : Except ReusePoolError ReusePool := do
  if h : index < pool.pool.size then
    return { pool with pool := pool.pool.set index subpool h }
  else throw (.malformedPoolIndex index pool.pool.size)

private def subpoolAt (pool : ReusePool) (index : Nat) :
    Except ReusePoolError (Array ReusableAddress) := do
  match getSubpool? pool index with
  | some subpool => pure subpool
  | none => throw (.malformedPoolIndex index pool.pool.size)

private def entryAt? (entries : Array ReusableAddress) (index : Nat) :
    Option ReusableAddress := entries[index]?

private def lessKey (leftSize : Size) (leftThread : UInt32)
    (rightSize : Size) (rightThread : UInt32) : Bool :=
  leftSize.bytes < rightSize.bytes ||
    (leftSize.bytes == rightSize.bytes && leftThread < rightThread)

private def sortedEntries : List ReusableAddress → Bool
  | [] | [_] => true
  | first :: second :: rest =>
      lessKey first.size first.thread second.size second.thread &&
        sortedEntries (second :: rest)

/-- Source `partition_point`, implemented without unchecked array indexing. -/
private def partitionPoint (entries : Array ReusableAddress) (predicate : ReusableAddress → Bool) : Nat :=
  Id.run do
    let mut low := 0
    let mut high := entries.size
    while low < high do
      let middle := low + (high - low) / 2
      match entryAt? entries middle with
      | some entry => if predicate entry then low := middle + 1 else high := middle
      | none => high := middle
    return low

private def replaceAt (entries : Array ReusableAddress) (index : Nat)
    (entry : ReusableAddress) : Except ReusePoolError (Array ReusableAddress) := do
  if h : index < entries.size then return entries.set index entry h
  else throw (.malformedChoiceIndex index entries.size)

private def insertAt (entries : Array ReusableAddress) (index : Nat)
    (entry : ReusableAddress) : Except ReusePoolError (Array ReusableAddress) := do
  if h : index ≤ entries.size then return entries.insertIdx index entry h
  else throw (.malformedChoiceIndex index entries.size)

/-- Add an address using the explicit outcome of the source Bernoulli draw.
Stack addresses short-circuit before consuming that choice. -/
def addAddr (pool : ReusePool) (choice : Bool) (address : UInt64)
    (size : Size) (align : Align) (kind : AddressMemoryKind)
    (thread : AddressThreadId) (makeClock : Unit → VClock) : ReusePoolResult Unit := Id.run do
  if kind == .stack then return ⟨pool, .ok ()⟩
  if !bernoulliChoiceAllowed pool.addressReuseRate choice then
    return ⟨pool, .error (.illegalBernoulliChoice pool.addressReuseRate choice)⟩
  if !choice then return ⟨pool, .ok ()⟩
  let clock := makeClock ()
  let index ← match checkedPoolIndex align with
    | .ok index => pure index
    | .error error => return ⟨pool, .error error⟩
  let pool := ensureSubpool pool index
  let subpool ← match subpoolAt pool index with
    | .ok subpool => pure subpool
    | .error error => return ⟨pool, .error error⟩
  let position := partitionPoint subpool fun entry =>
    lessKey entry.size entry.thread size thread
  let inserted : ReusableAddress := ⟨address, size, thread, clock⟩
  let result ← if subpool.size ≥ maxReusePoolSize then
      let clamped := min position (subpool.size - 1)
      match replaceAt subpool clamped inserted with
      | .ok next => pure next
      | .error error => return ⟨pool, .error error⟩
    else
      match insertAt subpool position inserted with
      | .ok next => pure next
      | .error error => return ⟨pool, .error error⟩
  match updateSubpool pool index result with
  | .ok next => return ⟨next, .ok ()⟩
  | .error error => return ⟨pool, .error error⟩

private def candidateRange (entries : Array ReusableAddress) (size : Size)
    (thread : AddressThreadId) (crossThread : Bool) : Nat × Nat := Id.run do
  let begin := partitionPoint entries fun entry =>
    entry.size.bytes < size.bytes ||
      (entry.size.bytes == size.bytes && !crossThread && entry.thread < thread)
  let mut stop := begin
  let mut running := true
  while running do
    match entryAt? entries stop with
    | none => running := false
    | some entry =>
        if entry.size.bytes != size.bytes || (!crossThread && entry.thread != thread) then
          running := false
        else stop := stop + 1
  return (begin, stop)

/-- Source prefix before the pool-index random draw. Exposes the exact
half-open candidate range while retaining ensure_subpool mutations, so an
effectful choice input may be requested at the actual source event. -/
def prepareTakeAddr (pool : ReusePool) (reuseChoice crossThreadChoice : Bool)
    (size : Size) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId) :
    ReusePoolResult (Option (Nat × Nat)) := Id.run do
  if kind == .stack then return ⟨pool,.ok none⟩
  if !bernoulliChoiceAllowed pool.addressReuseRate reuseChoice then
    return ⟨pool,.error (.illegalBernoulliChoice pool.addressReuseRate reuseChoice)⟩
  if !reuseChoice then return ⟨pool,.ok none⟩
  if !bernoulliChoiceAllowed pool.addressReuseCrossThreadRate crossThreadChoice then
    return ⟨pool,.error (.illegalBernoulliChoice pool.addressReuseCrossThreadRate crossThreadChoice)⟩
  let index ← match checkedPoolIndex align with
    | .ok index => pure index | .error error => return ⟨pool,.error error⟩
  let pool := ensureSubpool pool index
  let subpool ← match subpoolAt pool index with
    | .ok subpool => pure subpool | .error error => return ⟨pool,.error error⟩
  let (begin,stop) := candidateRange subpool size thread crossThreadChoice
  if stop == begin then return ⟨pool,.ok none⟩
  return ⟨pool,.ok (some (begin,stop))⟩

/-- Try taking a reusable address. `reuseChoice` and `crossThreadChoice` are
the two source Bernoulli outcomes; `selection` is the absolute `usize` index
sampled from the source's eligible half-open `[begin, stop)` range. A missing
candidate returns `none` while keeping the source's possibly extended empty
subpool. -/
def takeAddr (pool : ReusePool) (reuseChoice crossThreadChoice : Bool)
    (selection : Nat) (size : Size) (align : Align) (kind : AddressMemoryKind)
    (thread : AddressThreadId) : ReusePoolResult (Option ReusedAddress) := Id.run do
  if kind == .stack then return ⟨pool, .ok none⟩
  if !bernoulliChoiceAllowed pool.addressReuseRate reuseChoice then
    return ⟨pool, .error (.illegalBernoulliChoice pool.addressReuseRate reuseChoice)⟩
  if !reuseChoice then return ⟨pool, .ok none⟩
  if !bernoulliChoiceAllowed pool.addressReuseCrossThreadRate crossThreadChoice then
    return ⟨pool, .error (.illegalBernoulliChoice pool.addressReuseCrossThreadRate crossThreadChoice)⟩
  let index ← match checkedPoolIndex align with
    | .ok index => pure index
    | .error error => return ⟨pool, .error error⟩
  let pool := ensureSubpool pool index
  let subpool ← match subpoolAt pool index with
    | .ok subpool => pure subpool
    | .error error => return ⟨pool, .error error⟩
  let (begin, stop) := candidateRange subpool size thread crossThreadChoice
  if stop == begin then return ⟨pool, .ok none⟩
  if selection < begin || selection ≥ stop then
    return ⟨pool, .error (.invalidRangeChoice selection begin stop)⟩
  let selectedIndex := selection
  if hSelected : selectedIndex < subpool.size then
    let selected := subpool[selectedIndex]
    let nextSubpool := subpool.eraseIdx selectedIndex hSelected
    match updateSubpool pool index nextSubpool with
    | .error error => return ⟨pool, .error error⟩
    | .ok next =>
        if selected.size.bytes < size.bytes then
          return ⟨next, .error (.malformedChoiceIndex selectedIndex subpool.size)⟩
        let alignment ← match Align.bytes align with
          | .ok alignment => pure alignment
          | .error error => return ⟨next, .error (.invalidAlignment error)⟩
        if selected.address % alignment != 0 then
          return ⟨next, .error (.reusedAddressMisaligned selected.address alignment)⟩
        if !crossThreadChoice && selected.thread != thread then
          return ⟨next, .error (.malformedChoiceIndex selectedIndex subpool.size)⟩
        let clock := if selected.thread == thread then none else some selected.clock
        return ⟨next, .ok (some ⟨selected.address, clock⟩)⟩
  else
    return ⟨pool, .error (.malformedChoiceIndex selectedIndex subpool.size)⟩

/-- The sorted-and-bounded pool invariant maintained by public mutations. -/
def WellFormed (pool : ReusePool) : Prop :=
  pool.pool.all fun entries =>
    entries.size ≤ maxReusePoolSize && sortedEntries entries.toList

theorem emptyPool_wellFormed (reuseRate crossThreadRate : Float) :
    (⟨reuseRate, crossThreadRate, #[]⟩ : ReusePool).WellFormed := by
  simp [WellFormed, maxReusePoolSize]

end ReusePool

end Miri.Memory.AllocAddresses
