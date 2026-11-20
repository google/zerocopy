import Miri.Interpreter.TimeShims
import Miri.Concurrency.SyncObject

/-! Complete pinned unix/freebsd/sync.rs _umtx_op WAIT/WAKE policy. -/
namespace Miri.Interpreter.FreeBsdSync
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
structure Hooks (S R : Type) where
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  readI32 : OpTy Provenance → M S Int32
  readUsize : OpTy Provenance → M S UInt64
  libcI32 : String → M S Int32
  libcU32 : String → M S UInt32
  layout : String → M S LocalLayout
  place : Pointer (Option Provenance) → LocalLayout → M S (MPlaceTy Provenance)
  project : MPlaceTy Provenance → Nat → M S (MPlaceTy Provenance)
  readPlaceU32 : MPlaceTy Provenance → M S UInt32
  readPlaceScalar : MPlaceTy Provenance → M S (Scalar Provenance)
  readTimespec : MPlaceTy Provenance → M S (Option Clock.Duration)
  parseClockId : Scalar Provenance → M S (Option Clock.TimeoutClock)
  noIsolation : String → M S Unit
  isNull : Pointer (Option Provenance) → M S Bool
  seqCstFence : M S Unit
  readAcquireBits : MPlaceTy Provenance → M S U128
  metadata : SyncObject.MetadataHooks S R
  newFutex : M S R
  runtime : SyncRuntime.Hooks S R Int32 (MPlaceTy Provenance)
  timeout : Clock.TimeoutClock → Clock.TimeoutStyle → Clock.Duration → M S ThreadDeadline
  errnoNegOne : String → MPlaceTy Provenance → M S Unit
  writeInt : Int → MPlaceTy Provenance → M S Unit
  hostUsizeBits : Nat
structure UmtxTime where
  duration : Clock.Duration
  absolute : Bool
  clock : Clock.TimeoutClock

def readUmtxTime (h : Hooks S R) (place : MPlaceTy Provenance) : M S (Option UmtxTime) := do
  let absolute ← h.libcU32 "UMTX_ABSTIME"
  let timespec ← h.project place 0
  let some duration ← h.readTimespec timespec | return none
  let flags ← h.readPlaceU32 (← h.project place 1)
  let isAbsolute := flags &&& absolute != 0
  let flags := if isAbsolute then flags &&& (~~~absolute) else flags
  if flags != 0 then throw (.unsupported "unsupported _umtx_time flags")
  let clock ← h.readPlaceScalar (← h.project place 2)
  let some clock ← h.parseClockId clock | throw (.unsupported "unsupported _umtx_time clock")
  if clock == .realTime then h.noIsolation "`_umtx_op` with `CLOCK_REALTIME`"
  return some ⟨duration,isAbsolute,clock⟩
private def futex (h : Hooks S R) (pointer : Pointer (Option Provenance)) : M S (Option R) := do
  let object ← SyncObject.getOrInitMetadata h.metadata pointer do
    return {payload := ← h.newFutex, deleteOnWrite := false, onAccess := fun _ => pure ()}
  return object.map (·.payload)

def operation (h : Hooks S R) (obj op value uaddr uaddr2 : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let obj ← h.readPointer obj
  let op ← h.readI32 op
  let value ← h.readUsize value
  let uaddr ← h.readUsize uaddr
  let uaddr2 ← h.readPointer uaddr2
  let wait ← h.libcI32 "UMTX_OP_WAIT"
  let waitUint ← h.libcI32 "UMTX_OP_WAIT_UINT"
  let waitPrivate ← h.libcI32 "UMTX_OP_WAIT_UINT_PRIVATE"
  let wake ← h.libcI32 "UMTX_OP_WAKE"
  let wakePrivate ← h.libcI32 "UMTX_OP_WAKE_PRIVATE"
  let timespec ← h.layout "timespec"
  let umtxTime ← h.layout "_umtx_time"
  if timespec.layout.size == umtxTime.layout.size then throw (.invalidProgram "timespec and _umtx_time sizes must differ")
  if op == wait || op == waitUint || op == waitPrivate then
    let layout ← h.layout (if op == wait then "isize" else "u32")
    let place ← h.place obj layout
    h.seqCstFence
    let actual ← h.readAcquireBits place
    if actual.toNat != value.toNat then
      h.writeInt 0 dest
      return
    let some ref ← futex h obj | throw (.invalidProgram "acquire-read mutable futex lost allocation")
    let deadline ← if ← h.isNull uaddr2 then pure (some none) else do
      if uaddr == umtxTime.layout.size.bytes then
        let some time ← readUmtxTime h (← h.place uaddr2 umtxTime) | pure none
        pure (some (some (← h.timeout time.clock (if time.absolute then .absolute else .relative) time.duration)))
      else if uaddr == timespec.layout.size.bytes then
        h.noIsolation "`_umtx_op` with `timespec` timeout"
        let some duration ← h.readTimespec (← h.place uaddr2 timespec) | pure none
        pure (some (some (← h.timeout .realTime .relative duration)))
      else pure none
    let some deadline := deadline |
      h.errnoNegOne "EINVAL" dest
      return
    SyncRuntime.futexWait h.runtime ref 0xffffffff deadline (fun kind => do
      match kind with
      | .Ready => h.writeInt 0 dest
      | .TimedOut => h.errnoNegOne "ETIMEDOUT" dest) (some (.futexErrno dest))
  else if op == wake || op == wakePrivate then
    let some ref ← futex h obj |
      h.errnoNegOne "EFAULT" dest
      return
    let count := min value.toNat (2^h.hostUsizeBits-1)
    h.seqCstFence
    let _ ← SyncRuntime.futexWake h.runtime ref 0xffffffff count
    h.writeInt 0 dest
  else throw (.unsupported "unsupported _umtx_op operation")
end Miri.Interpreter.FreeBsdSync
