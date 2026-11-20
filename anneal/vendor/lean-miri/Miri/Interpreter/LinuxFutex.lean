import Miri.Interpreter.ShimSignatures
import Miri.Interpreter.TimeShims
import Miri.Concurrency.SyncObject

/-! Pinned linux_like/sync.rs syscall policy. Fence/load/comparison is one
shim action, so no scheduler preemption is introduced between these events. -/
namespace Miri.Interpreter.LinuxFutex
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
abbrev M := EStateM StepError
inductive ArgType where
  | u32Pointer | timespecPointer | i32 | u32
  | voidPointer | usize | charPointer | sockaddrPointer | socklenPointer
  deriving DecidableEq, Repr
structure Hooks (S R : Type) where
  takeArgs : Array ArgType → ShimSignatures.Varargs Provenance → M S (Array (OpTy Provenance))
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  readI32 : OpTy Provenance → M S Int32
  readU32 : OpTy Provenance → M S UInt32
  isNull : Pointer (Option Provenance) → M S Bool
  i32Place : Pointer (Option Provenance) → M S (MPlaceTy Provenance)
  libcI32 : String → M S Int32
  timespecPlace : OpTy Provenance → M S (MPlaceTy Provenance)
  readTimespec : MPlaceTy Provenance → M S (Option Clock.Duration)
  timeout : Clock.TimeoutClock → Clock.TimeoutStyle → Clock.Duration → M S ThreadDeadline
  noIsolation : String → M S Unit
  seqCstFence : M S Unit
  readAcquire : MPlaceTy Provenance → M S UInt32
  metadata : SyncObject.MetadataHooks S R
  newFutex : M S R
  wait : R → UInt32 → Option ThreadDeadline → MPlaceTy Provenance → M S Unit
  wake : R → UInt32 → Nat → M S Nat
  errnoNegOne : String → MPlaceTy Provenance → M S Unit
  writeInt : Int → MPlaceTy Provenance → M S Unit
  /-- Source scalar from_target_isize uses target width, not the syscall buffer. -/
  writeIsize : Int → MPlaceTy Provenance → M S Unit
  hostUsizeBits : Nat
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "checked futex argument missing")
private def futexRef (h : Hooks S R) (pointer : Pointer (Option Provenance)) : M S (Option R) := do
  let object ← SyncObject.getOrInitMetadata h.metadata pointer do
    return {payload := ← h.newFutex,deleteOnWrite := false,onAccess := fun _ => pure ()}
  return object.map (·.payload)

def syscall (h : Hooks S R) (args : ShimSignatures.Varargs Provenance)
    (dest : MPlaceTy Provenance) : M S Unit := do
  let fixed ← h.takeArgs #[.u32Pointer,.i32,.u32] args
  let pointer ← h.readPointer (← arg fixed 0)
  let op ← h.readI32 (← arg fixed 1)
  let value ← h.readU32 (← arg fixed 2)
  let address ← h.i32Place pointer
  let privateFlag ← h.libcI32 "FUTEX_PRIVATE_FLAG"
  let wait ← h.libcI32 "FUTEX_WAIT"
  let waitBitset ← h.libcI32 "FUTEX_WAIT_BITSET"
  let wake ← h.libcI32 "FUTEX_WAKE"
  let wakeBitset ← h.libcI32 "FUTEX_WAKE_BITSET"
  let realtime ← h.libcI32 "FUTEX_CLOCK_REALTIME"
  let op := op &&& ~~~privateFlag
  let rest : ShimSignatures.Varargs Provenance :=
    ⟨args.args.extract 3 args.args.size,args.alreadyGone+3⟩
  if op &&& ~~~realtime == wait || op &&& ~~~realtime == waitBitset then
    let bitsetWait := op &&& ~~~realtime == waitBitset
    let (timeout,bitset) ← if bitsetWait then do
        let extra ← h.takeArgs #[.timespecPointer,.u32Pointer,.u32] rest
        let second ← h.readPointer (← arg extra 1)
        unless ← h.isNull second do throw (.undefinedBehavior "FUTEX_WAIT_BITSET uaddr2 must be null")
        pure (← arg extra 0,← h.readU32 (← arg extra 2))
      else do
        let extra ← h.takeArgs #[.timespecPointer] rest
        pure (← arg extra 0,UInt32.ofNat (2^32-1))
    if bitset == 0 then h.errnoNegOne "EINVAL" dest; return
    let timeout ← h.timespecPlace timeout
    let deadline ← if ← h.isNull timeout.mplace.ptr then pure none else do
      let some duration ← h.readTimespec timeout | h.errnoNegOne "EINVAL" dest; return
      let clock ← if op &&& realtime == realtime then do
          h.noIsolation "futex realtime nonnull timeout"
          pure Clock.TimeoutClock.realTime
        else pure .monotonic
      let style := if bitsetWait then Clock.TimeoutStyle.absolute else .relative
      pure (some (← h.timeout clock style duration))
    h.seqCstFence
    let actual ← h.readAcquire address
    if value != actual then h.errnoNegOne "EAGAIN" dest; return
    let some ref ← futexRef h pointer
      | throw (.invalidProgram "atomic-acquire-readable futex has no mutable sync byte")
    h.wait ref bitset deadline dest
  else if op == wake || op == wakeBitset then
    -- EFAULT precedes optional argument checks and source fence.
    let some ref ← futexRef h pointer | h.errnoNegOne "EFAULT" dest; return
    let bitset ← if op == wakeBitset then do
        let extra ← h.takeArgs #[.timespecPointer,.u32Pointer,.u32] rest
        let timeout ← h.readPointer (← arg extra 0)
        unless ← h.isNull timeout do throw (.undefinedBehavior "FUTEX_WAKE_BITSET timeout must be null")
        let second ← h.readPointer (← arg extra 1)
        unless ← h.isNull second do throw (.undefinedBehavior "FUTEX_WAKE_BITSET uaddr2 must be null")
        h.readU32 (← arg extra 2)
      else pure (UInt32.ofNat (2^32-1))
    if bitset == 0 then h.errnoNegOne "EINVAL" dest; return
    h.seqCstFence
    if value.toNat >= 2^h.hostUsizeBits then throw (.invalidProgram "futex wake count usize conversion")
    let woken ← h.wake ref bitset value.toNat
    -- Source usize→isize conversion is HOST-width, then target scalar formation.
    if woken >= 2^(h.hostUsizeBits-1) then throw (.invalidProgram "futex wake count host isize conversion")
    h.writeIsize (Int.ofNat woken) dest
  else throw (.unsupported "unsupported futex syscall operation")
end Miri.Interpreter.LinuxFutex
