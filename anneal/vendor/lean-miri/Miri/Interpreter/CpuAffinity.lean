import Miri.Interpreter.ForeignItems
import Miri.Concurrency.Thread

/-! Pinned shims/cpu_affinity.rs and the FreeBSD cpuset_getaffinity arm.
Masks use target c_ulong chunks, not host endianness or pointer width. -/
namespace Miri.Interpreter.CpuAffinity
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
abbrev Mask := Vector UInt8 128

def maximumCpus : Nat := 1024

/-- Source set ignores out-of-range CPUs before querying chunk layout. -/
def set (chunkSize : Nat) (endian : Endian) (mask : Mask) (cpu : Nat) : Except StepError Mask := do
  if cpu >= maximumCpus then return mask
  unless chunkSize == 4 || chunkSize == 8 do
    throw (.invalidProgram "CpuAffinityMask unsupported c_ulong chunk size")
  let bits := chunkSize*8
  let start := cpu/bits*chunkSize
  let position := cpu%bits
  let byte := start + match endian with
    | .little => position/8
    | .big => chunkSize-1-position/8
  return mask.mapIdx fun i value => if i == byte then value ||| (UInt8.ofNat (2^(position%8))) else value

def initial (chunkSize : Nat) (endian : Endian) (cpuCount : UInt32) : Except StepError Mask := do
  let mut mask : Mask := Vector.replicate 128 0
  -- Higher CPUs are ignored by source set without any additional effects.
  for cpu in [:min cpuCount.toNat maximumCpus] do
    mask ← set chunkSize endian mask cpu
  return mask

def fromBytes (chunkSize : Nat) (endian : Endian) (cpuCount : UInt32)
    (bytes : ByteArray) : Except StepError (Option Mask) := do
  let available ← initial chunkSize endian cpuCount
  let masked := available.mapIdx fun i byte => byte &&& bytes.data[i]?.getD 0
  return if masked.toArray.any (· != 0) then some masked else none

structure Hooks (P S MD : Type) where
  os : String
  endian : Endian
  cpuCount : UInt32
  chunkSize : M S Nat
  readU32 : OpTy P → M S UInt32
  readI32 : OpTy P → M S Int32
  readI64 : OpTy P → M S Int64
  readUsize : OpTy P → M S UInt64
  readPointer : OpTy P → M S (Pointer (Option P))
  isNull : Pointer (Option P) → M S Bool
  masks : M S (Option (Array (ThreadId × Mask)))
  putMasks : Array (ThreadId × Mask) → M S Unit
  active : M S ThreadId
  linuxTid : UInt32 → M S (Option ThreadId)
  readBytes : Pointer (Option P) → UInt64 → M S ByteArray
  writeBytes : Pointer (Option P) → ByteArray → M S Unit
  writeZero : MD → M S Unit
  errnoNegOne : String → MD → M S Unit
  libcI32 : String → M S Int32

private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error

private def findThread (h : Hooks P S MD) (pid : UInt32) : M S (Option ThreadId) := do
  if pid == 0 then return some (← h.active)
  if h.os == "linux" || h.os == "android" then return ← h.linuxTid pid
  throw (.unsupported "sched affinity supports nonzero pid only on Linux/Android")

private def getMask (masks : Array (ThreadId × Mask)) (thread : ThreadId) : M S Mask := do
  let some (_,mask) := masks.find? (·.1 == thread)
    | throw (.invalidProgram "validated thread absent from CPU affinity map")
  return mask

private def copyMask (h : Hooks P S MD) (mask : Mask)
    (pointer : Pointer (Option P)) (size : UInt64) (dest : MD) : M S Unit := do
  h.writeBytes pointer ⟨mask.toArray.extract 0 (min 128 size.toNat)⟩
  h.writeZero dest

def getAffinity (h : Hooks P S MD) (pid size mask : OpTy P) (dest : MD) : M S Unit := do
  let pid ← h.readU32 pid
  let size ← h.readUsize size
  let pointer ← h.readPointer mask
  let some masks ← h.masks | throw (.unsupported "sched_getaffinity unsupported on no_core programs")
  let some thread ← findThread h pid | h.errnoNegOne "ESRCH" dest; return
  let chunk ← h.chunkSize
  if ← h.isNull pointer then h.errnoNegOne "EFAULT" dest; return
  if size == 0 then h.errnoNegOne "EINVAL" dest; return
  if chunk == 0 then throw (.invalidProgram "CPU affinity checked_rem zero chunk")
  if size.toNat%chunk != 0 then h.errnoNegOne "EINVAL" dest; return
  copyMask h (← getMask masks thread) pointer size dest

def setAffinity (h : Hooks P S MD) (pid size mask : OpTy P) (dest : MD) : M S Unit := do
  let pid ← h.readU32 pid
  let size ← h.readUsize size
  let pointer ← h.readPointer mask
  let some masks ← h.masks | throw (.unsupported "sched_setaffinity unsupported on no_core programs")
  let some thread ← findThread h pid | h.errnoNegOne "ESRCH" dest; return
  if ← h.isNull pointer then h.errnoNegOne "EFAULT" dest; return
  -- The full supplied range is read even though only its first 128 bytes matter.
  let bytes ← h.readBytes pointer size
  let chunk ← if h.cpuCount == 0 then pure 0 else h.chunkSize
  let mask ← lift (fromBytes chunk h.endian h.cpuCount bytes)
  match mask with
  | none => h.errnoNegOne "EINVAL" dest
  | some mask =>
    h.putMasks ((masks.filter (·.1 != thread)).push (thread,mask))
    h.writeZero dest

/-- Source FreeBSD legacy shim, including unused libc queries and null-pointer
precedence over unsupported level/which values. -/
def freeBsdGetAffinity (h : Hooks P S MD) (level which id size mask : OpTy P) (dest : MD) : M S Unit := do
  let level ← h.readI32 level
  let which ← h.readI32 which
  let id ← h.readI64 id
  let size ← h.readUsize size
  let pointer ← h.readPointer mask
  let some masks ← h.masks | throw (.unsupported "cpuset_getaffinity unsupported on no_core programs")
  let _ ← h.libcI32 "CPU_LEVEL_ROOT"
  let _ ← h.libcI32 "CPU_LEVEL_CPUSET"
  let levelWhich ← h.libcI32 "CPU_LEVEL_WHICH"
  let _ ← h.libcI32 "CPU_WHICH_TID"
  let whichPid ← h.libcI32 "CPU_WHICH_PID"
  let _ ← h.libcI32 "CPU_WHICH_JAIL"
  let _ ← h.libcI32 "CPU_WHICH_CPUSET"
  let _ ← h.libcI32 "CPU_WHICH_IRQ"
  unless id == -1 do throw (.unsupported "cpuset_getaffinity supports only pid -1")
  let thread ← h.active
  if ← h.isNull pointer then h.errnoNegOne "EFAULT" dest; return
  unless level == levelWhich && which == whichPid do
    throw (.unsupported "cpuset_getaffinity requires CPU_LEVEL_WHICH/CPU_WHICH_PID")
  let mask ← getMask masks thread
  if size.toNat < (h.cpuCount.toNat+7)/8 then h.errnoNegOne "ERANGE" dest; return
  copyMask h mask pointer size dest
end Miri.Interpreter.CpuAffinity
