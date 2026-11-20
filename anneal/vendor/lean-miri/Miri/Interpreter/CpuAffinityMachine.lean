import Miri.Interpreter.CpuAffinity
import Miri.Interpreter.ThreadMachine
import Miri.Interpreter.RawMemoryMachine

/-! Affinity masks live in ThreadMachine.Runtime, so source thread creation
inherits the same mask subsequently read/written by these shims. -/
namespace Miri.Interpreter.CpuAffinityMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
private def lift (value : Except StepError A) : ThreadStacks.M K U A :=
  match value with | .ok value => pure value | .error error => throw error

structure Runtime (U : Type) where
  get : U → ThreadMachine.Runtime CpuAffinity.Mask
  put : U → ThreadMachine.Runtime CpuAffinity.Mask → U

/-- Source machine initialization checks the count before selecting OS/no_core
support. The same runtime field is used by startRegularThread inheritance. -/
def initializeMasks (runtime : Runtime U) (os : String) (noCore : Bool) (cpuCount : UInt32)
    (endian : Endian) (chunkSize : ThreadStacks.M K U Nat) : ThreadStacks.M K U Unit := do
  if cpuCount.toNat > CpuAffinity.maximumCpus then
    throw (.invalidProgram "Miri supports at most 1024 configured CPUs")
  let masks ← if #["linux","freebsd","android"].contains os && !noCore then do
      let chunk ← if cpuCount == 0 then pure 0 else chunkSize
      let mask ← lift (CpuAffinity.initial chunk endian cpuCount)
      pure (some #[( (← get).machine.threads.activeThread,mask)])
    else pure none
  modify fun state => {state with machine := {state.machine with user := {state.machine.user with
    user := runtime.put state.machine.user.user {runtime.get state.machine.user.user with affinity := masks}}}}

/-- Compiler c_ulong layout, errno destination and actual pointer null
resolution remain supplied operations. All byte/scalar effects are canonical. -/
def bind [DecidableEq K] (runtime : Runtime U)
    (access : PlaceMachine.AccessConfig K (ThreadStacks.Storage U))
    (place : PlaceHooks Provenance (ThreadStacks.State K U) C MachineHooks.FrameExtra)
    (choice : C) (communicate : Bool) (hostPid : ThreadStacks.M K U UInt32)
    (base : CpuAffinity.Hooks Provenance (ThreadStacks.State K U) (MPlaceTy Provenance)) :
    CpuAffinity.Hooks Provenance (ThreadStacks.State K U) (MPlaceTy Provenance) :=
  let scalar := fun operand => do
    let value ← PlaceMachine.readImmediate access operand
    lift (value.imm.toScalar.mapError ScalarOps.immediateError)
  {base with
    endian := access.runtime.base.endian
    masks := do return (runtime.get (← get).machine.user.user).affinity
    putMasks := fun masks => modify fun state =>
      {state with machine := {state.machine with user := {state.machine.user with
        user := runtime.put state.machine.user.user {runtime.get state.machine.user.user with affinity := some masks}}}}
    active := do return (← get).machine.threads.activeThread
    linuxTid := fun tid => do
      unless base.os == "linux" || base.os == "android" do
        throw (.invalidProgram "get_thread_id_from_linux_tid target assertion")
      let pid ← ForeignItems.getPid communicate hostPid
      if tid < pid then return none
      return ((← get).machine.threads.threadIdTryFrom (tid-pid).toNat).toOption
    readU32 := fun operand => do lift ((← scalar operand).toUInt32.mapError ScalarOps.scalarError)
    readI32 := fun operand => do lift ((← scalar operand).toInt32.mapError ScalarOps.scalarError)
    readI64 := fun operand => do lift ((← scalar operand).toInt64.mapError ScalarOps.scalarError)
    readUsize := fun operand => do
      lift ((← scalar operand).toTargetUsize access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
    readPointer := fun operand => do
      lift ((← scalar operand).toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
    readBytes := RawMemoryMachine.readBytes access ⟨access.runtime.pointerSize⟩
    writeBytes := RawMemoryMachine.writeBytes access ⟨access.runtime.pointerSize⟩
    writeZero := fun dest => do
      let zero ← lift (Scalar.fromUInt (BitVec.ofNat 128 0) dest.layout.layout.size |>.mapError ScalarOps.scalarError)
      writePlaceImmediate place choice (.scalar zero) ⟨.memory dest.mplace,dest.layout⟩ }
end Miri.Interpreter.CpuAffinityMachine
