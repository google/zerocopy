import Miri.Interpreter.UnixThreadDispatch

/-! Concrete return and OS-thread-ID effects for the pthread wrapper family.
Shared ThreadStacks supplies the authoritative active thread and liveness. -/
namespace Miri.Interpreter.UnixThreadDispatchMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
private def lift (value : Except StepError A) : ThreadStacks.M K U A :=
  match value with | .ok value => pure value | .error error => throw error
private def write (place : PlaceHooks Provenance (ThreadStacks.State K U) C MachineHooks.FrameExtra)
    (choice : C) (value : Scalar Provenance) (dest : MPlaceTy Provenance) : ThreadStacks.M K U Unit :=
  writePlaceImmediate place choice (.scalar value) ⟨.memory dest.mplace,dest.layout⟩
private def writeInt (place : PlaceHooks Provenance (ThreadStacks.State K U) C MachineHooks.FrameExtra)
    (choice : C) (value : Int) (dest : MPlaceTy Provenance) : ThreadStacks.M K U Unit := do
  let value ← lift (Scalar.fromInt value dest.layout.layout.size |>.mapError ScalarOps.scalarError)
  write place choice value dest

def bind
    (place : PlaceHooks Provenance (ThreadStacks.State K U) C MachineHooks.FrameExtra)
    (choice : C) (thread : UnixThread.Hooks (ThreadStacks.State K U))
    (base : UnixThreadDispatch.Hooks (ThreadStacks.State K U) D B I) :
    UnixThreadDispatch.Hooks (ThreadStacks.State K U) D B I := Id.run do
  let process : EnvVars.ProcessHooks (ThreadStacks.State K U) := {base.apple.process with
    family := base.signatures.family
    os := base.signatures.os
    activeThread := do return UInt32.ofNat (← get).machine.threads.activeThread.toNat
    threadIdTryFrom := fun raw => do
      match (← get).machine.threads.threadIdTryFrom raw.toNat with
      | .ok id => pure (some (UInt32.ofNat id.toNat))
      | .error _ => pure none}
  return {base with
    thread := thread
    writeScalar := write place choice
    writeNull := writeInt place choice 0
    unixGettid := fun _ => do
      let tid ← EnvVars.currentTid process
      lift (Scalar.fromUInt (BitVec.ofNat 128 tid.toNat) (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)
    apple := {base.apple with
      os := base.signatures.os
      thread := thread
      process := process
      libc := base.libc
      writeInt := writeInt place choice}}
end Miri.Interpreter.UnixThreadDispatchMachine
