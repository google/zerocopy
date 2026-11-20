import Miri.Interpreter.UnixThread
import Miri.Interpreter.RawMemoryMachine

/-! Canonical pthread lifecycles and thread-name byte effects. Pointer/ABI
compiler services remain explicit; create and join invoke actual ThreadMachine. -/
namespace Miri.Interpreter.UnixThreadMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
private def lift (value : Except StepError A) : ThreadStacks.M K U A :=
  match value with | .ok value => pure value | .error error => throw error

def bind [DecidableEq K] (thread : ThreadMachine.Hooks K U C O X F A Aff)
    (access : PlaceMachine.AccessConfig K (ThreadStacks.Storage U))
    (choice : C) (cNonUnwindAbi : X) (reuseClock : Option VectorIdx)
    (misalignment : Pointer (Option Provenance) → Align → ThreadStacks.M K U (Option Misalignment))
    (base : UnixThread.Hooks (ThreadStacks.State K U)) : UnixThread.Hooks (ThreadStacks.State K U) :=
  let scalar := fun operand => do
    let value ← PlaceMachine.readImmediate access operand
    lift (value.imm.toScalar.mapError ScalarOps.immediateError)
  let pointer := fun operand => do
    lift ((← scalar operand).toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
  {base with
    threads := do return (← get).machine.threads
    putThreads := ThreadStacks.installManager
    start := fun output routine argument layout => do
      let _ ← ThreadMachine.startRegularThread thread choice output routine cNonUnwindAbi argument layout reuseClock
      pure ()
    join := ThreadMachine.joinExclusive thread choice
    detach := fun id => do
      match (← get).machine.threads.detachThread id false with
      | .ok manager => ThreadStacks.installManager manager
      | .error (.detachAlreadyConsumed _) | .error (.detachNotJoinable _) =>
        throw (.undefinedBehavior "trying to detach an already joined or detached thread")
      | .error error => throw (.invalidProgram s!"pthread detach thread manager: {reprStr error}")
    readScalar := scalar
    readPointer := pointer
    readImmediate := PlaceMachine.readImmediate access
    scalarPointer := fun value => lift (value.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
    scalarUsize := fun value => lift (value.toTargetUsize access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
    dereference := fun operand layout => do
      let pointer ← pointer operand
      unless layout.layout.isSized do throw (.invalidProgram "deref_pointer_as requires sized pthread_t")
      return ⟨⟨pointer,.none,← misalignment pointer layout.layout.align.abi⟩,layout⟩
    writeCString := RawMemoryMachine.writeCString access ⟨access.runtime.pointerSize⟩ }

/-- Keep the required source C-string scan plus second full initialized read. -/
def bindStrings (strings : MemoryShims.Hooks Provenance S D MD B I) (scanBudget : Nat)
    (base : UnixThread.Hooks S) : UnixThread.Hooks S :=
  {base with readCString := MemoryShims.readCString strings scanBudget}
end Miri.Interpreter.UnixThreadMachine
