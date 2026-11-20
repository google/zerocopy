import Miri.Interpreter.ThreadMachine
import Miri.Interpreter.MiriShims

namespace Miri.Interpreter.ThreadShimMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency

/-- Install concrete scalar memory writes including source validation. -/
def bindMemory (h : ThreadMachine.Hooks K U C O X F A Aff)
    (place : PlaceHooks Provenance (ThreadStacks.State K U) C MachineHooks.FrameExtra) :
    ThreadMachine.Hooks K U C O X F A Aff :=
  {h with writeScalar := fun choice scalar dest =>
    writePlaceImmediate place choice (.scalar scalar) ⟨.memory dest.mplace,dest.layout⟩}

/-- miri_thread_spawn/join use actual typed memory destinations and Rust ABI.
The clock-reuse choice is an explicit permitted execution input. -/
def bind [DecidableEq K] (h : ThreadMachine.Hooks K U C O X F A Aff)
    (choice : C) (unitLayout : LocalLayout) (reuseClock : Option VectorIdx)
    (base : MiriShims.Hooks Provenance (ThreadStacks.State K U) D (MPlaceTy Provenance) B I HostPath) :
    MiriShims.Hooks Provenance (ThreadStacks.State K U) D (MPlaceTy Provenance) B I HostPath :=
  {base with
    spawnThread := fun dest routine argument => do
      let _ ← ThreadMachine.startRegularThread h choice (some dest) routine h.functions.call.rustAbi
        argument unitLayout reuseClock
      pure ()
    threadFromUsize := ThreadMachine.threadFromUsize
    joinExclusive := fun joined success dest => ThreadMachine.joinExclusive h choice joined (Scalar.fromBool success) dest
    yieldThread := do ThreadStacks.installManager (ThreadManager.yield (← get).machine.threads)}
end Miri.Interpreter.ThreadShimMachine
