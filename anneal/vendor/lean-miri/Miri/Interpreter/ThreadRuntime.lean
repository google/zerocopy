import Miri.Interpreter.ThreadLoops
import Miri.Interpreter.ThreadShimMachine
import Miri.Interpreter.CallMachine

/-! Coherent threaded runtime assembly. Spawned MIR root frames, ordinary
calls, TLS roots, scalar results and allocation extras share the same actual
machine dictionaries. Compiler ABI/body facts and host effects remain
required inputs; this is not a second executable MIR representation. -/
namespace Miri.Interpreter.ThreadRuntime
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency

structure Configuration (K U C O X F A Aff Payload : Type) where
  thread : ThreadMachine.Hooks K U C O X F A Aff
  access : PlaceMachine.AccessConfig K (ThreadStacks.Storage U)
  compiler : PlaceMachine.CompilerHooks K (ThreadStacks.Storage U) C
  lifecycle : CallMachine.Lifecycle K (ThreadStacks.Storage U) C
  unwind : Unwind.Hooks K (ThreadStacks.Storage U) C O
  retag : TypedRetag.Hooks K (ThreadStacks.Storage U)
  retagBudget : Nat
  copy : PlaceCopyHooks Provenance (ThreadStacks.State K U) C
  evaluatePlace : C → MIR.Place → Bool → ThreadStacks.M K U (RuntimePlace Provenance)
  extras : MemoryExtras.Hooks K (ThreadStacks.Storage U) Payload
  weakMemory : Bool

/-- Every constructed root frame uses canonical LoadedBody, compiler frame
relevance, global locals identity supply, FnEntry retag/argument protection,
real local storage/copy and actual after-pop unwind/cache behavior. -/
def thread [DecidableEq K] (config : Configuration K U C O X F A Aff Payload) :
    ThreadMachine.Hooks K U C O X F A Aff :=
  let access := MemoryExtras.bindAccess config.extras config.access
  let allocation := MemoryExtras.bindAllocation config.extras config.weakMemory config.thread.allocation
  let lifecycle := CallMachine.withUnwind config.lifecycle config.unwind
  let call := CallMachine.threadedHooks config.thread.functions.call lifecycle access allocation config.compiler
    config.retag config.retagBudget config.copy config.evaluatePlace
  let functions := {config.thread.functions with call}
  let spans := {config.thread.spans with debugAssertions := config.compiler.debugAssertions}
  ThreadShimMachine.bindMemory {config.thread with allocation, functions, spans}
    (PlaceMachine.placeHooks access allocation config.compiler)

/-- Return/unwind terminators share the exact frame cleanup/protector/cache
pipeline used by root calls and ordinary calls. -/
def control [DecidableEq K] (config : Configuration K U C O X F A Aff Payload)
    (base : ControlHooks Provenance LocalLayout MachineHooks.FrameExtra
      (MachineHooks.MachineState K (ThreadStacks.Storage U)) C (OpTy Provenance)) :
    ControlHooks Provenance LocalLayout MachineHooks.FrameExtra
      (MachineHooks.MachineState K (ThreadStacks.Storage U)) C (OpTy Provenance) :=
  let access := MemoryExtras.bindAccess config.extras config.access
  let allocation := MemoryExtras.bindAllocation config.extras config.weakMemory config.thread.allocation
  let lifecycle := CallMachine.withUnwind config.lifecycle config.unwind
  CallMachine.threadedControlHooks base lifecycle access allocation config.compiler config.copy config.retag

/-- Miri's ignored thread return slot has the fixed source Machine kind. -/
def miriThread (config : Configuration MiriMemoryKind U C O X F A Aff Payload) :
    ThreadMachine.Hooks MiriMemoryKind U C O X F A Aff :=
  {thread config with machineMemoryKind := .machine}

/-- TLS and normal-thread termination receive exactly the spawn/call dictionaries
above, including the same extras registry used for allocation and memory access. -/
def termination (config : Configuration MiriMemoryKind U C O X F A Aff Payload)
    (base : ThreadTerminationMachine.Hooks U C O X F A Aff Payload) :
    ThreadTerminationMachine.Hooks U C O X F A Aff Payload :=
  {base with
    tls := {base.tls with thread := miriThread config}}

/-- Scheduler iteration and callback/termination protocol are a single binding;
all callback take/restore actions are the checked source implementation. -/
def loop (config : Configuration MiriMemoryKind U C O X F A Aff Payload)
    (terminate : ThreadTerminationMachine.Hooks U C O X F A Aff Payload)
    (base : RunLoopHooks (ThreadStacks.State MiriMemoryKind U) C ThreadLoops.TakenTls)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind U) :
    RunLoopHooks (ThreadStacks.State MiriMemoryKind U) C ThreadLoops.TakenTls :=
  ThreadLoops.bindActual (termination config terminate) base scheduler

/-- The foreign Miri spawn/join arms share the same calls/allocations/retags as
the scheduler's TLS and root-frame cleanup. Reuse is a permitted choice input. -/
def shims (config : Configuration MiriMemoryKind U C O X F A Aff Payload)
    (choice : C) (reuseClock : Option VectorIdx)
    (base : MiriShims.Hooks Provenance (ThreadStacks.State MiriMemoryKind U)
      D (MPlaceTy Provenance) B I HostPath) :
    MiriShims.Hooks Provenance (ThreadStacks.State MiriMemoryKind U)
      D (MPlaceTy Provenance) B I HostPath :=
  let h := miriThread config
  ThreadShimMachine.bind h choice h.functions.unitLayout reuseClock base
end Miri.Interpreter.ThreadRuntime
