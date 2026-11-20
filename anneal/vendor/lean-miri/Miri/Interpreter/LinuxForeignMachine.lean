import Miri.Interpreter.LinuxForeign
import Miri.Interpreter.UnixMemoryMachine
import Miri.Interpreter.MainMachine

namespace Miri.Interpreter.LinuxForeignMachine
open Miri.ABI Miri.Memory

/-- Actual mmap allocation/deallocation plus Linux mremap's distinct Zero
initialization of growth bytes. Address and reuse choices are explicit. -/
def bindMemory (allocation : UnixMemoryMachine.Hooks U C Host Payload) (choice : C)
    (choices : UnixMemoryMachine.Choices)
    (base : LinuxMemory.Hooks (UnixMemoryMachine.State U) Place B I) :
    UnixMemoryMachine.M U (LinuxMemory.Hooks (UnixMemoryMachine.State U) Place B I) := do
  let memory ← UnixMemoryMachine.bind allocation choice choices base.memory
  return {base with memory, reallocateZero := fun pointer oldSize newSize align => do
    let config ← UnixMemoryMachine.allocationForKind allocation .mmap
    let pointer ← ReallocationDriver.reallocate config pointer (some (oldSize,align)) newSize align
      (.machine .mmap) .Zero choices.allocation choices.reuse
    return pointer.withOptionalProvenance}

/-- Lift the existing physical pointer/allocation engine through a lawful
record embedding. Every memory/thread/race/tree/error prefix is retained. -/
private def addressAction (lens : FunctionPointers.AddressLens User Payload)
    (action : PointerMachine.M K Payload A) : MachineHooks.M K User A := fun state =>
  let initial : PointerMachine.State K Payload := ⟨state.stack,{state.machine with user := lens.get state.machine.user}⟩
  match action initial with
  | .ok value after => .ok value ⟨after.stack,{after.machine with user := lens.put state.machine.user after.machine.user}⟩
  | .error error after => .error error ⟨after.stack,{after.machine with user := lens.put state.machine.user after.machine.user}⟩

def bindReallocateVia (lens : FunctionPointers.AddressLens User Payload)
    (allocation : UnixMemoryMachine.Hooks Payload C Host Extra) (choices : UnixMemoryMachine.Choices)
    (base : LinuxMemory.Hooks (MachineHooks.State MiriMemoryKind User) Place B I) :
    LinuxMemory.Hooks (MachineHooks.State MiriMemoryKind User) Place B I := {
  base with reallocateZero := fun pointer oldSize newSize align => addressAction lens do
    let config ← UnixMemoryMachine.allocationForKind allocation .mmap
    let pointer ← ReallocationDriver.reallocate config pointer (some (oldSize,align)) newSize align
      (.machine .mmap) .Zero choices.allocation choices.reuse
    return pointer.withOptionalProvenance }

/-- Canonical ThreadStacks stores the address engine as its actual user;
these kernel-checked laws justify lifting allocation without shadow state. -/
def threadAddressLens : FunctionPointers.AddressLens (ThreadStacks.Storage (PointerMachine.User U)) U where
  get := fun user => user.user
  put := fun user addresses => {user with user := addresses}
  getPut := by intros; rfl
  putGet := by intros; rfl
  putPut := by intros; rfl

/-- GNU thread atexit shares the actual static symbol map, compiler instance
registry and destructor arena. DSO comparison remains address-only as source. -/
def bindTls (main : MainMachine.Hooks U C O X FnABI ArgABI Aff P)
    (statics : U → ExternStatic.State)
    (base : LinuxForeign.Hooks (MainMachine.State U) Place H D Other E HM Os B I) :
    LinuxForeign.Hooks (MainMachine.State U) Place H D Other E HM Os B I := {
  base with
  dsoHandle := do
    let entries := (statics (← get).machine.user.user).symbols.filter (·.1 == "__dso_handle")
    unless entries.size == 1 do throw (.invalidProgram "canonical __dso_handle static missing or duplicated")
    let some (_,pointer) := entries[0]? | throw (.invalidProgram "checked __dso_handle entry missing")
    pure pointer.withOptionalProvenance
  getPtrFnInstance := fun pointer => do
    match ← FunctionPointers.getPtrFn main.functions pointer with
    | .Instance fnInstance => pure fnInstance
    | .Other _ => throw (.unsupported "GNU atexit destructor is not a compiler instance")
  addThreadAtexit := fun fnInstance data => do
    let active := (← get).machine.threads.activeThread
    let span ← AllocationDriver.currentUserRelevantSpan main.termination.tls.thread.spans
    let tls := main.termination.tls
    modify fun state =>
      let store := tls.data state.machine.user.user
      let values := store.values.addThreadAtexit active ⟨fnInstance,data,span⟩
      let payload := tls.putData state.machine.user.user {store with values}
      {state with machine := {state.machine with user := {state.machine.user with user := payload}}} }
end Miri.Interpreter.LinuxForeignMachine
