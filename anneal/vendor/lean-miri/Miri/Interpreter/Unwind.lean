import Miri.Interpreter.TypedMachineBindings

/-! Pinned shims/unwind.rs: handle_miri_start_unwind, handle_catch_unwind,
handle_stack_pop_unwind; machine.rs::after_stack_pop (profiling omitted).
Payload tokens are an internal representation of Thread::unwind_payloads:
actual typed immediates live in the arena and are removed when popped. They
are neither addresses nor allocation identities. Compiler/function-call and
memory operations remain required source operations. -/
namespace Miri.Interpreter.Unwind
open Miri.ABI Miri.Memory Miri.Concurrency
open MachineHooks (State M)

structure PayloadStore where
  nextToken : Nat
  values : Array (Nat × RvalueImmTy Provenance)

/-- Exact initial empty payload vector representation. -/
def PayloadStore.empty : PayloadStore := ⟨0, #[]⟩

structure User (Extra : Type) where
  payloads : PayloadStore
  extra : Extra

structure Hooks (K Extra C Other : Type) where
  payloads : Extra → PayloadStore
  setPayloads : PayloadStore → Extra → Extra
  readImmediate : C → OpTy Provenance → M K Extra (RvalueImmTy Provenance)
  readPointer : C → OpTy Provenance → M K Extra (Pointer (Option Provenance))
  forceAllocation : C → RuntimePlace Provenance → M K Extra (MPlaceTy Provenance)
  getPtrFn : C → Pointer (Option Provenance) → M K Extra (FnVal Other)
  /-- Source call_function uses Rust ABI, None destination, and these exact
  immediates/continuation. Bind to the canonical function-call implementation. -/
  callFunction : C → CallInstance → Array (RvalueImmTy Provenance) →
    ReturnContinuation → M K Extra Unit
  writeNull : C → MPlaceTy Provenance → M K Extra Unit
  writeScalar : C → Scalar Provenance → MPlaceTy Provenance → M K Extra Unit
  panicUnwinds : Bool

private def activeThread : M K Extra (ThreadId × ThreadRecord) := do
  let manager := (← get).machine.threads
  let some thread := manager.activeThread? |
    throw (.invalidProgram "unwind: invalid active thread")
  return (manager.activeThread, thread)

/-- Push after reading the complete typed immediate. Source fields in the
active thread and the arena are committed together. -/
def pushPayload (h : Hooks K Extra C Other) (payload : RvalueImmTy Provenance) :
    M K Extra Unit := do
  let (id, thread) ← activeThread
  let state ← get
  let store := h.payloads state.machine.user
  if store.values.any (fun entry => entry.1 == store.nextToken) then
    throw (.invalidProgram "unwind payload token is not fresh")
  let thread := { thread with unwindPayloads := thread.unwindPayloads ++ [store.nextToken] }
  let updatedStore : PayloadStore := {
    nextToken := store.nextToken + 1
    values := store.values.push (store.nextToken, payload) }
  let threads := { state.machine.threads with
    threads := state.machine.threads.threads.set id.toNat thread }
  let machine := { state.machine with
    threads := threads
    user := h.setPayloads updatedStore state.machine.user }
  set { state with machine := machine }

/-- Pop before resolving the catch function, as in the source. Missing or
ambiguous arena data is a representation obligation, never a fake payload. -/
def popPayload (h : Hooks K Extra C Other) : M K Extra (RvalueImmTy Provenance) := do
  let (id, thread) ← activeThread
  let some token := thread.unwindPayloads.getLast? |
    throw (.invalidProgram "unwind payload vector is empty")
  let state ← get
  let thread := { thread with unwindPayloads := thread.unwindPayloads.dropLast }
  let threads := { state.machine.threads with
    threads := state.machine.threads.threads.set id.toNat thread }
  set { state with machine := { state.machine with threads } }
  let state ← get
  let store := h.payloads state.machine.user
  let entries := store.values.filter (fun entry => entry.1 == token)
  let some entry := entries[0]? | throw (.invalidProgram "missing typed unwind payload")
  if entries.size != 1 then throw (.invalidProgram "ambiguous typed unwind payload")
  let store := { store with values := store.values.filter (fun entry => entry.1 != token) }
  set { state with machine := { state.machine with user := h.setPayloads store state.machine.user } }
  return entry.2

private def functionInstance (h : Hooks K Extra C Other) (choice : C)
    (pointer : Pointer (Option Provenance)) : M K Extra CallInstance := do
  match ← h.getPtrFn choice pointer with
  | .Instance fnInstance => return fnInstance
  | .Other _ => throw (.unsupported "foreign function pointer in unwind context")

/-- This operation only stores the payload. Its caller's unwind continuation
initiates unwinding; there is no invented jump here. -/
def handleStartUnwind (h : Hooks K Extra C Other) (choice : C)
    (payload : OpTy Provenance) : M K Extra Unit := do
  let value ← h.readImmediate choice payload
  pushPayload h value

/-- Source argument order, forced destination before calls, and post-call zero
write are retained. The metadata is installed on the frame active after the
try call, only for PanicStrategy::Unwind. -/
def handleCatchUnwind (h : Hooks K Extra C Other) (choice : C)
    (tryFn data catchFn : OpTy Provenance) (dest : RuntimePlace Provenance)
    (ret : Option MIR.BasicBlockId) : M K Extra Unit := do
  let tryPointer ← h.readPointer choice tryFn
  let data ← h.readImmediate choice data
  let catchPointer ← h.readPointer choice catchFn
  let dest ← h.forceAllocation choice dest
  let fnInstance ← functionInstance h choice tryPointer
  h.callFunction choice fnInstance #[data] (.goto ret .Continue)
  h.writeNull choice dest
  if h.panicUnwinds then
    let frame ← MachineHooks.currentFrame
    MachineHooks.setCurrentFrame { frame with extra := { frame.extra with
      catchUnwind := some ⟨catchPointer, data, dest, ret⟩ } }

/-- Source after-pop hook. The true return value is written before the payload
is popped. A pushed catch frame returns NoJump, preventing the old frame's
continuation from being followed by ControlFlow. -/
def afterStackPop (h : Hooks K Extra C Other) (choice : C)
    (extra : MachineHooks.FrameExtra) (unwinding : Bool) : M K Extra ReturnAction := do
  if unwinding then
    if let some caught := extra.catchUnwind then
      h.writeScalar choice (Scalar.fromBool true) caught.dest
      let payload ← popPayload h
      let fnInstance ← functionInstance h choice caught.catchFn
      h.callFunction choice fnInstance #[caught.data, payload] (.goto caught.ret .Unreachable)
      return .noJump
  return .normal

/-- The default concrete user-extension lens for payload storage. -/
def userHooks (base : Hooks K (User Extra) C Other) : Hooks K (User Extra) C Other :=
  { base with payloads := User.payloads, setPayloads := fun payloads user => { user with payloads } }

end Miri.Interpreter.Unwind
