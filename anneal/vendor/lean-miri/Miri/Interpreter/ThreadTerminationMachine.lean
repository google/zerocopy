import Miri.Interpreter.ThreadTlsMachine

/-! Source thread.rs:756–824, canonical Ready→termination integration. TLS
metadata is removed before frees, race finish follows successful cleanup, then
each typed join continuation executes in the waiter's actual frame context. -/
namespace Miri.Interpreter.ThreadTerminationMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency Miri.TreeBorrows
abbrev M := ThreadTlsMachine.M

structure Hooks (U C O X F A Aff Payload : Type) where
  tls : ThreadTlsMachine.Hooks U C O X F A Aff
  deallocationError : MemoryLifecycleError → StepError
  /-- Full-state deallocation operation, which owns active stack/address
  context instead of retaining it in a startup-time hook record. -/
  deallocate : Pointer (Option Provenance) → Option (Size × Align) →
    MemoryKind MiriMemoryKind → M U Unit

private def updateData (h : Hooks U C O X F A Aff Payload)
    (f : ThreadTlsMachine.Data → ThreadTlsMachine.Data) : M U Unit :=
  modify fun state => {state with machine := {state.machine with user := {state.machine.user with
    user := h.tls.putData state.machine.user.user (f (h.tls.data state.machine.user.user))}}}

/-- No token-only compatibility stack controls termination: the canonical
actual frame array determines the source empty-stack assertion. -/
def terminate (h : Hooks U C O X F A Aff Payload) (choice : C) (forExit : Bool) : M U Unit := do
  ThreadStacks.synchronize
  let state ← get
  let manager := state.machine.threads
  let gone := manager.activeThread
  let some thread := manager.activeThread? | throw (.invalidProgram "terminating active thread missing")
  ThreadStacks.installManager {manager with threads := manager.threads.set gone.toNat {thread with state := .Terminated}}
  unless forExit || state.stack.frames.isEmpty do
    throw (.invalidProgram "only an actual empty stack can terminate")
  let manager := (← get).machine.threads
  let entries := manager.threadLocalAllocs.filter (fun entry => entry.thread == gone)
  let pointers := (h.tls.data (← get).machine.user.user).statics
  ThreadStacks.installManager {manager with threadLocalAllocs := manager.threadLocalAllocs.filter fun entry => entry.thread != gone}
  updateData h fun data => {data with statics := data.statics.filter fun entry => entry.thread != gone}
  for entry in entries do
    let some pointer := pointers.find? (fun pointer => pointer.runtimeId.value.toNat == entry.pointerToken) |
      throw (.invalidProgram "TLS allocation token has no canonical pointer")
    unless pointer.definition == entry.definitionToken && pointer.thread == gone do
      throw (.invalidProgram "TLS allocation pointer identity mismatch")
    if forExit then
      if let some id := PointerProvenance.getAllocId pointer.pointer.provenance then
        updateData h fun data => {data with staticRoots := data.staticRoots.push id}
    else
      h.deallocate pointer.pointer.withOptionalProvenance none (.machine .tls)
  let machine := (← get).machine

  if let some global := machine.dataRace then
    let global ← match global.threadTerminated machine.threads with
      | .ok global => pure global
      | .error error => throw (.callback s!"thread termination clocks: {reprStr error}")
    modify fun state => {state with machine := {state.machine with dataRace := some global}}
  let manager := (← get).machine.threads
  let mut waiters := #[]
  for i in [:manager.threads.length] do
    if let some thread := manager.threads[i]? then
      if thread.isBlockedOn (.Join gone) then
        let waiter ← match ThreadId.ofNat i with
          | .ok waiter => pure waiter
          | .error error => throw (.invalidProgram s!"waiter identity: {reprStr error}")
        waiters := waiters.push waiter
  for waiter in waiters do
    ThreadStacks.unblockThread waiter (.Join gone) (ThreadMachine.resumeJoin h.tls.thread choice)

/-- Bind this to the scheduler's normal-thread callback. Program exit has a
separate exit handler and its explicit for_exit cleanup policy. -/
def onStackEmpty (h : Hooks U C O X F A Aff Payload) (choice : C) : M U StackEmptyCallbackResult := do
  match ← ThreadTlsMachine.onStackEmpty h.tls choice with
  | .Pending => return .Pending
  | .Ready =>
    terminate h choice false
    return .Ready
end Miri.Interpreter.ThreadTerminationMachine
