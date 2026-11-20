import Miri.Interpreter.ThreadLocal
import Miri.Concurrency.Lifecycle

/-! Pinned concurrency/thread.rs::terminate_active_thread (756-824) and
unblock_thread (849-867). This executes cleanup and callbacks, preserving all
prior memory/hook/manager effects on failure. TLS map removal precedes frees;
race termination follows all frees; joiners are discovered afterward. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.Concurrency

inductive ThreadExitRace where
  | none
  | vectorClocks (global : GlobalState)

inductive ThreadExitError (LeafError : Type) where
  | thread (error : ThreadError)
  | tls (error : ThreadLocalError)
  | deallocation (error : MemoryLifecycleError)
  | race (error : GlobalStateError)
  | leaf (error : LeafError)
  | pointerIdentityMismatch
  deriving Repr

structure ThreadExitState (P E H : Type) where
  tls : ThreadLocalState P E H
  staticRoots : Array AllocId
  race : ThreadExitRace

abbrev ThreadExitM (P E H Error A : Type) := EStateM (ThreadExitError Error) (ThreadExitState P E H) A

structure ThreadExitQueries (P E H ProvExtra Error : Type) where
  deallocation : MemoryLifecycleHooks P E MiriMemoryKind H ProvExtra
  /-- Execute the registered callback, including its join-clock and return
  destination actions, in the already-selected waiter's context. -/
  unblockCallback : UnblockCallbackObligation → ThreadExitM P E H Error Unit

private def ThreadExitState.manager (state : ThreadExitState P E H) : ThreadManager := state.tls.manager
private def setManager (value : ThreadManager) : ThreadExitM P E H Error Unit := do
  let state ← EStateM.get
  EStateM.set { state with tls := { state.tls with manager := value } }

/-- Call only after the stack-empty callback actually returned Ready. The
callback itself is orchestrated by the TLS destructor state machine. -/
def terminateActiveThread [PointerProvenance P] (queries : ThreadExitQueries P E H ProvExtra Error)
    (forExit : Bool) : ThreadExitM P E H Error Unit := do
  let initial ← EStateM.get
  let gone := initial.manager.activeThread
  let some thread := initial.manager.activeThread? | throw (.thread (.activeIdOutOfBounds gone))
  -- Source marks Terminated before asserting that its stack is empty.
  let marked := { initial.manager with threads := initial.manager.threads.set gone.toNat { thread with state := .Terminated } }
  setManager marked
  unless forExit || thread.stackFrames.isEmpty do throw (.thread (.stackNotEmptyAtTermination gone))
  let beforeCleanup ← EStateM.get
  let entries := beforeCleanup.manager.threadLocalAllocs.filter (·.thread == gone)
  let retained := beforeCleanup.manager.threadLocalAllocs.filter (·.thread != gone)
  let oldPointers := beforeCleanup.tls.pointers
  EStateM.set { beforeCleanup with tls := { beforeCleanup.tls with
    manager := { beforeCleanup.manager with threadLocalAllocs := retained },
    pointers := oldPointers.filter (·.thread != gone) } }
  for entry in entries do
    let some pointer := oldPointers.find? (fun p => p.runtimeId.value.toNat == entry.pointerToken)
      | throw (.tls (.missingPointerToken entry.pointerToken))
    unless pointer.definition == entry.definitionToken && pointer.thread == gone do throw .pointerIdentityMismatch
    let state ← EStateM.get
    if forExit then
      -- Source ignores a pointer without an allocation provenance here.
      if let some allocId := PointerProvenance.getAllocId pointer.pointer.provenance then
        EStateM.set { state with staticRoots := state.staticRoots.push allocId }
    else
      let result := MemoryLifecycle.deallocatePtr state.tls.memory state.tls.hooks
        (⟨pointer.pointer.offset, some pointer.pointer.provenance⟩) none (.machine .tls) queries.deallocation
      EStateM.set { state with tls := { state.tls with memory := result.memory, hooks := result.hooks } }
      match result.outcome with
      | .ok () => pure ()
      | .error error => throw (.deallocation error)
  let afterCleanup ← EStateM.get
  match afterCleanup.race with
  | .none => pure ()
  | .vectorClocks global =>
    match GlobalState.threadTerminated global afterCleanup.manager with
    | .error error => throw (.race error)
    | .ok global => EStateM.set { afterCleanup with race := .vectorClocks global }
  let afterRace ← EStateM.get
  let mut waiters := #[]
  for i in [:afterRace.manager.threads.length] do
    let some thread := afterRace.manager.threads[i]? | throw (.thread .invalidId)
    if thread.isBlockedOn (.Join gone) then
      match ThreadId.ofNat i with
      | .ok id => waiters := waiters.push id
      | .error error => throw (.thread error)
  for waiter in waiters do
    let before ← EStateM.get
    -- Source enables before checking its previous blocked state.
    let some record := before.manager.thread? waiter | throw (.thread .invalidId)
    let enabled := { before.manager with threads := before.manager.threads.set waiter.toNat { record with state := .Enabled } }
    setManager enabled
    let (reason,callbackToken) ← match record.state with
      | .Blocked reason _ callback => pure (reason,callback)
      | _ => throw (.thread (.targetNotBlocked waiter))
    unless reason == .Join gone do throw (.thread (.wrongBlockReason (.Join gone) reason))
    let callback : UnblockCallbackObligation := ⟨waiter,before.manager.activeThread,reason,callbackToken,.Ready⟩
    setManager { enabled with activeThread := waiter }
    queries.unblockCallback callback
    -- Failure above deliberately skips restoration, matching source `?`.
    let after ← EStateM.get
    setManager (after.manager.restoreAfterCallback callback)

end Miri.Interpreter
