import Miri.Concurrency.SyncRuntime

/-! Complete pinned concurrency/init_once.rs state transitions and typed
callback execution. Rc identity is supplied by the same canonical registry. -/
namespace Miri.Concurrency.InitOnce
open Miri.Interpreter
abbrev M := EStateM StepError
inductive Status where | Uninitialized | Begun | Complete deriving DecidableEq, Repr
structure State where
  status : Status := .Uninitialized
  waiters : List ThreadId := []
  clock : VClock := .default
  deriving Repr
structure Hooks (S R V D : Type) where
  runtime : SyncRuntime.Hooks S R V D
  get : R → M S State
  put : R → State → M S Unit
  new : M S R

def begin (h : Hooks S R V D) (ref : R) : M S Unit := do
  let state ← h.get ref
  if state.status != .Uninitialized then throw (.invalidProgram "beginning already begun or complete init once")
  h.put ref { state with status := .Begun }
private def release (h : Hooks S R V D) (ref : R) : M S Unit := do
  match h.runtime.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.prepareRelease (← h.runtime.global) (← h.runtime.threads) with
    | .error error => throw (h.runtime.error (SyncError.ofClock error))
    | .ok (clock,finish) =>
      let state ← h.get ref
      h.put ref {state with clock := clock}
      match finish with
      | .error error => throw (h.runtime.error (SyncError.ofClock error))
      | .ok global => h.runtime.putGlobal global

private def unblock (h : Hooks S R V D) (thread : ThreadId) : M S Unit := do
  match (← h.runtime.threads).unblockThread thread .InitOnce with
  | .error error => throw (h.runtime.error (.threadManager error))
  | .ok (threads,obligation) =>
    h.runtime.putThreads threads
    SyncRuntime.runUnblockCallback h.runtime obligation

def enqueueAndBlock (h : Hooks S R V D) (ref : R) (callback : SyncRuntime.Callback S)
    (capture : Option (SyncRuntime.UserCapture R D) := none) : M S Unit := do
  let state ← h.get ref
  let thread := (← h.runtime.threads).activeThread
  if state.status == .Complete then throw (.invalidProgram "queueing on complete init once")
  h.put ref { state with waiters := state.waiters ++ [thread] }
  let token ← SyncRuntime.register h.runtime (capture.map .user) callback
  match (← h.runtime.threads).blockThread .InitOnce none token with
  | .error error =>
    SyncRuntime.cancelCallback h.runtime token
    throw (h.runtime.error (.threadManager error))
  | .ok threads => h.runtime.putThreads threads

def complete (h : Hooks S R V D) (ref : R) : M S Unit := do
  let state ← h.get ref
  if state.status != .Begun then throw (.invalidProgram "completing already complete or uninit init once")
  h.put ref { state with status := .Complete }
  release h ref
  let state ← h.get ref
  let waiters := state.waiters
  h.put ref { state with waiters := [] }
  for waiter in waiters do unblock h waiter

def fail (h : Hooks S R V D) (ref : R) : M S Unit := do
  let state ← h.get ref
  if state.status != .Begun then throw (.invalidProgram "failing already complete or uninit init once")
  h.put ref { state with status := .Uninitialized }
  release h ref
  let state ← h.get ref
  if let waiter :: rest := state.waiters then
    h.put ref { state with waiters := rest }
    unblock h waiter

def observeCompleted (h : Hooks S R V D) (ref : R) : M S Unit := do
  let state ← h.get ref
  if state.status != .Complete then throw (.invalidProgram "observing incomplete init once")
  match h.runtime.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.acquire (← h.runtime.global) (← h.runtime.threads) state.clock with
    | .error error => throw (h.runtime.error (SyncError.ofClock error))
    | .ok global => h.runtime.putGlobal global
end Miri.Concurrency.InitOnce
