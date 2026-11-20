import Miri.Concurrency.Sync
import Miri.Interpreter.PlaceTypes
import Miri.Interpreter.Step

/-! Source concurrency/sync.rs futex wait/wake with an actual optional clock
handler and typed FnOnce captures. None never reads or manufactures a global
clock. Callback tokens use the owner's shared thread callback identity supply.
-/
namespace Miri.Concurrency.FutexRuntime
open Miri.Interpreter Miri.Memory
abbrev M := EStateM StepError
structure Ref where
  index : Nat
  deriving DecidableEq, Repr
structure Callback (D : Type) where
  futex : Ref
  destination : D
structure Storage (D : Type) where
  objects : Array FutexState := #[]
  callbacks : Array (Nat × Callback D) := #[]
structure Hooks (S D : Type) where
  handler : M S SyncClockHandler
  global : M S (Option GlobalState)
  putGlobal : GlobalState → M S Unit
  threads : M S ThreadManager
  putThreads : ThreadManager → M S Unit
  communicate : M S Bool
  futex : Ref → M S FutexState
  putFutex : Ref → FutexState → M S Unit
  register : Callback D → M S Nat
  take : Nat → M S (Callback D)
  cancel : Nat → M S Unit
  unblock : ThreadId → (Nat → UnblockKind → M S Unit) → M S Unit
  ready : D → M S Unit
  timedOut : D → M S Unit
  error : SyncError → StepError

private def global (h : Hooks S D) : M S GlobalState := do
  let some g ← h.global | throw (.invalidProgram "vector-clock sync handler lacks canonical global")
  pure g
private def acquire (h : Hooks S D) (clock : VClock) : M S Unit := do
  match ← h.handler with
  | .none => pure ()
  | .vectorClocks =>
    match (← global h).acquireClock (← h.threads) clock with
    | .error error => throw (h.error (.globalState error))
    | .ok g => h.putGlobal g
private def release (h : Hooks S D) (ref : Ref) : M S Unit := do
  match ← h.handler with
  | .none => pure ()
  | .vectorClocks =>
    let g ← global h
    let threads ← h.threads
    let (_,current) ← match g.activeThreadState threads with
      | .ok value => pure value
      | .error error => throw (h.error (.globalState error))
    -- release_clock invokes its closure on the old clock before incrementing.
    h.putFutex ref {(← h.futex ref) with clock := current.clock}
    match g.releaseClock threads with
    | .error error => throw (h.error (.globalState error))
    | .ok (g,_) => h.putGlobal g

/-- Box<Self> is consumed before the first callback effect. Ready acquires;
timeout removes the active waiter; only then does the syscall result write. -/
def invoke (h : Hooks S D) (token : Nat) (kind : UnblockKind) : M S Unit := do
  let callback ← h.take token
  match kind with
  | .Ready =>
    acquire h (← h.futex callback.futex).clock
    h.ready callback.destination
  | .TimedOut =>
    let state ← h.futex callback.futex
    let active := (← h.threads).activeThread
    h.putFutex callback.futex {state with waiters := state.waiters.filter (·.thread != active)}
    h.timedOut callback.destination

/-- Enqueue precedes callback creation and source block-thread constraints.
A failed block drops the callback but retains the already appended waiter. -/
def wait (h : Hooks S D) (ref : Ref) (bitset : UInt32)
    (deadline : Option ThreadDeadline) (destination : D) : M S Unit := do
  let active := (← h.threads).activeThread
  let state ← h.futex ref
  if state.waiters.any (·.thread == active) then
    throw (h.error (.futexThreadAlreadyWaiting active))
  h.putFutex ref {state with waiters := state.waiters ++ [⟨active,bitset⟩]}
  let token ← h.register ⟨ref,destination⟩
  try
    let communicate ← h.communicate
    let blocked ← match (← h.threads).blockThreadWithRuntimeConstraints .Futex deadline token communicate with
      | .ok blocked => pure blocked
      | .error error => throw (h.error (.blockThreadSource error))
    h.putThreads blocked
  catch error =>
    unless (← h.threads).threads.any (fun t => match t.state with | .Blocked _ _ actual => actual == token | _ => false) do
      h.cancel token
    throw error

private def extract (waiters : List FutexWaiter) (bitset : UInt32) (count : Nat) :
    List FutexWaiter × List FutexWaiter :=
  match waiters with
  | [] => ([],[])
  | w::rest =>
    let selected := count > 0 && (w.bitset &&& bitset) != 0
    let (take,keep) := extract rest bitset (if selected then count-1 else count)
    if selected then (w::take,keep) else (take,w::keep)

/-- Release precedes extraction, including count=0. All matching removals
precede any callback; unblocks execute FIFO with actual stack switching. -/
def wake (h : Hooks S D) (ref : Ref) (bitset : UInt32) (count : Nat) : M S Nat := do
  release h ref
  let state ← h.futex ref
  let (selected,kept) := extract state.waiters bitset count
  h.putFutex ref {state with waiters := kept}
  for waiter in selected do h.unblock waiter.thread (invoke h)
  pure selected.length
end Miri.Concurrency.FutexRuntime
