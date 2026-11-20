import Miri.Interpreter.Readiness

/-! Pinned unix/poll.rs. Compiler field/layout queries, actual memory access and
monotonic deadline creation are mandatory leaves, never synthetic pollfd data. -/
namespace Miri.Interpreter.PollShims
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
inductive DeferredBackend (S : Type) where
  | legacy
  | typed (block : Nat → Array (Int32 × MPlaceTy Provenance) → MPlaceTy Provenance → Option ThreadDeadline → M S Unit)
structure Hooks (S F Iter : Type) where
  deferred : DeferredBackend S
  readiness : Readiness.Hooks S F
  /-- True exactly for Linux, Android, FreeBSD, Illumos target OS. -/
  hasRdHup : Bool
  libcU16 : String → M S UInt16
  readI32 : OpTy Provenance → M S Int32
  /-- Query nfds_t layout, read scalar, signed conversion at that size, checked u64. -/
  readNfds : OpTy Provenance → M S UInt64
  derefArray : OpTy Provenance → String → UInt64 → M S (MPlaceTy Provenance)
  arrayFields : MPlaceTy Provenance → M S Iter
  nextField : Iter → M S (Option (MPlaceTy Provenance × Iter))
  namedField : MPlaceTy Provenance → String → M S (MPlaceTy Provenance)
  readFieldI32 : MPlaceTy Provenance → M S Int32
  readFieldU16 : MPlaceTy Provenance → M S UInt16
  writeU16 : UInt16 → MPlaceTy Provenance → M S Unit
  writeU32 : UInt32 → MPlaceTy Provenance → M S Unit
  /-- Actual FD-table lookup clones a reference, including temporary is_some lookup. -/
  lookupFd : Int32 → M S (Option F)
  newWatcher : M S Nat
  deadlineMillis : UInt32 → M S ThreadDeadline
  /-- Explicit execution resource for source effectful array iteration. -/
  iterationBudget : Nat

def onError (action : M S A) (cleanup : M S Unit) : M S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state =>
    match cleanup state with | .ok _ state => .error error state | .error next state => .error next state

def block (h : Readiness.Hooks S F) (deadline : Option ThreadDeadline)
    (callback : SyncRuntime.Callback S) : M S Unit := do
  let runtime := h.runtime
  let registry ← runtime.callbacks
  -- Canonical SyncRuntime owns source FnOnce take-before-invoke semantics.
  let (registry,token) := registry.register callback
  runtime.putCallbacks registry
  match (← runtime.threads).blockThreadWithRuntimeConstraints .Readiness deadline token runtime.communicate with
  | .error error =>
    SyncRuntime.cancelCallback runtime token
    throw (runtime.error (.blockThreadSource error))
  | .ok threads => runtime.putThreads threads

def toFlags (h : Hooks S F I) (ready : Files.Readiness) : M S UInt16 := do
  let input ← h.libcU16 "POLLIN"
  let output ← h.libcU16 "POLLOUT"
  let hup ← h.libcU16 "POLLHUP"
  let err ← h.libcU16 "POLLERR"
  let mut result := 0
  if ready.readable then result := result ||| input
  if ready.writable then result := result ||| output
  if ready.writeClosed then result := result ||| hup
  if ready.error then result := result ||| err
  if h.hasRdHup then
    let rd ← h.libcU16 "POLLRDHUP"
    if ready.readClosed then result := result ||| rd
  return result

def fromFlags (h : Hooks S F I) (flags : UInt16) : M S Files.Readiness := do
  let input ← h.libcU16 "POLLIN"
  let output ← h.libcU16 "POLLOUT"
  let hup ← h.libcU16 "POLLHUP"
  let err ← h.libcU16 "POLLERR"
  let invalid ← h.libcU16 "POLLNVAL"
  let mut flags := flags
  let mut result : Files.Readiness := { writeClosed := true, error := true }
  if flags &&& input == input then
    result := { result with readable := true }
    flags := flags &&& ~~~input
  if flags &&& output == output then
    result := { result with writable := true }
    flags := flags &&& ~~~output
  for ignored in #[hup,err,invalid] do
    if flags &&& ignored == ignored then flags := flags &&& ~~~ignored
  if h.hasRdHup then
    let rd ← h.libcU16 "POLLRDHUP"
    if flags &&& rd == rd then
      result := { result with readClosed := true }
      flags := flags &&& ~~~rd
  if flags != 0 then throw (.unsupported "poll: unsupported poll event bits")
  return result

def checkedIncrement (value : UInt32) : M S UInt32 := do
  if value == 4294967295 then throw (.invalidProgram "source u32 strict_add overflow")
  return value + 1

private def collect (h : Hooks S F I) (wakeBudget budget watcher : Nat) (iter : I)
    (interests : Array (Int32 × MPlaceTy Provenance)) (invalid : UInt32) :
    M S (Array (Int32 × MPlaceTy Provenance) × UInt32) := do
  match budget with
  | 0 => throw (.unsupported "poll: array iteration resource exhausted")
  | budget + 1 =>
    let some (entry,iter) ← h.nextField iter | return (interests,invalid)
    let number ← h.readFieldI32 (← h.namedField entry "fd")
    let events ← h.readFieldU16 (← h.namedField entry "events")
    let revents ← h.namedField entry "revents"
    let relevant ← fromFlags h events
    let existing ← h.lookupFd number
    let present ← match existing with
      | none => pure false
      | some fd => h.readiness.dropFd fd *> pure true
    let mut interests := interests
    let mut invalid := invalid
    let mut flags := 0
    if present then
      if interests.any (·.1 == number) then
        throw (.unsupported "poll: multiple interests for same file descriptor")
      interests := interests.push (number,revents)
      if number < 0 then throw (.invalidProgram "poll: existing negative FD cannot convert to u64")
      if !(← Readiness.addInterest wakeBudget h.readiness watcher number relevant false number.toUInt32.toUInt64) then
        throw (.invalidProgram "poll: duplicate watcher interest after uniqueness check")
    else if number >= 0 then
      invalid := (← checkedIncrement invalid)
      flags := (← h.libcU16 "POLLNVAL")
    h.writeU16 flags revents
    collect h wakeBudget budget watcher iter interests invalid

/-- ready_count is sampled before getReadyInterests processes delayed updates. -/
def writeReady (budget : Nat) (h : Hooks S F I) (watcher : Nat)
    (interests : Array (Int32 × MPlaceTy Provenance)) : M S UInt32 := do
  let ready ← Readiness.getReadyInterests budget (← Readiness.readyCount h.readiness watcher) h.readiness watcher
  let mut count := 0
  for interest in ready do
    if interest.data > 2147483647 then throw (.invalidProgram "poll: readiness data is not FD")
    let number := interest.data.toUInt32.toInt32
    let some (_,place) := interests.find? (·.1 == number)
      | throw (.invalidProgram "poll: ready interest should exist")
    count := (← checkedIncrement count)
    h.writeU16 (← toFlags h interest.active) place
  return count

def poll (budget : Nat) (h : Hooks S F I) (fds nfds timeout : OpTy Provenance)
    (dest : MPlaceTy Provenance) : M S Unit := do
  let length ← h.readNfds nfds
  let timeout ← h.readI32 timeout
  let iter ← h.arrayFields (← h.derefArray fds "pollfd" length)
  let watcher ← h.newWatcher
  let pending : Option (Option ThreadDeadline × Array (Int32 × MPlaceTy Provenance)) ← onError (do
    let (interests,invalid) ← collect h budget h.iterationBudget watcher iter #[] 0
    let immediate : Bool ← if timeout == 0 then pure true else if invalid > 0 then pure true
      else do pure ((← Readiness.readyCount h.readiness watcher) > 0)
    if immediate then
      let count ← writeReady budget h watcher interests
      if count.toNat + invalid.toNat > 4294967295 then throw (.invalidProgram "poll: total strict_add overflow")
      h.writeU32 (count + invalid) dest
      return none
    Readiness.addBlockedThread h.readiness watcher (← h.readiness.runtime.threads).activeThread
    let deadline ← if timeout > 0 then (h.deadlineMillis timeout.toUInt32).map some else pure none
    pure (some (deadline,interests))
  ) (h.readiness.dropWatcher watcher)
  match pending with
  | none => h.readiness.dropWatcher watcher
  | some (deadline,interests) =>
    match h.deferred with
    | .typed block => block watcher interests dest deadline
    | .legacy => onError (block h.readiness deadline fun reason => Files.withDrop (do
        match reason with
        | .TimedOut => h.writeU32 0 dest
        | .Ready => h.writeU32 (← writeReady budget h watcher interests) dest
      ) (h.readiness.dropWatcher watcher)) (h.readiness.dropWatcher watcher)
end Miri.Interpreter.PollShims
