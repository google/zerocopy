import Miri.Interpreter.Clock
import Miri.Interpreter.MachineHooks
import Miri.Interpreter.Scheduling

/-! Typed deadlines behind ThreadDeadline's internal tokens, and the stateful
source thread.rs::unblock_expired_deadlines. Host readings interleave with
thread enabling exactly during the sweep; callbacks execute only afterwards.
No precomputed clock observation list is assumed to represent those effects.
-/
namespace Miri.Interpreter.DeadlineMachine
open Miri.Memory Miri.Concurrency
open MachineHooks (M)

structure Registry (Host System : Type) where
  nextToken : Nat
  /-- Each token retains every associated row so malformed duplicate live
  metadata remains detectable. The map makes lookup and collision checks
  independent of the number of deadlines created in earlier waits. -/
  entries : Std.HashMap Nat (Array (Clock.Deadline Host System))
  /-- Nested source operations can temporarily keep expired deadlines alive
  while callbacks retry with the same token. -/
  pruneDepth : Nat := 0

def Registry.empty : Registry Host System := { nextToken := 0, entries := {} }

/-- Keep exactly the token identities still held by blocked threads. Pruning
is deferred while a nested deadline/callback transition is in progress; the
outermost successful scope supplies the current live set. -/
def Registry.retain (registry : Registry Host System) (live : Std.HashSet Nat) :
    Registry Host System := Id.run do
  if registry.pruneDepth > 0 then return registry
  let mut entries : Std.HashMap Nat (Array (Clock.Deadline Host System)) := {}
  for (token, deadlines) in registry.entries.toList do
    if live.contains token then entries := entries.insert token deadlines
  return { registry with entries }

def Registry.enterPruneSuppression (registry : Registry Host System) :
    Registry Host System :=
  { registry with pruneDepth := registry.pruneDepth + 1 }

def Registry.leavePruneSuppression (registry : Registry Host System)
    (live : Std.HashSet Nat) : Except StepError (Registry Host System) := do
  if registry.pruneDepth == 0 then
    throw (.invalidProgram "deadline prune-suppression depth underflow")
  let updated := { registry with pruneDepth := registry.pruneDepth - 1 }
  return updated.retain live

def Registry.leavePruneSuppressionOnError (registry : Registry Host System) :
    Except StepError (Registry Host System) := do
  if registry.pruneDepth == 0 then
    throw (.invalidProgram "deadline prune-suppression depth underflow")
  return { registry with pruneDepth := registry.pruneDepth - 1 }

/-- Tokens are representation identities, not times or addresses. -/
def Registry.intern (registry : Registry Host System) (deadline : Clock.Deadline Host System) :
    Except StepError (Registry Host System × ThreadDeadline) := do
  if registry.entries.contains registry.nextToken then
    throw (.invalidProgram "deadline registry token collision")
  let token := match deadline with
    | .monotonic _ => ThreadDeadline.Monotonic registry.nextToken
    | .realTime _ => ThreadDeadline.RealTime registry.nextToken
  let updated := { registry with
    nextToken := registry.nextToken + 1
    entries := registry.entries.insert registry.nextToken #[deadline] }
  return (updated, token)

def Registry.lookup (registry : Registry Host System) (deadline : ThreadDeadline) :
    Except StepError (Clock.Deadline Host System) := do
  let token := match deadline with | .Monotonic token | .RealTime token => token
  let some entries := registry.entries[token]? | throw (.invalidProgram "missing actual deadline")
  let some entry := entries[0]? | throw (.invalidProgram "missing actual deadline")
  if entries.size != 1 then throw (.invalidProgram "ambiguous actual deadline")
  match deadline,entry with
  | .Monotonic _,.monotonic _ | .RealTime _,.realTime _ => return entry
  | _,_ => throw (.invalidProgram "deadline token clock-kind mismatch")

structure Hooks (K User Host System : Type) where
  registry : User → Registry Host System
  setRegistry : Registry Host System → User → User
  clock : User → Clock.Monotonic Host
  host : Clock.HostHooks Host System (MachineHooks.State K User)
  communicate : M K User Bool
  /-- SystemTime::duration_since returns Err before zero substitution when
  the deadline is past. This is a real host operation, not a virtual timestamp. -/
  systemDurationSince : System → System → M K User (Option Clock.Duration)
  /-- Actual thread view swap, including its complete typed stack. -/
  selectThread : ThreadId → M K User ThreadId
  invokeCallback : Nat → UnblockKind → M K User Unit

/-- The operation needed to create a relative monotonic millisecond deadline.
It exposes the actual clock and deadline-token registry, while leaving
scheduler callback selection and invocation out of consumers that only create
deadlines (for example Unix poll's timeout path). -/
structure MonotonicMillisHooks (K User Host System : Type) where
  registry : User → Registry Host System
  setRegistry : Registry Host System → User → User
  clock : User → Clock.Monotonic Host
  host : Clock.HostHooks Host System (MachineHooks.State K User)

private def lift (value : Except StepError A) : M K User A :=
  match value with | .ok value => pure value | .error error => throw error

def intern (h : Hooks K User Host System) (deadline : Clock.Deadline Host System) : M K User ThreadDeadline := do
  let state ← get
  let (registry,token) ← lift ((h.registry state.machine.user).intern deadline)
  modify fun state => { state with machine := { state.machine with user := h.setRegistry registry state.machine.user } }
  return token

def timeout (h : Hooks K User Host System) (kind : Clock.TimeoutClock) (style : Clock.TimeoutStyle)
    (duration : Clock.Duration) : M K User ThreadDeadline := do
  let communicate ← if kind == .realTime then h.communicate else pure false
  let deadline ← Clock.timeout h.host (h.clock (← get).machine.user) communicate kind style duration
  intern h deadline

/-- Intern an actual source monotonic deadline for a relative millisecond
timeout. This is the minimal operation required by poll and Windows
WaitOnAddress; it shares the source registry, clock, and host arithmetic. -/
def monotonicDeadlineMillisFrom
    (h : MonotonicMillisHooks K User Host System)
    (milliseconds : UInt32) : M K User ThreadDeadline := do
  let duration ← lift (Clock.Duration.fromNanos (milliseconds.toNat * 1000000))
  let now ← (h.clock (← get).machine.user).now h.host
  let deadline := .monotonic (← now.addLossy h.host duration)
  let state ← get
  let (registry,token) ← lift ((h.registry state.machine.user).intern deadline)
  modify fun state => { state with machine := { state.machine with
    user := h.setRegistry registry state.machine.user } }
  return token

/-- Windows WaitOnAddress uses the same relative monotonic millisecond
deadline operation, projected from the complete scheduler hooks. -/
def monotonicDeadlineMillis (h : Hooks K User Host System) (milliseconds : UInt32) : M K User ThreadDeadline :=
  monotonicDeadlineMillisFrom ⟨h.registry,h.setRegistry,h.clock,h.host⟩ milliseconds

private def remaining (h : Hooks K User Host System) (communicate : Bool) (token : ThreadDeadline) : M K User Nat := do
  let deadline ← lift ((h.registry (← get).machine.user).lookup token)
  match deadline with
  | .monotonic instant =>
    let now ← (h.clock (← get).machine.user).now h.host
    return (← instant.durationSince h.host now).asNanos
  | .realTime time =>
    unless communicate do throw (.invalidProgram "RealTime timeout with isolation")
    let now ← h.host.systemNow
    let duration ← h.systemDurationSince time now
    return match duration with | none => 0 | some duration => duration.asNanos

def liveTokens (threads : ThreadManager) : Std.HashSet Nat := Id.run do
  let mut live : Std.HashSet Nat := {}
  for thread in threads.threads do
    if let .Blocked _ (some deadline) _ := thread.state then
      let token := match deadline with
        | .Monotonic token | .RealTime token => token
      live := live.insert token
  return live

/-- Minimum wait is exact duration nanoseconds. Expired states are enabled in
thread order before any callbacks; errors preserve each completed mutation.
The callback may block again or change stacks. Restore only on normal return. -/
private def unblockExpiredDeadlinesBody (h : Hooks K User Host System) : M K User (Option Nat) := do
  let communicate ← h.communicate
  let count := (← get).machine.threads.threads.length
  let mut minimum : Option Nat := none
  let mut callbacks : Array (ThreadId × Nat) := #[]
  for index in [:count] do
    let id ← lift ((ThreadId.ofNat index).mapError fun error => .invalidProgram s!"deadline thread ID: {reprStr error}")
    let some thread := (← get).machine.threads.thread? id |
      throw (.invalidProgram "deadline thread disappeared during sweep")
    if let .Blocked _ (some deadline) callback := thread.state then
      let wait ← remaining h communicate deadline
      if wait == 0 then
        modify fun state => { state with machine := { state.machine with threads :=
          { state.machine.threads with threads := state.machine.threads.threads.set index { thread with state := .Enabled } } } }
        callbacks := callbacks.push (id,callback)
      else
        minimum := some (match minimum with | none => wait | some old => min old wait)
  for (thread,callback) in callbacks do
    let previous ← h.selectThread thread
    h.invokeCallback callback .TimedOut
    let _ ← h.selectThread previous
  return minimum

set_option autoImplicit false in
/-- Defer stale-token pruning across nested source transitions. Success at the
outermost scope prunes against the then-current blocked threads; an error only
restores the depth, preserving the exact error-state registry prefix. -/
def withPruneSuppressed {K User Host System A : Type}
    (registry : User → Registry Host System)
    (setRegistry : Registry Host System → User → User)
    (action : M K User A) : M K User A := fun state => Id.run do
  let current := registry state.machine.user
  let entered := { state with machine := { state.machine with
    user := setRegistry current.enterPruneSuppression state.machine.user } }
  match action.run entered with
  | .ok value after =>
    let current := registry after.machine.user
    let live := if current.pruneDepth == 1 then liveTokens after.machine.threads else {}
    match current.leavePruneSuppression live with
    | .ok updated =>
      let after := { after with machine := { after.machine with
        user := setRegistry updated after.machine.user } }
      return (.ok value after)
    | .error error => return (.error error after)
  | .error error after =>
    let current := registry after.machine.user
    match current.leavePruneSuppressionOnError with
    | .ok updated =>
      let after := { after with machine := { after.machine with
        user := setRegistry updated after.machine.user } }
      return (.error error after)
    | .error _ => return (.error error after)

def unblockExpiredDeadlines (h : Hooks K User Host System) : M K User (Option Nat) :=
  withPruneSuppressed h.registry h.setRegistry (unblockExpiredDeadlinesBody h)

def bindScheduling (base : SchedulingHooks (MachineHooks.State K User) C)
    (h : Hooks K User Host System) : SchedulingHooks (MachineHooks.State K User) C :=
  { base with unblockExpiredDeadlines := fun _ state =>
    match (unblockExpiredDeadlines h).run state with
    | .ok minimum state => (state,.ok minimum)
    | .error error state => (state,.error error) }

end Miri.Interpreter.DeadlineMachine
