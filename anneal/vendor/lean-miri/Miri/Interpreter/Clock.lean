import Miri.Interpreter.Step
import Miri.ABI.Size

/-! Pinned clock.rs. Host time is an explicit environment, never substituted
with virtual time. Nanoseconds are exact integers; u128 saturation, Duration's
u64 seconds bound, mixed-clock assertions and host checked-add fallback are
preserved. No particular host clock trace is a proof over all environments. -/
namespace Miri.Interpreter.Clock
open Miri.ABI

structure Duration where
  seconds : UInt64
  nanos : UInt32
  nanosBound : nanos.toNat < 1000000000
  deriving Repr

def Duration.asNanos (d : Duration) : Nat := d.seconds.toNat * 1000000000 + d.nanos.toNat

def Duration.fromNanos (n : Nat) : Except StepError Duration := do
  if n / 1000000000 < 2^64 then
    let nanos := UInt32.ofNat (n % 1000000000)
    if p : nanos.toNat < 1000000000 then return ⟨UInt64.ofNat (n / 1000000000), nanos, p⟩
    else throw (.invalidProgram "Duration remainder conversion")
  else throw (.resourceExhaustion "Duration::from_nanos_u128 exceeds u64 seconds")

inductive Instant (Host : Type) where
  | host (value : Host)
  | virtual (nanoseconds : U128)
  deriving Repr
inductive Monotonic (Host : Type) where
  | host (epoch : Host)
  | virtual (nanoseconds : U128)
  deriving Repr
inductive Deadline (Host System : Type) where
  | monotonic (instant : Instant Host)
  | realTime (time : System)
  deriving Repr
inductive TimeoutClock where | monotonic | realTime deriving DecidableEq, Repr
inductive TimeoutStyle where | relative | absolute deriving DecidableEq, Repr

abbrev M (S A : Type) := EStateM StepError S A

structure HostHooks (Host System S : Type) where
  monotonicNow : M S Host
  systemNow : M S System
  unixEpoch : System
  checkedAddMonotonic : Host → Duration → M S (Option Host)
  checkedAddSystem : System → Duration → M S (Option System)
  durationSince : Host → Host → M S Duration
  sleep : Duration → M S Unit

private def oneHour : Duration := ⟨3600,0,by decide⟩

/-- On host overflow the source retries exactly one hour, then asserts that
this succeeds. It does not clamp to a fabricated maximum host timestamp. -/
def addHostLossy (checkedAdd : H → Duration → M S (Option H))
    (time : H) (duration : Duration) : M S H := do
  if let some result ← checkedAdd time duration then return result
  let some result ← checkedAdd time oneHour |
    throw (.invalidProgram "clock checked_add of one hour overflowed")
  return result

def Instant.addLossy (h : HostHooks Host System S) (instant : Instant Host)
    (duration : Duration) : M S (Instant Host) := do
  match instant with
  | .host instant => return .host (← addHostLossy h.checkedAddMonotonic instant duration)
  | .virtual n => return .virtual (BitVec.ofNat 128 (min (2^128-1) (n.toNat + duration.asNanos)))

def Instant.durationSince (h : HostHooks Host System S) (instant earlier : Instant Host) : M S Duration := do
  match instant,earlier with
  | .host instant,.host earlier => h.durationSince instant earlier
  | .virtual instant,.virtual earlier =>
    match Duration.fromNanos (instant.toNat - earlier.toNat) with
    | .ok duration => return duration
    | .error error => throw error
  | _,_ => throw (.invalidProgram "all clock instants must be of the same kind")

def Monotonic.new (h : HostHooks Host System S) (communicate : Bool) : M S (Monotonic Host) := do
  if communicate then return .host (← h.monotonicNow)
  else return .virtual 0

/-- Rust's virtual tick uses ordinary u128 addition. The source build's
arithmetic overflow-check setting is explicit, rather than silently saturating. -/
def Monotonic.tick (checkedArithmetic : Bool) (clock : Monotonic Host) : Except StepError (Monotonic Host) := do
  match clock with
  | .host _ => return clock
  | .virtual n =>
    if checkedArithmetic && n.toNat + 5000 ≥ 2^128 then
      throw (.invalidProgram "virtual clock tick arithmetic overflow")
    return .virtual (BitVec.ofNat 128 (n.toNat + 5000))

def Monotonic.sleep (h : HostHooks Host System S) (clock : Monotonic Host)
    (duration : Duration) : M S (Monotonic Host) := do
  match clock with
  | .host _ => h.sleep duration; return clock
  | .virtual n =>
    if n.toNat + duration.asNanos ≥ 2^128 then
      throw (.invalidProgram "virtual clock cannot represent an execution this long")
    return .virtual (BitVec.ofNat 128 (n.toNat + duration.asNanos))

def Monotonic.epoch : Monotonic Host → Instant Host
  | .host epoch => .host epoch
  | .virtual _ => .virtual 0

def Monotonic.now (h : HostHooks Host System S) (clock : Monotonic Host) : M S (Instant Host) := do
  match clock with
  | .host _ => return .host (← h.monotonicNow)
  | .virtual n => return .virtual n

def Deadline.addLossy (h : HostHooks Host System S) (deadline : Deadline Host System)
    (duration : Duration) : M S (Deadline Host System) := do
  match deadline with
  | .monotonic instant => return .monotonic (← instant.addLossy h duration)
  | .realTime time => return .realTime (← addHostLossy h.checkedAddSystem time duration)

/-- Preserve source effect ordering: RealTime checks communication before
reading the host; Absolute monotonic uses epoch without reading `now`. -/
def timeout (h : HostHooks Host System S) (clock : Monotonic Host)
    (communicate : Bool) (kind : TimeoutClock) (style : TimeoutStyle)
    (duration : Duration) : M S (Deadline Host System) := do
  let zero ← match kind with
    | .realTime => do
      unless communicate do throw (.invalidProgram "RealTime timeout with isolation")
      let base ← match style with
        | .absolute => pure h.unixEpoch
        | .relative => h.systemNow
      pure (Deadline.realTime base)
    | .monotonic => do
      let base ← match style with
        | .absolute => pure clock.epoch
        | .relative => clock.now h
      pure (Deadline.monotonic base)
  zero.addLossy h duration

end Miri.Interpreter.Clock
