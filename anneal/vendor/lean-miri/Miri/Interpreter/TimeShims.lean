import Miri.Interpreter.Clock
import Miri.Concurrency.SyncRuntime
import Miri.Interpreter.EnvVars

/-! Pinned shims/time.rs. Host time, Chrono timezone data and target layouts
are required effects; all source clock/error/control/arithmetic policy is here. -/
namespace Miri.Interpreter.TimeShims
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
inductive Constant where
  | realtime | monotonic | realtimeCoarse | monotonicCoarse | uptimeRaw | timerAbstime
  deriving DecidableEq, Repr
inductive Layout where | inferred | timespec | filetime | i64 | u64 | machTimebase deriving DecidableEq, Repr
structure BrokenDown where
  second : Nat
  minute : Nat
  hour : Nat
  day : Nat
  month0 : Nat
  weekdaySunday : Nat
  ordinal0 : Nat
  year : Int32
  offsetSeconds : Int32
structure Hooks (S Host System TZ Timestamp : Type) where
  family : ForeignItems.Family
  os : String
  communicate : Bool
  host : Clock.HostHooks Host System S
  monotonic : M S (Clock.Monotonic Host)
  encodeDeadline : Clock.Deadline Host System → M S ThreadDeadline
  runtime : SyncRuntime.Hooks S Nat Int32 (MPlaceTy Provenance)
  noIsolation : String → M S Unit
  systemDurationSinceUnix : System → M S (Option Clock.Duration)
  constant : Constant → M S (Scalar Provenance)
  readScalar : OpTy Provenance → M S (Scalar Provenance)
  scalarSigned : Scalar Provenance → Size → M S Int
  clockIdSize : M S Size
  readI32 : OpTy Provenance → M S Int32
  readU32 : OpTy Provenance → M S UInt32
  readU64 : OpTy Provenance → M S UInt64
  deref : OpTy Provenance → Layout → M S (MPlaceTy Provenance)
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  isNull : Pointer (Option Provenance) → M S Bool
  projectNamed : MPlaceTy Provenance → String → M S (MPlaceTy Provenance)
  readSignedPlace : MPlaceTy Provenance → M S Int
  writeFields : Array Int → MPlaceTy Provenance → M S Unit
  writeNamed : Array (String × Int) → MPlaceTy Provenance → M S Unit
  writeInt : Int → MPlaceTy Provenance → M S Unit
  writePointer : Pointer (Option Provenance) → MPlaceTy Provenance → M S Unit
  dedupBytes : ByteArray → M S (Pointer (Option Provenance))
  setEinvalAndReturnNeg1 : M S Int32
  /-- Source DateTime::from_timestamp(...). None is its source assertion failure. -/
  utcTimestamp : Int64 → M S (Option Timestamp)
  getTimezoneEnv : M S (Option (Except Unit String))
  utc : TZ
  parseTimezone : String → M S (Option TZ)
  withTimezone : Timestamp → TZ → M S BrokenDown
private def lift (r : Except StepError A) : M S A :=
  match r with | .ok value => pure value | .error error => throw error
private def target (h : Hooks S H Y Z T) (family : ForeignItems.Family) : M S Unit := do
  if h.family != family then throw (.invalidProgram "time shim target family mismatch")
private def macos (h : Hooks S H Y Z T) : M S Unit := do
  if h.os != "macos" then throw (.invalidProgram "Mach time shim requires macOS")

def systemTimeToDuration (h : Hooks S H Y Z T) (time : Y) : M S Clock.Duration := do
  let some duration ← h.systemDurationSinceUnix time
    | throw (.unsupported "times before Unix epoch are not supported")
  return duration

def parseClockId (h : Hooks S H Y Z T) (id : Scalar Provenance) : M S (Option Clock.TimeoutClock) := do
  if id == (← h.constant .realtime) then return some .realTime
  if id == (← h.constant .monotonic) then return some .monotonic
  if #["linux","freebsd","android"].contains h.os then
    if id == (← h.constant .realtimeCoarse) then return some .realTime
    if id == (← h.constant .monotonicCoarse) then return some .monotonic
  else if h.os == "macos" then
    if id == (← h.constant .uptimeRaw) then return some .monotonic
  return none
private def elapsed (h : Hooks S H Y Z T) : M S Clock.Duration := do
  let clock ← h.monotonic
  let now ← clock.now h.host
  now.durationSince h.host clock.epoch

def clockGettime (h : Hooks S H Y Z T) (id tp : OpTy Provenance)
    (dest : MPlaceTy Provenance) : M S Unit := do
  target h .unix
  let id ← h.readScalar id
  let tp ← h.deref tp .inferred
  let some kind ← parseClockId h id
    | h.runtime.writeScalar (← h.setEinvalAndReturnNeg1) dest; return
  let duration ← match kind with
    | .realTime => do
      h.noIsolation "clock_gettime with REALTIME clocks"
      systemTimeToDuration h (← h.host.systemNow)
    | .monotonic => elapsed h
  h.writeFields #[Int.ofNat duration.seconds.toNat,Int.ofNat duration.nanos.toNat] tp
  h.writeInt 0 dest

def gettimeofday (h : Hooks S H Y Z T) (tv tz : OpTy Provenance) : M S Int32 := do
  target h .unix
  h.noIsolation "gettimeofday"
  let tv ← h.deref tv .inferred
  let tz ← h.readPointer tz
  if !(← h.isNull tz) then return ← h.setEinvalAndReturnNeg1
  let duration ← systemTimeToDuration h (← h.host.systemNow)
  h.writeFields #[Int.ofNat duration.seconds.toNat,Int.ofNat (duration.nanos.toNat / 1000)] tv
  return 0

def readTimespec (h : Hooks S H Y Z T) (place : MPlaceTy Provenance) : M S (Option Clock.Duration) := do
  let sec ← h.readSignedPlace (← h.projectNamed place "tv_sec")
  let nsec ← h.readSignedPlace (← h.projectNamed place "tv_nsec")
  if sec < 0 then throw (.unsupported "timespec with negative tv_sec is not supported")
  if sec >= 2^64 then throw (.invalidProgram "tv_sec should fit in64bits")
  if nsec < 0 || nsec >= 1000000000 then return none
  return some (← lift (Clock.Duration.fromNanos (sec.toNat * 1000000000 + nsec.toNat)))

def readTimeval (h : Hooks S H Y Z T) (place : MPlaceTy Provenance) : M S (Option Clock.Duration) := do
  let sec ← h.readSignedPlace (← h.projectNamed place "tv_sec")
  let usec ← h.readSignedPlace (← h.projectNamed place "tv_usec")
  if sec < 0 || sec >= 2^64 || usec < 0 || usec >= 1000000 then return none
  return some (← lift (Clock.Duration.fromNanos (sec.toNat * 1000000000 + usec.toNat * 1000)))

private def sleepUntil (h : Hooks S H Y Z T) (deadline : Clock.Deadline H Y) : M S Unit := do
  let deadline ← h.encodeDeadline deadline
  let callback : SyncRuntime.Callback S := fun kind => do
    if kind != .TimedOut then throw (.invalidProgram "sleep callback must time out")
  let token ← SyncRuntime.register h.runtime (some (.user .sleep)) callback
  match (← h.runtime.threads).blockThreadWithRuntimeConstraints .Sleep (some deadline) token
      h.runtime.communicate with
  | .error error =>
    SyncRuntime.cancelCallback h.runtime token
    throw (h.runtime.error (.blockThreadSource error))
  | .ok threads => h.runtime.putThreads threads
private def relativeMonotonic (h : Hooks S H Y Z T) (duration : Clock.Duration) : M S Unit := do
  let now ← (← h.monotonic).now h.host
  sleepUntil h (.monotonic (← now.addLossy h.host duration))

def nanosleep (h : Hooks S H Y Z T) (duration rem : OpTy Provenance) : M S Int32 := do
  target h .unix
  let duration ← h.deref duration .timespec
  let _ ← h.readPointer rem
  let some duration ← readTimespec h duration | return ← h.setEinvalAndReturnNeg1
  relativeMonotonic h duration
  return 0

def clockNanosleep (h : Hooks S H Y Z T) (clock flags spec rem : OpTy Provenance) : M S Int32 := do
  let size ← h.clockIdSize
  let clock ← h.scalarSigned (← h.readScalar clock) size
  let spec ← h.deref spec .timespec
  let flags ← h.readI32 flags
  let _ ← h.readPointer rem
  let expected ← h.scalarSigned (← h.constant .monotonic) size
  if clock != expected then throw (.unsupported "clock_nanosleep only CLOCK_MONOTONIC supported")
  let some duration ← readTimespec h spec | return ← h.setEinvalAndReturnNeg1
  let style ← if flags == 0 then pure Clock.TimeoutStyle.relative
    else
      let abstime ← h.scalarSigned (← h.constant .timerAbstime) (Size.ofBytes 4)
      if flags.toInt == abstime then pure .absolute
      else throw (.unsupported "clock_nanosleep unsupported flags")
  let deadline ← Clock.timeout h.host (← h.monotonic) h.communicate .monotonic style duration
  sleepUntil h deadline
  return 0

def sleep (h : Hooks S H Y Z T) (timeout : OpTy Provenance) : M S Unit := do
  target h .windows
  let millis ← h.readU32 timeout
  relativeMonotonic h (← lift (Clock.Duration.fromNanos (millis.toNat * 1000000)))

def systemTimeSinceWindowsEpoch (h : Hooks S H Y Z T) (time : Y) : M S Clock.Duration := do
  let duration ← systemTimeToDuration h time
  if duration.seconds.toNat + 11644473600 >= 2^64 then
    throw (.invalidProgram "SystemTime Windows epoch Duration addition overflow")
  lift (Clock.Duration.fromNanos (duration.asNanos + 11644473600 * 1000000000))

def windowsTicksFor (duration : Clock.Duration) : Except StepError UInt64 := do
  let ticks := duration.asNanos / 100
  if ticks >= 2^64 then throw (.unsupported "program runs more than2^64Windows ticks after Windows epoch")
  return UInt64.ofNat ticks

def getSystemTimeAsFileTime (h : Hooks S H Y Z T) (name : String) (op : OpTy Provenance) : M S Unit := do
  target h .windows
  h.noIsolation name
  let dest ← h.deref op .filetime
  let ticks ← lift (windowsTicksFor (← systemTimeSinceWindowsEpoch h (← h.host.systemNow)))
  h.writeFields #[Int.ofNat (ticks.toNat % 2^32),Int.ofNat (ticks.toNat / 2^32)] dest

def queryPerformanceCounter (h : Hooks S H Y Z T) (op : OpTy Provenance) : M S Int32 := do
  target h .windows
  let duration ← elapsed h
  if duration.asNanos >= 2^63 then throw (.unsupported "programs running longer than2^63nanoseconds unsupported")
  h.writeInt (Int.ofNat duration.asNanos) (← h.deref op .i64)
  return -1

def queryPerformanceFrequency (h : Hooks S H Y Z T) (op : OpTy Provenance) : M S Int32 := do
  target h .windows
  h.writeInt 1000000000 (← h.deref op .u64)
  return -1

def machAbsoluteTime (h : Hooks S H Y Z T) : M S UInt64 := do
  macos h
  let duration ← elapsed h
  if duration.asNanos >= 2^64 then throw (.unsupported "programs running longer than2^64nanoseconds unsupported")
  return UInt64.ofNat duration.asNanos

def machTimebaseInfo (h : Hooks S H Y Z T) (op : OpTy Provenance) : M S Int32 := do
  macos h
  h.writeFields #[1,1] (← h.deref op .machTimebase)
  return 0

def machWaitUntil (h : Hooks S H Y Z T) (op : OpTy Provenance) : M S Int32 := do
  macos h
  let nanos ← h.readU64 op
  let duration ← lift (Clock.Duration.fromNanos nanos.toNat)
  let epoch := (← h.monotonic).epoch
  sleepUntil h (.monotonic (← epoch.addLossy h.host duration))
  return 0
private def padTwo (number : Nat) : String :=
  let text := toString number
  if text.length < 2 then "0" ++ text else text

def localtimeR (h : Hooks S H Y Z T) (timep result : OpTy Provenance) : M S (Pointer (Option Provenance)) := do
  target h .unix
  h.noIsolation "localtime_r"
  let timep ← h.deref timep .inferred
  let result ← h.deref result .inferred
  let seconds ← h.readSignedPlace timep
  if seconds < -(2^63 : Int) || seconds >= 2^63 then throw (.invalidProgram "time_t does not fit i64")
  let some timestamp ← h.utcTimestamp (Int64.ofInt seconds) | throw (.invalidProgram "Invalid timestamp")
  let timezone ← h.getTimezoneEnv
  let timezone : Z ← match timezone with
    | some (.ok text) => do pure ((← h.parseTimezone text).getD h.utc)
    | _ => pure h.utc
  let dt ← h.withTimezone timestamp timezone
  let year := dt.year.toInt - 1900
  if year < -(2^31 : Int) || year >= 2^31 then throw (.invalidProgram "tm_year overflow")
  h.writeNamed #[("tm_sec",Int.ofNat dt.second),("tm_min",Int.ofNat dt.minute),
    ("tm_hour",Int.ofNat dt.hour),("tm_mday",Int.ofNat dt.day),("tm_mon",Int.ofNat dt.month0),
    ("tm_year",year),("tm_wday",Int.ofNat dt.weekdaySunday),("tm_yday",Int.ofNat dt.ordinal0),("tm_isdst",-1)] result
  if h.os != "solaris" && h.os != "illumos" then
    let offset := dt.offsetSeconds.toInt
    let magnitude := offset.natAbs
    let zone := (if offset < 0 then "-" else "+") ++ padTwo (magnitude / 3600) ++
      (if magnitude % 3600 / 60 == 0 then "" else padTwo (magnitude % 3600 / 60))
    let pointer ← h.dedupBytes (zone.toUTF8.push 0)
    h.writePointer pointer (← h.projectNamed result "tm_zone")
    h.writeNamed #[("tm_gmtoff",offset)] result
  return result.mplace.ptr
end Miri.Interpreter.TimeShims
