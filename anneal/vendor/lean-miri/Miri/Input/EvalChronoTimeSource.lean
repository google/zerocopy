import Miri.Interpreter.ChronoTz
import Miri.Interpreter.OsStrings
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.EvalCallDispatchConstruction
import Miri.Input.EvalSourceHostEffects
import Miri.Input.EvalTimeConstruction

/-! The input-layer adapter for the pure Chrono/Chrono-TZ source port. Keeping
this out of the `Interpreter` umbrella avoids an Interpreter → Input cycle. -/
namespace Miri.Input.EvalChronoTimeSource
open Miri.Interpreter

def effects (S : Type) : EvalTimeConstruction.HostEffects S
    ChronoTz.TZ ChronoTz.Timestamp := {
  utc := "UTC"
  utcTimestamp := fun seconds => pure (ChronoTz.timestamp seconds)
  parseTimezone := fun text => pure (ChronoTz.timezone text)
  withTimezone := fun stamp zone =>
    match ChronoTz.convert stamp zone with
    | some value => pure value
    | none => throw (.invalidProgram "Chrono-TZ source table lookup failed") }

/-- Construct the source's optional time provider from actual host OsString
encoding operations. The environment lookup remains a guest-state operation
inside EvalTimeConstruction; this host input only performs Unix into_string. -/
def sourceTimeSource {Os SourceState : Type}
    (os : EvalHostRuntimeConstruction.OsHostEffects Os) :
    EvalSourceHostEffects.TimeSource Os SourceState := {
  Zone := ChronoTz.TZ
  Timestamp := ChronoTz.Timestamp
  timezoneString := fun value =>
    match OsStrings.unixIntoStringOf os.encodedBytes value with
    | some text => .ok text
    | none => .error ()
  effects := effects SourceState }

set_option autoImplicit false in
/-- Install the built-in provider only as an explicit source-factory choice.
The host seed's optional `time` field remains absent when callers do not use
this constructor, preserving Core's demand-local no-provider fallback. -/
def install {Os R EnvControl SourceState H D O Aff B Raw Listener TcpStream Error ErrorHost
      Meta Path Poll AddrIter Instant System Native Profiler RunState : Type}
    (host : EvalSourceHostEffects.Seed Os R EnvControl SourceState H D O Aff B Raw Listener
      TcpStream Error ErrorHost Meta Path Poll AddrIter Instant System Native Profiler RunState) :
    EvalSourceHostEffects.Seed Os R EnvControl SourceState H D O Aff B Raw Listener TcpStream
      Error ErrorHost Meta Path Poll AddrIter Instant System Native Profiler RunState :=
  { host with time := some (sourceTimeSource host.os) }

set_option autoImplicit false in
/-- Explicit production-source constructor adapter: preserve all supplied raw
host leaves and install the built-in Unix chrono provider in the host seed.
Callers that need the demand-local missing-provider behavior can pass the
unmodified `SourceInput` instead. -/
def installSourceInput {Os R H D Aff B Poll Instant System Native Profiler Raw Listener
      TcpStream Error ErrorHost Meta Path AddrIter : Type}
    (input : EvalCallDispatchConstruction.SourceInput Os R H D Aff B Poll Instant System
      Native Profiler Raw Listener TcpStream Error ErrorHost Meta Path AddrIter) :
    EvalCallDispatchConstruction.SourceInput Os R H D Aff B Poll Instant System
      Native Profiler Raw Listener TcpStream Error ErrorHost Meta Path AddrIter :=
  { input with host := install input.host }

end Miri.Input.EvalChronoTimeSource
