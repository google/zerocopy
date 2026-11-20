import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.EvalUnixConstruction
import Miri.Input.EvalUnixIoConstruction
import Miri.Input.EvalUnixNativeFdConstruction
import Miri.Input.EvalCallbackSocketRegistry
import Miri.Input.EvalCallbackSyncConstruction
import Miri.Input.EvalUnixSourceConstruction
import Miri.Input.EvalUnixFsConstruction
import Miri.Input.EvalTimeConstruction

/-! Narrow source-runner host residuals. This module contains host operations
only: it does not accept a Core, compiler-derived dispatch, Main hooks, guest
memory policy, or completed callback dictionaries. Source algorithms and
canonical state projections are assembled by the invocation-time Core. -/
namespace Miri.Input.EvalSourceHostEffects
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

/-- Only the true native-library and OS-error host effects are retained here.
The active native-library path list is read from `HostRuntime` by Core. -/
structure Native (S : Type) where
  call : String → MPlaceTy Provenance → Array (OpTy Provenance) →
    EStateM StepError S Bool

/-- Process-global interrupt and abnormal-cleanup capabilities used by the
source loop. Kept local so this seed does not import the runner. -/
structure Process (S : Type) where
  interrupted : S → Bool
  handleAbnormalTermination : S → S

/-- Optional raw host filesystem operations for the pinned Unix source family.
The directory iterator entry type is existential and remains a transient host
value; the actual rooted directory table uses the existing runtime `R`. -/
structure Filesystem
    (Os SourceState H D O Path Meta System Error R : Type) : Type 1 where
  Entry : Type
  /-- Convert the host OS-string representation to the host path carrier used
  by the raw filesystem leaves. -/
  pathFromOs : Os → Path
  osFromPath : Path → Os
  effects : EvalUnixFsConstruction.HostEffects
    SourceState H D O Path Meta System Error R Entry
  /-- Raw `std::path::absolute` result for host paths. Windows file shims
  need this for `GetFullPathNameW`; when absent, that operation remains
  demand-local Unsupported. This is deliberately not synthesized from cwd or
  canonicalization. -/
  absolute : Option (Path → EStateM StepError SourceState
    (Except (IoError.HostError Error) Path)) := none

/-- Raw host chrono/database operations for the pinned time shims. Timezone
selection still comes from the guest environment; `timezoneString` is only the
host's `OsString::into_string` conversion. Zone and timestamp types are packed
existentially so source packages can carry the real host representation. -/
structure TimeSource (Os SourceState : Type) : Type 1 where
  Zone : Type
  Timestamp : Type
  timezoneString : Os → Except Unit String
  effects : EvalTimeConstruction.HostEffects SourceState Zone Timestamp

/-- Host-residual seed shared by the source Core, startup, Unix dispatch, and
runner. The independent state parameters are unified by Core at the
final callsite; this record does not snapshot or manufacture those states. -/
structure Seed
    (Os R EnvControl SourceState H D O Aff B Raw Listener TcpStream Error ErrorHost
      Meta Path Poll AddrIter Instant System NativeHandle Profiler RunState : Type) where
  /-- Whether this Miri host build enables Rust overflow checks for ordinary
  additions in `iovec` length accumulation. This is a native build-profile
  fact, not a guest target property: callers provide it for the pinned Miri
  executable/profile. The repository's reference `target/debug/miri` is built
  with Cargo's development profile, whose default enables overflow checks;
  pinned `cargo-miri/src/setup.rs` also explicitly keeps them enabled for the
  Miri sysroot with `-Coverflow-checks=on`. Other host builds must pass their
  actual profile setting. -/
  hostOverflowChecks : Bool
  os : EvalHostRuntimeConstruction.OsHostEffects Os
  environment : EvalHostRuntimeConstruction.EnvironmentHostEffects EnvControl
  unixConfig : EvalUnixConstruction.HostConfigEffects SourceState Os Error
  ioError : EvalUnixConstruction.IoHostEffects SourceState Error
  native : Native SourceState
  openFiles : EvalUnixNativeFdConstruction.OpenHostEffects
    SourceState H D Error Meta Path Os
  fileResources : EvalUnixIoConstruction.FileResourceEffects SourceState H D O
  hostFiles : EvalUnixIoConstruction.HostFileEffects SourceState H D O Error Meta
  /-- Raw host `getrandom::fill` result used only when Miri communicates with
  its host. Isolated execution continues to draw bytes from the guest choice
  tape. Absence remains a demand-local Unsupported result at the random shim. -/
  getrandom : Option (Nat → EStateM StepError SourceState (Except String ByteArray)) := none
  fileLocks : EvalUnixIoConstruction.FileLockEffects SourceState H Error
  positional : EvalUnixNativeFdConstruction.OtherPositionalEffects SourceState H D O Error
  control : EvalUnixIoConstruction.ControlSourceEffects SourceState
  /-- Absent host filesystem support leaves Unix filesystem names as explicit
  demand-local Unsupported results. -/
  filesystem : Option (Filesystem Os SourceState H D O Path Meta System Error R) := none
  /-- Absent chrono/database support remains an explicit demand-local gap. -/
  time : Option (TimeSource Os SourceState) := none
  socket : EvalCallbackSocketConstruction.HostEffects
    SourceState H D O Raw Listener TcpStream Error Poll AddrIter
  sync : EvalCallbackSyncConstruction.HostEffects Os R H D
    (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error)
    Aff B Poll Instant System NativeHandle Profiler ErrorHost
  clock : Clock.HostHooks Instant System RunState
  systemDurationSince : System → System → EStateM StepError RunState
    (Option Clock.Duration)
  process : Process RunState

end Miri.Input.EvalSourceHostEffects
