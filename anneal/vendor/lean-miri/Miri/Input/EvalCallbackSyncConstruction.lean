import Miri.Input.EvalSyncObjectAccess
import Miri.Input.EvalTypedSyncMachine
import Miri.Interpreter.CompilerExecutionProviders
import Miri.Interpreter.TimeShims

/-! Source-owned synchronization callback adapters. The selected backend,
target word size, callback writes, memory access hooks, and callback shims are
derived from the live source state and final execution configuration. Only
host errno/Windows plumbing and host clock/time operations remain residuals. -/
namespace Miri.Input.EvalCallbackSyncConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency

abbrev World Os R H D O Aff B Poll Instant System Native Profiler :=
  EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D O Aff B Poll Instant System Native Profiler
abbrev User Os R H D O Aff B Poll Instant System Native Profiler :=
  EvalSyncMachine.User Os R EvalSyncObjectAccess.Payload H D O Aff B
    Poll Instant System Native Profiler
abbrev State Os R H D O Aff B Poll Instant System Native Profiler :=
  EvalSyncMachine.State Os R EvalSyncObjectAccess.Payload H D O Aff B
    Poll Instant System Native Profiler
abbrev M Os R H D O Aff B Poll Instant System Native Profiler A :=
  MachineHooks.M MiriMemoryKind (User Os R H D O Aff B Poll Instant System Native Profiler) A

/-- Genuine platform residuals used by synchronization wrappers. Memory writes,
backend selection, pointer width, and source error-pointer ownership are bound
by `sourceEffects`; this record contains only actual host error translation and
Windows-specific return/error effects. -/
structure HostEffects (Os R H D O Aff B Poll Instant System Native Profiler ErrorHost : Type) where
  ioError : IoError.Hooks
    (State Os R H D O Aff B Poll Instant System Native Profiler) ErrorHost
  windowsTrue : EStateM StepError
    (State Os R H D O Aff B Poll Instant System Native Profiler) Int32
  windowsFalse : EStateM StepError
    (State Os R H D O Aff B Poll Instant System Native Profiler) Int32
  windowsTimeoutError : EStateM StepError
    (State Os R H D O Aff B Poll Instant System Native Profiler) Unit

private def lift (value : Except StepError A) : EStateM StepError S A :=
  match value with
  | .ok result => pure result
  | .error error => throw error

private def selectedHandler
    (state : State Os R H D O Aff B Poll Instant System Native Profiler) :
    Except StepError SyncClockHandler := do
  match EvalBackendMachine.handler state.machine with
  | .error error => throw error
  | .ok .none => pure .none
  | .ok (.vclocks _) => pure .vectorClocks

def sourceEffects [DecidableEq MiriMemoryKind]
    (prepared : CompilerFactAdapters.Prepared)
    (configuration : HostRuntime.Configuration)
    (place : PlaceHooks Provenance
      (State Os R H D O Aff B Poll Instant System Native Profiler)
      C MachineHooks.FrameExtra)
    (choice : C)
    (host : HostEffects Os R H D O Aff B Poll Instant System Native Profiler ErrorHost) :
    M Os R H D O Aff B Poll Instant System Native Profiler
      (TypedSyncMachine.Effects
        (MachineHooks.State MiriMemoryKind
          (EvalSyncMachine.User Os R EvalSyncObjectAccess.Payload H D O Aff B
            Poll Instant System Native Profiler))) := do
  let current ← get
  let handler ← match selectedHandler current with
    | .ok result => pure result
    | .error error => throw error
  let usizeLayout ← match prepared.context.primitiveLayout "usize" with
    | .ok layout => pure layout
    | .error error => throw (.unsupported s!"compiler usize layout: {error}")
  let u32Layout ← match prepared.context.primitiveLayout "u32" with
    | .ok layout => pure layout
    | .error error => throw (.unsupported s!"compiler u32 layout: {error}")
  let errors := EvalSyncMachine.errors u32Layout host.ioError
  let outputPlace (dest : TypedSyncRuntime.Dest) : RuntimePlace Provenance :=
    ⟨.memory dest.mplace,dest.layout⟩
  let writeScalar := fun value dest => do
    let scalar ← lift (Scalar.fromInt value.toInt (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)
    writePlaceImmediate place choice (.scalar scalar) (outputPlace dest)
  let writeInt := fun value dest => do
    let scalar ← lift (Scalar.fromInt value dest.layout.layout.size |>.mapError ScalarOps.scalarError)
    writePlaceImmediate place choice (.scalar scalar) (outputPlace dest)
  pure {
    handler
    usizeBits := usizeLayout.layout.size.bytes.toNat * 8
    communicate := configuration.communicate
    writeScalar
    writeInt
    errnoNegOne := fun name dest =>
      IoError.setErrnoAndReturnNeg1 errors (.libc name) dest
    windowsTrue := host.windowsTrue
    windowsFalse := host.windowsFalse
    windowsTimeoutError := host.windowsTimeoutError }

/-- Build the actual time-independent physical synchronization projection from
the live Core memory/backend fields. It has no futex clock, deadline, errno or
isolation input, so pthread object metadata remains usable when optional time
host capabilities are absent. The projected object storage is the existing
HostRuntime.sync view, not a new registry. -/
def objectHooksFromSource [DecidableEq MiriMemoryKind]
    (prepared : CompilerFactAdapters.Prepared)
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler))
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler))
    (compiler : PlaceMachine.CompilerHooks MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler) C)
    (dynamic : DynamicLayoutHooks Provenance
      (State Os R H D O Aff B Poll Instant System Native Profiler) C)
    (vtable : VTableHooks Provenance
      (State Os R H D O Aff B Poll Instant System Native Profiler) C
      (FnVal O) (FnAbi TyId))
    (dynamicFuel : Nat)
    (atomic : AtomicAccessHooks Provenance
      (State Os R H D O Aff B Poll Instant System Native Profiler) C
      (RuntimePlace Provenance))
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler)
      EvalSyncObjectAccess.Payload)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control
        (ThreadStacks.Storage
          (World Os R H D O Aff B Poll Instant System Native Profiler))))
     :
    LinuxFutexMachine.ObjectHooks MiriMemoryKind
      (World Os R H D O Aff B Poll Instant System Native Profiler) C
      EvalSyncObjectAccess.Payload O B := {
  views := EvalSyncMachine.views
  payload := EvalSyncObjectAccess.linuxFutexEmbedding
  access
  allocation
  compiler
  pointers
  pointerCompiler := CompilerExecutionProviders.pointerCompiler prepared
  dynamic
  vtable
  dynamicFuel
  atomic
  backend := fun state => EvalBackendMachine.handler state.machine
  extras }

def futexHooksWithReader [DecidableEq MiriMemoryKind]
    (prepared : CompilerFactAdapters.Prepared)
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler))
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler))
    (compiler : PlaceMachine.CompilerHooks MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler) C)
    (dynamic : DynamicLayoutHooks Provenance
      (State Os R H D O Aff B Poll Instant System Native Profiler) C)
    (vtable : VTableHooks Provenance
      (State Os R H D O Aff B Poll Instant System Native Profiler) C
      (FnVal O) (FnAbi TyId))
    (dynamicFuel : Nat)
    (atomic : AtomicAccessHooks Provenance
      (State Os R H D O Aff B Poll Instant System Native Profiler) C
      (RuntimePlace Provenance))
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler)
      EvalSyncObjectAccess.Payload)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control
        (ThreadStacks.Storage
          (World Os R H D O Aff B Poll Instant System Native Profiler))))
    (configuration : HostRuntime.Configuration)
    (readTimespec : MPlaceTy Provenance → M Os R H D O Aff B Poll Instant System Native Profiler
      (Option Clock.Duration))
    (deadline : DeadlineMachine.Hooks MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler) Instant System)
    (errors : IoError.Hooks
      (State Os R H D O Aff B Poll Instant System Native Profiler) ErrorHost) :
    M Os R H D O Aff B Poll Instant System Native Profiler
      (LinuxFutexMachine.Hooks MiriMemoryKind
        (World Os R H D O Aff B Poll Instant System Native Profiler)
        C EvalSyncObjectAccess.Payload O B Instant System Z T ErrorHost) := do
  let current ← get
  let _ ← match selectedHandler current with
    | .ok result => pure result
    | .error error => throw error
  let i32Layout ← match prepared.context.runtime.integerLayout .i32 with
    | .ok layout => pure layout
    | .error error => throw (.callback s!"compiler i32 layout: {error}")
  let u32Layout ← match prepared.context.runtime.integerLayout .u32 with
    | .ok layout => pure layout
    | .error error => throw (.callback s!"compiler u32 layout: {error}")
  let errors := EvalSyncMachine.errors u32Layout errors
  pure {
    views := EvalSyncMachine.views
    payload := EvalSyncObjectAccess.linuxFutexEmbedding
    access
    allocation
    compiler
    pointers
    pointerCompiler := CompilerExecutionProviders.pointerCompiler prepared
    dynamic
    vtable
    dynamicFuel
    atomic
    backend := fun state => EvalBackendMachine.handler state.machine
    extras := {extras with onAccess :=
      LinuxFutexMachine.onAccess EvalSyncObjectAccess.linuxFutexEmbedding extras.onAccess}
    i32Layout
    readTimespec
    deadline
    errors
    communicate := pure configuration.communicate }

/-- Compatibility wrapper for callers with complete time-shim hooks. Futex
only consumes the compiler-checked timespec reader; its deadline remains the
separately supplied canonical DeadlineMachine capability. -/
def futexHooks [DecidableEq MiriMemoryKind]
    (prepared : CompilerFactAdapters.Prepared)
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler))
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler))
    (compiler : PlaceMachine.CompilerHooks MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler) C)
    (dynamic : DynamicLayoutHooks Provenance
      (State Os R H D O Aff B Poll Instant System Native Profiler) C)
    (vtable : VTableHooks Provenance
      (State Os R H D O Aff B Poll Instant System Native Profiler) C
      (FnVal O) (FnAbi TyId))
    (dynamicFuel : Nat)
    (atomic : AtomicAccessHooks Provenance
      (State Os R H D O Aff B Poll Instant System Native Profiler) C
      (RuntimePlace Provenance))
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler)
      EvalSyncObjectAccess.Payload)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control
        (ThreadStacks.Storage
          (World Os R H D O Aff B Poll Instant System Native Profiler))))
    (configuration : HostRuntime.Configuration)
    (time : TimeShims.Hooks
      (State Os R H D O Aff B Poll Instant System Native Profiler) Instant System Z T)
    (deadline : DeadlineMachine.Hooks MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler) Instant System)
    (errors : IoError.Hooks
      (State Os R H D O Aff B Poll Instant System Native Profiler) ErrorHost) :
    M Os R H D O Aff B Poll Instant System Native Profiler
      (LinuxFutexMachine.Hooks MiriMemoryKind
        (World Os R H D O Aff B Poll Instant System Native Profiler)
        C EvalSyncObjectAccess.Payload O B Instant System Z T ErrorHost) :=
  futexHooksWithReader prepared access allocation compiler dynamic vtable dynamicFuel atomic extras
    pointers configuration (TimeShims.readTimespec time) deadline errors

end Miri.Input.EvalCallbackSyncConstruction
