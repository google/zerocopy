import Miri.Input.EvalCallbackSyncConstruction
import Miri.Input.EvalCallbackMachine
import Miri.Input.CompilerLibcTypeLayouts
import Miri.Input.CompilerNamedFields
import Miri.Input.CompilerFactAdapters

/-! Canonical callback-aware futex construction. Futex requires only a checked
compiler timespec reader plus the real shared deadline registry; constructing
it does not require chrono, UTC, or a full TimeShims dictionary. The source
callback builder supplies the already-routed deadline in the inner state that
owns the futex/deadline stores. -/
namespace Miri.Input.EvalCallbackFutexConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency

abbrev User Os R H D O Aff B Poll Instant System Native Profiler :=
  EvalSyncMachine.User Os R EvalSyncObjectAccess.Payload H D O Aff B Poll Instant System Native Profiler
abbrev State Os R H D O Aff B Poll Instant System Native Profiler :=
  EvalSyncMachine.State Os R EvalSyncObjectAccess.Payload H D O Aff B Poll Instant System Native Profiler
abbrev World Os R H D O Aff B Poll Instant System Native Profiler :=
  EvalSyncMachine.World Os R EvalSyncObjectAccess.Payload H D O Aff B Poll Instant System Native Profiler

private def lift {S : Type} (result : Except StepError A) : EStateM StepError S A :=
  match result with
  | .ok value => pure value
  | .error error => throw error

/-- Parse a Linux futex timespec using the actual pointee layout supplied by
compiler-checked shim transmutation and the same effectful field projection as
source memory. Invalid nanoseconds retain TimeShims.readTimespec's
`none` result; negative seconds and overflow remain visible failures. -/
def readTimespecFromSource
    (runtime : RuntimeMetadata)
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler))
    (projection : PlaceProjectionHooks Provenance
      (State Os R H D O Aff B Poll Instant System Native Profiler) C MachineHooks.FrameExtra)
    (choice : C) (place : MPlaceTy Provenance) :
    EStateM StepError (State Os R H D O Aff B Poll Instant System Native Profiler)
      (Option Clock.Duration) := do
  let field := fun name => do
    let index ← match CompilerNamedFields.fieldIndex runtime place.layout name with
      | .ok value => pure value
      | .error error => throw error
    let projected ← PlaceDynamic.field projection choice
      ⟨.memory place.mplace,place.layout⟩ index
    match projected.ref with
    | .memory memory => pure ⟨memory,projected.layout⟩
    | .local .. => throw (.invalidProgram "futex timespec field projected to a local")
  let readSigned := fun (field : MPlaceTy Provenance) => do
    let immediate ← PlaceMachine.readImmediate access ⟨.indirect field.mplace,field.layout⟩
    let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
    lift (scalar.toInt field.layout.layout.size |>.mapError ScalarOps.scalarError)
  let seconds ← readSigned (← field "tv_sec")
  let nanos ← readSigned (← field "tv_nsec")
  if seconds < 0 then throw (.unsupported "timespec with negative tv_sec is not supported")
  if seconds >= 2^64 then throw (.invalidProgram "tv_sec should fit in64bits")
  if nanos < 0 || nanos >= 1000000000 then return none
  return some (← lift (Clock.Duration.fromNanos (seconds.toNat * 1000000000 + nanos.toNat)))

/-- Assemble physical futex hooks from the exact Core projections, its
callback-aware inner-state deadline and compiler layout. Core constructs that
deadline once from the final callback router. The result shares HostRuntime
futex/deadline registries, real memory/atomic state, and typed sync effects. -/
def fromSource [DecidableEq MiriMemoryKind]
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
          (EvalCallbackFutexConstruction.World Os R H D O Aff B Poll Instant System Native Profiler))))
    (configuration : HostRuntime.Configuration)
    (projection : PlaceProjectionHooks Provenance
      (State Os R H D O Aff B Poll Instant System Native Profiler) C MachineHooks.FrameExtra)
    (choice : C)
    (deadline : DeadlineMachine.Hooks MiriMemoryKind
      (User Os R H D O Aff B Poll Instant System Native Profiler) Instant System)
    (errors : IoError.Hooks
      (State Os R H D O Aff B Poll Instant System Native Profiler) ErrorHost) :
    EStateM StepError (State Os R H D O Aff B Poll Instant System Native Profiler)
      (LinuxFutexMachine.Hooks MiriMemoryKind
        (World Os R H D O Aff B Poll Instant System Native Profiler)
        C EvalSyncObjectAccess.Payload O B Instant System Zone Timestamp ErrorHost) := do
  let readTimespec := fun place => readTimespecFromSource prepared.context.runtime access
    projection choice place
  EvalCallbackSyncConstruction.futexHooksWithReader
    prepared access allocation compiler dynamic vtable dynamicFuel atomic extras pointers
    configuration readTimespec deadline errors

end Miri.Input.EvalCallbackFutexConstruction
