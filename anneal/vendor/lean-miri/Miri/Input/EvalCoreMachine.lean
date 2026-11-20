import Miri.Input.EvalProjectionMachine
import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.TypedMemoryProviders
import Miri.Interpreter.ExecutionIntrinsic
import Miri.Interpreter.IntrinsicMachine
import Miri.Interpreter.ExecutionChoiceBindings
import Miri.Input.RuntimeArrayFacts

/-! Physical core construction for the actual EvalWorld payload. Supplied
compiler/host policies survive; memory operations, scalar arithmetic, validity,
atomic storage and SIMD lanes are replaced by canonical source drivers. -/
namespace Miri.Input.EvalCoreMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
abbrev World := EvalWorld.World
abbrev Stored Os R P H D O Aff B Host := ThreadStacks.Storage (World Os R P H D O Aff B Host)
abbrev User Os R P H D O Aff B Host := ExecutionStateTransport.Inner (World Os R P H D O Aff B Host)
abbrev State Os R P H D O Aff B Host := MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host)

/-- One tape in the actual World; registry and Control survive every draw. -/
def tape : ExecutionChoices.Access (State Os R P H D O Aff B Host) where
  get := fun s => s.machine.user.payload.payload.user.choices
  put := fun s choices => {s with machine := {s.machine with user := {s.machine.user with payload :=
    {s.machine.user.payload with payload := {s.machine.user.payload.payload with user :=
      {s.machine.user.payload.payload.user with choices}}}}}}

/-- Sync payload execution is an actual required machine operation; its
registry is always the single shared runtime.extras, never caller-selected. -/
def extras
    (onAccess : P → Miri.Concurrency.SyncObject.AccessKind →
      PlaceMachine.MachineM MiriMemoryKind (User Os R P H D O Aff B Host) Unit)
    (weakError : Miri.Concurrency.StoreBufferAllocError → StepError) :
    MemoryExtras.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) P where
  get := fun u => u.payload.payload.user.runtime.extras
  put := fun u value => {u with payload := {u.payload with payload := {u.payload.payload with user :=
    {u.payload.payload.user with runtime := {u.payload.payload.user.runtime with extras := value}}}}}
  onAccess := onAccess
  weakError := weakError

/-- Close the caller-visible core configuration on EvalWorld. Backend dispatch,
compiler allocation/global/vtable queries, diagnostic policy, platform calls,
and allocation storage remain explicit source dependencies. The physical
callbacks overwritten here cannot be chosen independently by the caller. -/
def config
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (limits : ExecutionMachine.Limits) (choice : C) (failureRate : UInt64)
    (spans : AllocationDriver.SpanHooks)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Stored Os R P H D O Aff B Host)))
    (sync : P → Miri.Concurrency.SyncObject.AccessKind →
      PlaceMachine.MachineM MiriMemoryKind (User Os R P H D O Aff B Host) Unit)
    (weakError : Miri.Concurrency.StoreBufferAllocError → StepError)
    (deallocation : AllocationMachine.DeallocationHooks MiriMemoryKind (User Os R P H D O Aff B Host) P)

    (base : ExecutionMachine.Config MiriMemoryKind (User Os R P H D O Aff B Host) C O X ClockHost) :
    ExecutionMachine.Config MiriMemoryKind (User Os R P H D O Aff B Host) C O X ClockHost := Id.run do
  let extra := extras sync weakError
  let access := EvalBackendMachine.access
    (MemoryExtras.bindAccess extra (TypedMemoryProviders.bindAccess pointers base.access))
  let allocation := EvalAllocationMachine.allocation pointers extra base.allocation
  let pointerCompiler := CompilerExecutionProviders.pointerCompiler prepared
  let vtable := ExecutionChoiceBindings.vtableHooks tape base.validity.vtable
  let projection := EvalProjectionMachine.bindProjection prepared base.projection
  let dynamic := PlaceDynamic.withVTable projection.dynamic vtable
  let compiler := EvalProjectionMachine.bindCompiler prepared projection.maxSizeOfVal pointers base.compiler
  let compiler := PointerPlaceMachine.bindCompiler access allocation pointerCompiler dynamic vtable
    projection.dynamicFuel (ValidityMachine.compilerPolicy compiler)
  let projection := {projection with dynamic,place := ValidityMachine.placeHooks access allocation compiler}
  let validityBase := {base.validity with projection,vtable}
  let retag := RuntimeArrayFacts.retagHooks EvalProjectionMachine.arrays prepared.context
    (TypedValidityProviders.retagHooks prepared runtime access projection vtable pointers choice base.retag)
  let validity := RuntimeArrayQueries.validityHooks EvalProjectionMachine.arrays
    (TypedValidityProviders.visitor prepared runtime access allocation compiler pointers retag limits.retag validityBase)
  let (compiler,copy) := ValidityMachine.bindValidation compiler base.copy validity limits.validation
  let floats := ExecutionChoiceBindings.floatHooks tape (CompilerExecutionProviders.floatHooks prepared.context base.floats)
  let scalar := CompilerExecutionProviders.machineScalarHooks prepared access pointers dynamic vtable
    projection.dynamicFuel floats (ExecutionMachine.scalarHooks base)
  let discr := TypedMemoryProviders.discriminant prepared.context access projection (ExecutionMachine.discriminantHooks base)
  let deallocation := { deallocation with
    extras := extra
    resolvePointer := TypedMemoryProviders.lifecycleResolver pointers }
  let atomics := ExecutionIntrinsic.Atomic.access {
      loadChoiceRank := fun _ count => ExecutionChoices.index tape .atomicStale count
      weakPolicy := .mayFail
      weakSuccessChoice := fun _ => do
        let rate ← match ExecutionChoiceBindings.successRate failureRate with
          | .ok rate => pure rate | .error error => throw error
        ExecutionChoices.bernoulli tape .weakCasSuccess rate
      diagnostic := base.atomics.diagnostic
      classifyDispatchError := base.atomics.classifyDispatchError
      classifyGlobalError := base.atomics.classifyGlobalError }
    scalar access projection.place pointers extra
  let intrinsics := fun callee => Id.run do
    let source := base.intrinsics callee
    let intrinsic := IntrinsicMachine.bind source access allocation deallocation compiler copy pointers
      dynamic projection.dynamicFuel validity limits.validation
    let intrinsic := PointerPlaceMachine.bindIntrinsics access pointerCompiler dynamic vtable projection.dynamicFuel intrinsic
    let atomic := ExecutionIntrinsic.Atomic.dispatcher atomics
      source.atomicHooks.orderingConst source.atomicHooks.volatileConst
      source.atomicHooks.derefPointer access projection.place source.atomicHooks.returnToBlock
    let simd := IntrinsicVectorMachine.bindSimd {intrinsic.simdHooks with scalarOps := scalar,floatOps := floats}
      access projection copy pointerCompiler pointers
    -- Math hooks are captured while the outer source configuration is being
    -- assembled. Rebind the stateful memory/numeric dictionaries here, where
    -- the live canonical `C` and EvalWorld state are known, just as for the
    -- ordinary intrinsic fields above.
    let mathHooks := source.mathHooks.map fun hooks =>
      let hooks := {hooks with
        floatOps := floats
        scalarOps := scalar
        readImmediate := fun _ => PlaceMachine.readImmediate access
        writeImmediate := writePlaceImmediate projection.place
        destLayout := RuntimePlace.layout
        genericFloat := fun choice types => do
          let some ty := types[0]? | throw (.invalidProgram "native float intrinsic requires its source type argument")
          floats.formatOf choice ty}
      ExecutionChoiceBindings.mathHooks tape hooks
    return ExecutionChoiceBindings.intrinsicHooks tape failureRate
      {intrinsic with atomicHooks := atomic,simdHooks := simd,scalarOps := scalar,floatOps := floats,mathHooks}

  return {base with
    access,allocation,compiler,projection,copy,validity,floats,intrinsics,retag,atomics
    virtual := {base.virtual with alignment := PointerPlaceMachine.controlledAlignment}
    scalar := ExecutionScalar.Leaves.ofHooks scalar
    operands := {base.operands with
      dereference := PointerPlaceMachine.dereference access pointerCompiler dynamic vtable projection.dynamicFuel
      boolLayout := scalar.boolLayout}
    lifecycle := {base.lifecycle with storage := {base.lifecycle.storage with
      deallocateStack := fun ptr => EvalAllocationMachine.deallocate spans pointers extra deallocation ptr none .stack}}
    backend := EvalBackendMachine.dispatcher
    discriminant := ExecutionLeaves.Discriminant.ofHooks discr
    casts := {base.casts with
      exposeProvenance := fun _ provenance => PointerMachine.exposeProvenance pointers provenance
      pointerFromExposedAddress := fun _ address => PointerMachine.pointerFromExposedAddress pointers address}
    addresses := PointerMachine.User.addresses
    arithmetic := pointers.arithmetic
    validationRecursive := fun _ _ => ValidityMachine.enforceValidityRecursively}

/-- Actual outer-state MIR entry: the physical closure above is mandatory. -/
def step
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (limits : ExecutionMachine.Limits) (choice : C) (failureRate : UInt64)
    (spans : AllocationDriver.SpanHooks)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Stored Os R P H D O Aff B Host)))
    (sync : P → Miri.Concurrency.SyncObject.AccessKind →
      PlaceMachine.MachineM MiriMemoryKind (User Os R P H D O Aff B Host) Unit)
    (weakError : Miri.Concurrency.StoreBufferAllocError → StepError)
    (deallocation : AllocationMachine.DeallocationHooks MiriMemoryKind (User Os R P H D O Aff B Host) P)

    (base : ExecutionMachine.Config MiriMemoryKind (User Os R P H D O Aff B Host) C O X ClockHost)
    (state : MachineHooks.State MiriMemoryKind (ExecutionStateTransport.Outer (World Os R P H D O Aff B Host))) :
    StepResult (MachineHooks.State MiriMemoryKind (ExecutionStateTransport.Outer (World Os R P H D O Aff B Host))) Bool :=
  ExecutionStateTransport.step
    (config prepared runtime limits choice failureRate spans pointers sync weakError deallocation base)
    limits choice state

end Miri.Input.EvalCoreMachine
