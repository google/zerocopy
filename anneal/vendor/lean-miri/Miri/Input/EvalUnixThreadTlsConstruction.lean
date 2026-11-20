import Miri.Input.CompilerProviders
import Miri.Input.CompilerUnixThreadDispatch
import Miri.Input.CompilerUnixTls
import Miri.Input.EvalCoreMachine
import Miri.Input.EvalSocketStorage
import Miri.Interpreter.UnixEnvironmentDispatch
import Miri.Interpreter.MainMachine
import Miri.Interpreter.UnixThreadDispatchMachine
import Miri.Interpreter.UnixTlsMachine
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.ExecutionMemoryTransport
import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.ExecutionChoiceBindings

/-! Source construction for Unix pthread and pthread-TLS bindings over the
initialized MainMachine and its actual ThreadManager/TLS arena. Thread create,
join, detach, names, current IDs, pthread keys, destructor identities and
errno all use the shared execution state. -/
namespace Miri.Input.EvalUnixThreadTlsConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Payload Os R P H D O Aff B Host :=
  ValidityMachine.UserState (EvalCoreMachine.World Os R P H D O Aff B Host)
abbrev State Os R P H D O Aff B Host :=
  MainMachine.State (Payload Os R P H D O Aff B Host)
abbrev M Os R P H D O Aff B Host A :=
  ThreadStacks.M MiriMemoryKind (Payload Os R P H D O Aff B Host) A

structure Components (S D B I : Type) where
  thread : UnixThreadDispatch.Hooks S D B I
  tls : UnixTlsDispatch.Hooks S D B I

private def lift (value : Except StepError A) : M Os R P H D O Aff B Host A :=
  match value with | .ok result => pure result | .error error => throw error

private def pointerOf (access : PlaceMachine.AccessConfig MiriMemoryKind
    (ThreadStacks.Storage (Payload Os R P H D O Aff B Host)))
    (operand : OpTy Provenance) : M Os R P H D O Aff B Host (Pointer (Option Provenance)) := do
  let immediate ← PlaceMachine.readImmediate access operand
  let scalar ← lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
  lift (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)

/-- Pinned `read_c_str`: scan one byte at a time, stop at the first NUL, then
perform the separate initialized bulk read, including the empty-string read. -/
private def readCString [DecidableEq MiriMemoryKind]
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (ThreadStacks.Storage (Payload Os R P H D O Aff B Host)))
    (budget : Nat) (pointer : Pointer (Option Provenance)) :
    M Os R P H D O Aff B Host ByteArray := do
  let arithmetic : PointerArithmetic := ⟨access.runtime.pointerSize⟩
  let rec scan : Nat → Nat → M Os R P H D O Aff B Host UInt64
    | 0, _ => throw (.resourceExhaustion "C string scan budget")
    | fuel + 1, length => do
      if length >= 2^64 then throw (.invalidProgram "C string length overflow")
      let actual ← lift (RawMemoryMachine.offset arithmetic pointer (UInt64.ofNat length))
      if (← RawMemoryMachine.readByte access arithmetic actual) == 0 then
        return UInt64.ofNat length
      scan fuel (length + 1)
  let length ← scan budget 0
  let bytes ← RawMemoryMachine.readBytes access arithmetic pointer length
  unless bytes.size == length.toNat do
    throw (.invalidProgram "C string byte-read length mismatch")
  return bytes

private def targetTlsPlatform (facts : CompilerExternStatic.TargetFacts) : TlsPlatform :=
  { unix := facts.families.contains "unix"
    os := match facts.os with
      | "linux" => .linux
      | "macos" => .macos
      | "windows" => .windows
      | os => .other os }

/-- Build source thread and pthread-TLS dispatch fields from compiler facts,
the canonical main execution component, and its shared TLS arena. `hostUsizeBits`
is the actual interpreter-host width used only at source host-size conversion
boundaries; the guest `usize` layout is still compiler-derived. -/
def fromRuntime [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (main : MainMachine.Hooks (Payload Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff ProgramExitPoll)
    (environment : UnixEnvironmentDispatch.Hooks (State Os R P H D O Aff B Host)
      Os E EnvVars.Kind)
    (signatures : ShimSignatures.Hooks Provenance (State Os R P H D O Aff B Host)
      (MPlaceTy Provenance) (MPlaceTy Provenance) (Pointer (Option Provenance)) B I)
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (choice : C)
    (hostUsizeBits stringScanBudget : Nat) :
    Except StepError (Components (State Os R P H D O Aff B Host)
      (MPlaceTy Provenance) B I) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.families.contains "unix" do
    throw (.invalidProgram s!"Unix thread/TLS hooks requested on `{target.os}`")
  unless environment.env.os == target.os && signatures.foreign.os == target.os do
    throw (.invalidProgram "Unix thread/TLS components disagree on compiler target OS")
  let primitiveSignatures := ShimSignatures.primitiveView signatures
  let access := main.access
  let alignment : PointerPlaceMachine.AlignmentContext
      (ThreadStacks.Storage (Payload Os R P H D O Aff B Host)) := {
    policy := fun storage => storage.user.payload.alignment
    promises := fun storage => storage.user.symbolicAlignment }
  let misalignment := PointerPlaceMachine.misalignmentWith access alignment
  let threadMachine := main.termination.tls.thread
  let threadChoices : ExecutionChoices.Access
      (ThreadMachine.State MiriMemoryKind (Payload Os R P H D O Aff B Host)) := {
    get := fun state => state.machine.user.user.payload.payload.choices
    put := fun state tape => {state with machine := {state.machine with user :=
      {state.machine.user with user := {state.machine.user.user with payload :=
        {state.machine.user.user.payload with payload :=
          {state.machine.user.user.payload.payload with choices := tape}}}}}}}
  let threadMachine := ExecutionChoiceBindings.threadClockReuse threadChoices threadMachine
  let threadBase : UnixThread.Hooks (State Os R P H D O Aff B Host) := {
    pthreadLayout := throw (.unsupported "compiler pthread_t layout was not installed")
    unitPointerLayout := throw (.unsupported "compiler unit-pointer layout was not installed")
    readScalar := fun _ => throw (.unsupported "pthread scalar read adapter was not installed")
    readPointer := fun _ => throw (.unsupported "pthread pointer read adapter was not installed")
    readImmediate := fun _ => throw (.unsupported "pthread immediate read adapter was not installed")
    dereference := fun _ _ => throw (.unsupported "pthread dereference adapter was not installed")
    isNull := fun pointer => pure (pointer.offset.bytes == 0)
    scalarPointer := fun _ => throw (.unsupported "pthread scalar-pointer adapter was not installed")
    scalarUsize := fun _ => throw (.unsupported "pthread usize adapter was not installed")
    readCString := readCString access stringScanBudget
    writeCString := fun bytes pointer capacity =>
      RawMemoryMachine.writeCString access ⟨access.runtime.pointerSize⟩ bytes pointer capacity
    threads := return (← get).machine.threads
    putThreads := ThreadStacks.installManager
    start := fun _ _ _ _ => throw (.unsupported "pthread start adapter was not installed")
    join := fun _ _ _ => throw (.unsupported "pthread join adapter was not installed")
    detach := fun _ => throw (.unsupported "pthread detach adapter was not installed")
    hostUsizeBits }
  let threadPolicy := UnixThreadMachine.bind threadMachine access choice main.cNoUnwind
    none misalignment threadBase
  let libc := fun name =>
    match CompilerLibcConstants.scalar p.namedConstants name with
    | .ok scalar => pure scalar
    | .error reason => throw (.unsupported s!"compiler libc scalar `{name}`: {reason}")
  let writeScalar := fun (scalar : Scalar Provenance)
      (destination : MPlaceTy Provenance) =>
    writePlaceImmediate place choice (.scalar scalar)
      ⟨.memory destination.mplace,destination.layout⟩
  let writeInt := fun (value : Int) (destination : MPlaceTy Provenance) => do
    let scalar ← lift (Scalar.fromInt value destination.layout.layout.size
      |>.mapError ScalarOps.scalarError)
    writeScalar scalar destination
  let dispatchBase : UnixThreadDispatch.Hooks (State Os R P H D O Aff B Host)
      (MPlaceTy Provenance) B I := {
    thread := threadPolicy
    signatures := primitiveSignatures
    signature := CompilerUnixThread.signature p.namedAbi
    writeScalar := fun _ _ => throw (.unsupported "pthread return writer was not installed")
    writeNull := fun _ => throw (.unsupported "pthread null writer was not installed")
    libc
    errnoNegOne := fun name => do
      let value ← IoError.setErrnoAndReturnNeg1I32 environment.env.errors (.libc name)
      lift (Scalar.fromInt value.toInt (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)
    unixGettid := fun _ => throw (.unsupported "Unix current thread ID adapter was not installed")
    apple := {
      os := target.os
      thread := threadPolicy
      process := environment.env.process
      libc
      u64Layout := match p.primitiveLayout "u64" with
        | .ok layout => pure layout
        | .error reason => throw (.unsupported s!"compiler u64 layout: {reason}")
      writeInt } }
  let threadDispatch := UnixThreadDispatchMachine.bind place choice threadPolicy dispatchBase
    |> CompilerUnixThreadDispatch.hooks p p.namedConstants p.namedAbi

  let tlsBase := UnixTlsMachine.hooks
    (UnixTlsMachine.threadData main.termination.tls)
    access place choice main.functions main.termination.tls.thread.spans misalignment
    primitiveSignatures (CompilerUnixTls.signature p.namedAbi)
    (CompilerUnixTls.keyLayout p.runtime)
  let tlsDispatch := CompilerUnixTls.hooks p.runtime p.namedAbi tlsBase
  pure ⟨threadDispatch,tlsDispatch⟩

abbrev SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.World Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev OuterSourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  MachineHooks.State MiriMemoryKind
    (ExecutionStateTransport.Outer
      (SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))

private def sourceTlsData
    (user : SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) :
    ThreadTlsMachine.Data := user.payload.payload.user.runtime.tls

private def putSourceTlsData
    (user : SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (value : ThreadTlsMachine.Data) :
    SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  {user with payload := {user.payload with payload := {user.payload.payload with user :=
    {user.payload.payload.user with runtime := {user.payload.payload.user.runtime with tls := value}}}}}

private def transportUnixThread
    (h : UnixThread.Hooks (OuterSourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)) :
    UnixThread.Hooks (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) := {
  pthreadLayout := ExecutionStateTransport.reverseAction h.pthreadLayout
  unitPointerLayout := ExecutionStateTransport.reverseAction h.unitPointerLayout
  readScalar := fun operand => ExecutionStateTransport.reverseAction (h.readScalar operand)
  readPointer := fun operand => ExecutionStateTransport.reverseAction (h.readPointer operand)
  readImmediate := fun operand => ExecutionStateTransport.reverseAction (h.readImmediate operand)
  dereference := fun operand layout => ExecutionStateTransport.reverseAction (h.dereference operand layout)
  isNull := fun pointer => ExecutionStateTransport.reverseAction (h.isNull pointer)
  scalarPointer := fun scalar => ExecutionStateTransport.reverseAction (h.scalarPointer scalar)
  scalarUsize := fun scalar => ExecutionStateTransport.reverseAction (h.scalarUsize scalar)
  readCString := fun pointer => ExecutionStateTransport.reverseAction (h.readCString pointer)
  writeCString := fun bytes pointer capacity =>
    ExecutionStateTransport.reverseAction (h.writeCString bytes pointer capacity)
  threads := ExecutionStateTransport.reverseAction h.threads
  putThreads := fun manager => ExecutionStateTransport.reverseAction (h.putThreads manager)
  start := fun output routine argument layout =>
    ExecutionStateTransport.reverseAction (h.start output routine argument layout)
  join := fun id value destination => ExecutionStateTransport.reverseAction (h.join id value destination)
  detach := fun id => ExecutionStateTransport.reverseAction (h.detach id)
  hostUsizeBits := h.hostUsizeBits }

private def sourceThreadCString [DecidableEq MiriMemoryKind]
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (ThreadStacks.Storage (ValidityMachine.UserState
        (SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))))
    (budget : Nat) (pointer : Pointer (Option Provenance)) :
    ThreadStacks.M MiriMemoryKind (ValidityMachine.UserState
      (SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)) ByteArray := do
  let arithmetic : PointerArithmetic := ⟨access.runtime.pointerSize⟩
  let rec scan : Nat → Nat → ThreadStacks.M MiriMemoryKind (ValidityMachine.UserState
      (SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)) UInt64
    | 0, _ => throw (.resourceExhaustion "C string scan budget")
    | fuel + 1, length => do
      if length >= 2^64 then throw (.invalidProgram "C string length overflow")
      let actual ← lift (RawMemoryMachine.offset arithmetic pointer (UInt64.ofNat length))
      if (← RawMemoryMachine.readByte access arithmetic actual) == 0 then return UInt64.ofNat length
      scan fuel (length + 1)
  let length ← scan budget 0
  let bytes ← RawMemoryMachine.readBytes access arithmetic pointer length
  unless bytes.size == length.toNat do throw (.invalidProgram "C string byte-read length mismatch")
  return bytes

private def sourceProcess
    (environment : UnixEnvironmentDispatch.Hooks
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Os E EnvVars.Kind) :
    EnvVars.ProcessHooks
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) := {
  environment.env.process with
  family := .unix
  activeThread := do return UInt32.ofNat (← get).machine.threads.activeThread.toNat
  threadIdTryFrom := fun raw => do
    match (← get).machine.threads.threadIdTryFrom raw.toNat with
    | .ok id => pure (some (UInt32.ofNat id.toNat))
    | .error _ => pure none }

/-! Unlike the legacy startup builder, this constructor is called at the
actual source foreign boundary. Its function-call thunk is the bounded nested
MIR configuration used by Core; the runtime thread manager, allocation,
memory, errno, TLS arena, and backend are all the live EvalWorld fields. -/
def fromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (environment : UnixEnvironmentDispatch.Hooks
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Os E EnvVars.Kind)
    (signatures : ShimSignatures.PrimitiveHooks Provenance
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind
      (SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (place : PlaceHooks Provenance
      (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C)
    (threadFunctions : Unit → Except StepError
      (FunctionCalls.Hooks Provenance
        (ThreadMachine.State MiriMemoryKind
          (ValidityMachine.UserState
            (SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)))
        C MachineHooks.FrameExtra (EvalSocketStorage.Other Raw Listener TcpStream Error)
        ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId)))
    (spans : AllocationDriver.SpanHooks)
    (functions : FunctionPointers.Hooks MiriMemoryKind
      (SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (EvalSocketStorage.Other Raw Listener TcpStream Error))
    (hostUsizeBits stringScanBudget : Nat) :
    Except StepError (Components
        (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        (MPlaceTy Provenance) B I) :=
  match threadFunctions () with
  | .error error => .error error
  | .ok threadCallHooks => do
    let target ← match p.externStatics.targetFacts with
      | .ok value => pure value
      | .error reason => throw (.unsupported s!"Unix thread compiler target: {reason}")
    unless target.families.contains "unix" && environment.env.os == target.os &&
        signatures.os == target.os do
      throw (.invalidProgram "Unix thread/TLS components disagree with compiler target")
    let runtime := fun (u : ValidityMachine.UserState
        (SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)) =>
      u.payload.payload.runtime.threads
    let putRuntime := fun (u : ValidityMachine.UserState
        (SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
        (threads : ThreadMachine.Runtime Aff) =>
      {u with payload := {u.payload with payload := {u.payload.payload with runtime :=
        {u.payload.payload.runtime with threads}}}}

    let writeOuter := fun c value destination =>
      ExecutionStateTransport.action (writePlaceImmediate place c (.scalar value)
        ⟨.memory destination.mplace,destination.layout⟩)
    let threadMachine : ThreadMachine.Hooks MiriMemoryKind
        (ValidityMachine.UserState
          (SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
        C (EvalSocketStorage.Other Raw Listener TcpStream Error) ABI.ExternAbi
        (FnAbi TyId) (ArgAbi TyId) Aff := {
      runtime
      putRuntime
      functions := threadCallHooks
      allocation := ExecutionMemoryTransport.allocation allocation
      machineMemoryKind := .machine
      writeScalar := writeOuter
      spans }
    let threadChoices : ExecutionChoices.Access
        (ThreadMachine.State MiriMemoryKind
          (ValidityMachine.UserState
            (SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))) := {
      get := fun state => state.machine.user.user.payload.payload.choices
      put := fun state tape => {state with machine := {state.machine with user :=
        {state.machine.user with user := {state.machine.user.user with payload :=
          {state.machine.user.user.payload with payload :=
            {state.machine.user.user.payload.payload with choices := tape}}}}}}}
    let threadMachine := ExecutionChoiceBindings.threadClockReuse threadChoices threadMachine
    let accessOuter := ExecutionMemoryTransport.access access
    let alignment : PointerPlaceMachine.AlignmentContext
        (ThreadStacks.Storage (ValidityMachine.UserState
          (SourceWorld Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))) := {
      policy := fun storage => storage.user.payload.alignment
      promises := fun storage => storage.user.symbolicAlignment }
    let misalignment := PointerPlaceMachine.misalignmentWith accessOuter alignment
    let threadBase : UnixThread.Hooks (OuterSourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) := {
      pthreadLayout := throw (.unsupported "compiler pthread_t layout was not installed")
      unitPointerLayout := throw (.unsupported "compiler unit-pointer layout was not installed")
      readScalar := fun _ => throw (.unsupported "pthread scalar read adapter was not installed")
      readPointer := fun _ => throw (.unsupported "pthread pointer read adapter was not installed")
      readImmediate := fun _ => throw (.unsupported "pthread immediate read adapter was not installed")
      dereference := fun _ _ => throw (.unsupported "pthread dereference adapter was not installed")
      isNull := fun pointer => pure (pointer.offset.bytes == 0)
      scalarPointer := fun _ => throw (.unsupported "pthread scalar-pointer adapter was not installed")
      scalarUsize := fun _ => throw (.unsupported "pthread usize adapter was not installed")
      readCString := sourceThreadCString accessOuter stringScanBudget
      writeCString := fun bytes pointer capacity =>
        RawMemoryMachine.writeCString accessOuter ⟨accessOuter.runtime.pointerSize⟩ bytes pointer capacity
      threads := return (← get).machine.threads
      putThreads := ThreadStacks.installManager
      start := fun _ _ _ _ => throw (.unsupported "pthread start adapter was not installed")
      join := fun _ _ _ => throw (.unsupported "pthread join adapter was not installed")
      detach := fun _ => throw (.unsupported "pthread detach adapter was not installed")
      hostUsizeBits }
    let threadOuter := UnixThreadMachine.bind threadMachine accessOuter choice (.C false)
      none misalignment threadBase
    let threadInner := transportUnixThread (CompilerUnixThread.hooks p threadOuter)
    let libc := fun name =>
      match CompilerLibcConstants.scalar p.namedConstants name with
      | .ok value => pure value
      | .error reason => throw (.unsupported s!"compiler libc scalar `{name}`: {reason}")
    let writeScalar := fun value destination =>
      writePlaceImmediate place choice (.scalar value)
        ⟨.memory destination.mplace,destination.layout⟩
    let writeInt := fun value destination => do
      let scalar ← match Scalar.fromInt value destination.layout.layout.size with
        | .ok scalar => pure scalar
        | .error error => throw (ScalarOps.scalarError error)
      writeScalar scalar destination
    let process := sourceProcess environment
    let threadBase : UnixThreadDispatch.Hooks
        (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        (MPlaceTy Provenance) B I := {
      thread := threadInner
      signatures
      signature := CompilerUnixThread.signature p.namedAbi
      writeScalar
      writeNull := writeInt 0
      libc
      errnoNegOne := fun name => do
        let value ← IoError.setErrnoAndReturnNeg1I32 environment.env.errors (.libc name)
        match Scalar.fromInt value.toInt (Size.ofBytes 4) with
        | .ok scalar => pure scalar
        | .error error => throw (ScalarOps.scalarError error)
      unixGettid := fun _ => do
        let tid ← EnvVars.currentTid process
        match Scalar.fromUInt (BitVec.ofNat 128 tid.toNat) (Size.ofBytes 4) with
        | .ok scalar => pure scalar
        | .error error => throw (ScalarOps.scalarError error)
      apple := {
        os := target.os
        thread := threadInner
        process
        libc
        u64Layout := match p.primitiveLayout "u64" with
          | .ok value => pure value
          | .error reason => throw (.unsupported s!"compiler u64 layout: {reason}")
        writeInt } }
    let threadDispatch := CompilerUnixThreadDispatch.hooks p p.namedConstants p.namedAbi threadBase
    let dataAccess : UnixTlsMachine.DataAccess
        (SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) := {
      get := sourceTlsData
      put := putSourceTlsData }
    let misalignmentInner := PointerPlaceMachine.misalignmentWith access
      PointerPlaceMachine.controlledAlignment
    let tlsBase := UnixTlsMachine.hooks dataAccess access place choice functions spans
      misalignmentInner signatures (CompilerUnixTls.signature p.namedAbi)
      (CompilerUnixTls.keyLayout p.runtime)
    let tlsDispatch := CompilerUnixTls.hooks p.runtime p.namedAbi tlsBase
    pure ⟨threadDispatch,tlsDispatch⟩

end Miri.Input.EvalUnixThreadTlsConstruction
