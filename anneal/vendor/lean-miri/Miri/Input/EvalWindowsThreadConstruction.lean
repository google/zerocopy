import Miri.Input.CompilerCallConstruction
import Miri.Input.CompilerForeignSymbols
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerProviders
import Miri.Input.CompilerWindowsConstants
import Miri.Input.EvalCoreMachine
import Miri.Input.EvalWindowsEnvironmentDispatchConstruction
import Miri.Interpreter.MainMachine
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.WindowsFileMachine
import Miri.Interpreter.WindowsThreadDispatch

/-! Canonical source construction for Windows thread/TLS shims. Thread starts,
joins, TLS keys and destructor identities all reuse the initialized Main hooks
and their existing ThreadManager/TLS arena. The file-handle view is expected
to come from the same source Windows file construction. -/
namespace Miri.Input.EvalWindowsThreadConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Payload Os R P H D O Aff B Host :=
  ValidityMachine.UserState (EvalCoreMachine.World Os R P H D O Aff B Host)
abbrev State Os R P H D O Aff B Host :=
  MainMachine.State (Payload Os R P H D O Aff B Host)
abbrev FileRef H D O := WindowsFileMachine.Ref H D O

private def lift (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok result => pure result | .error error => throw error

private def tlsError (operation : String) : ThreadTlsError → StepError
  | .nonexistentKey key => .undefinedBehavior s!"{operation} a nonexistent TLS key: {key.toNat}"
  | .keySpaceExhausted => .unsupported "we ran out of TLS key space"
  | .keyCounterOverflow => .invalidProgram "TLS key counter overflow"
  | .duplicateKey => .invalidProgram "TLS key counter generated a duplicate"
  | other => .invalidProgram s!"TLS key invariant: {reprStr other}"

set_option autoImplicit false in
def fromSource [DecidableEq MiriMemoryKind]
    {Os R P H D O Aff B Host C Error : Type}
    (p : CompilerProviders.Prepared)
    (main : MainMachine.Hooks
      (Payload Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff ProgramExitPoll)
    (environment : WindowsEnvironmentDispatch.Hooks
      (State Os R P H D O Aff B Host) Os Error EnvVars.Kind)
    (handles : WindowsHandles.Hooks
      (State Os R P H D O Aff B Host) (FileRef H D O))
    (place : PlaceHooks Provenance
      (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (choice : C)
    (compatibilityBudget : Nat) :
    Except StepError (WindowsThreadDispatch.Hooks
      (State Os R P H D O Aff B Host) (FileRef H D O)) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.os == "windows" || target.families.contains "windows" do
    throw (.invalidProgram s!"Windows thread hooks requested for `{target.os}`")
  unless environment.env.env.family == .windows &&
      environment.env.process.family == .windows do
    throw (.invalidProgram "Windows thread/environment family mismatch")
  let u32Raw ← CompilerPrimitiveFacts.u32Layout p.runtime |>.mapError StepError.unsupported
  let pointerRaw ← CompilerPrimitiveFacts.unitPointerConstLayout p.runtime
    |>.mapError StepError.unsupported
  let u32Layout : LocalLayout := ⟨u32Raw.ty,u32Raw.layout⟩
  let pointerLayout : LocalLayout := ⟨pointerRaw.ty,pointerRaw.layout⟩
  let access := main.access
  let alignment : PointerPlaceMachine.AlignmentContext
      (ThreadStacks.Storage (Payload Os R P H D O Aff B Host)) := {
    policy := fun storage => storage.user.payload.alignment
    promises := fun storage => storage.user.symbolicAlignment }
  let readScalar := fun (operand : OpTy Provenance) => do
    let immediate ← PlaceMachine.readImmediate access operand
    lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)
  let readPointer := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
  let readU32 := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toUInt32 |>.mapError ScalarOps.scalarError)
  let readUsize := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toTargetUsize access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
  let dereference := fun operand layout => do
    let pointer ← readPointer operand
    let mismatch ← PointerPlaceMachine.misalignmentWith access alignment pointer layout.layout.align.abi
    pure ⟨⟨pointer,.none,mismatch⟩,layout⟩
  let windows : String → EStateM StepError
      (State Os R P H D O Aff B Host) (Scalar Provenance) := fun name => do
    match CompilerWindowsConstants.scalar p.namedConstants "c" name with
    | .ok value => pure value
    | .error reason => throw (.unsupported reason)
  let threads := main.termination.tls.thread
  let base : WindowsThread.Hooks (State Os R P H D O Aff B Host) (FileRef H D O) := {
    handles
    readPointer
    readImmediate := PlaceMachine.readImmediate access
    readUsize
    readU32
    u32Layout := pure u32Layout
    dereference
    pointerLayout := pure pointerLayout
    windowsU32 := fun name => do
      let scalar ← windows name
      lift (scalar.toUInt32 |>.mapError ScalarOps.scalarError)
    start := fun _ _ _ _ => throw (.unsupported "Windows ThreadMachine binding missing")
    join := fun _ _ _ => throw (StepError.unsupported "Windows join binding missing")
    getTls := do return (main.termination.tls.data (← get).machine.user.user).values
    putTls := fun values => modify fun state =>
      let user := state.machine.user.user
      let data := main.termination.tls.data user
      {state with machine := {state.machine with user := {state.machine.user with
        user := main.termination.tls.putData user {data with values}}}}
    tlsError := tlsError "Windows TLS operation"
    resolveDestructor := fun pointer => do
      let fnInstance ← match ← threads.functions.call.getPtrFn choice pointer with
        | .Instance value => pure value
        | .Other _ => throw (.unsupported "FLS destructor is not a callable MIR instance")
      let span ← AllocationDriver.currentUserRelevantSpan threads.spans
      pure ⟨fnInstance,span⟩
    readWide := environment.env.strings.readWideString
    putThreads := ThreadStacks.installManager
    allocateName := fun bytes => do
      let name ← lift (OsStrings.bytesToOsStr environment.env.strings bytes)
      OsStrings.allocOsString environment.env.strings name .winLocal true
    writePointer := fun pointer destination => do
      let scalar ← lift (Scalar.fromMaybePointer access.runtime.base pointer
        |>.mapError ScalarOps.scalarError)
      writePlaceImmediate place choice (.scalar scalar)
        ⟨.memory destination.mplace,destination.layout⟩
  }
  let thread := WindowsThreadMachine.bind threads choice (.System false) none base
  let thread := WindowsThreadMachine.bindNames environment.env.strings .winLocal thread
  let symbols ← p.foreignSymbols
    |>.mapError StepError.unsupported
  let calls := CompilerCallConstruction.compiler p compatibilityBudget
  let writeScalar := fun (value : Scalar Provenance)
      (destination : MPlaceTy Provenance) =>
    writePlaceImmediate place choice (.scalar value)
      ⟨.memory destination.mplace,destination.layout⟩
  let writePointer := fun (value : Pointer (Option Provenance))
      (destination : MPlaceTy Provenance) => do
    let scalar ← lift (Scalar.fromMaybePointer access.runtime.base value
      |>.mapError ScalarOps.scalarError)
    writeScalar scalar destination
  let writeInt := fun (value : Int)
      (destination : MPlaceTy Provenance) => do
    let scalar ← lift (Scalar.fromInt value destination.layout.layout.size
      |>.mapError ScalarOps.scalarError)
    writeScalar scalar destination
  let transmute := fun (operand : OpTy Provenance)
      (layout : TyAndLayout TyId) => do
    let projection ← place.projection choice
    match operand.transmute projection layout |>.mapError
        IntrinsicVectorMachine.projectionError with
    | .ok value => pure value
    | .error error => throw error
  return {
    thread
    systemConvention := do
      return (← CompilerNamedShimAbi.query p.namedAbi "CreateThread").conv
    expectedAbi := fun name request => do
      let some operation := WindowsThreadDispatch.parse name |
        throw (.unsupported s!"Windows thread ABI requested for unknown `{name}`")
      let expected := WindowsThreadDispatch.signature operation
      unless expected.args == request.args && expected.ret == request.ret do
        throw (.invalidProgram s!"Windows thread ABI recipe disagrees with `{name}`")
      CompilerNamedShimAbi.query p.namedAbi name
    argumentCompat := calls.checkArgumentCompat choice
    checkSymbolClash := fun name =>
      match CompilerForeignSymbols.checkSymbolClash symbols name with
      | .ok () => pure ()
      | .error error => throw error
    transmute
    writeScalar
    writePointer
    writeInt
  }

end Miri.Input.EvalWindowsThreadConstruction
