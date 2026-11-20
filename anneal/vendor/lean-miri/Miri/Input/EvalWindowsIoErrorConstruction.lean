import Miri.Input.CompilerWindowsConstants
import Miri.Input.CompilerLibcConstants
import Miri.Input.EvalWindowsEnvironmentConstruction
import Miri.Interpreter.ReallocationDriver

/-! Windows `shims/io_error.rs` construction. Last-error storage is the real
active thread's lazy Machine allocation; host error translation uses the
pinned Windows table and exact compiler constants. -/
namespace Miri.Input.EvalWindowsIoErrorConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev State := EvalWindowsEnvironmentConstruction.State
abbrev InnerState := EvalCoreMachine.State

private def lift (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error error => throw error

set_option autoImplicit false in
def fromSource
    {Os R P H D O Aff B Host C Error : Type}
    (p : CompilerProviders.Prepared)
    (hostUnix : Bool)
    (host : EvalUnixConstruction.IoHostEffects
      (State Os R P H D O Aff B Host) Error)
    (memory : EvalWindowsEnvironmentConstruction.Memory Os R P H D O Aff B Host C) :
    Except StepError (IoError.Hooks (State Os R P H D O Aff B Host) Error) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.os == "windows" do
    throw (.invalidProgram s!"Windows IO errors requested for `{target.os}`")
  let raw ← CompilerPrimitiveFacts.u32Layout p.runtime |>.mapError StepError.unsupported
  let u32 : LocalLayout := ⟨raw.ty,raw.layout⟩
  unless u32.layout.isSized && u32.layout.size.bytes == 4 do
    throw (.invalidProgram "Windows last-error compiler u32 layout mismatch")
  let getPlace : EStateM StepError (InnerState Os R P H D O Aff B Host)
      (Option (MPlaceTy Provenance)) := do
    let state ← get
    let some thread := state.machine.threads.activeThread? |
      throw (.invalidProgram "last-error active thread missing")
    let some token := thread.lastErrorLocation | return none
    let entries := state.machine.user.payload.payload.user.runtime.errnoPlaces.filter
      (fun entry => entry.1.value.toNat == token)
    let some (_,place) := entries[0]? |
      throw (.invalidProgram "last-error token has no typed pointer")
    unless entries.size == 1 && place.layout == u32 do
      throw (.invalidProgram "last-error pointer metadata mismatch")
    pure (some place)
  let setPlace : MPlaceTy Provenance → EStateM StepError
      (InnerState Os R P H D O Aff B Host) Unit := fun place => do
    let some provenance := place.mplace.ptr.provenance |
      throw (.invalidProgram "last-error place has no provenance")
    let some id := PointerProvenance.getAllocId provenance |
      throw (.invalidProgram "last-error place has no allocation provenance")
    let state ← get
    let manager := state.machine.threads
    let some thread := manager.activeThread? |
      throw (.invalidProgram "last-error active thread missing")
    let thread := {thread with lastErrorLocation := some id.value.toNat}
    let world := state.machine.user.payload.payload.user
    let world := {world with runtime := {world.runtime with errnoPlaces :=
      (world.runtime.errnoPlaces.filter
        (fun (entry : AllocId × MPlaceTy Provenance) => entry.1 != id)).push (id,place)}}
    set {state with machine := {state.machine with
      threads := {manager with threads := manager.threads.set manager.activeThread.toNat thread}
      user := {state.machine.user with payload := {state.machine.user.payload with
        payload := {state.machine.user.payload.payload with user := world}}}}}
  let writeScalar := fun value destination => ExecutionStateTransport.action
    (writePlaceImmediate memory.projection.place memory.choice (.scalar value)
      ⟨.memory destination.mplace,destination.layout⟩)
  pure {
    family := .windows
    os := target.os
    hostUnix
    hostErrno := host.hostErrno
    hostFromRaw := host.hostFromRaw
    hostFromKind := host.hostFromKind
    libc := fun name =>
      match CompilerLibcConstants.scalar p.namedConstants name with
      | .ok value => pure value
      | .error reason => throw (.unsupported reason)
    windows := fun name =>
      match CompilerWindowsConstants.scalar p.namedConstants "c" name with
      | .ok value => pure value
      | .error reason => throw (.unsupported reason)
    scalarI32 := fun value => lift (value.toInt32 |>.mapError ScalarOps.scalarError)
    scalarU32 := fun value => lift (value.toUInt32 |>.mapError ScalarOps.scalarError)
    getLastErrorPlace := ExecutionStateTransport.action getPlace
    setLastErrorPlace := fun place => ExecutionStateTransport.action (setPlace place)
    allocateU32Machine := ExecutionStateTransport.action do
      let pointer ← ReallocationDriver.allocateConfigured memory.allocation
        u32.layout.size u32.layout.align.abi (.machine .machine) .Uninit
      pure ⟨⟨pointer.withOptionalProvenance,.none,none⟩,u32⟩
    writeScalar
    readScalar := fun destination => ExecutionStateTransport.action do
      let immediate ← PlaceMachine.readImmediate memory.access
        ⟨.indirect destination.mplace,destination.layout⟩
      lift (immediate.imm.toScalar |>.mapError ScalarOps.immediateError)
    writeInt := fun value destination => do
      let scalar ← lift (Scalar.fromInt value destination.layout.layout.size
        |>.mapError ScalarOps.scalarError)
      writeScalar scalar destination }

end Miri.Input.EvalWindowsIoErrorConstruction
