import Miri.Input.EvalUnixSourceConstruction
import Miri.Input.CompilerProviders
import Miri.Input.CompilerLibcTypeLayouts
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerNamedFields
import Miri.Input.CompilerLibcConstants
import Miri.Interpreter.SolarishForeign
import Miri.Interpreter.ValidityMachine
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.PlaceDynamic

/-! Build the existing Solarish foreign-item machine from compiler facts and
the active Unix memory/environment products. The Solarish shim semantics stay
in `SolarishForeign`; this module supplies their exact target layouts,
constants, physical place operations, and canonical event/epoll machines. -/
namespace Miri.Input.EvalUnixSolarishConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Other Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.Other Raw Listener TcpStream Error
abbrev User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.User Os R P H D Aff B Poll Instant System Native Profiler
    Raw Listener TcpStream Error
abbrev State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.State Os R P H D Aff B Poll Instant System Native Profiler
    Raw Listener TcpStream Error
abbrev Stored Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.Stored Os R P H D Aff B Poll Instant System Native Profiler
    Raw Listener TcpStream Error
abbrev FD H D O := EvalUnixSourceConstruction.FD H D O

private def readScalar
    (access : ValidityMachine.Access MiriMemoryKind
      (Stored Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (operand : OpTy Provenance) : EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Scalar Provenance) := do
  let immediate ← ValidityMachine.readImmediate access operand
  match immediate.imm.toScalar with
  | .ok scalar => pure scalar
  | .error error => throw (ScalarOps.immediateError error)

private def pointerPlace
    (access : ValidityMachine.Access MiriMemoryKind
      (Stored Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (operand : OpTy Provenance) (layout : LocalLayout) : EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (MPlaceTy Provenance) := do
  let immediate ← ValidityMachine.readImmediate access operand
  let scalar ← match immediate.imm.toScalar with
    | .ok scalar => pure scalar
    | .error error => throw (ScalarOps.immediateError error)
  let pointer ← match scalar.toPointer access.runtime.base with
    | .ok pointer => pure pointer
    | .error error => throw (ScalarOps.scalarError error)
  PointerPlaceMachine.fromPointer access pointer layout false

/-- Construct every Solarish foreign-item hook from the live Unix environment,
compiler layout/constant tables, and canonical memory/event state. Only the
already source-constructed foreign core and event/epoll operation machines
cross this boundary; no operation callback is supplied individually. -/
def fromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (environment : UnixEnvironmentDispatch.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Os Error EnvVars.Kind)
    (foreign : ForeignItems.Core Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (RuntimePlace Provenance) (MPlaceTy Provenance) (Pointer (Option Provenance)) LoadedBody CallInstance)
    (access : ValidityMachine.Access MiriMemoryKind
      (Stored Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (place : PlaceHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C)
    (epoll : EpollShims.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) EvalUnixFdConstruction.ArrayCursor)
    (event : EventFd.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)))
    (pollBudget : Nat) (stackAddress stackSize : UInt64) :
    Except StepError (SolarishForeign.CoreHooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) EvalUnixFdConstruction.ArrayCursor
      (RuntimePlace Provenance) Error LoadedBody CallInstance) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.families.contains "unix" &&
      #[("solaris" : String),"illumos"].contains target.os &&
      environment.env.os == target.os && foreign.os == target.os &&
      foreign.family == .unix do
    throw (.invalidProgram "Solarish constructor target disagrees with compiler/environment facts")
  let readI32 := fun operand => do
    match (← readScalar access operand).toInt32 with
    | .ok value => pure value
    | .error error => throw (ScalarOps.scalarError error)
  let readPointer := fun operand => do
    match (← readScalar access operand).toPointer access.runtime.base with
    | .ok value => pure value
    | .error error => throw (ScalarOps.scalarError error)
  let writeInt := fun (value : Int) (destination : MPlaceTy Provenance) => do
    let scalar ← match Scalar.fromInt value destination.layout.layout.size with
      | .ok scalar => pure scalar
      | .error error => throw (ScalarOps.scalarError error)
    writePlaceImmediate place choice (.scalar scalar)
      ⟨.memory destination.mplace,destination.layout⟩
  let projectNamed := fun (parent : MPlaceTy Provenance) (name : String) => do
    let index ← match CompilerNamedFields.fieldIndex p.runtime parent.layout name with
      | .ok index => pure index
      | .error error => throw error
    let projected ← PlaceDynamic.field projection choice
      ⟨.memory parent.mplace,parent.layout⟩ index
    match projected.ref with
    | .memory memory => pure ⟨memory,projected.layout⟩
    | .local .. => throw (.invalidProgram "Solarish named field projection became a local")
  let libcI32 := fun name => do
    let scalar : Scalar Provenance ← match CompilerLibcConstants.scalar p.namedConstants name with
      | .ok scalar => pure scalar
      | .error error => throw (.unsupported s!"compiler Solarish libc constant `{name}`: {error}")
    match scalar.toInt32 with
    | .ok value => pure value
    | .error error => throw (ScalarOps.scalarError error)
  let derefStack := fun operand => do
    let layout ← match CompilerLibcTypeLayouts.layout p.runtime "stack_t" with
      | .ok layout => pure layout
      | .error error => throw (.unsupported s!"compiler Solarish stack_t layout: {error}")
    pointerPlace access operand layout
  let derefU32 := fun operand => do
    let layout ← match p.primitiveLayout "u32" with
      | .ok layout => pure layout
      | .error error => throw (.unsupported s!"compiler Solarish u32 layout: {error}")
    pointerPlace access operand ⟨layout.ty,layout.layout⟩
  pure {
    foreign
    errors := environment.env.errors
    epoll
    event
    pollBudget
    readI32
    readPointer
    isNull := fun pointer => pure (pointer.offset.bytes == 0)
    libcI32
    derefStack
    derefU32
    projectNamed
    writeInt
    stackAddress
    stackSize
    numCpus := environment.env.numCpus }

end Miri.Input.EvalUnixSolarishConstruction
