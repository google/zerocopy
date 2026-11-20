import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerProviders
import Miri.Input.EvalCoreMachine
import Miri.Interpreter.MainMachine
import Miri.Interpreter.WindowsRandomDispatch

/-! Source construction for the three Windows entropy entry points in pinned
`shims/windows/foreign_items.rs`. Memory and isolated choices belong to the
same Main state; host entropy is the only optional external operation. -/
namespace Miri.Input.EvalWindowsRandomConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Payload Os R P H D O Aff B Host :=
  ValidityMachine.UserState (EvalCoreMachine.World Os R P H D O Aff B Host)
abbrev State Os R P H D O Aff B Host :=
  MainMachine.State (Payload Os R P H D O Aff B Host)

private def lift (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok result => pure result | .error error => throw error

set_option autoImplicit false in
def fromAccess [DecidableEq MiriMemoryKind]
    {Os R P H D O Aff B Host C Destination Body Instance : Type}
    (p : CompilerProviders.Prepared)
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (ThreadStacks.Storage (Payload Os R P H D O Aff B Host)))
    (foreign : ForeignItems.Core Provenance (State Os R P H D O Aff B Host)
      Destination (MPlaceTy Provenance) (Pointer (Option Provenance)) Body Instance)
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host)
      C MachineHooks.FrameExtra)
    (tape : ExecutionChoices.Access (State Os R P H D O Aff B Host))
    (choice : C) (communicate : Bool) (hostUsizeBits : Nat)
    (hostFill : Option (Nat → EStateM StepError (State Os R P H D O Aff B Host)
      (Except String ByteArray))) :
    Except StepError (WindowsRandomDispatch.Hooks
      (State Os R P H D O Aff B Host) Destination Body Instance) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.os == "windows" || target.families.contains "windows" do
    throw (.invalidProgram s!"Windows random source requested for `{target.os}`")
  unless foreign.family == .windows && foreign.os == "windows" do
    throw (.invalidProgram "Windows random foreign target mismatch")
  let random := RandomMemory.machine access tape communicate hostUsizeBits
    (hostFill.getD (fun _ => pure (.error "source host random fill is unavailable")))
  let writeScalar := fun (scalar : Scalar Provenance) (destination : MPlaceTy Provenance) =>
    writePlaceImmediate place choice (.scalar scalar)
      ⟨.memory destination.mplace,destination.layout⟩
  let writeInt := fun (value : Int) (destination : MPlaceTy Provenance) => do
    let scalar ← lift (Scalar.fromInt value destination.layout.layout.size
      |>.mapError ScalarOps.scalarError)
    writeScalar scalar destination
  let readU32 := fun operand => do
    let immediate ← PlaceMachine.readImmediate access operand
    let scalar ← lift (immediate.imm.toScalar |>.mapError ScalarOps.immediateError)
    lift (scalar.toUInt32 |>.mapError ScalarOps.scalarError)
  pure (WindowsRandomDispatch.sourceHooks foreign random
    (CompilerNamedShimAbi.query p.namedAbi) readU32 writeScalar writeInt)

set_option autoImplicit false in
def fromSource [DecidableEq MiriMemoryKind]
    {Os R P H D O Aff B Host C Destination Body Instance : Type}
    (p : CompilerProviders.Prepared)
    (main : MainMachine.Hooks (Payload Os R P H D O Aff B Host)
      C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff ProgramExitPoll)
    (foreign : ForeignItems.Core Provenance (State Os R P H D O Aff B Host)
      Destination (MPlaceTy Provenance) (Pointer (Option Provenance)) Body Instance)
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host)
      C MachineHooks.FrameExtra)
    (tape : ExecutionChoices.Access (State Os R P H D O Aff B Host))
    (choice : C) (communicate : Bool) (hostUsizeBits : Nat)
    (hostFill : Option (Nat → EStateM StepError (State Os R P H D O Aff B Host)
      (Except String ByteArray))) :
    Except StepError (WindowsRandomDispatch.Hooks
      (State Os R P H D O Aff B Host) Destination Body Instance) :=
  fromAccess p main.access foreign place tape choice communicate hostUsizeBits hostFill

end Miri.Input.EvalWindowsRandomConstruction
