import Miri.Interpreter.EventFdMachine

/-! Linux and Android foreign_items.rs legacy eventfd wrapper. -/
namespace Miri.Interpreter.EventFdDispatch
open Miri.ABI Miri.Memory Miri.MIR
abbrev M := EStateM StepError
structure Hooks (S F D MD B I : Type) where
  event : EventFd.Hooks S F
  foreign : ForeignItems.Hooks Provenance S D MD (Pointer (Option Provenance)) B I
  writeI32 : Int32 → MD → M S Unit

/-- Nonrecursive eventfd operations used while assembling a source callback
    dispatcher. The caller supplies the exact source OS and symbol-clash
    operation, without needing a second, partially assembled Unix dispatcher. -/
structure SourceHooks (S F : Type) where
  event : EventFd.Hooks S F
  os : String
  checkSymbolClash : String → M S Unit
  writeI32 : Int32 → MPlaceTy Provenance → M S Unit

def emulateSource (h : SourceHooks S F) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) :
    M S (Option ForeignItems.EmulateItemResult) := do
  if name != "eventfd" then return none
  unless h.os == "linux" || h.os == "android" || h.os == "illumos" do return none
  h.checkSymbolClash name
  if abi.conv != .C then throw (.undefinedBehavior "eventfd calling convention mismatch")
  if abi.cVariadic then throw (.undefinedBehavior "eventfd variadic signature")
  if args.size != 2 then throw (.undefinedBehavior "eventfd argument count mismatch")
  let some value := args[0]? | throw (.invalidProgram "eventfd checked initial value absent")
  let some flags := args[1]? | throw (.invalidProgram "eventfd checked flags absent")
  h.writeI32 (← EventFd.create h.event value flags) dest
  return some .NeedsReturn

def emulate (h : Hooks S F D MD B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MD) : M S (Option ForeignItems.EmulateItemResult) := do
  if name != "eventfd" then return none
  unless h.foreign.os == "linux" || h.foreign.os == "android" do return none
  h.foreign.checkSymbolClash name
  if abi.conv != .C then throw (.undefinedBehavior "eventfd calling convention mismatch")
  if abi.cVariadic then throw (.undefinedBehavior "eventfd variadic signature")
  if args.size != 2 then throw (.undefinedBehavior "eventfd argument count mismatch")
  let some value := args[0]? | throw (.invalidProgram "eventfd checked initial value absent")
  let some flags := args[1]? | throw (.invalidProgram "eventfd checked flags absent")
  h.writeI32 (← EventFd.create h.event value flags) dest
  return some .NeedsReturn

def bind (h : Hooks S F D MD B I) :
    ForeignItems.Hooks Provenance S D MD (Pointer (Option Provenance)) B I :=
  {h.foreign with unix := fun name abi args dest => do
    if let some result ← emulate h name abi args dest then return result
    h.foreign.unix name abi args dest}

def bindWrite (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra)
    (choice : C) (base : Hooks (MachineHooks.State K U) F D (MPlaceTy Provenance) B I) :
    Hooks (MachineHooks.State K U) F D (MPlaceTy Provenance) B I :=
  {base with writeI32 := fun value dest => do
    let scalar ← match Scalar.fromInt value.toInt (Size.ofBytes 4) with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    writePlaceImmediate place choice (.scalar scalar) ⟨.memory dest.mplace,dest.layout⟩}
end Miri.Interpreter.EventFdDispatch
