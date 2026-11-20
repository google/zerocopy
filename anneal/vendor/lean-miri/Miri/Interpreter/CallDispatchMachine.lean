import Miri.Interpreter.RaceMode
import Miri.Interpreter.ForeignItems
import Miri.Interpreter.IntrinsicBackend

/-! machine.rs find_mir_or_eval_fn/call_extra_fn. The foreign interpreter owns its effects; body loading is an exact compiler query. -/
namespace Miri.Interpreter.CallDispatchMachine
open Miri.ABI Miri.Memory Miri.MIR
abbrev M := EStateM StepError
structure Backend (S : Type) where
  selection : S → Except StepError IntrinsicBackend.Kind

structure Hooks (S C Other : Type) where
  /-- Foreign interpretation is constructed at the actual call state. This
  keeps live source policy (for example native-library enablement) from being
  captured when the outer execution configuration was created. -/
  foreign : Option (M S (ForeignItems.Hooks Provenance S (RuntimePlace Provenance) (RuntimePlace Provenance)
    (Pointer (Option Provenance)) LoadedBody CallInstance))
  returnToBlock : Option BasicBlockId → M S Unit
  isForeignItem : CallInstance → M S Bool
  symbolName : CallInstance → M S String
  loadMir : C → CallInstance → M S LoadedBody
  backend : Backend S
  dynSymName : Other → String
  /-- Source-owned scope around the complete foreign shim action. Deadline
  tokens are created and consumed inside one shim call, including callbacks
  run between timeout creation and blocking; keep those temporary tokens live
  until the call returns. Low-level constructors may retain identity scope. -/
  foreignScope : ∀ {A : Type}, M S A → M S A

def findMirOrEvalFn (h : Hooks S C Other) (choice : C) (callee : CallInstance)
    (abi : FnAbi TyId) (args : Array (FnArg Provenance)) (destination : RuntimeStackPlace Provenance)
    (ret : Option BasicBlockId) (unwind : UnwindAction) : M S (Option (LoadedBody × CallInstance)) := do
  if ← h.isForeignItem callee then
    let copies := args.map FnArg.copyFnArg
    let name ← h.symbolName callee
    let some foreignAction := h.foreign
      | throw (.unsupported s!"foreign call requires complete source platform input: {name}")
    return ← h.foreignScope do
      let foreign ← foreignAction
      ForeignItems.emulate foreign name abi copies destination.toRuntimePlace ret unwind
  let _ ← match h.backend.selection (← get) with
    | .ok selected => pure selected
    | .error error => throw error
  return some (← h.loadMir choice callee,callee)

def callExtra (h : Hooks S C Other) (_choice : C) (symbol : Other)
    (abi : FnAbi TyId) (args : Array (FnArg Provenance)) (destination : RuntimeStackPlace Provenance)
    (ret : Option BasicBlockId) (unwind : UnwindAction) : M S Unit := do
  let some foreignAction := h.foreign
    | throw (.unsupported "dynamic foreign call requires complete source platform input")
  h.foreignScope do
    let foreign ← foreignAction
    ForeignItems.emulateDynSym foreign (h.dynSymName symbol) abi
      (args.map FnArg.copyFnArg) destination.toRuntimePlace ret unwind
end Miri.Interpreter.CallDispatchMachine
