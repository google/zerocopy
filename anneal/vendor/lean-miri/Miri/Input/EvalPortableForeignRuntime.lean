import Miri.Input.CompilerForeignSymbols
import Miri.Input.EvalPortableForeignConstruction
import Miri.Input.CompilerProviders
import Miri.Input.CompilerBacktraceFacts
import Miri.Interpreter.PointerPlaceMachine

/-! Final compiler/runtime binding for the portable foreign source family.
This layer replaces caller-chosen symbol, function-pointer, allocation and
backtrace-global callbacks with the prepared compiler tables and canonical
runtime registries. True host effects and physical machine configurations
remain explicit. -/
namespace Miri.Input.EvalPortableForeignRuntime
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open EvalPortableForeignConstruction

abbrev User Os R P H D O Aff B Host := EvalCoreMachine.User Os R P H D O Aff B Host
abbrev State Os R P H D O Aff B Host := EvalCoreMachine.State Os R P H D O Aff B Host
abbrev M Os R P H D O Aff B Host A := MachineHooks.M MiriMemoryKind
  (User Os R P H D O Aff B Host) A

private def lift (result : Except String A) : M Os R P H D O Aff B Host A :=
  match result with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"portable compiler evidence: {error}")

def prepareSymbols (providers : CompilerProviders.Prepared) :
    Except String CompilerForeignSymbols.Prepared :=
  providers.foreignSymbols

def sourceSymbols (providers : CompilerProviders.Prepared)
    (prepared : CompilerForeignSymbols.Prepared) :
    EvalForeignConstruction.Symbols (State Os R P H D O Aff B Host) :=
  CompilerForeignSymbols.hooks prepared providers.lifecycle.calls

def sourceOptions (prepared : CompilerForeignSymbols.Prepared)
    (options : EvalForeignConstruction.Options) : EvalForeignConstruction.Options :=
  CompilerForeignSymbols.options prepared options

/-- The actual backtrace source engine uses `CompilerBacktraceSource.Prepared`
from the final provider pipeline, `FunctionPointers` for concrete function
identity/address/provenance, `PointerPlaceMachine` for source misalignment,
and the exact compiler unit-pointer layout query. -/
def backtraceCore [DecidableEq MiriMemoryKind]
    (providers : CompilerProviders.Prepared)
    (image : AllocationImage.Imported)
    (functionPointers : FunctionPointers.Hooks MiriMemoryKind
      (User Os R P H D O Aff B Host) O)
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (User Os R P H D O Aff B Host))
    (arithmetic : PointerArithmetic)
    (projection : PlaceProjectionHooks Provenance (State Os R P H D O Aff B Host)
      C MachineHooks.FrameExtra)
    (choice : C) (hostUsizeMax : Nat)
    (foreign : ForeignItems.Core Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance) :
    Backtrace.CoreHooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance) LoadedBody CallInstance
      MachineHooks.FrameExtra CompilerBacktraceSource.Position :=
  let functionPointers := CompilerFunctionPointers.hooks providers.pointers image functionPointers
  let source := CompilerBacktraceSource.source providers.lifecycle.backtrace hostUsizeMax
    (lift (CompilerBacktraceFacts.unitPointerLayout providers.lifecycle.calls))
    (PointerPlaceMachine.misalignmentWith access PointerPlaceMachine.controlledAlignment)
    (fun callee => do
      let pointer ← FunctionPointers.functionPointer functionPointers (.Instance callee)
      return pointer.withOptionalProvenance)
    (FunctionPointers.allocation functionPointers)
    (FunctionPointers.globalFunction functionPointers)
  BacktraceMachine.core access arithmetic projection choice source foreign

/-- Attach the exact compiler-backed backtrace source family to an existing
foreign resolver. Layout and source-map queries remain lazy until requested;
other portable calls continue through the existing resolver. -/
def bindBacktrace [DecidableEq MiriMemoryKind]
    (providers : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (functionPointers : FunctionPointers.Hooks MiriMemoryKind
      (User Os R P H D O Aff B Host) O)
    (access : PlaceMachine.AccessConfig MiriMemoryKind (User Os R P H D O Aff B Host))
    (arithmetic : PointerArithmetic)
    (projection : PlaceProjectionHooks Provenance (State Os R P H D O Aff B Host)
      C MachineHooks.FrameExtra)
    (choice : C) (hostUsizeMax : Nat)
    (foreign : ForeignItems.Hooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance) :
    ForeignItems.Hooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance :=
  let backtrace := backtraceCore providers image functionPointers access arithmetic
    projection choice hostUsizeMax foreign.toCore
  {foreign with otherPortable := fun name abi args destination => do
    if let some result ← Backtrace.Source.emulate backtrace
        (CompilerBacktraceFacts.reprCHook providers.lifecycle.calls) name abi args destination then
      return some result
    foreign.otherPortable name abi args destination}

/-- Complete portable source family binding. Allocator identity, fallback
function lookup and symbol-clash checks are compiler evidence; backtrace
addresses and allocation identities are source machine registries. The only
unbound external effects are the actual host/diagnostic effects in `MiriEffects`.
-/
def portableOther [DecidableEq MiriMemoryKind]
    (providers : CompilerProviders.Prepared)
    (symbols : CompilerForeignSymbols.Prepared)
    (image : AllocationImage.Imported)
    (foreign : ForeignItems.Core Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance)
    (machine : MiriShimMachine.Hooks MiriMemoryKind
      (Control Os R P H D O Aff B Host) C MachineHooks.FrameExtra Other)
    (choice : C)
    (thread : ThreadMachine.Hooks MiriMemoryKind
      (EntryUser Os R P H D O Aff B Host) C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff)
    (unitLayout : LocalLayout) (reuseClock : Option Concurrency.VectorIdx)
    (effects : MiriEffects Os R P H D O Aff B Host HostPath)
    (functionPointers : FunctionPointers.Hooks MiriMemoryKind
      (User Os R P H D O Aff B Host) O)
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (User Os R P H D O Aff B Host))
    (arithmetic : PointerArithmetic)
    (projection : PlaceProjectionHooks Provenance (State Os R P H D O Aff B Host)
      C MachineHooks.FrameExtra)
    (hostUsizeMax : Nat)
    (memory : MemoryShims.CoreHooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance) LoadedBody CallInstance)
    (stringBudget : Nat) :
    String → FnAbi TyId → Array (OpTy Provenance) → RuntimePlace Provenance →
      M Os R P H D O Aff B Host (Option ForeignItems.EmulateItemResult) := by
  let exactForeign : EvalForeignConstruction.Symbols (State Os R P H D O Aff B Host) :=
    CompilerForeignSymbols.hooks symbols providers.lifecycle.calls
  let sourceForeign := {foreign with
    noAllocShimSymbol := symbols.noAllocShimSymbol
    allocatorSymbol := exactForeign.allocatorSymbol
    lookupFunction := exactForeign.lookupFunction
    checkSymbolClash := exactForeign.checkSymbolClash }
  let functionPointers := CompilerFunctionPointers.hooks providers.pointers image functionPointers
  exact EvalPortableForeignConstruction.portableOtherFromSource sourceForeign machine choice
    thread unitLayout reuseClock effects access arithmetic projection providers.lifecycle.backtrace
    hostUsizeMax (lift (CompilerBacktraceFacts.unitPointerLayout providers.lifecycle.calls))
    (PointerPlaceMachine.misalignmentWith access PointerPlaceMachine.controlledAlignment)
    (fun callee => do
      let pointer ← FunctionPointers.functionPointer functionPointers (.Instance callee)
      return pointer.withOptionalProvenance)
    (FunctionPointers.allocation functionPointers)
    (FunctionPointers.globalFunction functionPointers)
    (fun ty => lift (CompilerBacktraceFacts.adtReprC providers.lifecycle.calls ty))
    memory stringBudget

end Miri.Input.EvalPortableForeignRuntime
