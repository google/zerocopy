import Lean.Util.Profile
import Miri.Interpreter.MainMachine
import Miri.Interpreter.EnvVars
import Miri.Interpreter.ExternStatic
import Miri.Input.CompilerFunctionPointers
import Miri.Input.CompilerVTableMachine
import Miri.Input.CompilerIntrinsicSymbols
import Miri.Input.CompilerGlobalBytes

/-! eval.rs::create_ecx / machine.rs::late_init on an actual initial machine.
The caller supplies the fully configured initial context and compiler image;
this module neither synthesizes target facts nor substitutes successful host
operations. Every failed initialization retains its already executed prefix. -/
namespace Miri.Input.EvalBootstrap
open Miri.Memory Miri.MIR Miri.Interpreter

structure Configuration (Os : Type) where
  arguments : Array String
  entry : DefId
  entryType : MainEntryType
  communicate : Bool
  forwarded : Array Os
  environment : Array (Os × Os)
  overrides : Array (Os × Os)

structure Hooks (U C O X F A Aff Payload AddressPayload Os : Type) where
  arguments : EntryArguments.Hooks MiriMemoryKind (ThreadStacks.Storage U) AddressPayload Payload C
  main : MainMachine.Hooks U C O X F A Aff Payload
  environment : EnvVars.Hooks (Option Provenance) Os (MainMachine.State U)
  externStatics : ExternStatic.InitHooks (MainMachine.State U)
  compiler : CompilerProviders.Prepared
  symbols : IntrinsicSymbolsMachine.Access (ThreadStacks.Storage U)
  image : AllocationImage.Imported
  vtableRuntime : VTableMachine.Hooks MiriMemoryKind (ThreadStacks.Storage U) O

/-- Salt-zero identities are attached to the actual imported image before
allocating runtime arguments. Source late_init then initializes environment,
extern statics, and finally installs the captured main-thread callback. -/
def createContextWithBytesProfiled [DecidableEq Os] (profile : Lean.Options)
    (h : Hooks U C O X F A Aff P AP Os)
    (config : Configuration Os) (choice : C) : MainMachine.M U CompilerGlobalBytes.Prepared := do
  let bytes ← CompilerGlobalBytes.attachProfiled profile h.compiler.program h.compiler.runtime
    (some h.compiler.sourceEquality)
  CompilerFunctionPointers.attachProfiled profile h.compiler.pointers h.image h.main.functions
  CompilerVTableMachine.attachProfiled profile h.compiler.vtables h.image h.vtableRuntime
  CompilerIntrinsicSymbols.attachProfiled profile h.compiler h.image h.symbols
  let arguments ← EntryArguments.initializeMiri h.arguments choice config.arguments
  EnvVars.init h.environment config.communicate config.forwarded config.environment config.overrides
  ExternStatic.initExternStatics h.externStatics
  MainMachine.install h.main config.entry config.entryType arguments h.arguments.windows
  pure bytes

def createContextWithBytes [DecidableEq Os] (h : Hooks U C O X F A Aff P AP Os)
    (config : Configuration Os) (choice : C) : MainMachine.M U CompilerGlobalBytes.Prepared :=
  createContextWithBytesProfiled {} h config choice

theorem createContextWithBytes_profile_identity [DecidableEq Os]
    (h : Hooks U C O X F A Aff P AP Os) (config : Configuration Os) (choice : C) :
    createContextWithBytes h config choice = createContextWithBytesProfiled {} h config choice := rfl

/-- Compatibility entry; initialization still attaches the actual compiler byte pool. -/
def createContext [DecidableEq Os] (h : Hooks U C O X F A Aff P AP Os)
    (config : Configuration Os) (choice : C) : MainMachine.M U Unit := do
  let _ ← createContextWithBytes h config choice
  pure ()

/-- A finite execution prefix, not successful program completion. Exit remains
an actual termination outcome of the source loop; exhausting supplied choices
returns the current state so a caller can extend the execution prefix. -/
def executePrefix (h : MainMachine.Hooks U C O X F A Aff P)
    (base : RunLoopHooks (MainMachine.State U) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind U)
    (choices : List C) (initial : MainMachine.State U) : StepResult (MainMachine.State U) Unit :=
  go (MainMachine.bindLoop h base scheduler) choices initial
where
  go (loop : RunLoopHooks (MainMachine.State U) C MainMachine.Callback) :
      List C → MainMachine.State U → StepResult (MainMachine.State U) Unit
    | [],state => (state,.ok ())
    | choice::rest,state =>
      match RunLoop.iteration loop choice state with
      | (state,.error error) => (state,.error error)
      | (state,.ok ()) => go loop rest state

end Miri.Input.EvalBootstrap
