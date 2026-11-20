import Miri.Interpreter.RaceMode
import Miri.Input.EvalBootstrap
import Miri.Interpreter.WindowsExitMachine
import Miri.Input.RuntimeArrayTypes
import Miri.Interpreter.IntrinsicSymbolsMachine
import Miri.Interpreter.ExecutionChoices
import Miri.Interpreter.ExecutionSafety
import Miri.Interpreter.ValidityMachine

/-! Single persistent storage composition for the canonical interpreter. No
address/type/function/callback table is mirrored for compiler or GC adapters. -/
namespace Miri.Input.EvalWorld
open Miri.Memory Miri.Interpreter
structure World (Os R Payload H D O Aff B Host : Type) where
  runtime : MachineGCRoots.Storage Os R Payload H D O Aff
  main : Option MainMachine.Data
  exit : WindowsExitMachine.Registry := {}
  types : RuntimeArrayTypes.World
  functions : FunctionPointers.Registry O
  vtables : VTableMachine.Registry
  symbols : IntrinsicSymbolsMachine.Registry := .empty
  choices : ExecutionChoices.Tape
  /-- The source machine's persistent tracked allocation set. This is shared
  by Miri tracking shims; it is not an allocation identity conversion table. -/
  trackedAllocations : Array AllocId := #[]
  backend : RaceMode.Selection B
  host : Host
abbrev User (Os R Payload H D O Aff B Host : Type) :=
  ThreadStacks.Storage (PointerMachine.User (ValidityMachine.Control (World Os R Payload H D O Aff B Host)))
abbrev State (Os R Payload H D O Aff B Host : Type) :=
  MachineHooks.State MiriMemoryKind (User Os R Payload H D O Aff B Host)

def addresses : FunctionPointers.AddressLens (User Os R Payload H D O Aff B Host)
    (ValidityMachine.Control (World Os R Payload H D O Aff B Host)) where
  get := fun user => user.user
  put := fun user value => {user with user := value}
  getPut := by intros; rfl
  putGet := by intros; rfl
  putPut := by intros; rfl

def roots : MachineGCRoots.Views (User Os R Payload H D O Aff B Host) Os R Payload H D O where
  stacks := fun user => user.registry
  tls := fun user => user.user.payload.payload.runtime.tls
  errnoPlaces := fun user => user.user.payload.payload.runtime.errnoPlaces
  unwindPayloads := fun user => user.user.payload.payload.runtime.unwindPayloads
  extras := fun user => user.user.payload.payload.runtime.extras
  environment := fun user => user.user.payload.payload.runtime.environment
  directories := fun user => user.user.payload.payload.runtime.directories
  descriptors := fun user => user.user.payload.payload.runtime.descriptors
  ownership := fun user => user.user.payload.payload.runtime.ownership
  entry := fun user => user.user.payload.payload.runtime.entry
  externStatics := fun user => user.user.payload.payload.runtime.externStatics
/-- Every source provenance visitor reads the same runtime storage used by
execution. In particular callback closures are not invented GC roots. -/
def collect : MachineHooks.M MiriMemoryKind (User Os R Payload H D O Aff B Host) Unit :=
  MachineGCRoots.run roots addresses
/-- Operational safety uses every permitted finite prefix, not an executable
fuel bound or a single supplied tape. The relation stays conditional on the
actual assembled operations and the semantic choice-support predicate. -/
def ubFreedom (main : MainMachine.Hooks U C O X F A Aff P)
    (base : RunLoopHooks (MainMachine.State U) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind U)
    (allowed : MainMachine.State U → C → Prop) (initial : MainMachine.State U → Prop) : Prop :=
  RunLoop.UBFreedomFrom (MainMachine.bindLoop main base scheduler) allowed initial

end Miri.Input.EvalWorld
