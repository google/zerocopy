import Miri.Input.EvalPortableForeignConstruction
import Miri.Interpreter.MiriShims
import Miri.Interpreter.MiriShimMachine

/-! Attach the source-built physical Miri shim machine and source effects to an
already assembled foreign resolver. Miri runs first in the portable family;
unrecognized names continue through the pre-existing backtrace and C
memory/string handlers. -/
namespace Miri.Input.EvalMiriSourceRuntime
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev User Os R P H D O Aff B Host := EvalCoreMachine.User Os R P H D O Aff B Host
abbrev State Os R P H D O Aff B Host := EvalCoreMachine.State Os R P H D O Aff B Host
abbrev Stored Os R P H D O Aff B Host := EvalCoreMachine.Stored Os R P H D O Aff B Host
abbrev World Os R P H D O Aff B Host := EvalWorld.World Os R P H D O Aff B Host
abbrev Control Os R P H D O Aff B Host := ValidityMachine.Control (Stored Os R P H D O Aff B Host)
abbrev EntryUser Os R P H D O Aff B Host := ValidityMachine.UserState (World Os R P H D O Aff B Host)
abbrev M Os R P H D O Aff B Host A := MachineHooks.M MiriMemoryKind
  (User Os R P H D O Aff B Host) A

/-- Bind physical source Miri operations without replacing any other portable
family. Allocation/provenance/GC/bookkeeping come from `machine`; thread
creation and joining use the canonical source `ThreadMachine`; only true host,
diagnostic, and selected-backend effects are supplied in `effects`. -/
def bindPhysical [DecidableEq MiriMemoryKind]
    {Os R P H D O Aff B Host Other HostPath : Type}
    (machine : MiriShimMachine.Hooks MiriMemoryKind
      (Control Os R P H D O Aff B Host) C MachineHooks.FrameExtra Other)
    (choice : C)
    (thread : ThreadMachine.Hooks MiriMemoryKind
      (EntryUser Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff)
    (unitLayout : M Os R P H D O Aff B Host LocalLayout)
    (reuseClock : Option Concurrency.VectorIdx)
    (effects : EvalPortableForeignConstruction.MiriEffects
      Os R P H D O Aff B Host HostPath)
    (foreign : ForeignItems.Hooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance) :
    ForeignItems.Hooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance := by
  let miri := EvalPortableForeignConstruction.miriCore machine choice thread
    unitLayout reuseClock effects foreign.toCore
  exact {foreign with otherPortable := fun name abi args destination => do
    if let some result ← MiriShims.Source.emulate miri name abi args destination then
      return some result
    foreign.otherPortable name abi args destination}

end Miri.Input.EvalMiriSourceRuntime
