import Miri.Interpreter.RaceMode
import Miri.Input.EvalWorld
import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.IntrinsicBackend
import Miri.Interpreter.TypedMemoryProviders

/-! Select disabled race tracking or canonical vector clocks from the shared EvalWorld; reject inconsistent clock storage. -/

namespace Miri.Input.EvalBackendMachine
open Miri.ABI Miri.Memory Miri.Interpreter
abbrev User Os R P H D O Aff B Host := ExecutionStateTransport.Inner (EvalWorld.World Os R P H D O Aff B Host)
abbrev Machine Os R P H D O Aff B Host := MachineHooks.MachineState MiriMemoryKind (User Os R P H D O Aff B Host)
abbrev State Os R P H D O Aff B Host := MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Host)

def handler (m : Machine Os R P H D O Aff B Host) : Except StepError (RaceMode.Handler B) := do
  match m.user.payload.payload.user.backend with
  | .none =>
    if m.dataRace.isSome then throw (.invalidProgram "disabled race handler has vector clocks")
    pure .none
  | .vclocks =>
    let some clocks := m.dataRace | throw (.invalidProgram "vector-clock handler missing canonical clocks")
    pure (.vclocks clocks)

/-- Preserve source diagnostic staging and validate canonical clock storage
before continuing to race/synchronization memory hooks. -/
def access
    (base : PlaceMachine.AccessConfig MiriMemoryKind (User Os R P H D O Aff B Host)) :
    PlaceMachine.AccessConfig MiriMemoryKind (User Os R P H D O Aff B Host) :=
  {base with diagnostic := fun write id range => do
    base.diagnostic write id range
    match handler (← get) with
    | .ok _ => pure ()
    | .error error => throw error}

def dispatcher : IntrinsicBackend.Dispatcher (State Os R P H D O Aff B Host) C V where
  selection := fun state => do
    match ← handler state.machine with
    | .none => pure .none
    | .vclocks _ => pure .vclocks

end Miri.Input.EvalBackendMachine
