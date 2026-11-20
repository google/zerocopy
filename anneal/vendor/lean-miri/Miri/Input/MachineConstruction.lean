import Miri.Input.InitialMachine
import Miri.Input.HostRuntime
import Miri.Interpreter.CpuAffinity

/-! Connected portable and host machine.rs::new construction. Source resource
creation is ordered, and all resulting handles live in the actual World.host. -/
namespace Miri.Input.MachineConstruction
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
abbrev Host := HostRuntime.Storage
structure Target where
  os : String
  noCore : Bool
  cpuCount : UInt32
  cUlongBytes : Nat
  endian : Endian

private def lift (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error error => throw error

def create (h : HostRuntime.Hooks S Poll Instant System Native Profiler)
    (hostConfig : HostRuntime.Configuration) (target : Target)
    (config : InitialMachine.Configuration CpuAffinity.Mask B)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (types : RuntimeArrayTypes.World) (choices : ExecutionChoices.Tape) :
    EStateM StepError S (EvalWorld.State Os R P H D O CpuAffinity.Mask B
      (Host Poll Instant System H D O Native Profiler)) := do
  -- The source checks this limit and computes affinity after profiler creation,
  -- but before eager host poll construction. Query facts are actual target data.
  let beforePoll := do
    if target.cpuCount.toNat > CpuAffinity.maximumCpus then
      throw (.invalidProgram "configured CPU count exceeds source MAX_CPUS")
    if (target.os == "linux" || target.os == "freebsd" || target.os == "android") then
      if !target.noCore then
        let _ ← lift (CpuAffinity.initial target.cUlongBytes target.endian target.cpuCount)
        pure ()
  let beforeDescriptors := do
    let _ ← lift ((GlobalAddressState.new config.provenance config.addressMode
      config.geometry.stackAddress config.addressStop config.addressReuse).mapError
        (fun error => .invalidProgram s!"initial addresses: {reprStr error}"))
    pure ()
  let (host,descriptors,ownership) ← HostRuntime.create h hostConfig beforePoll beforeDescriptors
  HostRuntime.protect h host (do
    let affinity ← if (target.os == "linux" || target.os == "freebsd" || target.os == "android") then
      if !target.noCore then pure (some (← lift (CpuAffinity.initial target.cUlongBytes target.endian target.cpuCount)))
      else pure none
      else pure none
    let config := {config with affinity, muteOutput := hostConfig.muteOutput, hostUsizeBits := hostConfig.hostUsizeBits}
    let state ← lift (InitialMachine.create (H := H) (D := D) config memory types choices host)
    -- Use the actual source-created owning descriptor table (no shadow copy).
    let world := state.machine.user.user.payload.payload
    let runtime := {world.runtime with descriptors,ownership}
    return {state with machine := {state.machine with user := {state.machine.user with user :=
      {state.machine.user.user with payload := {state.machine.user.user.payload with payload :=
        {world with runtime}}}}}}
  )
end Miri.Input.MachineConstruction
