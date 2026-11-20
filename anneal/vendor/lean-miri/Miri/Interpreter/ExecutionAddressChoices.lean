import Miri.Interpreter.ExecutionChoices
import Miri.Interpreter.PointerMachine

/-! Source-point persistent address choices. Cached, dead/type-id and external
address paths do not consume managed reuse/slack draws. Pool-prefix mutations
and inverse-map removal remain visible if the following tape is exhausted. -/
namespace Miri.Interpreter.ExecutionAddressChoices
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open ExecutionChoices
abbrev State := PointerMachine.State
abbrev M := PointerMachine.M
private def setAddresses (addresses : GlobalAddressState) : M K U Unit :=
  modify fun state => {state with machine := {state.machine with user := {state.machine.user with addresses}}}
private def rate (access : Access (State K U)) (site : BoolSite) (probability : _root_.Float) : M K U Bool :=
  bernoulli access site probability.toBits
private def slack (access : Access (State K U)) : M K U (Fin 16) := do
  let selected ← index access .addressSlack 16
  if valid : selected < 16 then pure ⟨selected,valid⟩
  else throw (.invalidProgram "checked address slack exceeded support")

/-- AddressRandomChoices is only a transport for the existing source algorithm;
unused fields are never sampled. Every used field comes from a fresh tape event. -/
def addrFromAllocId (access : Access (State K U)) (h : PointerMachine.Hooks K U)
    (id : AllocId) (kind : Option AddressMemoryKind) : M K U UInt64 := do
  let initial := (← get).machine.user.addresses
  if let some cached := initial.baseAddr.find? (fun entry => entry.allocId == id) then return cached.address
  let some kind := kind | throw (h.classifyAddressError (.missingMemoryKind id))
  let state ← get
  let info ← match state.machine.memory.getAllocInfo id with
    | .ok info => pure info
    | .error error => throw (.callback s!"address allocation metadata: {reprStr error}")
  if info.kind == .dead || !state.machine.memory.isAllocLive id then
    throw (h.classifyAddressError (.deadAllocation id))
  let unused : AddressRandomChoices := ⟨false,false,0,⟨0,by decide⟩⟩
  if info.kind == .typeId || initial.addressMode != .managed then
    return ← PointerMachine.addrFromAllocId h id (some kind) unused
  let some generation := initial.generation | throw (h.classifyAddressError .missingAddressGeneration)
  let reuse ← if kind == .stack then pure false else rate access .addressReuse generation.reusePool.addressReuseRate
  let cross ← if reuse then rate access .addressCrossThread generation.reusePool.addressReuseCrossThreadRate else pure false
  let prepared := generation.reusePool.prepareTakeAddr reuse cross info.size info.align kind
    (UInt32.ofNat (← get).machine.threads.activeThread.toNat)
  setAddresses {initial with generation := some {generation with reusePool := prepared.state}}
  let range ← match prepared.outcome with
    | .ok range => pure range | .error error => throw (h.classifyAddressError (.reusePool error))
  let choices ← match range with
    | none => do
      let selected ← slack access
      pure {unused with reuse, crossThread := cross, slack := selected}
    | some (begin,stop) => do
      let selected ← index access .addressPool (stop-begin)
      pure {unused with reuse, crossThread := cross, poolIndex := begin+selected}
  PointerMachine.addrFromAllocId h id (some kind) choices

/-- Source free_alloc_id removes inverse/exposure mappings before the reuse
Bernoulli draw, then release-clock and add_addr, including error partial state. -/
def freeAllocId (access : Access (State K U)) (h : PointerMachine.Hooks K U)
    (id : AllocId) (size : Size) (align : Align) (kind : AddressMemoryKind) : M K U Unit := do
  let initial := (← get).machine.user.addresses
  let base := (initial.baseAddr.find? (fun entry => entry.allocId == id)).map (·.address)
  let removed := {initial with generation := none}.freeAllocId id size align kind 0 false
    (fun _ => Miri.Concurrency.VClock.default)
  let next := match removed.outcome with
    | .error (.inverseEntryMismatch ..) => {removed.state with exposed := initial.exposed}
    | _ => removed.state
  setAddresses {next with generation := initial.generation}
  match removed.outcome with | .ok () => pure () | .error error => throw (h.classifyAddressError error)
  let some generation := initial.generation | return ()
  let some base := base | throw (.invalidProgram "free address lost base cache")
  let reuse ← if kind == .stack then pure false else rate access .addressFreeReuse generation.reusePool.addressReuseRate
  let machine ← get
  let clock ← if reuse then
      match machine.machine.dataRace with
      | none => pure Miri.Concurrency.VClock.default
      | some global =>
        match global.releaseClock machine.machine.threads with
        | .error error => throw (.callback s!"free address release clock: {reprStr error}")
        | .ok (global,clock) =>
          modify fun state => {state with machine := {state.machine with dataRace := some global}}
          pure clock
    else pure Miri.Concurrency.VClock.default
  let result := generation.reusePool.addAddr reuse base size align kind
    (UInt32.ofNat (← get).machine.threads.activeThread.toNat) (fun _ => clock)
  let current := (← get).machine.user.addresses
  setAddresses {current with generation := some {generation with reusePool := result.state}}
  match result.outcome with | .ok () => pure () | .error error => throw (h.classifyAddressError (.reusePool error))
end Miri.Interpreter.ExecutionAddressChoices
