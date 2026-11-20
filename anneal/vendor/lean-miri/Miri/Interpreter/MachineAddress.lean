import Miri.Interpreter.PointerMachine
import Miri.Interpreter.ExecutionChoices

/-! The same source address algorithm on the actual machine-only hook state.
Global allocation conversion cannot invent a MIR frame merely to adjust a
pointer. Source choices, address-map updates and reuse clock acquisition retain
exact ordering; the low-level GlobalAddressState algorithm remains shared. -/
namespace Miri.Interpreter.MachineAddress
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
abbrev State K U := MachineHooks.MachineState K (PointerMachine.User U)
abbrev M K U A := EStateM StepError (State K U) A
structure Hooks (K U : Type) where
  arithmetic : PointerArithmetic
  externalAddress : AllocId → AllocationAddressInfo → M K U UInt64
  classifyAddressError : AddressStateError → StepError
private def addresses : M K U GlobalAddressState := return (← get).user.addresses
private def setAddresses (value : GlobalAddressState) : M K U Unit :=
  modify fun state => {state with user := {state.user with addresses := value}}
private def finish (h : Hooks K U) (result : AddressStateResult A) : M K U A := do
  setAddresses result.state
  match result.outcome with
  | .ok value => pure value | .error error => throw (h.classifyAddressError error)
private def rate (access : ExecutionChoices.Access (State K U)) (site : ExecutionChoices.BoolSite)
    (probability : _root_.Float) : M K U Bool :=
  ExecutionChoices.bernoulli access site probability.toBits
private def slack (access : ExecutionChoices.Access (State K U)) : M K U (Fin 16) := do
  let selected ← ExecutionChoices.index access .addressSlack 16
  if valid : selected < 16 then pure ⟨selected,valid⟩
  else throw (.invalidProgram "checked address slack exceeded support")
open ExecutionChoices
def assign (h : Hooks K U) (id : AllocId)
    (kind : Option AddressMemoryKind) (choice : AddressRandomChoices) : M K U UInt64 := do
  let state ← addresses
  if let some cached := state.baseAddr.find? (fun entry => entry.allocId == id) then
    return cached.address
  let some kind := kind | throw (h.classifyAddressError (.missingMemoryKind id))
  let memory := (← get).memory
  let info ← match memory.getAllocInfo id with
    | .ok info => pure info
    | .error error => throw (.callback s!"address allocation metadata: {reprStr error}")
  let info : AllocationAddressInfo := {
    kind := if info.kind == .dead then .dead else if info.kind == .typeId then .typeId else .liveData
    live := memory.isAllocLive id
    size := info.size, align := info.align, memoryKind := some kind
    thread := UInt32.ofNat (← get).threads.activeThread.toNat }
  let external ← if state.addressMode != .managed && info.kind != .typeId && info.live then
      pure (some (← h.externalAddress id info)) else pure none
  -- Native address acquisition may install prepared backing in this same
  -- source address state. Cache against the updated state, retaining ownership.
  let current ← addresses
  let result := current.addrFromAllocId id (some info) choice ⟨external⟩
  let assignment ← finish h result
  match assignment with
  | .ready address => return address
  | .acquireRequired id address clock =>
    let machine ← get
    if let some global := machine.dataRace then
      match global.acquireClock machine.threads clock with
      | .error error => throw (.callback s!"address reuse clock acquisition: {reprStr error}")
      | .ok global => modify fun state => {state with dataRace := some global}
    let cached ← addresses
    finish h (cached.cacheAddress id address)
    return address

def addrFromAllocId (access : Access (State K U)) (h : Hooks K U)
    (id : AllocId) (kind : Option AddressMemoryKind) : M K U UInt64 := do
  let initial := (← get).user.addresses
  if let some cached := initial.baseAddr.find? (fun entry => entry.allocId == id) then return cached.address
  let some kind := kind | throw (h.classifyAddressError (.missingMemoryKind id))
  let state ← get
  let info ← match state.memory.getAllocInfo id with
    | .ok info => pure info
    | .error error => throw (.callback s!"address allocation metadata: {reprStr error}")
  if info.kind == .dead || !state.memory.isAllocLive id then
    throw (h.classifyAddressError (.deadAllocation id))
  let unused : AddressRandomChoices := ⟨false,false,0,⟨0,by decide⟩⟩
  if info.kind == .typeId || initial.addressMode != .managed then
    return ← assign h id (some kind) unused
  let some generation := initial.generation | throw (h.classifyAddressError .missingAddressGeneration)
  let reuse ← if kind == .stack then pure false else rate access .addressReuse generation.reusePool.addressReuseRate
  let cross ← if reuse then rate access .addressCrossThread generation.reusePool.addressReuseCrossThreadRate else pure false
  let prepared := generation.reusePool.prepareTakeAddr reuse cross info.size info.align kind
    (UInt32.ofNat (← get).threads.activeThread.toNat)
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
  assign h id (some kind) choices


/-- The stack-miss source branch requests exactly one Fin16 slack sample
before the deterministic assignment. No source address success is assumed. -/
theorem stack_miss_request (access : Access (State K U)) (h : Hooks K U)
    (state : State K U) (id : AllocId) (info : AllocationInfo)
    (generation : AddressGenerationState)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.memory.isAllocLive id = true)
    (managed : state.user.addresses.addressMode = .managed)
    (currentGeneration : state.user.addresses.generation = some generation) :
    addrFromAllocId access h id (some .stack) state =
      (do let selected ← ExecutionChoices.index access .addressSlack 16
          if valid : selected < 16 then
            assign h id (some .stack) ⟨false,false,0,⟨selected,valid⟩⟩
          else throw (StepError.invalidProgram "checked address slack exceeded support")) state := by
  simp [addrFromAllocId,missing,metadata,data,live,managed,currentGeneration,
    ReusePool.prepareTakeAddr,setAddresses,slack,Id.run,
    get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,
    MonadStateOf.modifyGet,EStateM.modifyGet,bind,EStateM.bind,pure,EStateM.pure]
  simp only [←currentGeneration,←managed]
  cases supplied : ExecutionChoices.index access .addressSlack 16 state with
  | error error after => simp
  | ok value after =>
    by_cases within : value < 16
    · simp [within,EStateM.pure]
    · simp [within,throw,throwThe,MonadExceptOf.throw,EStateM.throw]


/-- A legal supplied stack-slack sample is consumed exactly once before
actual source assignment; assignment's non-choice outcome remains explicit. -/
theorem stack_miss_supplied (access : Access (State K U)) (h : Hooks K U)
    (state : State K U) (id : AllocId) (info : AllocationInfo)
    (generation : AddressGenerationState) (tape : Tape) (value : Nat)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.memory.isAllocLive id = true)
    (managed : state.user.addresses.addressMode = .managed)
    (currentGeneration : state.user.addresses.generation = some generation)
    (currentTape : access.get state = tape) (strict : tape.policy = .strict)
    (head : tape.inputs[tape.cursor]? = some (.index .addressSlack value))
    (supported : value < 16) :
    addrFromAllocId access h id (some .stack) state =
      assign h id (some .stack) ⟨false,false,0,⟨value,supported⟩⟩
        (access.put state {tape with cursor := tape.cursor+1, events := tape.events.push ⟨.index .addressSlack 16,.index .addressSlack value⟩}) := by
  rw [stack_miss_request access h state id info generation missing metadata data live managed currentGeneration]
  have draw := ExecutionChoices.index_supplied access state tape .addressSlack 16 value currentTape strict head supported
  simp only [bind,EStateM.bind,draw,supported,↓reduceDIte]

/-- Source action outcomes retain their effects on both error and success. -/
def resultState {S A : Type} : EStateM.Result StepError S A → S
  | .ok _ state => state
  | .error _ state => state

theorem assign_managed_payload (h : Hooks K U) (state : State K U)
    (id : AllocId) (kind : Option AddressMemoryKind) (choices : AddressRandomChoices)
    (managed : state.user.addresses.addressMode = .managed)
    (noRace : state.dataRace = none) :
    (resultState (assign h id kind choices state)).user.payload = state.user.payload := by
  cases cache : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) with
  | some cached =>
    simp [assign,addresses,cache,get,getThe,MonadStateOf.get,EStateM.get,
      bind,EStateM.bind,pure,EStateM.pure,resultState]
  | none =>
    cases kind with
    | none =>
      simp [assign,addresses,cache,get,getThe,MonadStateOf.get,EStateM.get,
        bind,EStateM.bind,pure,EStateM.pure,resultState,
        throw,throwThe,MonadExceptOf.throw,EStateM.throw]
    | some kind =>
      cases metadata : state.memory.getAllocInfo id with
      | error error =>
        simp [assign,addresses,cache,metadata,get,getThe,MonadStateOf.get,EStateM.get,
          bind,EStateM.bind,pure,EStateM.pure,resultState,
          throw,throwThe,MonadExceptOf.throw,EStateM.throw]
      | ok info =>
        let addrInfo : AllocationAddressInfo := {
          kind := if info.kind == .dead then .dead else if info.kind == .typeId then .typeId else .liveData
          live := state.memory.isAllocLive id
          size := info.size
          align := info.align
          memoryKind := some kind
          thread := UInt32.ofNat state.threads.activeThread.toNat }
        cases outcome : state.user.addresses.addrFromAllocId id (some addrInfo) choices ⟨none⟩ with
        | mk afterAddress result =>
          simp only [addrInfo,beq_iff_eq] at outcome
          cases result with
          | error error =>
            simp [assign,addresses,finish,setAddresses,cache,metadata,managed,noRace,outcome,
              get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
              modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,resultState,
              throw,throwThe,MonadExceptOf.throw,EStateM.throw]
          | ok assignment =>
            cases assignment with
            | ready address =>
              simp [assign,addresses,finish,setAddresses,cache,metadata,managed,noRace,outcome,
                get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
                modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,resultState]
            | acquireRequired target address clock =>
              cases cached : afterAddress.cacheAddress target address with
              | mk cachedState result =>
                cases result <;>
                  simp [assign,addresses,finish,setAddresses,cache,metadata,managed,noRace,outcome,cached,
                    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
                    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,resultState,
                    throw,throwThe,MonadExceptOf.throw,EStateM.throw]

end Miri.Interpreter.MachineAddress
