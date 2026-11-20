import Miri.Interpreter.Native.Bindings
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.ValidityMachine
import Miri.Interpreter.PointerMachineBindings

/-! Concrete native memory adapter. Source: native_lib/mod.rs:181–360,550–600
and rustc interpret/memory.rs:1104–1134. FFI execution, actual stable native
backing pointers, physical exposure and process-global state remain explicit
host effects, not fabricated native execution results. -/
namespace Miri.Interpreter.NativeMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Memory.AllocAddresses
abbrev User := ValidityMachine.UserState
abbrev State K U := ValidityMachine.State K U
abbrev M K U := ValidityMachine.M K U
abbrev Data := Allocation Provenance Miri.TreeBorrows.BorrowTree

private def lift (value : Except StepError A) : M K U A :=
  match value with | .ok value => pure value | .error error => throw error
private def allocationError (access : ValidityMachine.Access K U) (error : AllocError) : StepError :=
  access.memoryError (.allocation error)

/-- Raw access has no Rust read/write hooks. Global conversion effects and
failed mutable materialization are committed before returning its error. -/
def raw [DecidableEq K] (access : ValidityMachine.Access K U) (id : AllocId)
    (mutable : Bool) : M K U Data := do
  let state ← get
  let context : PlaceMachine.AccessState K (User U) := ⟨state.machine,none⟩
  let result := if mutable then
    MemoryLifecycle.getAllocRawMut state.machine.memory context id access.globalKind access.globalHooks
    else MemoryLifecycle.getAllocRaw state.machine.memory context id access.globalKind access.globalHooks
  set {state with machine := {result.hooks.machine with memory := result.memory}}
  match result.outcome with
  | .ok allocation => pure allocation
  | .error error => throw (result.hooks.pendingError.getD (access.memoryError (.pointerAccess (.rawAccess error))))

private def commit [DecidableEq K] (id : AllocId) (allocation : Data) : M K U Unit := do
  let state ← get
  let memory ← lift ((state.machine.memory.setLiveAllocation id allocation).mapError
    (fun error => .invalidProgram s!"native backing allocation update: {reprStr error}"))
  set {state with machine := {state.machine with memory}}

/-- The host publication callback preserves already observed bytes even when
its subsequent FFI operation fails. No mask/provenance transition runs here. -/
def publish [DecidableEq K] (access : ValidityMachine.Access K U) (id : AllocId)
    (bytes : Array UInt8) : M K U Unit := do
  let state ← get
  let some (_,entry) := state.machine.memory.live.find? (·.1 == id)
    | throw (.invalidProgram "native host published a non-owned backing")
  let allocation ← lift (entry.allocation.refreshNativeBytes bytes |>.mapError (allocationError access))
  commit id allocation

private def processSnapshot [DecidableEq K] (access : ValidityMachine.Access K U) (id : AllocId)
    (allocation : Data) (range : Option (Nat × Nat)) : M K U Unit := do
  let range ← match range with
    | none => pure none
    | some (start,size) =>
      if start >= 2^64 || size >= 2^64 then throw (.invalidProgram "native allocation range exceeds Size")
      pure (some (allocRange (Size.ofBytes (UInt64.ofNat start)) (Size.ofBytes (UInt64.ofNat size))))
  match allocation.processNativeWrite access.runtime.base range with
  | .ok () allocation => commit id allocation
  | .error error allocation =>
    commit id allocation
    throw (allocationError access error)


def processWrite [DecidableEq K] (access : ValidityMachine.Access K U) (id : AllocId)
    (range : Option (Nat × Nat)) : M K U Unit := do
  processSnapshot access id (← raw access id true) range

private def pointerPlace (place : RuntimePlace Provenance) : Except StepError (Pointer (Option Provenance)) :=
  match place.ref with
  | .memory place => .ok place.ptr
  | .local .. => .error (.invalidProgram "native return destination must be allocated")

structure Host (K U C Code : Type) where
  hostBits : Nat
  typeShape : C → LocalLayout → M K U Native.TypeShape
  layoutOf : C → TyId → M K U (Except Unit LocalLayout)
  libraries : State K U → Array Native.Library
  /-- Index selects the actual loaded handle in the source library vector,
  including distinct handles with equal configured path strings. -/
  lookupSymbol : C → Nat → Native.Library → String → M K U (Option (Native.SymbolInfo Code))
  tracingEnabled : State K U → Bool
  /-- Same stable, correctly aligned host storage that the canonical native
  address provider exposes. May materialize actual host storage, never invent
  an address or substitute copied storage with a different lifetime. -/
  backingAddress : AllocId → Data → M K U Nat
  exposePhysical : AllocId → Bool → M K U Unit
  warningEmitted : State K U → Bool
  setWarningEmitted : State K U → Bool → State K U
  diagnosticSharedMemory : C → Bool → M K U Unit
  /-- Actual libffi + supervisor. Publish all changed owned backing snapshots
  through the supplied callback on every returning outcome, including errors;
  reports are host observations, not trusted claims of native program safety. -/
  execute : (AllocId → Array UInt8 → M K U Unit) → C → Code → Array Native.OwnedArg →
    Native.FfiType → Size → M K U (Array UInt8 × Option (Array Native.AccessEvent))

private def resolve (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (ptr : Pointer (Option Provenance)) (size : Nat) : M K U (Option (AllocId × Nat)) := do
  if size >= 2^63 then throw (.invalidProgram "native pointer range exceeds signed resolver")
  let state ← get
  let result := PointerMachine.resolvePointer pointers state.machine.memory state ptr (Int.ofNat size)
  set result.state
  match result.outcome with
  | .error error => throw (.callback error)
  | .ok (.error _) => pure none
  | .ok (.ok value) => pure (some (value.allocId,value.offset.bytes.toNat))

/-- LIFO traversal snapshots children before callback mutation, matching
visit_reachable_allocs. Fuel exhaustion is a resource error, not completion. -/
def visitReachable [DecidableEq K] (access : ValidityMachine.Access K U)
    (callback : AllocId → M K U Unit) : Nat → List AllocId → Array AllocId → M K U Unit
  | _,[],_ => pure ()
  | 0,_::_,_ => throw (.resourceExhaustion "native allocation reachability budget exhausted")
  | fuel+1,id::todo,done => do
    if done.contains id then visitReachable access callback fuel todo done
    else
      let info ← lift (((← get).machine.memory.getAllocInfo id).mapError
        (fun error => .invalidProgram s!"native reachable allocation metadata: {reprStr error}"))
      let children ← if info.kind == .liveData then do
        let allocation ← raw access id false
        pure (allocation.provenanceMap.provenances.filterMap Provenance.getAllocId).toList.reverse
        else pure []
      callback id
      visitReachable access callback fuel (children ++ todo) (done.push id)

/-- Direct Native.Hooks construction: only actual compiler/OS/FFI effects and
finite query/graph budgets remain supplied; all portable memory work is real. -/
private def hooks [DecidableEq K] (host : Host K U C Code) (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (validity : ValidityVisitor.Hooks Provenance (State K U) C MachineHooks.FrameExtra F A Pad)
    (validationBudget reachabilityBudget : Nat) :
    Native.Hooks Provenance (State K U) C (RuntimePlace Provenance) Code := {
  target := access.runtime.base
  hostBits := host.hostBits
  typeShape := host.typeShape
  layoutOf := host.layoutOf
  libraries := host.libraries
  lookupSymbol := fun c library name => do
    let indexed := (host.libraries (← get)).toList.zipIdx
    let some (_,index) := indexed.find? (fun entry => entry.1.path == library.path)
      | throw (.invalidProgram "internal native library descriptor is not loaded")
    host.lookupSymbol c index library name
  tracingEnabled := host.tracingEnabled
  placeLayout := RuntimePlace.layout
  placePointer := pointerPlace
  resolve := fun _ ptr size => do
    let some result ← resolve pointers ptr size | throw (.undefinedBehavior "native argument pointer has no allocation")
    pure result
  allocation := fun _ id => do
    let allocation ← raw access id false
    let address ← host.backingAddress id allocation
    unless address < 2^host.hostBits do throw (.invalidProgram "native backing address exceeds host usize")
    if let some cached := (← get).machine.user.addresses.baseAddr.find? (·.allocId == id) then
      unless cached.address.toNat == address do throw (.invalidProgram "native backing disagrees with canonical address")
    pure ⟨address,allocation.len,allocation.mutability == .Mut,allocation.provenanceMap.provenances⟩
  provenanceRange := fun _ id start size => do
    if start >= 2^64 || size >= 2^64 then throw (.invalidProgram "native provenance range exceeds Size")
    let allocation ← raw access id false
    let provenances ← lift ((allocation.provenanceMap.getRange
      (allocRange (Size.ofBytes (UInt64.ofNat start)) (Size.ofBytes (UInt64.ofNat size)))
      access.runtime.pointerSize).mapError (fun error => allocationError access (.provenance error)))
    pure (provenances.map Prod.snd)
  inspectOutsideInterpreter := fun _ id start size => do
    let allocation ← raw access id false
    lift (allocation.inspectWithUninitAndPtrOutsideInterpreter start (start+size) |>.mapError (allocationError access))
  expose := fun _ => PointerMachine.exposeProvenance pointers
  warningEmitted := host.warningEmitted
  setWarningEmitted := host.setWarningEmitted
  diagnosticSharedMemory := host.diagnosticSharedMemory
  visitExposed := fun _ callback => do
    let exposed := (← get).machine.user.addresses.exposedAllocations
    visitReachable access callback reachabilityBudget exposed.toList.reverse #[]
  isLiveData := fun _ id => do
    let info ← lift (((← get).machine.memory.getAllocInfo id).mapError
      (fun error => .invalidProgram s!"native allocation metadata: {reprStr error}"))
    pure (info.kind == .liveData)
  exposePhysical := fun _ => host.exposePhysical
  nativeWrite := fun _ => processWrite access
  rawCall := host.execute (publish access)
  writeBytes := fun _ ptr bytes => RawMemoryMachine.writeBytes access pointers.arithmetic ptr ⟨bytes⟩
  tryResolve := fun _ => resolve pointers
  enforceValidity := fun _ _ => ValidityMachine.enforceValidity
  enforceRecursively := fun _ _ => ValidityMachine.enforceValidityRecursively
  validate := fun c dest recursive reset => ValidityVisitor.validatePlace validity c validationBudget dest recursive reset
  allocationFromAddress := fun _ address size => do
    if address >= 2^64 || size >= 2^63 then throw (.invalidProgram "native address lookup exceeds source integer domain")
    let state ← get
    lift ((state.machine.user.addresses.allocIdFromAddr (UInt64.ofNat address) (Int64.ofInt (Int.ofNat size)) {
      sizeOf := fun id => (state.machine.memory.getAllocInfo id).toOption.map (·.size)
      isLive := fun id => some (state.machine.memory.isAllocLive id) }).mapError pointers.classifyAddressError) }
private def exposeArgument [DecidableEq K] (host : Host K U C Code)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (choice : C) (tracing : Bool) (prov : Provenance) : M K U Unit := do
  unless host.warningEmitted (← get) do
    modify fun state => host.setWarningEmitted state true
    host.diagnosticSharedMemory choice tracing
  PointerMachine.exposeProvenance pointers prov

/-- Keep one source allocation snapshot across provenance exposure and raw
argument inspection. The generic legacy Hook interface is not used to repeat
these raw global queries. Immediate conversion reuses the source serializer. -/
def argument [DecidableEq K] (host : Host K U C Code) (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (engine : Native.Hooks Provenance (State K U) C (RuntimePlace Provenance) Code)
    (choice : C) (fuel : Nat) (tracing : Bool) (value : OpTy Provenance) : M K U Native.OwnedArg := do
  match value.op with
  | .immediate _ => Native.argument engine choice fuel tracing value
  | .indirect place =>
    let type ← Native.ffiType engine choice fuel value.layout
    let size := value.layout.layout.size.bytes.toNat
    unless size < 2^host.hostBits do throw (.invalidProgram "native argument exceeds host usize")
    if size == 0 then throw (.unsupported "attempting to pass a ZST over FFI")
    let some (id,offset) ← resolve pointers place.ptr size
      | throw (.undefinedBehavior "native argument pointer has no allocation")
    unless offset+size < 2^host.hostBits do throw (.invalidProgram "native argument range exceeds host usize")
    let allocation ← raw access id false
    let provenances ← lift ((allocation.provenanceMap.getRange
      (allocRange (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes (UInt64.ofNat size)))
      access.runtime.pointerSize).mapError (fun error => allocationError access (.provenance error)))
    for (_,prov) in provenances do exposeArgument host pointers choice tracing prov
    let bytes ← lift (allocation.inspectWithUninitAndPtrOutsideInterpreter offset (offset+size)
      |>.mapError (allocationError access))
    pure ⟨type,bytes⟩

private def applyRange [DecidableEq K] (host : Host K U C Code) (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (event : Native.AccessEvent) (endAddr : Nat) : Nat → Nat → M K U Unit
  | 0,current => unless current >= endAddr do throw (.resourceExhaustion "native trace range budget exhausted")
  | fuel+1,current => do
    if current >= endAddr then return
    let state ← get
    if current >= 2^64 || endAddr-current-1 >= 2^63 then throw (.invalidProgram "native trace resolver range exceeds integer domain")
    let id ← lift ((state.machine.user.addresses.allocIdFromAddr (UInt64.ofNat current)
      (Int64.ofInt (Int.ofNat (endAddr-current-1))) {
        sizeOf := fun id => (state.machine.memory.getAllocInfo id).toOption.map (·.size)
        isLive := fun id => some (state.machine.memory.isAllocLive id) }).mapError pointers.classifyAddressError)
    let some id := id | throw (.undefinedBehavior "Foreign code did an out-of-bounds access!")
    let allocation ← raw access id false
    let address ← host.backingAddress id allocation
    if current < address || endAddr < address then throw (.invalidProgram "native allocation address subtraction underflow")
    let start := current-address
    let finish := min allocation.len (endAddr-address)
    if finish <= start then throw (.invalidProgram "native traced access has empty allocation overlap")
    let range := allocRange (Size.ofBytes (UInt64.ofNat start)) (Size.ofBytes (UInt64.ofNat (finish-start)))
    match event with
    | .read _ =>
      let provenances ← lift ((allocation.provenanceMap.getRange range access.runtime.pointerSize).mapError (fun error => allocationError access (.provenance error)))
      for (_,prov) in provenances do PointerMachine.exposeProvenance pointers prov
    | .write _ certain =>
      if certain || allocation.mutability == .Mut then processWrite access id (some (start,finish-start))
    applyRange host access pointers choice event endAddr fuel (current+finish-start)

/-- Connected native driver, including the source's single-snapshot argument
and trace paths and single mutable return query. Native.Hooks remains useful
for type conversion; no baseline NativeHooks is a production input. -/
def call [DecidableEq K] (host : Host K U C Code) (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (validity : ValidityVisitor.Hooks Provenance (State K U) C MachineHooks.FrameExtra F A Pad)
    (validationBudget reachabilityBudget : Nat) (choice : C) (fuel : Nat)
    (name : String) (dest : RuntimePlace Provenance) (args : Array (OpTy Provenance)) : M K U Bool := do
  let engine := hooks host access pointers validity validationBudget reachabilityBudget
  let mut selected := none
  let libraries := host.libraries (← get)
  for index in [:libraries.size] do
    let some library := libraries[index]? | throw (.invalidProgram "native library vector index unavailable")
    if let some symbol ← host.lookupSymbol choice index library name then
      if symbol.definingPath == library.path then
        selected := some symbol.code
        break
  let some code := selected | return false
  let tracing := host.tracingEnabled (← get)
  let mut owned := #[]
  for arg in args do owned := owned.push (← argument host access pointers engine choice fuel tracing arg)
  let retType ← Native.ffiType engine choice fuel dest.layout
  engine.visitExposed choice fun id => do
    unless ← engine.isLiveData choice id do return
    let allocation ← raw access id false
    host.exposePhysical id false
    unless tracing do
      for prov in allocation.provenanceMap.provenances do PointerMachine.exposeProvenance pointers prov
    if allocation.mutability == .Mut then
      -- Source takes the mutable borrow even when tracing skips invalidation.
      let mutableAllocation ← raw access id true
      unless tracing do processSnapshot access id mutableAllocation none
      host.exposePhysical id true
  let (bytes,events) ← host.execute (publish access) choice code owned retType dest.layout.layout.size
  if tracing then
    let some events := events | throw (.invalidProgram "native tracing enabled but supervisor returned no events")
    for event in events do
      let range := event.range
      unless range.addr+range.size < 2^host.hostBits do throw (.invalidProgram "native host usize arithmetic overflow")
      applyRange host access pointers choice event (range.addr+range.size) range.size range.addr
  let ptr ← lift (pointerPlace dest)
  RawMemoryMachine.writeBytes access pointers.arithmetic ptr ⟨bytes⟩
  if bytes.isEmpty then return true
  let some (id,offset) ← resolve pointers ptr 0 | throw (.invalidProgram "native return destination allocation unavailable")
  processWrite access id (some (offset,dest.layout.layout.size.bytes.toNat))
  if ← ValidityMachine.enforceValidity then
    let recursive ← ValidityMachine.enforceValidityRecursively
    ValidityVisitor.validatePlace validity choice validationBudget dest recursive true
  pure true

end Miri.Interpreter.NativeMachine
