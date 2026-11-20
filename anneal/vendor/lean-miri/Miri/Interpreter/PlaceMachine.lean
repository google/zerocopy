import Miri.Interpreter.PlaceDynamic

/-! Canonical Place ↔ Miri machine access. Vector-clock and Tree Borrows rules
are actual operations; address/global/weak-memory/synchronization policies are
required leaves. Typed failures survive the legacy string memory-hook boundary.
-/
namespace Miri.Interpreter.PlaceMachine
open Miri.ABI Miri.Memory Miri.TreeBorrows
abbrev Machine (K User : Type) := MachineHooks.MachineState K User
abbrev State (K User : Type) := MachineHooks.State K User
abbrev M (K User A : Type) := MachineHooks.M K User A
abbrev MachineM (K User A : Type) := EStateM StepError (Machine K User) A

structure AccessState (K User : Type) where
  machine : Machine K User
  pendingError : Option StepError := none

/-- Policies outside ordinary non-atomic VClock/Tree-Borrows access. Diagnostic
runs before races; weakMemoryWrite after successful race write; syncAccess after
successful Tree Borrows. Hooks may change User/external indices, not live bytes;
the allocation-access layer owns byte/extra commits. Disabled policies must be
chosen explicitly by the machine configuration. -/
structure AccessConfig (K User : Type) where
  runtime : RuntimeTargetDataLayout
  ghostMode : Bool
  globalKind : Option K
  globalHooks : GlobalAllocationHooks Provenance BorrowTree K (AccessState K User)
  dynamicLayout : DynamicLayoutResolver Provenance BorrowTree K (AccessState K User)
  resolvePointer : MemoryState Provenance BorrowTree K → Pointer (Option Provenance) → Int →
    MachineM K User (Except UInt64 (ResolvedPointer ProvenanceExtra))
  beforeAllocationAccess : AllocId → MachineM K User Unit
  diagnostic : Bool → AllocId → AllocRange → MachineM K User Unit
  weakMemoryWrite : AllocId → AllocRange → MachineM K User Unit
  syncAccess : Bool → AllocId → AllocRange → MachineM K User Unit
  retainTouched : Machine K User → Option (AllocationAccessRef Provenance BorrowTree) → Machine K User
  memoryError : MemoryOperandError → StepError

private def treeError (status : BorrowTree.BorrowTreeAccessStatus) : StepError :=
  match status with
  | .AccessFailure _ (.TransitionError ..)
  | .WildcardFailure _ (.TransitionError ..)
  | .WildcardFailure _ (.NoValidExposedReferences ..) =>
    .undefinedBehavior s!"Tree Borrows: {reprStr status}"
  | _ => .invalidProgram s!"Tree Borrows invariant: {reprStr status}"

private def bridge (state : AccessState K User) (action : MachineM K User A) :
    MachineHookResult (AccessState K User) A :=
  match action state.machine with
  | .ok value machine => ⟨{ state with machine }, .ok value⟩
  | .error error machine => ⟨⟨machine, some error⟩, .error (reprStr error)⟩

/-- Source before_memory_read/write order, retaining the tree after access UB
and prior clock/weak-memory effects on every failure. -/
def memoryAccess (config : AccessConfig K User) (write : Bool)
    (state : AccessState K User) (tree : BorrowTree) (allocId : AllocId)
    (provenance : ProvenanceExtra) (range : AllocRange) :
    AllocationExtraHookResult (AccessState K User) BorrowTree := Id.run do
  let mut state := state
  let diagnostic := bridge state (config.diagnostic write allocId range)
  state := diagnostic.state
  if let .error error := diagnostic.outcome then return ⟨state, tree, .error error⟩
  let (machine, race) := MachineHooks.memoryRaceAccess state.machine allocId range
    (if write then some .Write else none) .Read
  state := { state with machine }
  if let .error error := race then return ⟨{state with pendingError := some error}, tree, .error (reprStr error)⟩
  if write then
    let weak := bridge state (config.weakMemoryWrite allocId range)
    state := weak.state
    if let .error error := weak.outcome then return ⟨state, tree, .error error⟩
  let mut tree := tree
  if let some tracker := state.machine.borrowTracker then
    let accessed := tree.performBorrowAccessRange provenance range.start range.size
      (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed
    tree := accessed.tree
    if accessed.status != .Completed then
      let error := treeError accessed.status
      return ⟨{state with pendingError := some error}, tree, .error (reprStr error)⟩
  let sync := bridge state (config.syncAccess write allocId range)
  return ⟨sync.state, tree, sync.outcome⟩

def accessHooks (config : AccessConfig K User) :
    AllocationAccessHooks Provenance BorrowTree K (AccessState K User) ProvenanceExtra := {
  resolvePointer := fun memory state ptr size => bridge state (config.resolvePointer memory ptr size)
  beforeAllocationAccess := fun state id => bridge state (config.beforeAllocationAccess id)
  beforeMemoryRead := fun state tree _ id provenance range => memoryAccess config false state tree id provenance range
  beforeMemoryWrite := fun state tree _ id provenance range => memoryAccess config true state tree id provenance range }

private def commit (config : AccessConfig K User)
    (memory : MemoryState Provenance BorrowTree K) (hooks : AccessState K User)
    (touched : Option (AllocationAccessRef Provenance BorrowTree)) : M K User Unit :=
  modify fun state => { state with machine := config.retainTouched {hooks.machine with memory} touched }

private def finish (config : AccessConfig K User) (hooks : AccessState K User)
    (outcome : Except MemoryOperandError A) : M K User A := do
  match outcome with
  | .ok value => return value
  | .error error => throw (hooks.pendingError.getD (config.memoryError error))

def readImmediate [DecidableEq K] (config : AccessConfig K User) (operand : OpTy Provenance) :
    M K User (RvalueImmTy Provenance) := do
  let state ← get
  let result := Miri.Interpreter.readImmediate state.machine.memory ⟨state.machine, none⟩ operand.op
    (localMemoryLayout operand.layout) config.runtime config.ghostMode config.globalKind
    config.globalHooks (accessHooks config) config.dynamicLayout
  commit config result.memory result.hooks result.touched
  let value ← finish config result.hooks result.outcome
  return ⟨value.value, operand.layout⟩

def readRaw [DecidableEq K] (config : AccessConfig K User) (operand : OpTy Provenance) :
    M K User (ImmediateOrPlace Provenance) := do
  let state ← get
  let result := Miri.Interpreter.readImmediateRaw state.machine.memory ⟨state.machine, none⟩ operand.op
    (localMemoryLayout operand.layout) config.runtime config.ghostMode config.globalKind
    config.globalHooks (accessHooks config) config.dynamicLayout
  commit config result.memory result.hooks result.touched
  finish config result.hooks result.outcome

def writeMemory [DecidableEq K] (config : AccessConfig K User)
    (willValidate : MemoryOperandLayout → Bool) (value : Immediate Provenance)
    (place : MPlaceTy Provenance) : M K User Unit := do
  let state ← get
  let result := writeImmediateToMplaceNoValidate state.machine.memory ⟨state.machine, none⟩ value
    ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
    config.globalHooks (accessHooks config) config.dynamicLayout willValidate
  commit config result.memory result.hooks result.touched
  finish config result.hooks result.outcome

/-- The canonical zero-sized unit write preserves the entire machine and stack.
No allocation lookup, pointer resolution or permission transition is assumed.
The layout and pointer-size premises concern compiler/target data only. -/
theorem writeMemory_zero_uninit [DecidableEq K]
    (config : AccessConfig K User) (later : MemoryOperandLayout → Bool)
    (place : MPlaceTy Provenance) (pointer : Pointer (Option Provenance))
    (ty : Option Nat) (pointerSize : Size)
    (unitLayout : localMemoryLayout place.layout =
      ⟨Size.ZERO, Align.ONE, .Memory (sized := true), ty⟩)
    (placeMemory : place.mplace = ⟨pointer, .none, none⟩)
    (pointerMetadata : config.runtime.pointerSizeIn config.runtime.defaultAddressSpace = .ok pointerSize)
    (retain : ∀ machine, config.retainTouched machine none = machine)
    (state : State K User) :
    writeMemory config later .uninit place state = .ok () state := by
  simp only [writeMemory, unitLayout, placeMemory]
  simp only [zero_uninit_write (pointerSize := pointerSize) (pointerMetadata := pointerMetadata)]
  simp [commit, finish, retain]
  with_unfolding_all rfl

/-- Source stack init_allocation: root borrow tree before allocation race
state. Stack allocation time comes from the active thread; historical local
clocks are transferred by afterLocalMovedToMemory later. Span-only diagnostic
and weak-memory construction leaves remain explicit. -/
def initStackExtra (allocationTail : AllocId → Size → Align → MachineM K User Unit)
    (id : AllocId) (size : Size) (align : Align) : MachineM K User BorrowTree := do
  let machine ← get
  let (machine, tag) ← match machine.borrowTracker with
    | none => pure (machine, BorTag.one)
    | some tracker =>
      match tracker.global.rootPointerTag id with
      | .error e => throw (.resourceExhaustion s!"allocation root tag: {repr e}")
      | .ok (global, tag) => pure ({machine with borrowTracker := some {tracker with global}}, tag)
  set machine
  let tree := BorrowTree.new tag size
  if let some global := machine.dataRace then
    let (index, clocks) ← match global.activeThreadState machine.threads with
      | .error e => throw (.invalidProgram s!"allocation clocks: {repr e}")
      | .ok value => pure value
    let length := Miri.Concurrency.ByteSize.ofU64 size.bytes.toNat (by have h := UInt64.toNat_lt size.bytes; omega)
    let allocation := Miri.Concurrency.VClockAlloc.newAllocation length (clocks.clock.index index) index
    modify fun machine => {machine with raceAllocations :=
      (machine.raceAllocations.filter fun entry => entry.1 != id).push (id, allocation)}
  allocationTail id size align
  return tree

structure AllocationConfig (K User : Type) where
  maximumObjectSize : Size
  zeroedStorage : Size → Align → Option (Array UInt8)
  nativeStorage : Option (Size → Align → AllocInit → M K User (Except AllocError (Allocation Provenance Unit))) := none
  nativeDrop : Option (Allocation Provenance Unit → M K User Unit) := none
  diagnostic : AllocId → Size → Align → MachineM K User Unit
  allocationTail : AllocId → Size → Align → MachineM K User Unit
  /-- Actual address-map allocation with the existing root tag. This must not
  replace the tag or derive an absolute address from allocation identity. -/
  adjustRootAddress : AllocId → BorTag → M K User (Pointer Provenance)

/-- Actual uninitialized stack allocation, with root/tree/clock effects
retained when a later root-address adjustment fails. -/
def allocateStackRaw [DecidableEq K] (config : AllocationConfig K User) (size : Size) (align : Align) :
    M K User (Pointer (Option Provenance)) := do
  let created ← match config.nativeStorage with
    | some create => create size align .Uninit
    | none => pure (Allocation.tryNew (Prov := Provenance) size align .Uninit config.zeroedStorage)
  let allocation ← match created with
    | .ok allocation => pure allocation
    | .error e => throw (.callback s!"stack allocation storage: {repr e}")
  try
    if allocation.byteSize.bytes > config.maximumObjectSize.bytes then
      throw (.resourceExhaustion "stack allocation exceeds maximum object size")
    let state ← get
    let (memory, reserved) := state.machine.memory.reserveAllocId
    set {state with machine := {state.machine with memory}}
    let id ← match reserved with
      | .ok id => pure id
      | .error e => throw (.resourceExhaustion s!"stack allocation ID: {repr e}")
    let initialized : MachineM K User BorrowTree := do
      config.diagnostic id size align
      initStackExtra config.allocationTail id size align
    let state ← get
    let tree ← match initialized state.machine with
      | .ok tree machine =>
        set {state with machine}
        pure tree
      | .error error machine =>
        set {state with machine}
        throw error
    modify fun state => {state with machine := {state.machine with memory :=
      {state.machine.memory with live := state.machine.memory.live.push (id, ⟨.stack, allocation.withExtra tree⟩)}}}
    let state ← get
    let tag ← match state.machine.borrowTracker with
      | none => pure BorTag.one
      | some tracker =>
        match tracker.global.rootTag? id with
        | some tag => pure tag
        | none => throw (.invalidProgram "initialized allocation missing root tag")
    let pointer ← config.adjustRootAddress id tag
    return pointer.withOptionalProvenance
  catch error =>
    if allocation.nativeBuffer.isSome then
      let retained := (← get).machine.memory.live.any fun (_,entry) => entry.allocation.nativeBuffer == allocation.nativeBuffer
      unless retained do
        let some drop := config.nativeDrop | throw (.invalidProgram "native stack backing lacks drop capability")
        drop allocation
    throw error


/-- Typed stack allocation retains the source sized-layout check. Raw temporary
buffers use allocateStackRaw directly and require no fabricated compiler type. -/
def allocateStack [DecidableEq K] (config : AllocationConfig K User) (layout : LocalLayout) :
    M K User (MPlaceTy Provenance) := do
  if !layout.layout.isSized then throw (.invalidProgram "unsized stack allocation")
  let pointer ← allocateStackRaw config layout.layout.size layout.layout.align.abi
  return ⟨⟨pointer,.none,none⟩,layout⟩

structure CompilerHooks (K User C : Type) where
  debugAssertions : Bool
  layout : C → MIR.LocalId → M K User LocalLayout
  validationInProgress : M K User Bool
  projection : C → M K User (ProjectionCx Provenance)
  deref : C → RuntimePlace Provenance → Bool → M K User (RuntimePlace Provenance)
  checkPlaceType : C → MIR.Place → RuntimePlace Provenance → M K User Unit
  memoryOffset : C → MemPlace Provenance → Size → OffsetMode → MemPlaceMeta Provenance → M K User (MemPlace Provenance)
  debugAbiCheck : Immediate Provenance → LocalLayout → M K User Unit
  localSpan : MIR.Body → MIR.LocalId → M K User MIR.SpanRef
  enforceValidity : C → LocalLayout → M K User Bool
  validate : C → RuntimePlace Provenance → M K User Unit
  willValidateMemory : MemoryOperandLayout → Bool

def layoutLocal (compiler : CompilerHooks K User C) (choice : C) (id : MIR.LocalId) : M K User LocalLayout := do
  let frame ← MachineHooks.currentFrame
  let slot ← match frame.getLocal id with | .ok s => pure s | .error e => throw (.stack e)
  if let some layout := slot.layout then return layout
  let layout ← compiler.layout choice id
  let (frame, layout) ← match (← MachineHooks.currentFrame).getOrCacheLocalLayout id layout with
    | .ok value => pure value | .error e => throw (.stack e)
  MachineHooks.setCurrentFrame frame
  return layout

/-- Source local read, with layout/cache resolution provided separately from
unrelated compiler/place operations. The actual read event remains mandatory. -/
def localToOpCore (layoutOf : MIR.LocalId → M K User LocalLayout)
    (validationInProgress : M K User Bool) (id : MIR.LocalId) : M K User (OpTy Provenance) := do
  let layout ← layoutOf id
  let op ← match (← MachineHooks.currentFrame).getLocalOperand id with
    | .ok op => pure op | .error e => throw (.stack e)
  if let .immediate _ := op then
    if !layout.layout.isSized then throw (.invalidProgram "unsized local is immediate")
    unless ← validationInProgress do MachineHooks.afterLocalRead id
  return ⟨op, layout⟩

def localToOp (compiler : CompilerHooks K User C) (choice : C) (id : MIR.LocalId) : M K User (OpTy Provenance) :=
  localToOpCore (layoutLocal compiler choice) compiler.validationInProgress id

def placeHooks [DecidableEq K] (access : AccessConfig K User) (allocation : AllocationConfig K User)
    (compiler : CompilerHooks K User C) : PlaceHooks Provenance (State K User) C MachineHooks.FrameExtra := {
  getFrame := MachineHooks.currentFrame, setFrame := MachineHooks.setCurrentFrame
  debugAssertions := compiler.debugAssertions
  frameIndex := do match (← get).stack.frameIndex with | .ok i => pure i | .error e => throw (.stack e)
  resolveLayout := compiler.layout, localToOp := localToOp compiler
  projection := compiler.projection, deref := compiler.deref, checkPlaceType := compiler.checkPlaceType
  allocateStack := fun _ => allocateStack allocation
  writeMemoryNoValidate := fun _ => writeMemory access compiler.willValidateMemory
  afterLocalMovedToMemory := fun _ id place => MachineHooks.afterLocalMovedToMemory id place compiler.localSpan
  memoryOffset := compiler.memoryOffset
  writeLocalImmediate := fun _ => placeWriteLocalImmediate MachineHooks.currentFrame MachineHooks.setCurrentFrame
    compiler.validationInProgress MachineHooks.afterLocalWrite compiler.debugAbiCheck
  enforceValidity := compiler.enforceValidity, validate := compiler.validate }

/-- Compiler/type/layout preparation remains fallible; the write-uninit stage
is supplied by the actual typed memory writer below, including races and TB. -/
structure RetagQueries (K User : Type) where
  preparePointerRetag : RvalueImmTy Provenance → MIR.TyId → Miri.TreeBorrows.RetagPolicy.RetagMode →
    M K User Miri.TreeBorrows.RetagPipeline.Request
  reconstructImmediate : RvalueImmTy Provenance → Option Provenance → M K User (RvalueImmTy Provenance)
  preparePlaceProtection : MPlaceTy Provenance → M K User Miri.TreeBorrows.RetagPipeline.Request
  ensureTreeExtra : AllocId → M K User Unit

def retagHooks [DecidableEq K] (access : AccessConfig K User) (queries : RetagQueries K User) :
    MachineHooks.Hooks K User := {
  preparePointerRetag := queries.preparePointerRetag
  reconstructImmediate := queries.reconstructImmediate
  preparePlaceProtection := queries.preparePlaceProtection
  ensureTreeExtra := queries.ensureTreeExtra
  writeUninit := writeMemory access (fun _ => false) .uninit }

/-- Bind canonical typed places and actual retag/race hooks to the existing
rvalue interpreter. The supplied evaluator is normally PlaceDynamic.evalPlace;
operand evaluation/projection, casts and compiler facts stay required in base.
No unconditional retag is inserted on raw-pointer or integer copies: the source
rvalue dispatcher chooses Default/TwoPhase/Raw/None and its retag trigger. -/
def bindRvalue [DecidableEq K]
    (base : RvalueHooks Provenance (State K User) C (RuntimePlace Provenance))
    (access : AccessConfig K User) (allocation : AllocationConfig K User)
    (compiler : CompilerHooks K User C) (queries : RetagQueries K User)
    (copy : PlaceCopyHooks Provenance (State K User) C)
    (evaluatePlace : C → MIR.Place → Bool → M K User (RuntimePlace Provenance)) :
    RvalueHooks Provenance (State K User) C (RuntimePlace Provenance) :=
  let place := placeHooks access allocation compiler
  let retag := retagHooks access queries
  { base with
    placeLayout := RuntimePlace.layout
    evalPlace := evaluatePlace
    readImmediate := fun _ => readImmediate access
    writeImmediate := fun c value dest => writePlaceImmediate place c value dest
    writePointer := fun c pointer dest => do
      let value ← match Scalar.fromMaybePointer access.runtime.base pointer with
        | .ok value => pure value
        | .error error => throw (.invalidProgram s!"pointer immediate: {repr error}")
      writePlaceImmediate place c (.scalar value) dest
    forceAllocation := fun c dest => return (← forceAllocation place c dest).mplace
    toRef := fun _ memory =>
      match memory.toRef access.runtime.base with
      | .ok value => pure value
      | .error error => throw (.invalidProgram s!"place reference: {repr error}")
    withRetagMode := fun _ mode action => MachineHooks.withRetagMode mode action
    retagPtrValue := fun _ value ty => MachineHooks.retagPtrValue retag value ty
    enforceValidity := compiler.enforceValidity
    copyOp := fun c source dest => copyRuntimePlace place copy c source dest false
    copyOpAllowTransmute := fun c source dest => copyRuntimePlace place copy c source dest true }

end Miri.Interpreter.PlaceMachine

namespace Miri.Interpreter.PlaceMachine
open Miri.ABI Miri.Memory Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
variable {K User : Type}
/-- Internal stage composition for the fresh allocation's first whole write.
The caller discharges diagnostic/weak/sync edges from the current raw machine. -/
theorem memoryAccess_fresh_write (config : AccessConfig K User)
    (machine : Machine K User) (id : AllocId) (tag : BorTag) (size : Size)
    (noClocks : machine.dataRace = none)
    (diagnostic : config.diagnostic true id (allocRange Size.ZERO size) machine = .ok () machine)
    (weak : config.weakMemoryWrite id (allocRange Size.ZERO size) machine = .ok () machine)
    (sync : config.syncAccess true id (allocRange Size.ZERO size) machine = .ok () machine) :
    memoryAccess config true ⟨machine,none⟩ (BorrowTree.new tag size) id (.concrete tag)
      (allocRange Size.ZERO size) = ⟨⟨machine,none⟩,BorrowTree.new tag size,.ok ()⟩ := by
  unfold memoryAccess bridge
  dsimp only [Id.run]
  rw [diagnostic]
  simp only [Id.run,bind,Bind.bind,pure,Pure.pure,MachineHooks.memoryRaceAccess,noClocks]
  rw [weak]
  cases tracked : machine.borrowTracker with
  | none => simp [tracked,sync,bind,Bind.bind,pure,Pure.pure]
  | some tracker =>
    have tree := BorrowTree.fresh_root_full_write tag size tracker.global.protectedTags
    simp only [tracked,allocRange,↓reduceIte]
    rw [tree.1,tree.2]
    simp only [allocRange] at sync
    simp [sync,bind,Bind.bind,pure,Pure.pure]
/-- An internal exact resolver equation lifted through the production bridge. -/
theorem resolvePointer_ok (config : AccessConfig K User) (memory : MemoryState Provenance BorrowTree K)
    (machine : Machine K User) (pointer : Pointer (Option Provenance)) (amount : Int)
    (result : Except UInt64 (ResolvedPointer ProvenanceExtra))
    (resolved : config.resolvePointer memory pointer amount machine = .ok result machine) :
    (accessHooks config).resolvePointer memory ⟨machine,none⟩ pointer amount = ⟨⟨machine,none⟩,.ok result⟩ := by
  simp [accessHooks,bridge,resolved]

/-- Commit a successful actual operand mutation through the production
memory writer; every stack/user field outside memory is retained exactly. -/
theorem writeMemory_of_result [DecidableEq K] (config : AccessConfig K User)
    (later : MemoryOperandLayout → Bool) (value : Immediate Provenance) (place : MPlaceTy Provenance)
    (state : State K User) (memory : MemoryState Provenance BorrowTree K)
    (touched : Option (AllocationAccessRef Provenance BorrowTree))
    (retain : config.retainTouched = fun machine _ => machine)
    (operand : writeImmediateToMplaceNoValidate state.machine.memory ⟨state.machine,none⟩ value
      ⟨place.mplace,localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
      config.globalHooks (accessHooks config) config.dynamicLayout later =
      ⟨memory,⟨state.machine,none⟩,touched,.ok ()⟩) :
    writeMemory config later value place state = .ok () {state with machine := {state.machine with memory}} := by
  unfold writeMemory
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind]
  rw [operand]
  simp [commit,finish,retain,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    pure,Pure.pure,EStateM.pure,bind,Bind.bind,EStateM.bind]

end Miri.Interpreter.PlaceMachine
