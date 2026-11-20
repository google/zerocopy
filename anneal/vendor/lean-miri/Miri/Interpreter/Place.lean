import Miri.Interpreter.MachineHooks

/-! Pinned place.rs local_to_place/eval_place/force_allocation and mutable-local
selection. Canonical layouts retain type identity across frame and memory forms.
Memory and machine leaves are mandatory stateful operations. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory

abbrev PlaceM (S A : Type) := EStateM StepError S A
structure PlaceHooks (P S C E : Type) where
  getFrame : PlaceM S (Frame P LocalLayout E)
  setFrame : Frame P LocalLayout E → PlaceM S Unit
  debugAssertions : Bool
  frameIndex : PlaceM S Nat
  resolveLayout : C → MIR.LocalId → PlaceM S LocalLayout
  /-- Must invoke canonical immediate-local read hooks outside validation. -/
  localToOp : C → MIR.LocalId → PlaceM S (OpTy P)
  projection : C → PlaceM S (ProjectionCx P)
  /-- Normal deref performs pointer validity; simple deref bypass uses readImmediate
  followed by imm_ptr_to_mplace, precisely the skip flag's source distinction. -/
  deref : C → RuntimePlace P → Bool → PlaceM S (RuntimePlace P)
  checkPlaceType : C → MIR.Place → RuntimePlace P → PlaceM S Unit
  allocateStack : C → LocalLayout → PlaceM S (MPlaceTy P)
  writeMemoryNoValidate : C → Immediate P → MPlaceTy P → PlaceM S Unit
  /-- Required machine hook: transfer vector clocks and declaration span to
  fresh allocation extras, preserving provenance/borrow state. -/
  afterLocalMovedToMemory : C → MIR.LocalId → MPlaceTy P → PlaceM S Unit
  memoryOffset : C → MemPlace P → Size → OffsetMode → MemPlaceMeta P → PlaceM S (MemPlace P)
  writeLocalImmediate : C → MIR.LocalId → LocalLayout → Immediate P → PlaceM S Unit
  enforceValidity : C → LocalLayout → PlaceM S Bool
  validate : C → RuntimePlace P → PlaceM S Unit

private def placeLift (value : Except StepError A) : PlaceM S A :=
  match value with | .ok value => pure value | .error error => throw error
/-- Successful physical/compiler results lift without state effects. -/
@[simp] theorem placeLift_ok (value : A) :
    placeLift (.ok value) = (pure value : PlaceM S A) := rfl

private def stackLift (value : Except StackError A) : PlaceM S A :=
  placeLift (value.mapError .stack)
/-- Successful stack results lift without changing interpreter state. -/
@[simp] theorem stackLift_ok (value : A) :
    stackLift (.ok value) = (pure value : PlaceM S A) := rfl

private def projectionLift (value : Except ProjectionError A) : PlaceM S A :=
  placeLift (value.mapError fun error => match error with
    | .machineError error => error
    | _ => .callback s!"place projection: {repr error}")

def placeLayoutOfLocal (h : PlaceHooks P S C E) (choice : C) (localId : MIR.LocalId) : PlaceM S LocalLayout := do
  let state ← stackLift ((← h.getFrame).getLocal localId)
  if let some layout := state.layout then return layout
  let layout ← h.resolveLayout choice localId
  let (frame, cached) ← stackLift ((← h.getFrame).getOrCacheLocalLayout localId layout)
  h.setFrame frame
  return cached

private def requireCurrent (h : PlaceHooks P S C E) (frame : Nat) : PlaceM S Unit := do
  if (← h.frameIndex) != frame then throw (.invalidProgram "place refers to another frame")

/-- Source debug_assert_eq!(locals_addr, frame.locals_addr()). The existing
frame-index structural check is separate. This failure is never Rust UB. -/
private def checkLocalIdentity (h : PlaceHooks P S C E) (identity : LocalsIdentity) : PlaceM S Unit := do
  if h.debugAssertions then
    if identity != (← h.getFrame).localsIdentity then
      throw (.invalidProgram "local place refers to a different locals buffer")

/-- Public source equation for the structural current-frame guard. -/
theorem requireCurrent_eq (h : PlaceHooks P S C E) (frame : Nat) :
    requireCurrent h frame = (do
      if (← h.frameIndex) != frame then throw (.invalidProgram "place refers to another frame")) := rfl

/-- Debug-disabled local identity assertions are query-free. -/
@[simp] theorem checkLocalIdentity_debugOff (h : PlaceHooks P S C E)
    (identity : LocalsIdentity) (off : h.debugAssertions = false) :
    checkLocalIdentity h identity = pure () := by
  simp [checkLocalIdentity, off]

def localToPlace (h : PlaceHooks P S C E) (choice : C) (localId : MIR.LocalId) : PlaceM S (RuntimePlace P) := do
  let layout ← placeLayoutOfLocal h choice localId
  if layout.layout.isSized then
    return ⟨.local (← h.frameIndex) localId none (← h.getFrame).localsIdentity, layout⟩
  match ← stackLift ((← h.getFrame).getLocalOperand localId) with
  | .indirect mplace => return ⟨.memory mplace, layout⟩
  | .immediate _ => throw (.invalidProgram "unsized local is immediate")

/-- Project local places without allocating or reading their values. Reuse the
canonical projector with a local-offset carrier; its memoryOffset is replaced
by source PlaceTy's checked Size addition, never a fabricated memory access. -/
def projectRuntimePlace [PointerProvenance P] (h : PlaceHooks P S C E) (choice : C)
    (place : RuntimePlace P) (elem : MIR.ProjectionElem) : PlaceM S (RuntimePlace P) := do
  if elem == .Deref then return ← h.deref choice place false
  let cx ← h.projection choice
  match place.ref with
  | .memory mplace =>
    let projected ← projectionLift (project cx ⟨.indirect mplace, place.layout⟩ elem)
    match projected.op with
    | .indirect mplace => return ⟨.memory mplace, projected.layout⟩
    | .immediate _ => throw (.invalidProgram "memory projection returned immediate")
  | .local frame localId offset identity =>
    requireCurrent h frame
    if !place.layout.layout.isSized then throw (.invalidProgram "unsized local place")
    let baseOffset := offset.getD Size.ZERO
    let cx := { cx with memoryOffset := fun carrier amount _ metadata => do
      if metadata.hasMeta then throw (.invariant "metadata on projected local")
      let newOffset ← carrier.ptr.offset.add amount |>.mapError .size
      return { carrier with ptr := { carrier.ptr with offset := newOffset }, metadata := .none } }
    let carrier : MemPlace P := ⟨⟨baseOffset, none⟩, .none, none⟩
    let projected ← projectionLift (project cx ⟨.indirect carrier, place.layout⟩ elem)
    let .indirect result := projected.op | throw (.invalidProgram "local projection returned immediate")
    if !projected.layout.layout.isSized || result.metadata.hasMeta then
      throw (.invalidProgram "unsized projected local")
    let bound ← placeLift ((result.ptr.offset.add projected.layout.layout.size).mapError fun error =>
      .callback s!"projected local size: {repr error}")
    let endOffset ← placeLift ((baseOffset.add place.layout.layout.size).mapError fun error =>
      .callback s!"local size: {repr error}")
    if result.ptr.offset.bytes < baseOffset.bytes || bound.bytes > endOffset.bytes then
      throw (.invalidProgram "projected local is out of bounds")
    return ⟨.local frame localId (some result.ptr.offset) identity, projected.layout⟩

def evalPlace [PointerProvenance P] (h : PlaceHooks P S C E) (choice : C)
    (mirPlace : MIR.Place) (skipValidityForSimpleDeref : Bool) : PlaceM S (RuntimePlace P) := do
  let mut place ← localToPlace h choice mirPlace.localId
  if skipValidityForSimpleDeref && mirPlace.projection == #[.Deref] then
    return ← h.deref choice place true
  for elem in mirPlace.projection do
    place ← projectRuntimePlace h choice place elem
  h.checkPlaceType choice mirPlace place
  return place

/-- Allocation and old-value write precede machine migration, and only then is
local storage replaced. Hook failures retain allocation/write effects, with the
old local still immediate. Replacement fetches the current frame, preserving
machine hook changes to race clocks and borrow metadata. -/
def forceAllocation (h : PlaceHooks P S C E) (choice : C) (place : RuntimePlace P) :
    PlaceM S (MPlaceTy P) := do
  let mplace ← match place.ref with
    | .memory mplace => pure mplace
    | .local frameIndex localId offset identity => do
      requireCurrent h frameIndex
      checkLocalIdentity h identity
      let old ← stackLift ((← h.getFrame).getLocalOperand localId)
      let whole ← match old with
        | .indirect mplace => pure mplace
        | .immediate value => do
          let layout ← placeLayoutOfLocal h choice localId
          if !layout.layout.isSized then throw (.invalidProgram "unsized immediate local allocation")
          let allocated ← h.allocateStack choice layout
          match value with
          | .uninit => pure ()
          | _ => h.writeMemoryNoValidate choice value allocated
          h.afterLocalMovedToMemory choice localId allocated
          let updated ← stackLift ((← h.getFrame).setLocalOperand localId (.indirect allocated.mplace))
          h.setFrame updated
          pure allocated.mplace
      match offset with
      | none => pure whole
      | some offset => h.memoryOffset choice whole offset .wrapping .none
  return ⟨mplace, place.layout⟩

inductive MutablePlace (P : Type) where
  | memory (place : MPlaceTy P)
  | immediateLocal (localId : MIR.LocalId) (layout : LocalLayout)

def asMplaceOrMutableLocal (h : PlaceHooks P S C E) (choice : C) (place : RuntimePlace P) :
    PlaceM S (MutablePlace P) := do
  match place.ref with
  | .memory mplace => return .memory ⟨mplace, place.layout⟩
  | .local frame localId offset identity =>
    if offset.isSome then return .memory (← forceAllocation h choice place)
    requireCurrent h frame
    checkLocalIdentity h identity
    if h.debugAssertions then
      let layout ← placeLayoutOfLocal h choice localId
      if layout != place.layout then throw (.invalidProgram "whole-local layout mismatch")
    let layout := place.layout
    match ← stackLift ((← h.getFrame).getLocalOperand localId) with
    | .indirect mplace => return .memory ⟨mplace, layout⟩
    | .immediate _ => return .immediateLocal localId layout

def writePlaceImmediateNoValidate (h : PlaceHooks P S C E) (choice : C)
    (value : Immediate P) (dest : RuntimePlace P) : PlaceM S Unit := do
  if !dest.layout.layout.isSized then throw (.invalidProgram "unsized immediate destination")
  match ← asMplaceOrMutableLocal h choice dest with
  | .memory place => h.writeMemoryNoValidate choice value place
  | .immediateLocal localId layout => h.writeLocalImmediate choice localId layout value

def writePlaceImmediate (h : PlaceHooks P S C E) (choice : C)
    (value : Immediate P) (dest : RuntimePlace P) : PlaceM S Unit := do
  writePlaceImmediateNoValidate h choice value dest
  if ← h.enforceValidity choice dest.layout then h.validate choice dest

/-- Read-only capability slice of place-to-operand conversion. Keeping this
slice explicit avoids recursive construction of a complete place dictionary. -/
def placeToOpCore [PointerProvenance P]
    (getFrame : PlaceM S (Frame P LocalLayout E)) (debugAssertions : Bool)
    (frameIndex : PlaceM S Nat) (localToOp : C → MIR.LocalId → PlaceM S (OpTy P))
    (projection : C → PlaceM S (ProjectionCx P)) (choice : C)
    (place : RuntimePlace P) : PlaceM S (OpTy P) := do
  match place.ref with
  | .memory mplace => return ⟨.indirect mplace, place.layout⟩
  | .local frame localId offset identity =>
    if (← frameIndex) != frame then throw (.invalidProgram "place refers to another frame")
    if debugAssertions then
      if !place.layout.layout.isSized then throw (.invalidProgram "unsized local place operand")
    if debugAssertions then
      if identity != (← getFrame).localsIdentity then
        throw (.invalidProgram "local place refers to a different locals buffer")
    let base ← localToOp choice localId
    match offset with
    | none =>
      if debugAssertions then
        if base.layout != place.layout then throw (.invalidProgram "local operand layout mismatch")
      return base
    | some offset => projectionLift (base.offset (← projection choice) offset place.layout)

def placeToOp [PointerProvenance P] (h : PlaceHooks P S C E) (choice : C)
    (place : RuntimePlace P) : PlaceM S (OpTy P) :=
  placeToOpCore h.getFrame h.debugAssertions h.frameIndex h.localToOp h.projection choice place

/-- Actual memory-place offset operation with target arithmetic and required
live-allocation/provenance resolution, preserving cached misalignment. -/
def placeMemoryOffset (target : PointerArithmetic) (resolve : PointerResolver P ProvExtra)
    (lookup : LiveAllocationLookup) (place : MemPlace P) (offset : Size)
    (mode : OffsetMode) (metadata : MemPlaceMeta P) : PlaceM S (MemPlace P) :=
  placeLift ((place.offsetWithMeta offset mode metadata target resolve lookup).mapError fun error =>
    .callback s!"place memory offset: {repr error}")

/-- Whole-state optimized-local writer. The current frame is replaced before
machine effects; subsequent hooks operate on that state directly, so canonical
race clocks and borrow metadata are never overwritten by an old frame copy. -/
def placeWriteLocalImmediate
    (getFrame : PlaceM S (Frame P LocalLayout E))
    (setFrame : Frame P LocalLayout E → PlaceM S Unit)
    (validationInProgress : PlaceM S Bool)
    (afterLocalWrite : MIR.LocalId → Bool → PlaceM S Unit)
    (debugAbiCheck : Immediate P → LocalLayout → PlaceM S Unit)
    (localId : MIR.LocalId) (layout : LocalLayout) (value : Immediate P) : PlaceM S Unit := do
  if !layout.layout.isSized then throw (.invalidProgram "unsized optimized local write")
  let frame ← getFrame
  match ← stackLift (frame.getLocalOperand localId) with
  | .indirect _ => throw (.invalidProgram "optimized local write received memory local")
  | .immediate _ => pure ()
  setFrame (← stackLift (frame.setLocalOperand localId (.immediate value)))
  unless ← validationInProgress do afterLocalWrite localId false
  debugAbiCheck value layout

/-- Concrete stack materialization allocator. Root adjustment and allocation
extras must install the canonical provenance, borrow tree and race clocks. -/
def placeAllocateStack [DecidableEq Kind]
    (maximumObjectSize : Size)
    (zeroedStorage : Size → Align → Option (Array UInt8))
    (synchronizeMemory : MemoryState P Extra Kind → HookState → HookState)
    (initExtra : MemoryState P Extra Kind → HookState → AllocId → MemoryKind Kind →
      Size → Align → MemoryStateHookResult P Extra Kind HookState Extra)
    (adjustRoot : MemoryState P Extra Kind → HookState → AllocId → MemoryKind Kind →
      MemoryStateHookResult P Extra Kind HookState (Pointer P))
    (getMemory : S → MemoryState P Extra Kind) (getHooks : S → HookState)
    (putMemoryHooks : S → MemoryState P Extra Kind → HookState → S)
    (layout : LocalLayout) : PlaceM S (MPlaceTy P) := do
  if !layout.layout.isSized then throw (.invalidProgram "stack materialization requires sized local")
  let state ← get
  let result := MemoryLifecycle.allocatePtr (getMemory state) (getHooks state) synchronizeMemory
    layout.layout.size layout.layout.align.abi .stack .Uninit maximumObjectSize none
    zeroedStorage initExtra adjustRoot
  set (putMemoryHooks state result.memory result.hooks)
  match result.outcome with
  | .error error => throw (.callback s!"place stack allocation: {repr error}")
  | .ok ptr => return ⟨⟨⟨ptr.offset, some ptr.provenance⟩, .none, none⟩, layout⟩

/-- Concrete bridge to the existing memory writer. Memory/hooks are committed
before propagating errors; callers select canonical machine allocation hooks. -/
def placeMemoryWrite [DecidableEq Kind] [DecidableEq P] [PointerProvenance P]
    (context : LocalReadContext P Extra Kind HookState ProvExtra)
    (willValidate : MemoryOperandLayout → Bool)
    (getMemory : S → MemoryState P Extra Kind) (getHooks : S → HookState)
    (putMemoryHooks : S → MemoryState P Extra Kind → HookState → S)
    (putTouched : S → Option (AllocationAccessRef P Extra) → S)
    (value : Immediate P) (place : MPlaceTy P) : PlaceM S Unit := do
  let state ← get
  let result := writeImmediateToMplaceNoValidate (getMemory state) (getHooks state)
    value ⟨place.mplace, localMemoryLayout place.layout⟩ context.runtime context.ghostMode
    context.globalKind context.globalHooks context.accessHooks context.dynamicLayout willValidate
  set (putTouched (putMemoryHooks state result.memory result.hooks) result.touched)
  match result.outcome with
  | .error error => throw (.callback s!"place memory write: {repr error}")
  | .ok () => pure ()

def placeReadRaw [DecidableEq Kind] [DecidableEq P] [PointerProvenance P]
    (context : LocalReadContext P Extra Kind HookState ProvExtra)
    (getMemory : S → MemoryState P Extra Kind) (getHooks : S → HookState)
    (putMemoryHooks : S → MemoryState P Extra Kind → HookState → S)
    (putTouched : S → Option (AllocationAccessRef P Extra) → S)
    (source : OpTy P) : PlaceM S (ImmediateOrPlace P) := do
  let state ← get
  let result := readImmediateRaw (getMemory state) (getHooks state) source.op
    (localMemoryLayout source.layout) context.runtime context.ghostMode context.globalKind
    context.globalHooks context.accessHooks context.dynamicLayout
  set (putTouched (putMemoryHooks state result.memory result.hooks) result.touched)
  match result.outcome with
  | .error error => throw (.callback s!"place memory read: {repr error}")
  | .ok value => pure value

/-- Source slow-copy path: destination dynamic size, debug source size (or
fixed-part approximation), nonoverlapping memory copy, then cached alignment
checks in source/destination order. Memory hooks and partial writes survive UB. -/
def placeMemoryCopy [DecidableEq Kind]
    (debugAssertions : Bool) (pointerSize : Size)
    (sizeAndAlign : MPlaceTy P → PlaceM S (Option (Size × Align)))
    (hooks : MemoryCopyHooks P Extra Kind HookState ProvExtra)
    (getMemory : S → MemoryState P Extra Kind) (getHooks : S → HookState)
    (putMemoryHooks : S → MemoryState P Extra Kind → HookState → S)
    (source dest : MPlaceTy P) : PlaceM S Unit := do
  let some (size, _) ← sizeAndAlign dest
    | throw (.invalidProgram "copy requires dynamically sized destination")
  if debugAssertions then
    let some (sourceSize, _) ← sizeAndAlign source
      | throw (.invalidProgram "copy requires dynamically sized source")
    if sourceSize != size then throw (.invalidProgram "copy dynamic size mismatch")
  else if source.layout.layout.size != dest.layout.layout.size then
    throw (.invalidProgram "copy fixed size mismatch")
  let state ← get
  let result := MemoryLifecycle.memCopyRepeatedly (getMemory state) (getHooks state)
    source.mplace.ptr dest.mplace.ptr size 1 true pointerSize hooks
  set (putMemoryHooks state result.memory result.hooks)
  match result.outcome with
  | .error error => throw (.callback s!"place memory copy: {repr error}")
  | .ok () => pure ()
  if let some error := source.mplace.misaligned then
    throw (.undefinedBehavior s!"copy source misalignment: {repr error}")
  if let some error := dest.mplace.misaligned then
    throw (.undefinedBehavior s!"copy destination misalignment: {repr error}")

structure PlaceCopyHooks (P S C : Type) where
  compatible : LocalLayout → LocalLayout → Except StepError Bool
  hasPadding : LocalLayout → Except StepError Bool
  readRaw : C → OpTy P → PlaceM S (ImmediateOrPlace P)
  /-- Resolve dynamic sizes; require sizes compatible; mem_copy nonoverlapping
  true; check source then destination misalignment only after memory copy. -/
  memoryCopy : C → MPlaceTy P → MPlaceTy P → PlaceM S Unit
  /-- Source-layout validation pass includes transmute, recursive policy and
  reset of provenance/padding. Destination validation is done by PlaceHooks. -/
  validateSource : C → LocalLayout → RuntimePlace P → PlaceM S Unit

/-- Connected copy_op_no_validate, with materialization through forceAllocation.
All type identity stays canonical; the memory read result supplies only bytes. -/
def copyRuntimePlaceNoValidate (h : PlaceHooks P S C E) (copy : PlaceCopyHooks P S C)
    (choice : C) (source : OpTy P) (dest : RuntimePlace P) (allowTransmute : Bool) : PlaceM S Unit := do
  let compatible ← placeLift (copy.compatible source.layout dest.layout)
  if !compatible && !allowTransmute then throw (.invalidProgram "copy type mismatch")
  let padding ← placeLift (copy.hasPadding source.layout)
  let value ← if padding then pure (match source.op with
      | .immediate value => ImmediateOrPlace.immediate ⟨value, localMemoryLayout source.layout⟩
      | .indirect mplace => .place ⟨mplace, localMemoryLayout source.layout⟩)
    else copy.readRaw choice source
  match value with
  | .immediate value =>
    if !source.layout.layout.isSized || !dest.layout.layout.isSized then
      throw (.invalidProgram "copy immediate is unsized")
    if source.layout.layout.size != dest.layout.layout.size then
      throw (.invalidProgram "copy immediate size mismatch")
    if compatible then writePlaceImmediateNoValidate h choice value.value dest
    else
      let memory ← forceAllocation h choice dest
      h.writeMemoryNoValidate choice value.value ⟨memory.mplace, source.layout⟩
  | .place memory =>
    let target ← forceAllocation h choice dest
    copy.memoryCopy choice ⟨memory.mplace, source.layout⟩ target

def copyRuntimePlace (h : PlaceHooks P S C E) (copy : PlaceCopyHooks P S C)
    (choice : C) (source : OpTy P) (dest : RuntimePlace P) (allowTransmute : Bool) : PlaceM S Unit := do
  copyRuntimePlaceNoValidate h copy choice source dest allowTransmute
  if ← h.enforceValidity choice dest.layout then
    if source.layout.ty != dest.layout.ty then copy.validateSource choice source.layout dest
    h.validate choice dest

end Miri.Interpreter
