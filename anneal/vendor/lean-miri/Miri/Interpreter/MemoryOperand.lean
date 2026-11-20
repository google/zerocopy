import Miri.Interpreter.Operand
import Miri.Memory.AllocationAccess
import Miri.ABI.RuntimeLayout

/-!
The typed-immediate branch of pinned `operand.rs` and `place.rs`. The
`MemoryOperandLayout` is only the TyAndLayout projection consumed here; ABI
backend representations and scalar sizing come directly from `rustc_abi`'s
runtime-layout port. Pointer resolution, global lookup, and Miri access hooks
are delegated to the required `AllocationAccess` and dynamic-layout hooks.
-/

namespace Miri.Interpreter

open Miri.ABI Miri.Memory

abbrev BackendPrimitive := Miri.ABI.Primitive

variable {Prov Extra MachineKind HookState ProvExtra : Type}

structure MemoryOperandLayout where
  size : Size
  align : Align
  backendRepr : BackendRepr
  /-- Canonical compiler type identity, retained for effectful unsized layout.
  Byte-level standalone views may omit it; typed machine views never do. -/
  canonicalType : Option Nat := none
  deriving DecidableEq, Repr

structure MemoryOperandPlace (Prov : Type) where
  mplace : MemPlace Prov
  layout : MemoryOperandLayout
  deriving DecidableEq, Repr

structure ImmediateValue (Prov : Type) where
  value : Immediate Prov
  layout : MemoryOperandLayout
  deriving DecidableEq, Repr

inductive ImmediateOrPlace (Prov : Type) where
  | place (value : MemoryOperandPlace Prov)
  | immediate (value : ImmediateValue Prov)
  deriving DecidableEq, Repr

inductive MemoryOperandError where
  | runtimeLayout (error : RuntimeLayoutError)
  | scalarLayout (error : ScalarLayoutError)
  | pointerAccess (error : PtrAllocationError)
  | dynamicLayoutFailure (message : String)
  | allocation (error : AllocError)
  | memoryRange (error : MemoryError)
  | sourceInvariant (message : String)
  | immediate (error : ImmediateError)
  | invalidPrimitiveRead
  | rawReadReturnedPlace
  | invalidUninitBytes
  | unsizedImmediateWrite
  | immediateAbiMismatch
  | immediateSizeMismatch (expected actual : Size)
  | immediateCarriesNonPointerProvenance
  | memoryUpdate (error : AllocationLookupError)
  deriving DecidableEq, Repr

structure MemoryOperandResult
    (Prov Extra MachineKind HookState α : Type) where
  memory : MemoryState Prov Extra MachineKind
  hooks : HookState
  /-- Updated allocation extras from access hooks, including on hook failure. -/
  touched : Option (AllocationAccessRef Prov Extra)
  outcome : Except MemoryOperandError α

structure DynamicLayoutResult
    (Prov Extra MachineKind HookState : Type) where
  memory : MemoryState Prov Extra MachineKind
  hooks : HookState
  outcome : Except String (Option (Size × Align))

abbrev DynamicLayoutResolver (Prov Extra MachineKind HookState : Type) :=
  MemoryState Prov Extra MachineKind → HookState → MemoryOperandPlace Prov →
    DynamicLayoutResult Prov Extra MachineKind HookState

private def pointerArithmeticFor (layout : RuntimeTargetDataLayout) :
    Except MemoryOperandError PointerArithmetic := do
  let pointerSize ← layout.pointerSizeIn layout.defaultAddressSpace
    |>.mapError MemoryOperandError.runtimeLayout
  return ⟨pointerSize⟩

private def selectedSizeAndAlign
    (memory : MemoryState Prov Extra MachineKind) (hooks : HookState)
    (place : MemoryOperandPlace Prov)
    (dynamicLayout : DynamicLayoutResolver Prov Extra MachineKind HookState) :
    MemoryState Prov Extra MachineKind × HookState × Except MemoryOperandError (Size × Align) := Id.run do
  if place.layout.backendRepr.isUnsized then
    let resolved := dynamicLayout memory hooks place
    match resolved.outcome with
    | .error message =>
        return (resolved.memory, resolved.hooks, .error (.dynamicLayoutFailure message))
    | .ok dynamic? =>
        return (resolved.memory, resolved.hooks,
          .ok (dynamic?.getD (place.layout.size, place.layout.align)))
  return (memory, hooks, .ok (place.layout.size, place.layout.align))

private def finishPlaceAccess
    (result : PtrAllocationResult Prov Extra MachineKind HookState
      (Option (AllocationAccessRef Prov Extra)))
    (misaligned : Option Misalignment) :
    MemoryOperandResult Prov Extra MachineKind HookState
      (Option (AllocationAccessRef Prov Extra)) :=
  match result.outcome with
  | .error error =>
      ⟨result.memory, result.hooks, result.touched, .error (.pointerAccess error)⟩
  | .ok reference? =>
      match misaligned with
      | some bad =>
          ⟨result.memory, result.hooks, result.touched,
            .error (.pointerAccess (.access (.alignmentCheckFailed bad)))⟩
      | none => ⟨result.memory, result.hooks, result.touched, .ok reference?⟩

/-! These two functions preserve the get_place_alloc and
get_place_alloc_mut order: dynamic layout first; pointer access and hooks next;
the cached misalignment check last, with pointer/mutability errors taking
precedence. -/

def getPlaceAlloc [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooks : HookState)
    (place : MemoryOperandPlace Prov) (runtime : RuntimeTargetDataLayout)
    (ghostMode : Bool) (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra)
    (dynamicLayout : DynamicLayoutResolver Prov Extra MachineKind HookState) :
    MemoryOperandResult Prov Extra MachineKind HookState
      (Option (AllocationAccessRef Prov Extra)) := Id.run do
  let (memory, hooks, sizeAndAlign) := selectedSizeAndAlign memory hooks place dynamicLayout
  let (size, _align) ← match sizeAndAlign with
    | .ok pair => pure pair
    | .error error => return ⟨memory, hooks, none, .error error⟩
  let target ← match pointerArithmeticFor runtime with
    | .ok target => pure target
    | .error error => return ⟨memory, hooks, none, .error error⟩
  let accessed := AllocationAccess.getPtrAlloc memory hooks target place.mplace.ptr size
      ghostMode globalKind globalHooks accessHooks
  return finishPlaceAccess accessed place.mplace.misaligned

def getPlaceAllocMut [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooks : HookState)
    (place : MemoryOperandPlace Prov) (runtime : RuntimeTargetDataLayout)
    (ghostMode : Bool) (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra)
    (dynamicLayout : DynamicLayoutResolver Prov Extra MachineKind HookState) :
    MemoryOperandResult Prov Extra MachineKind HookState
      (Option (AllocationAccessRef Prov Extra)) := Id.run do
  let (memory, hooks, sizeAndAlign) := selectedSizeAndAlign memory hooks place dynamicLayout
  let (size, _align) ← match sizeAndAlign with
    | .ok pair => pure pair
    | .error error => return ⟨memory, hooks, none, .error error⟩
  let target ← match pointerArithmeticFor runtime with
    | .ok target => pure target
    | .error error => return ⟨memory, hooks, none, .error error⟩
  let accessed := AllocationAccess.getPtrAllocMut memory hooks target place.mplace.ptr size
      ghostMode globalKind globalHooks accessHooks
  return finishPlaceAccess accessed place.mplace.misaligned

private inductive ImmediateReadPlan where
  | scalar (size : Size) (readProvenance : Bool)
  | pair (aSize bSize bOffset : Size) (aReadProvenance bReadProvenance : Bool)

private def scalarReadProvenance (scalar : BackendPrimitive) : Bool :=
  match scalar with
  | .Pointer _ => true
  | .Int _ _ | .Float _ => false

private def readPlan (layout : MemoryOperandLayout)
    (runtime : RuntimeTargetDataLayout) : Except MemoryOperandError (Option ImmediateReadPlan) := do
  if layout.backendRepr.isUnsized then return none
  match layout.backendRepr with
  | .Scalar (.Initialized (value := scalar) ..) => do
      let size ← (Miri.ABI.Primitive.size scalar runtime).mapError MemoryOperandError.runtimeLayout
      if size != layout.size then
        throw (.sourceInvariant "abi::Scalar size does not match layout size")
      return some (.scalar size (scalarReadProvenance scalar))
  | .ScalarPair (a := .Initialized (value := a) ..)
      (b := .Initialized (value := b) ..) (bOffset := bOffset) => do
      if bOffset.bytes == 0 then
        throw (.sourceInvariant "ScalarPair has a zero second-field offset")
      let aSize ← (Miri.ABI.Primitive.size a runtime).mapError MemoryOperandError.runtimeLayout
      let bSize ← (Miri.ABI.Primitive.size b runtime).mapError MemoryOperandError.runtimeLayout
      return some (.pair aSize bSize bOffset
        (scalarReadProvenance a) (scalarReadProvenance b))
  | _ => return none

private def componentRange (reference : AllocationAccessRef Prov Extra)
    (offset size : Size) : Except MemoryOperandError AllocRange := do
  let localRange := allocRange offset size
  (reference.range.subrange localRange).mapError MemoryOperandError.memoryRange

private def readScalarAt [DecidableEq Prov] [PointerProvenance Prov]
    (reference : AllocationAccessRef Prov Extra) (runtime : RuntimeTargetDataLayout)
    (offset size : Size) (readProvenance : Bool) : Except MemoryOperandError (Scalar Prov) := do
  let range ← componentRange reference offset size
  (reference.allocation.readScalar runtime.base range readProvenance)
    |>.mapError MemoryOperandError.allocation

private def scalarMatchesPrimitive [PointerProvenance Prov]
    (value : Scalar Prov) (primitive : BackendPrimitive)
    (runtime : RuntimeTargetDataLayout) : Except MemoryOperandError Unit := do
  let expected ← (Miri.ABI.Primitive.size primitive runtime)
    |>.mapError MemoryOperandError.runtimeLayout
  if value.size != expected then
    throw (.immediateSizeMismatch expected value.size)
  match primitive with
  | .Pointer _ => pure ()
  | .Int .. | .Float _ =>
      if value.isPointer then throw .immediateCarriesNonPointerProvenance

/-- The source `Immediate::assert_matches_abi` check, with its assertion and
bug outcomes retained as explicit errors. This runs before mutable place
access in `write_immediate_to_mplace_no_validate`. -/
private def immediateMatchesAbi [PointerProvenance Prov]
    (value : Immediate Prov) (layout : MemoryOperandLayout)
    (runtime : RuntimeTargetDataLayout) : Except MemoryOperandError Unit := do
  match value, layout.backendRepr with
  | .scalar scalar, .Scalar abiScalar =>
      scalarMatchesPrimitive scalar abiScalar.primitive runtime
  | .scalarPair a b, .ScalarPair (a := abiA) (b := abiB) .. => do
      scalarMatchesPrimitive a abiA.primitive runtime
      scalarMatchesPrimitive b abiB.primitive runtime
  | .uninit, repr =>
      if repr.isUnsized then throw .unsizedImmediateWrite
  | _, _ => throw .immediateAbiMismatch

private def writeRange (reference : AllocationAccessRef Prov Extra)
    (offset size : Size) : Except MemoryOperandError AllocRange := do
  let relative := allocRange offset size
  (reference.range.subrange relative).mapError MemoryOperandError.memoryRange

private def commitAllocationMutation [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooks : HookState)
    (reference : AllocationAccessRef Prov Extra)
    (mutation : EStateM.Result AllocError (Allocation Prov Extra) Unit) :
    MemoryOperandResult Prov Extra MachineKind HookState Unit := Id.run do
  let updatedAllocation := match mutation with
    | .ok _ allocation | .error _ allocation => allocation
  let updatedReference := { reference with allocation := updatedAllocation }
  let updatedMemory ← match memory.setLiveAllocation reference.allocId updatedAllocation with
    | .ok next => pure next
    | .error error =>
        return ⟨memory, hooks, some updatedReference, .error (.memoryUpdate error)⟩
  match mutation with
  | .ok () _ =>
      return ⟨updatedMemory, hooks, some updatedReference, .ok ()⟩
  | .error error _ =>
      return ⟨updatedMemory, hooks, some updatedReference,
        .error (.allocation error)⟩

private def writeScalarAt [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooks : HookState)
    (reference : AllocationAccessRef Prov Extra) (runtime : RuntimeTargetDataLayout)
    (offset : Size) (value : Scalar Prov) :
    MemoryOperandResult Prov Extra MachineKind HookState Unit := Id.run do
  let range ← match writeRange reference offset value.size with
    | .ok range => pure range
    | .error error => return ⟨memory, hooks, some reference, .error error⟩
  let mutation := Allocation.writeScalar runtime.base range value reference.allocation
  return commitAllocationMutation memory hooks reference mutation

private def writeUninitFull [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooks : HookState)
    (reference : AllocationAccessRef Prov Extra) (pointerSize : Size) :
    MemoryOperandResult Prov Extra MachineKind HookState Unit := Id.run do
  let mutation := Allocation.writeUninit reference.range pointerSize reference.allocation
  return commitAllocationMutation memory hooks reference mutation

/-! Source `read_immediate_from_mplace_raw`. In particular, an unsized layout
returns before touching memory; a zero-sized access with no allocation becomes
`Uninit`; all layouts that are not fully initialized scalar/scalar-pair ABIs
remain in memory. -/
def readImmediateFromMplaceRaw [DecidableEq MachineKind] [DecidableEq Prov]
    [PointerProvenance Prov]
    (memory : MemoryState Prov Extra MachineKind) (hooks : HookState)
    (place : MemoryOperandPlace Prov) (runtime : RuntimeTargetDataLayout)
    (ghostMode : Bool) (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra)
    (dynamicLayout : DynamicLayoutResolver Prov Extra MachineKind HookState) :
    MemoryOperandResult Prov Extra MachineKind HookState (Option (ImmediateValue Prov)) := Id.run do
  if place.layout.backendRepr.isUnsized then
    return ⟨memory, hooks, none, .ok none⟩
  let access := getPlaceAlloc memory hooks place runtime ghostMode globalKind
      globalHooks accessHooks dynamicLayout
  let reference? ← match access.outcome with
    | .error error =>
        return ⟨access.memory, access.hooks, access.touched, .error error⟩
    | .ok reference? => pure reference?
  let some reference := reference?
    | return ⟨access.memory, access.hooks, access.touched,
        .ok (some ⟨.uninit, place.layout⟩)⟩
  let plan ← match readPlan place.layout runtime with
    | .ok plan => pure plan
    | .error error =>
        return ⟨access.memory, access.hooks, access.touched, .error error⟩
  match plan with
  | none => return ⟨access.memory, access.hooks, access.touched, .ok none⟩
  | some (.scalar size readProvenance) =>
      match readScalarAt reference runtime Size.ZERO size readProvenance with
      | .ok scalar =>
          return ⟨access.memory, access.hooks, access.touched,
            .ok (some ⟨.scalar scalar, place.layout⟩)⟩
      | .error error =>
          return ⟨access.memory, access.hooks, access.touched, .error error⟩
  | some (.pair aSize bSize bOffset aReadProvenance bReadProvenance) =>
      match readScalarAt reference runtime Size.ZERO aSize aReadProvenance with
      | .error error =>
          return ⟨access.memory, access.hooks, access.touched, .error error⟩
      | .ok a =>
        match readScalarAt reference runtime bOffset bSize bReadProvenance with
        | .error error =>
            return ⟨access.memory, access.hooks, access.touched, .error error⟩
        | .ok b =>
            return ⟨access.memory, access.hooks, access.touched,
              .ok (some ⟨.scalarPair a b, place.layout⟩)⟩

/-! Raw operand reads retain the source's memory fallback. The caller supplies
the layout cached on the source `OpTy`; a local-to-place projection that must
materialize a local remains an explicit higher-level operation. -/
def readImmediateRaw [DecidableEq MachineKind] [DecidableEq Prov]
    [PointerProvenance Prov]
    (memory : MemoryState Prov Extra MachineKind) (hooks : HookState)
    (operand : Operand Prov) (layout : MemoryOperandLayout)
    (runtime : RuntimeTargetDataLayout) (ghostMode : Bool)
    (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra)
    (dynamicLayout : DynamicLayoutResolver Prov Extra MachineKind HookState) :
    MemoryOperandResult Prov Extra MachineKind HookState (ImmediateOrPlace Prov) := Id.run do
  match operand with
  | .immediate value =>
      return ⟨memory, hooks, none, .ok (.immediate ⟨value, layout⟩)⟩
  | .indirect mplace =>
      let typedPlace : MemoryOperandPlace Prov := ⟨mplace, layout⟩
      let read := readImmediateFromMplaceRaw memory hooks typedPlace runtime ghostMode
          globalKind globalHooks accessHooks dynamicLayout
      match read.outcome with
      | .error error =>
          return ⟨read.memory, read.hooks, read.touched, .error error⟩
      | .ok (some value) =>
          return ⟨read.memory, read.hooks, read.touched, .ok (.immediate value)⟩
      | .ok none =>
          return ⟨read.memory, read.hooks, read.touched, .ok (.place typedPlace)⟩

private def isPrimitiveReadable : BackendRepr → Bool
  | .Scalar (.Initialized ..) => true
  | .ScalarPair (a := .Initialized ..) (b := .Initialized ..) => true
  | _ => false

/-! Source `read_immediate`, with the source span-bug and UB branches made
explicit. Unavailable pointer/machine semantics are retained by the wrapped
allocation-access error and are never interpreted as a valid value. -/
def readImmediate [DecidableEq MachineKind] [DecidableEq Prov]
    [PointerProvenance Prov]
    (memory : MemoryState Prov Extra MachineKind) (hooks : HookState)
    (operand : Operand Prov) (layout : MemoryOperandLayout)
    (runtime : RuntimeTargetDataLayout) (ghostMode : Bool)
    (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra)
    (dynamicLayout : DynamicLayoutResolver Prov Extra MachineKind HookState) :
    MemoryOperandResult Prov Extra MachineKind HookState (ImmediateValue Prov) := Id.run do
  if !isPrimitiveReadable layout.backendRepr then
    return ⟨memory, hooks, none, .error .invalidPrimitiveRead⟩
  let read := readImmediateRaw memory hooks operand layout runtime ghostMode globalKind
      globalHooks accessHooks dynamicLayout
  match read.outcome with
  | .error error =>
      return ⟨read.memory, read.hooks, read.touched, .error error⟩
  | .ok (.place _) =>
      return ⟨read.memory, read.hooks, read.touched, .error .rawReadReturnedPlace⟩
  | .ok (.immediate value) =>
      match value.value with
      | .uninit =>
          return ⟨read.memory, read.hooks, read.touched, .error .invalidUninitBytes⟩
      | _ => return ⟨read.memory, read.hooks, read.touched, .ok value⟩

def readScalar [DecidableEq MachineKind] [DecidableEq Prov]
    [PointerProvenance Prov]
    (memory : MemoryState Prov Extra MachineKind) (hooks : HookState)
    (operand : Operand Prov) (layout : MemoryOperandLayout)
    (runtime : RuntimeTargetDataLayout) (ghostMode : Bool)
    (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra)
    (dynamicLayout : DynamicLayoutResolver Prov Extra MachineKind HookState) :
    MemoryOperandResult Prov Extra MachineKind HookState (Scalar Prov) := Id.run do
  let read := readImmediate memory hooks operand layout runtime ghostMode globalKind
      globalHooks accessHooks dynamicLayout
  match read.outcome with
  | .error error => return ⟨read.memory, read.hooks, read.touched, .error error⟩
  | .ok value =>
      match value.value.toScalar with
      | .ok scalar => return ⟨read.memory, read.hooks, read.touched, .ok scalar⟩
      | .error error =>
          return ⟨read.memory, read.hooks, read.touched,
            .error (.immediate error)⟩

/-! Source `write_immediate_to_mplace_no_validate`. The ABI assertion precedes
pointer access; the scalar-pair offset assertion follows mutable place access;
padding is cleared before either component write; and each allocation update
is committed before the next operation so later failures retain partial state.
Machine validity policy is an explicit input, matching `M::enforce_validity`. -/
def writeImmediateToMplaceNoValidate [DecidableEq MachineKind]
    [DecidableEq Prov] [PointerProvenance Prov]
    (memory : MemoryState Prov Extra MachineKind) (hooks : HookState)
    (value : Immediate Prov) (place : MemoryOperandPlace Prov)
    (runtime : RuntimeTargetDataLayout) (ghostMode : Bool)
    (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra)
    (dynamicLayout : DynamicLayoutResolver Prov Extra MachineKind HookState)
    (willLaterValidate : MemoryOperandLayout → Bool) :
    MemoryOperandResult Prov Extra MachineKind HookState Unit := Id.run do
  if place.layout.backendRepr.isUnsized then
    return ⟨memory, hooks, none, .error .unsizedImmediateWrite⟩
  match immediateMatchesAbi value place.layout runtime with
  | .error error => return ⟨memory, hooks, none, .error error⟩
  | .ok () => pure ()
  let access := getPlaceAllocMut memory hooks place runtime ghostMode globalKind
      globalHooks accessHooks dynamicLayout
  let reference? ← match access.outcome with
    | .error error =>
        return ⟨access.memory, access.hooks, access.touched, .error error⟩
    | .ok reference? => pure reference?
  let some reference := reference?
    | return ⟨access.memory, access.hooks, access.touched, .ok ()⟩
  match value with
  | .scalar scalar =>
      return writeScalarAt access.memory access.hooks reference runtime Size.ZERO scalar
  | .scalarPair a b =>
      let .ScalarPair (bOffset := bOffset) .. := place.layout.backendRepr
        | return ⟨access.memory, access.hooks, some reference,
            .error .immediateAbiMismatch⟩
      if bOffset.bytes == 0 then
        return ⟨access.memory, access.hooks, some reference,
          .error (.sourceInvariant "ScalarPair has a zero second-field offset")⟩
      let componentSize ← match Size.add a.size b.size with
        | .ok size => pure size
        | .error _ =>
            return ⟨access.memory, access.hooks, some reference,
              .error (.sourceInvariant "scalar-pair component-size addition overflow")⟩
      let mut currentMemory := access.memory
      let mut currentHooks := access.hooks
      let mut currentReference := reference
      if !willLaterValidate place.layout && componentSize != place.layout.size then
        let clear := writeUninitFull currentMemory currentHooks currentReference
          runtime.pointerSize
        currentMemory := clear.memory
        currentHooks := clear.hooks
        match clear.outcome with
        | .error error =>
            return ⟨currentMemory, currentHooks, clear.touched, .error error⟩
        | .ok () => pure ()
        match clear.touched with
        | some updated => currentReference := updated
        | none =>
            return ⟨currentMemory, currentHooks, none,
              .error (.sourceInvariant "successful allocation write lost its allocation reference")⟩
      let first := writeScalarAt currentMemory currentHooks currentReference runtime
          Size.ZERO a
      currentMemory := first.memory
      currentHooks := first.hooks
      match first.outcome with
      | .error error =>
          return ⟨currentMemory, currentHooks, first.touched, .error error⟩
      | .ok () => pure ()
      match first.touched with
      | some updated => currentReference := updated
      | none =>
          return ⟨currentMemory, currentHooks, none,
            .error (.sourceInvariant "successful first scalar write lost its allocation reference")⟩
      let second := writeScalarAt currentMemory currentHooks currentReference runtime
          bOffset b
      return second
  | .uninit =>
      return writeUninitFull access.memory access.hooks reference runtime.pointerSize

theorem unsized_raw_read_does_not_call_dynamic_access
    [DecidableEq MachineKind] [DecidableEq Prov] [PointerProvenance Prov]
    (memory : MemoryState Prov Extra MachineKind) (hooks : HookState)
    (place : MemoryOperandPlace Prov) (runtime : RuntimeTargetDataLayout)
    (ghostMode : Bool) (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra)
    (dynamicLayout : DynamicLayoutResolver Prov Extra MachineKind HookState)
    (h : place.layout.backendRepr.isUnsized = true) :
    (readImmediateFromMplaceRaw memory hooks place runtime ghostMode globalKind
      globalHooks accessHooks dynamicLayout).memory = memory := by
  simp [readImmediateFromMplaceRaw, h]

/-- Unit storage has no byte write, for any aligned pointer and arbitrary
memory/access hooks. Only the target pointer-size query is a metadata premise. -/
theorem zero_uninit_write {P E K H X : Type} [DecidableEq K]
    [DecidableEq P] [PointerProvenance P]
    (memory : MemoryState P E K) (hooks : H)
    (pointer : Pointer (Option P)) (runtime : RuntimeTargetDataLayout)
    (pointerSize : Size)
    (pointerMetadata : runtime.pointerSizeIn runtime.defaultAddressSpace = .ok pointerSize)
    (ghost : Bool) (kind : Option K)
    (globals : GlobalAllocationHooks P E K H)
    (access : AllocationAccessHooks P E K H X)
    (dynamic : DynamicLayoutResolver P E K H)
    (later : MemoryOperandLayout → Bool) (ty : Option Nat) :
    writeImmediateToMplaceNoValidate memory hooks .uninit
      ⟨⟨pointer, .none, none⟩, ⟨Size.ZERO, Align.ONE, .Memory (sized := true), ty⟩⟩
      runtime ghost kind globals access dynamic later =
      ⟨memory, hooks, none, .ok ()⟩ := by
  unfold writeImmediateToMplaceNoValidate getPlaceAllocMut
  simp only [BackendRepr.isUnsized]
  unfold immediateMatchesAbi selectedSizeAndAlign pointerArithmeticFor
  simp only [BackendRepr.isUnsized]
  rw [pointerMetadata]
  cases ghost <;> with_unfolding_all rfl


end Miri.Interpreter

namespace Miri.Interpreter
open Miri.ABI Miri.Memory
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
variable {P E K H X : Type} [DecidableEq K]
/-- Internal positive-access composition after raw source resolution. -/
theorem getPlaceAllocMut_sized_of_access
    (memory : MemoryState P E K) (hooks : H) (place : MemoryOperandPlace P)
    (runtime : RuntimeTargetDataLayout) (pointerSize : Size) (kind : Option K)
    (global : GlobalAllocationHooks P E K H) (access : AllocationAccessHooks P E K H X)
    (dynamic : DynamicLayoutResolver P E K H) (reference : AllocationAccessRef P E)
    (sized : place.layout.backendRepr.isUnsized = false) (aligned : place.mplace.misaligned = none)
    (pointer : runtime.pointerSizeIn runtime.defaultAddressSpace = .ok pointerSize)
    (actual : AllocationAccess.getPtrAllocMut memory hooks ⟨pointerSize⟩ place.mplace.ptr place.layout.size
      false kind global access = ⟨memory,hooks,some reference,.ok (some reference)⟩) :
    getPlaceAllocMut memory hooks place runtime false kind global access dynamic =
      ⟨memory,hooks,some reference,.ok (some reference)⟩ := by
  unfold getPlaceAllocMut selectedSizeAndAlign pointerArithmeticFor
  simp only [sized,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,Bind.bind,pure,Pure.pure]
  rw [pointer]
  simp only [Except.mapError,Except.bind,Except.pure,Bool.false_eq_true,↓reduceIte,bind,Bind.bind,pure,Pure.pure]
  rw [actual]
  simp [finishPlaceAccess,aligned]
end Miri.Interpreter

namespace Miri.Interpreter
open Miri.ABI Miri.Memory
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
variable {P E K H X : Type} [DecidableEq K] [DecidableEq P] [PointerProvenance P]
private theorem zero_subrange (size width : Size) (bound : width.bytes ≤ size.bytes) :
    (allocRange Size.ZERO size).subrange (allocRange Size.ZERO width) = .ok (allocRange Size.ZERO width) := by
  cases size; cases width
  simp [AllocRange.subrange,AllocRange.endExclusive,AllocRange.end,allocRange,Size.ZERO,Size.add,Size.ofBytes,
    bound,Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

/-- The actual scalar immediate writer, composed with its derived mutable
access and pure allocation mutation. These are internal operation edges. -/
theorem writeImmediate_scalar_of_access
    (memory afterMemory : MemoryState P E K) (hooks : H) (place : MemoryOperandPlace P)
    (runtime : RuntimeTargetDataLayout) (kind : Option K) (global : GlobalAllocationHooks P E K H)
    (access : AllocationAccessHooks P E K H X) (dynamic : DynamicLayoutResolver P E K H)
    (later : MemoryOperandLayout → Bool) (value : Memory.Scalar P) (abi : Miri.ABI.Scalar)
    (id : AllocId) (allocation after : Allocation P E)
    (backend : place.layout.backendRepr = .Scalar abi)
    (width : Primitive.size abi.primitive runtime = .ok value.size)
    (category : match abi.primitive with | .Pointer _ => True | _ => value.isPointer = false)
    (bound : value.size.bytes ≤ place.layout.size.bytes)
    (actual : getPlaceAllocMut memory hooks place runtime false kind global access dynamic =
      ⟨memory,hooks,some ⟨id,allocRange Size.ZERO place.layout.size,allocation⟩,
        .ok (some ⟨id,allocRange Size.ZERO place.layout.size,allocation⟩)⟩)
    (written : Allocation.writeScalar runtime.base (allocRange Size.ZERO value.size) value allocation = .ok () after)
    (committed : memory.setLiveAllocation id after = .ok afterMemory) :
    writeImmediateToMplaceNoValidate memory hooks (.scalar value) place runtime false kind global access dynamic later =
      ⟨afterMemory,hooks,some ⟨id,allocRange Size.ZERO place.layout.size,after⟩,.ok ()⟩ := by
  have abiOk : immediateMatchesAbi (.scalar value) place.layout runtime = .ok () := by
    unfold immediateMatchesAbi
    rw [backend]
    dsimp only
    unfold scalarMatchesPrimitive
    rw [width]
    cases primitive : abi.primitive <;>
      simp_all [bind,Bind.bind,Except.bind,Except.mapError,pure,Pure.pure,Except.pure]
  unfold writeImmediateToMplaceNoValidate
  simp only [backend,BackendRepr.isUnsized,Bool.false_eq_true,↓reduceIte]
  rw [abiOk]
  dsimp only [Id.run,bind,Bind.bind,pure,Pure.pure]
  rw [actual]
  dsimp only [bind,Bind.bind,pure,Pure.pure]
  unfold writeScalarAt writeRange
  dsimp only [Id.run,bind,Bind.bind,pure,Pure.pure]
  rw [zero_subrange _ _ bound]
  simp only [Except.mapError,Except.bind,bind,Bind.bind,pure,Pure.pure]
  rw [written]
  simp [commitAllocationMutation,committed,Id.run,bind,Bind.bind,pure,Pure.pure]
end Miri.Interpreter

namespace Miri.Interpreter
open Miri.ABI Miri.Memory
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
variable {P E K H X : Type} [DecidableEq K] [DecidableEq P] [PointerProvenance P]
private theorem add_size_ok (left right : Size)
    (fits : left.bytes.toNat + right.bytes.toNat < 2^64) :
    Size.add left right = .ok (Size.ofBytes (left.bytes + right.bytes)) := by
  have noWrap : ¬ left.bytes + right.bytes < left.bytes := by
    simp only [UInt64.lt_iff_toNat_lt,UInt64.toNat_add,Nat.mod_eq_of_lt fits]
    omega
  simp [Size.add,noWrap]

private theorem offset_subrange (size offset width : Size)
    (bound : offset.bytes.toNat + width.bytes.toNat ≤ size.bytes.toNat) :
    (allocRange Size.ZERO size).subrange (allocRange offset width) = .ok (allocRange offset width) := by
  have fits : offset.bytes.toNat + width.bytes.toNat < 2^64 := by have := size.bytes.toNat_lt; omega
  have endpoint : (allocRange offset width).endExclusive = .ok (Size.ofBytes (offset.bytes+width.bytes)) := by
    unfold AllocRange.endExclusive AllocRange.end allocRange
    rw [add_size_ok offset width fits]
    rfl
  have outer : (allocRange Size.ZERO size).endExclusive = .ok size := by
    cases size
    simp [allocRange,AllocRange.endExclusive,AllocRange.end,Size.add,Size.ZERO,Size.ofBytes,Except.mapError]
  have contained : offset.bytes+width.bytes ≤ size.bytes := by
    simp only [UInt64.le_iff_toNat_le,UInt64.toNat_add,Nat.mod_eq_of_lt fits]
    exact bound
  have start : Size.add Size.ZERO offset = .ok offset := by
    cases offset
    simp [Size.add,Size.ZERO,Size.ofBytes]
  unfold AllocRange.subrange
  simp only [allocRange] at endpoint outer ⊢
  rw [start]
  simp only [Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  rw [endpoint,outer]
  simp [contained,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  exact contained

private theorem primitive_matches (runtime : RuntimeTargetDataLayout) (primitive : BackendPrimitive)
    (value : Memory.Scalar P)
    (category : match primitive with | .Pointer _ => True | _ => value.isPointer = false)
    (width : Primitive.size primitive runtime = .ok value.size) :
    scalarMatchesPrimitive value primitive runtime = .ok () := by
  unfold scalarMatchesPrimitive
  rw [width]
  cases primitive <;> simp_all [Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
private theorem scalar_at_of_write (memory afterMemory : MemoryState P E K) (hooks : H)
    (reference : AllocationAccessRef P E) (runtime : RuntimeTargetDataLayout) (offset : Size) (value : Memory.Scalar P)
    (range : AllocRange) (after : Allocation P E)
    (selected : reference.range.subrange (allocRange offset value.size) = .ok range)
    (written : Allocation.writeScalar runtime.base range value reference.allocation = .ok () after)
    (committed : memory.setLiveAllocation reference.allocId after = .ok afterMemory) :
    writeScalarAt memory hooks reference runtime offset value =
      ⟨afterMemory,hooks,some {reference with allocation := after},.ok ()⟩ := by
  unfold writeScalarAt writeRange
  dsimp only [Id.run,bind,Bind.bind,pure,Pure.pure]
  rw [selected]
  simp only [Except.mapError,Id.run,bind,Bind.bind,pure,Pure.pure]
  rw [written]
  simp [commitAllocationMutation,committed,Id.run,bind,Bind.bind,pure,Pure.pure]

/-- ScalarPair's real source branch under the caller's current shallow
validation policy; the two writes and intermediate cache update are retained. -/
theorem writeImmediate_pair_of_access
    (memory middleMemory afterMemory : MemoryState P E K) (hooks : H) (place : MemoryOperandPlace P)
    (runtime : RuntimeTargetDataLayout) (kind : Option K) (global : GlobalAllocationHooks P E K H)
    (access : AllocationAccessHooks P E K H X) (dynamic : DynamicLayoutResolver P E K H)
    (first second : Memory.Scalar P) (abiA abiB : Miri.ABI.Scalar) (offset : Size)
    (id : AllocId) (allocation middle after : Allocation P E)
    (backend : place.layout.backendRepr = .ScalarPair (a := abiA) (b := abiB) (bOffset := offset))
    (widthA : Primitive.size abiA.primitive runtime = .ok first.size)
    (widthB : Primitive.size abiB.primitive runtime = .ok second.size)
    (categoryA : match abiA.primitive with | .Pointer _ => True | _ => first.isPointer = false)
    (categoryB : match abiB.primitive with | .Pointer _ => True | _ => second.isPointer = false)
    (offsetPositive : offset.bytes ≠ 0) (firstEnd : first.size.bytes ≤ offset.bytes)
    (bound : offset.bytes.toNat + second.size.bytes.toNat ≤ place.layout.size.bytes.toNat)
    (actual : getPlaceAllocMut memory hooks place runtime false kind global access dynamic =
      ⟨memory,hooks,some ⟨id,allocRange Size.ZERO place.layout.size,allocation⟩,
        .ok (some ⟨id,allocRange Size.ZERO place.layout.size,allocation⟩)⟩)
    (writtenA : Allocation.writeScalar runtime.base (allocRange Size.ZERO first.size) first allocation = .ok () middle)
    (cacheA : memory.setLiveAllocation id middle = .ok middleMemory)
    (writtenB : Allocation.writeScalar runtime.base (allocRange offset second.size) second middle = .ok () after)
    (cacheB : middleMemory.setLiveAllocation id after = .ok afterMemory) :
    writeImmediateToMplaceNoValidate memory hooks (.scalarPair first second) place runtime false kind global access dynamic
      (fun _ => true) =
      ⟨afterMemory,hooks,some ⟨id,allocRange Size.ZERO place.layout.size,after⟩,.ok ()⟩ := by
  have firstNat : first.size.bytes.toNat ≤ offset.bytes.toNat := UInt64.le_iff_toNat_le.mp firstEnd
  have sumFits : first.size.bytes.toNat + second.size.bytes.toNat < 2^64 := by
    have limit := place.layout.size.bytes.toNat_lt
    omega
  have firstBound : first.size.bytes ≤ place.layout.size.bytes := by
    apply UInt64.le_iff_toNat_le.mpr
    omega
  have abiOk : immediateMatchesAbi (.scalarPair first second) place.layout runtime = .ok () := by
    unfold immediateMatchesAbi
    rw [backend]
    dsimp only
    have firstOk := primitive_matches runtime abiA.primitive first categoryA widthA
    have secondOk := primitive_matches runtime abiB.primitive second categoryB widthB
    rw [firstOk]
    dsimp only [bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
    rw [secondOk]
  have aWrite := scalar_at_of_write memory middleMemory hooks
    (⟨id,allocRange Size.ZERO place.layout.size,allocation⟩ : AllocationAccessRef P E) runtime Size.ZERO first
    (allocRange Size.ZERO first.size) middle (zero_subrange _ _ firstBound) writtenA cacheA
  have bWrite := scalar_at_of_write middleMemory afterMemory hooks
    (⟨id,allocRange Size.ZERO place.layout.size,middle⟩ : AllocationAccessRef P E) runtime offset second
    (allocRange offset second.size) after (offset_subrange _ _ _ bound) writtenB cacheB
  unfold writeImmediateToMplaceNoValidate
  simp only [backend,BackendRepr.isUnsized,Bool.false_eq_true,↓reduceIte]
  rw [abiOk]
  dsimp only [Id.run,bind,Bind.bind,pure,Pure.pure]
  rw [actual]
  dsimp only [bind,Bind.bind,pure,Pure.pure]
  simp only [backend,offsetPositive,bne_iff_ne,beq_iff_eq,↓reduceIte]
  rw [add_size_ok first.size second.size sumFits]
  dsimp only [bind,Bind.bind,pure,Pure.pure]
  simp only [Bool.not_true,Bool.false_and,Bool.false_eq_true,↓reduceIte]
  rw [aWrite]
  dsimp only [bind,Bind.bind,pure,Pure.pure]
  rw [bWrite]
end Miri.Interpreter
