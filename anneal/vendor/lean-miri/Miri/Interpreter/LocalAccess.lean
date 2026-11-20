import Miri.Interpreter.Stack
import Miri.Interpreter.Projection

/-! Source-shaped operand evaluation. Compiler normalization, projection, and
machine policy are mandatory contracts, never default successful operations. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory

abbrev TypedOperand := OpTy

/-- One-way projection for byte/ABI memory operations; canonical operands retain
full compiler type identity and layout. -/
def localMemoryLayout (layout : LocalLayout) : MemoryOperandLayout :=
  ⟨layout.layout.size, layout.layout.align.abi, layout.layout.backendRepr,some layout.ty⟩

inductive LocalAccessError where
  | stack (error : StackError)
  | memory (error : MemoryOperandError)
  | projection (error : ProjectionError)
  | unsizedImmediate
  | resolver (message : String)
  deriving DecidableEq, Repr

structure LocalAccessResult (Prov Extra State α : Type) where
  frame : Frame Prov LocalLayout Extra
  state : State
  outcome : Except LocalAccessError α

/-- `layout` implements `from_known_layout`, normalization and layout lookup.
`project` implements rustc Projectable including provenance and metadata.
`checkPlaceType` performs the debug-mode normalized MIR type sanity check when
that mode is enabled, and must explicitly implement the disabled-mode policy.
Constant evaluation includes instantiation, normalization and failure handling. -/
structure LocalAccessHooks (Prov Extra State : Type) where
  layout : Frame Prov LocalLayout Extra → State → MIR.LocalId →
    Option LocalLayout → LocalAccessResult Prov Extra State LocalLayout
  validationInProgress : State → Bool
  afterLocalRead : Frame Prov LocalLayout Extra → State → MIR.LocalId →
    LocalAccessResult Prov Extra State Unit
  project : Frame Prov LocalLayout Extra → State → TypedOperand Prov →
    MIR.ProjectionElem → LocalAccessResult Prov Extra State (TypedOperand Prov)
  checkPlaceType : Frame Prov LocalLayout Extra → State → MIR.Place →
    TypedOperand Prov → LocalAccessResult Prov Extra State Unit
  runtimeChecks : Frame Prov LocalLayout Extra → State → MIR.RuntimeChecks →
    LocalAccessResult Prov Extra State (TypedOperand Prov)
  constant : Frame Prov LocalLayout Extra → State → MIR.ConstOperand →
    Option LocalLayout → LocalAccessResult Prov Extra State (TypedOperand Prov)

/-- Use the executable canonical projector rather than a second projection IR. -/
def localProjectionHook [PointerProvenance Prov] (cx : ProjectionCx Prov)
    (frame : Frame Prov LocalLayout Extra) (state : State) (op : TypedOperand Prov)
    (elem : MIR.ProjectionElem) : LocalAccessResult Prov Extra State (TypedOperand Prov) :=
  ⟨frame, state, (project cx op elem).mapError fun e => .projection e⟩

/-- Pinned operand.rs local_to_op: layout cache precedes dead-localId checking;
only immediate reads outside validation invoke the machine read hook. -/
def localToOp (hooks : LocalAccessHooks Prov Extra State)
    (frame : Frame Prov LocalLayout Extra) (state : State)
    (localId : MIR.LocalId) (known : Option LocalLayout) :
    LocalAccessResult Prov Extra State (TypedOperand Prov) := Id.run do
  let old ← match frame.getLocal localId with
    | .error e => return ⟨frame, state, .error (.stack e)⟩
    | .ok old => pure old
  let mut frame := frame
  let mut state := state
  let layout ← match old.layout with
    | some layout => pure layout
    | none => do
      let resolved := hooks.layout frame state localId known
      frame := resolved.frame
      state := resolved.state
      let layout ← match resolved.outcome with
        | .error e => return ⟨frame, state, .error e⟩
        | .ok layout => pure layout
      match frame.getOrCacheLocalLayout localId layout with
      | .error e => return ⟨frame, state, .error (.stack e)⟩
      | .ok (updated, cached) =>
        frame := updated
        pure cached
  let op ← match frame.getLocalOperand localId with
    | .error e => return ⟨frame, state, .error (.stack e)⟩
    | .ok op => pure op
  match op with
  | .immediate _ =>
    if layout.layout.backendRepr.isUnsized then
      return ⟨frame, state, .error .unsizedImmediate⟩
    if !hooks.validationInProgress state then
      let read := hooks.afterLocalRead frame state localId
      frame := read.frame
      state := read.state
      match read.outcome with
      | .error e => return ⟨frame, state, .error e⟩
      | .ok () => pure ()
  | .indirect _ => pure ()
  return ⟨frame, state, .ok ⟨op, layout⟩⟩

def evalPlaceToOp (hooks : LocalAccessHooks Prov Extra State)
    (frame : Frame Prov LocalLayout Extra) (state : State)
    (place : MIR.Place) (known : Option LocalLayout) :
    LocalAccessResult Prov Extra State (TypedOperand Prov) := Id.run do
  let base := localToOp hooks frame state place.localId
    (if place.projection.isEmpty then known else none)
  let mut frame := base.frame
  let mut state := base.state
  let mut op ← match base.outcome with
    | .error e => return ⟨frame, state, .error e⟩
    | .ok op => pure op
  for elem in place.projection do
    let projected := hooks.project frame state op elem
    frame := projected.frame
    state := projected.state
    match projected.outcome with
    | .error e => return ⟨frame, state, .error e⟩
    | .ok next => op := next
  let checked := hooks.checkPlaceType frame state place op
  return ⟨checked.frame, checked.state, checked.outcome.map fun _ => op⟩

/-- Copy and Move deliberately share the source branch. Pinned rustc's FIXME
leaves move invalidation unimplemented; this port does not invent it. -/
def evalOperand (hooks : LocalAccessHooks Prov Extra State)
    (frame : Frame Prov LocalLayout Extra) (state : State)
    (operand : MIR.Operand) (known : Option LocalLayout) :
    LocalAccessResult Prov Extra State (TypedOperand Prov) :=
  match operand with
  | .Copy place | .Move place => evalPlaceToOp hooks frame state place known
  | .RuntimeChecks check => hooks.runtimeChecks frame state check
  | .Constant constant => hooks.constant frame state constant known

/-- Connected immediate-read context. Allocation/global/access hooks are the
existing memory port's required inputs. -/
structure LocalReadContext (Prov MemExtra Kind HookState ProvExtra : Type) where
  runtime : RuntimeTargetDataLayout
  ghostMode : Bool
  globalKind : Option Kind
  globalHooks : GlobalAllocationHooks Prov MemExtra Kind HookState
  accessHooks : AllocationAccessHooks Prov MemExtra Kind HookState ProvExtra
  dynamicLayout : DynamicLayoutResolver Prov MemExtra Kind HookState

/-- The actual `MemoryOperand.readImmediate` path, retaining memory, hook state,
and touched allocation even if decoding or access fails. -/
def readTypedImmediate [DecidableEq Kind] [DecidableEq Prov]
    [PointerProvenance Prov]
    (context : LocalReadContext Prov MemExtra Kind HookState ProvExtra)
    (memory : MemoryState Prov MemExtra Kind) (state : HookState)
    (op : TypedOperand Prov) :
    MemoryOperandResult Prov MemExtra Kind HookState (ImmediateValue Prov) :=
  readImmediate memory state op.op (localMemoryLayout op.layout) context.runtime context.ghostMode
    context.globalKind context.globalHooks context.accessHooks context.dynamicLayout

structure LocalReadState (Prov MemExtra Kind HookState : Type) where
  memory : MemoryState Prov MemExtra Kind
  hooks : HookState
  touched : Option (AllocationAccessRef Prov MemExtra)

/-- Evaluate MIR syntax and read its immediate using the existing allocation
semantics. Local hooks operate on this same memory and machine state. -/
def evalOperandImmediate [DecidableEq Kind] [DecidableEq Prov]
    [PointerProvenance Prov]
    (context : LocalReadContext Prov MemExtra Kind HookState ProvExtra)
    (hooks : LocalAccessHooks Prov Extra (LocalReadState Prov MemExtra Kind HookState))
    (frame : Frame Prov LocalLayout Extra)
    (state : LocalReadState Prov MemExtra Kind HookState)
    (operand : MIR.Operand) (known : Option LocalLayout) :
    LocalAccessResult Prov Extra (LocalReadState Prov MemExtra Kind HookState)
      (ImmediateValue Prov) :=
  let evaluated := evalOperand hooks frame state operand known
  match evaluated.outcome with
  | .error e => ⟨evaluated.frame, evaluated.state, .error e⟩
  | .ok op =>
    let read := readTypedImmediate context evaluated.state.memory evaluated.state.hooks op
    ⟨evaluated.frame, ⟨read.memory, read.hooks, read.touched⟩,
      read.outcome.mapError LocalAccessError.memory⟩

def readLocalImmediate [DecidableEq Kind] [DecidableEq Prov]
    [PointerProvenance Prov]
    (context : LocalReadContext Prov MemExtra Kind HookState ProvExtra)
    (hooks : LocalAccessHooks Prov Extra (LocalReadState Prov MemExtra Kind HookState))
    (frame : Frame Prov LocalLayout Extra)
    (state : LocalReadState Prov MemExtra Kind HookState) (localId : MIR.LocalId) :
    LocalAccessResult Prov Extra (LocalReadState Prov MemExtra Kind HookState)
      (ImmediateValue Prov) :=
  let evaluated := localToOp hooks frame state localId none
  match evaluated.outcome with
  | .error e => ⟨evaluated.frame, evaluated.state, .error e⟩
  | .ok op =>
    let read := readTypedImmediate context evaluated.state.memory evaluated.state.hooks op
    ⟨evaluated.frame, ⟨read.memory, read.hooks, read.touched⟩,
      read.outcome.mapError LocalAccessError.memory⟩

/-- Required post-write machine and ABI-debug policy, with no silent policy. -/
structure LocalWriteHooks (Prov Extra State : Type) where
  validationInProgress : State → Bool
  afterLocalWrite : Frame Prov LocalLayout Extra → State → MIR.LocalId →
    LocalAccessResult Prov Extra State Unit
  checkImmediateAbi : Frame Prov LocalLayout Extra → State → Immediate Prov →
    LocalLayout → LocalAccessResult Prov Extra State Unit

/-- Immediate-only whole-local branch, reusable without inventing an allocation
context. Callers must have selected an immediate-backed destination. -/
def writeImmediateLocalBranch (hooks : LocalWriteHooks Prov Extra State)
    (frame : Frame Prov LocalLayout Extra) (state : State)
    (localId : MIR.LocalId) (layout : LocalLayout) (value : Immediate Prov) :
    LocalAccessResult Prov Extra State Unit := Id.run do
  if !layout.layout.isSized then return ⟨frame, state, .error .unsizedImmediate⟩
  match frame.getLocalOperand localId with
  | .error e => return ⟨frame, state, .error (.stack e)⟩
  | .ok (.indirect _) => return ⟨frame, state, .error (.resolver "immediate local branch received indirect local")⟩
  | .ok (.immediate _) => pure ()
  let mut frame ← match frame.setLocalOperand localId (.immediate value) with
    | .error e => return ⟨frame, state, .error (.stack e)⟩
    | .ok frame => pure frame
  let mut state := state
  if !hooks.validationInProgress state then
    let written := hooks.afterLocalWrite frame state localId
    frame := written.frame
    state := written.state
    match written.outcome with
    | .error e => return ⟨frame, state, .error e⟩
    | .ok () => pure ()
  return hooks.checkImmediateAbi frame state value layout

/-- Whole-local immediate write branch from place.rs. The replacement precedes
both the machine hook and debug ABI check, so failures retain the new value.
Indirect locals use the existing memory writer, preserving metadata. -/
def writeLocalImmediateNoValidate [DecidableEq Kind] [DecidableEq Prov]
    [PointerProvenance Prov]
    (context : LocalReadContext Prov MemExtra Kind HookState ProvExtra)
    (willLaterValidate : MemoryOperandLayout → Bool)
    (hooks : LocalWriteHooks Prov Extra (LocalReadState Prov MemExtra Kind HookState))
    (frame : Frame Prov LocalLayout Extra)
    (state : LocalReadState Prov MemExtra Kind HookState)
    (localId : MIR.LocalId) (layout : LocalLayout) (value : Immediate Prov) :
    LocalAccessResult Prov Extra (LocalReadState Prov MemExtra Kind HookState) Unit := Id.run do
  if layout.layout.backendRepr.isUnsized then return ⟨frame, state, .error .unsizedImmediate⟩
  let old ← match frame.getLocalOperand localId with
    | .error e => return ⟨frame, state, .error (.stack e)⟩
    | .ok op => pure op
  match old with
  | .indirect place =>
    let written := writeImmediateToMplaceNoValidate state.memory state.hooks value
      ⟨place, localMemoryLayout layout⟩ context.runtime context.ghostMode context.globalKind
      context.globalHooks context.accessHooks context.dynamicLayout willLaterValidate
    return ⟨frame, ⟨written.memory, written.hooks, written.touched⟩,
      written.outcome.mapError LocalAccessError.memory⟩
  | .immediate _ =>
    return writeImmediateLocalBranch hooks frame state localId layout value

/-- Concrete raw-reader adapter for the copy pipeline's fast-path probe. -/
def localCopyReadRaw [DecidableEq Kind] [DecidableEq Prov] [PointerProvenance Prov]
    (context : LocalReadContext Prov MemExtra Kind HookState ProvExtra)
    (frame : Frame Prov LocalLayout Extra)
    (state : LocalReadState Prov MemExtra Kind HookState) (source : TypedOperand Prov) :
    LocalAccessResult Prov Extra (LocalReadState Prov MemExtra Kind HookState)
      (ImmediateOrPlace Prov) :=
  let read := readImmediateRaw state.memory state.hooks source.op
    (localMemoryLayout source.layout) context.runtime context.ghostMode context.globalKind
    context.globalHooks context.accessHooks context.dynamicLayout
  ⟨frame, ⟨read.memory, read.hooks, read.touched⟩, read.outcome.mapError .memory⟩

/-- Required source-copy dependencies. `hasPadding` includes the wide-pointer
special case and scalar-size queries. `copyMemory` must perform nonoverlapping
mem_copy before source then destination alignment checks, retaining effects.
`validate` performs the source/destination typed passes, provenance/padding
reset and recursive-validity policy from copy_op_inner. -/
structure LocalCopyHooks (Prov Extra State Dest : Type) where
  destinationLayout : Dest → LocalLayout
  compatible : LocalLayout → LocalLayout → Except LocalAccessError Bool
  hasPadding : LocalLayout → Except LocalAccessError Bool
  readRaw : Frame Prov LocalLayout Extra → State → TypedOperand Prov →
    LocalAccessResult Prov Extra State (ImmediateOrPlace Prov)
  writeImmediate : Frame Prov LocalLayout Extra → State → Dest → Immediate Prov →
    LocalAccessResult Prov Extra State Unit
  forceDestination : Frame Prov LocalLayout Extra → State → Dest →
    LocalAccessResult Prov Extra State (MemoryOperandPlace Prov)
  writeTransmuted : Frame Prov LocalLayout Extra → State → MemoryOperandPlace Prov →
    LocalLayout → Immediate Prov → LocalAccessResult Prov Extra State Unit
  copyMemory : Frame Prov LocalLayout Extra → State → MemoryOperandPlace Prov →
    MemoryOperandPlace Prov → LocalAccessResult Prov Extra State Unit
  validate : Frame Prov LocalLayout Extra → State → LocalLayout → Dest →
    LocalAccessResult Prov Extra State Unit

/-- Pinned place.rs copy_op_no_validate decision pipeline. Every slow-path
operation has an explicit contract; no missing memory operation succeeds. -/
def copyOperandNoValidate (hooks : LocalCopyHooks Prov Extra State Dest)
    (frame : Frame Prov LocalLayout Extra) (state : State)
    (source : TypedOperand Prov) (dest : Dest) (allowTransmute : Bool) :
    LocalAccessResult Prov Extra State Unit := Id.run do
  let destLayout := hooks.destinationLayout dest
  let compatible ← match hooks.compatible source.layout destLayout with
    | .error e => return ⟨frame, state, .error e⟩
    | .ok value => pure value
  if !allowTransmute && !compatible then
    return ⟨frame, state, .error (.resolver "type mismatch when copying")⟩
  let padding ← match hooks.hasPadding source.layout with
    | .error e => return ⟨frame, state, .error e⟩
    | .ok value => pure value
  let loaded := if padding then
      ⟨frame, state, .ok (match source.op with
        | .immediate value => .immediate ⟨value, localMemoryLayout source.layout⟩
        | .indirect place => .place ⟨place, localMemoryLayout source.layout⟩)⟩
    else hooks.readRaw frame state source
  let frame := loaded.frame
  let state := loaded.state
  let value ← match loaded.outcome with
    | .error e => return ⟨frame, state, .error e⟩
    | .ok value => pure value
  match value with
  | .immediate value =>
    if !source.layout.layout.isSized || !destLayout.layout.isSized then
      return ⟨frame, state, .error .unsizedImmediate⟩
    if source.layout.layout.size != destLayout.layout.size then
      return ⟨frame, state, .error (.resolver "immediate copy size mismatch")⟩
    if compatible then return hooks.writeImmediate frame state dest value.value
    let forced := hooks.forceDestination frame state dest
    match forced.outcome with
    | .error e => return ⟨forced.frame, forced.state, .error e⟩
    | .ok place => return hooks.writeTransmuted forced.frame forced.state place source.layout value.value
  | .place sourcePlace =>
    let forced := hooks.forceDestination frame state dest
    match forced.outcome with
    | .error e => return ⟨forced.frame, forced.state, .error e⟩
    | .ok place => return hooks.copyMemory forced.frame forced.state sourcePlace place

def copyOperand (hooks : LocalCopyHooks Prov Extra State Dest)
    (frame : Frame Prov LocalLayout Extra) (state : State)
    (source : TypedOperand Prov) (dest : Dest) (allowTransmute : Bool) :
    LocalAccessResult Prov Extra State Unit :=
  let copied := copyOperandNoValidate hooks frame state source dest allowTransmute
  match copied.outcome with
  | .error e => ⟨copied.frame, copied.state, .error e⟩
  | .ok () => hooks.validate copied.frame copied.state source.layout dest

theorem copy_move_same (hooks : LocalAccessHooks Prov Extra State)
    (frame : Frame Prov LocalLayout Extra) (state : State)
    (place : MIR.Place) (known : Option LocalLayout) :
    evalOperand hooks frame state (.Copy place) known =
      evalOperand hooks frame state (.Move place) known := rfl

end Miri.Interpreter
