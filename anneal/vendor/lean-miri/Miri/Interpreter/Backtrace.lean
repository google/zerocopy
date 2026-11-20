import Miri.Interpreter.ForeignItems
import Miri.Interpreter.MachineHooks

/-! Full pinned shims/backtrace.rs driver. Encoded frame pointers preserve
actual function provenance and source BytePos offsets. Host/compiler symbol,
source-map and hygiene queries are explicit typed leaves; all writes are real
machine operations supplied by the connected memory binding. -/
namespace Miri.Interpreter.Backtrace
open Miri.ABI Miri.Memory Miri.MIR
open ForeignItems (EmulateItemResult)
abbrev M := EStateM StepError

structure Operations (P S D MD B I E Loc : Type) where
  target : TargetDataLayout
  arithmetic : PointerArithmetic
  hostUsizeMax : Nat
  stack : M S (Stack P LocalLayout E)
  readU64 : OpTy P → M S UInt64
  unitPointerLayout : M S LocalLayout
  misaligned : Pointer (Option P) → Align → M S (Option Misalignment)
  memoryOffset : MemPlace P → Size → OffsetMode → MemPlaceMeta P → M S (MemPlace P)
  memoryPlace : MPlaceTy P → MD
  layout : MD → LocalLayout
  projectField : MD → Nat → M S MD
  writeScalar : Scalar P → MD → M S Unit
  writeBytes : Pointer (Option P) → ByteArray → M S Unit
  /-- Actual fn_ptr(FnVal::Instance(...)), including canonical global identity
  reservation and machine root-address adjustment, never a DefId-as-address. -/
  functionPointer : CallInstance → M S (Pointer (Option P))
  /-- hygiene::walk_chain_collapsed(current_span, body.span).lo(). Actual body
  metadata is selected by bodyIdentity, not by equal instructions or names. -/
  collapsedSpanLo : BodyIdentity → SpanRef → M S UInt32
  allocation : Pointer (Option P) → M S (AllocId × Size)
  globalFunction : AllocId → M S (Option CallInstance)
  lookupCharPos : UInt32 → M S Loc
  line : Loc → Nat
  column : Loc → Nat
  renderInstance : CallInstance → M S String
  remappedFilename : Loc → M S String


structure CoreHooks (P S D MD B I E Loc : Type) extends Operations P S D MD B I E Loc where
  foreign : ForeignItems.Core P S D MD (Pointer (Option P)) B I

structure Hooks (P S D MD B I E Loc : Type) extends Operations P S D MD B I E Loc where
  foreign : ForeignItems.Hooks P S D MD (Pointer (Option P)) B I

def Hooks.core (h : Hooks P S D MD B I E Loc) : CoreHooks P S D MD B I E Loc :=
  {toOperations := h.toOperations,foreign := h.foreign.toCore}
instance : CoeOut (Hooks P S D MD B I E Loc) (CoreHooks P S D MD B I E Loc) := ⟨Hooks.core⟩

namespace Source
private def invalid (message : String) : M S A := throw (.invalidProgram message)
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some value => pure value | none => invalid "backtrace checked argument missing"
private def lift (result : Except StepError A) : M S A :=
  match result with | .ok value => pure value | .error error => throw error

/-- stack.rs Frame::current_span, including the unwinding-span path. -/
def currentSpan (frame : Frame P LocalLayout E) : Except StepError SpanRef := do
  match frame.location with
  | .unwinding span => pure span
  | .mir location =>
    let some block := frame.body.basicBlocks[location.block]?
      | throw (.invalidProgram "backtrace frame block missing")
    if location.statementIndex == block.statements.size then return block.terminator.sourceInfo.span
    let some statement := block.statements[location.statementIndex]?
      | throw (.invalidProgram "backtrace frame statement missing")
    return statement.sourceInfo.span

private def scalar (value : Nat) (size : Size) : M S (Scalar P) :=
  match Scalar.fromUInt (BitVec.ofNat 128 value) size with
  | .ok value => pure value
  | .error error => invalid s!"backtrace scalar conversion: {reprStr error}"

private def targetUsize (h : CoreHooks P S D MD B I E Loc) (value : Nat) : M S (Scalar P) := do
  if value >= 2^64 then invalid "backtrace host length exceeds u64"
  scalar value h.arithmetic.pointerSize

private def checkDeprecated (h : CoreHooks P S D MD B I E Loc) (name : String)
    (abi : FnAbi TyId) (args : Array (OpTy P)) : M S Unit := do
  h.foreign.checkSymbolClash name
  if abi.conv != .Rust then throw (.undefinedBehavior "backtrace shim calling convention mismatch")
  if abi.cVariadic then throw (.undefinedBehavior "nonvariadic backtrace shim called c-variadic")
  if args.size != 2 then throw (.undefinedBehavior "incorrect argument count for miri_resolve_frame")

/-- No symbol or stack query occurs on the invalid-flags path. -/
def size (h : CoreHooks P S D MD B I E Loc) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD) : M S Unit := do
  let args ← ForeignItems.Core.checkSignature h.foreign "miri_backtrace_size" ⟨.Rust,#[.u64],.usize⟩ abi args
  let flags ← h.readU64 (← arg args 0)
  if flags != 0 then throw (.unsupported s!"unknown miri_backtrace_size flags {flags}")
  let count := (← h.stack).frames.size
  h.writeScalar (← targetUsize h count) dest

/-- Gather all source spans first, then create every encoded function pointer,
then check flags and write the caller's array in order. Even obsolete flags
perform the source pointer-generation effects before returning Unsupported. -/
def get (h : CoreHooks P S D MD B I E Loc) (abi : FnAbi TyId)
    (args : Array (OpTy P)) : M S Unit := do
  let pointerLayout ← h.unitPointerLayout
  let args ← ForeignItems.Core.checkSignature h.foreign "miri_get_backtrace"
    ⟨.Rust,#[.u64,.unitPointer],.unit⟩ abi args
  let flags ← h.readU64 (← arg args 0)
  let pointer ← h.foreign.readPointer (← arg args 1)
  if !pointerLayout.layout.isSized then invalid "backtrace buffer element layout unsized"
  let alignment ← h.misaligned pointer pointerLayout.layout.align.abi
  let buffer : MPlaceTy P := ⟨⟨pointer,.none,alignment⟩,pointerLayout⟩
  let mut data := #[]
  for frame in (← h.stack).frames.toList.reverse do
    let span ← lift (currentSpan frame)
    let position ← h.collapsedSpanLo frame.bodyIdentity span
    data := data.push (frame.functionInstance,position)
  let mut pointers := #[]
  for (fnInstance,position) in data do
    let pointer ← h.functionPointer fnInstance
    let pointer ← match pointer.wrappingOffset (Size.ofBytes position.toUInt64) h.arithmetic with
      | .ok value => pure value
      | .error error => invalid s!"backtrace wrapping function offset: {reprStr error}"
    pointers := pointers.push pointer
  if flags == 0 then throw (.unsupported "miri_get_backtrace v0 is not supported any more")
  if flags != 1 then throw (.unsupported s!"unknown miri_get_backtrace flags {flags}")
  for index in [:pointers.size] do
    if index >= 2^64 then invalid "backtrace buffer index exceeds u64"
    let some offset := pointerLayout.layout.size.checkedMul (UInt64.ofNat index) h.target
      | invalid "backtrace buffer offset checked_mul unwrap"
    let place ← h.memoryOffset buffer.mplace offset .inbounds .none
    let pointer ← arg pointers index
    h.foreign.writePointer pointer (h.memoryPlace ⟨place,pointerLayout⟩)

/-- The byte offset encodes source position; therefore ordinary get_ptr_fn,
which rejects nonzero function offsets, is deliberately not used. -/
def resolvePointer (h : CoreHooks P S D MD B I E Loc) (operand : OpTy P) :
    M S (CallInstance × Loc × String × String) := do
  let pointer ← h.foreign.readPointer operand
  let (id,offset) ← h.allocation pointer
  let some fnInstance ← h.globalFunction id
    | throw (.undefinedBehavior "expected static function pointer in backtrace")
  if offset.bytes.toNat >= 2^32 then invalid "backtrace BytePos conversion unwrap"
  let location ← h.lookupCharPos (UInt32.ofNat offset.bytes.toNat)
  let name ← h.renderInstance fnInstance
  let filename ← h.remappedFilename location
  return (fnInstance,location,name,filename)

def resolveFrame (h : CoreHooks P S D MD B I E Loc) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD)
    (adtReprC : TyId → M S (Option Bool)) : M S Unit := do
  checkDeprecated h "miri_resolve_frame" abi args
  let flags ← h.readU64 (← arg args 1)
  let (fnInstance,location,name,filename) ← resolvePointer h (← arg args 0)
  let fnPointer ← h.functionPointer fnInstance
  let layout := h.layout dest
  let count := layout.layout.fields.count
  if count < 4 || count > 5 then
    throw (.undefinedBehavior "miri_resolve_frame must return a struct with 5 fields")
  let line := h.line location
  let column := h.column location
  if line > h.hostUsizeMax || column > h.hostUsizeMax then invalid "source-map host usize out of range"
  let line := if line < 2^32 then line else 0
  let column := Nat.min (column + 1) h.hostUsizeMax
  let column := if column < 2^32 then column else 0
  if let some reprC ← adtReprC layout.ty then
    if !reprC then throw (.undefinedBehavior "miri_resolve_frame return ADT must be repr(C)")
  if flags == 0 then throw (.unsupported "miri_resolve_frame v0 is not supported any more")
  if flags != 1 then throw (.unsupported s!"unknown miri_resolve_frame flags {flags}")
  let value ← targetUsize h name.toUTF8.size
  h.writeScalar value (← h.projectField dest 0)
  let value ← targetUsize h filename.toUTF8.size
  h.writeScalar value (← h.projectField dest 1)
  let value ← scalar line (Size.ofBytes 4)
  h.writeScalar value (← h.projectField dest 2)
  let value ← scalar column (Size.ofBytes 4)
  h.writeScalar value (← h.projectField dest 3)
  if count == 5 then h.foreign.writePointer fnPointer (← h.projectField dest 4)

def resolveNames (h : CoreHooks P S D MD B I E Loc) (abi : FnAbi TyId)
    (args : Array (OpTy P)) : M S Unit := do
  let args ← ForeignItems.Core.checkSignature h.foreign "miri_resolve_frame_names"
    ⟨.Rust,#[.unitPointer,.u64,.unitPointer,.unitPointer],.unit⟩ abi args
  let flags ← h.readU64 (← arg args 1)
  if flags != 0 then throw (.unsupported s!"unknown miri_resolve_frame_names flags {flags}")
  let (_,_,name,filename) ← resolvePointer h (← arg args 0)
  let pointer ← h.foreign.readPointer (← arg args 2)
  h.writeBytes pointer name.toUTF8
  let pointer ← h.foreign.readPointer (← arg args 3)
  h.writeBytes pointer filename.toUTF8

def emulate (h : CoreHooks P S D MD B I E Loc) (adtReprC : TyId → M S (Option Bool))
    (name : String) (abi : FnAbi TyId) (args : Array (OpTy P)) (dest : MD) :
    M S (Option EmulateItemResult) := do
  if name == "miri_backtrace_size" then size h abi args dest
  else if name == "miri_get_backtrace" then get h abi args
  else if name == "miri_resolve_frame" then resolveFrame h abi args dest adtReprC
  else if name == "miri_resolve_frame_names" then resolveNames h abi args
  else return none
  return some .NeedsReturn

end Source

def currentSpan (frame : Frame P LocalLayout E) : Except StepError SpanRef := Source.currentSpan frame

def size (h : Hooks P S D MD B I E Loc) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD) : M S Unit := Source.size h.core abi args dest

def get (h : Hooks P S D MD B I E Loc) (abi : FnAbi TyId)
    (args : Array (OpTy P)) : M S Unit := Source.get h.core abi args

def resolvePointer (h : Hooks P S D MD B I E Loc) (operand : OpTy P) :
    M S (CallInstance × Loc × String × String) := Source.resolvePointer h.core operand

def resolveFrame (h : Hooks P S D MD B I E Loc) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD)
    (adtReprC : TyId → M S (Option Bool)) : M S Unit := Source.resolveFrame h.core abi args dest adtReprC

def resolveNames (h : Hooks P S D MD B I E Loc) (abi : FnAbi TyId)
    (args : Array (OpTy P)) : M S Unit := Source.resolveNames h.core abi args

def emulate (h : Hooks P S D MD B I E Loc) (adtReprC : TyId → M S (Option Bool))
    (name : String) (abi : FnAbi TyId) (args : Array (OpTy P)) (dest : MD) :
    M S (Option EmulateItemResult) := Source.emulate h.core adtReprC name abi args dest

def bind (h : Hooks P S D MD B I E Loc) (adtReprC : TyId → M S (Option Bool)) :
    ForeignItems.Hooks P S D MD (Pointer (Option P)) B I :=
  { h.foreign with otherPortable := fun name abi args dest => do
      if let some result ← Source.emulate h.core adtReprC name abi args dest then return some result
      h.foreign.otherPortable name abi args dest }

end Miri.Interpreter.Backtrace
