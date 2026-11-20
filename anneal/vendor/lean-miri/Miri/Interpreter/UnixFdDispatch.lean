import Miri.Interpreter.UnixOpen
import Miri.Interpreter.ShimSignatures

/-! Selected connected unix/foreign_items.rs FD/open dispatch. Varargs remain
real imported operands and are consumed only by the flag-selected mode query. -/
namespace Miri.Interpreter.UnixFdDispatch
open Miri.ABI Miri.Memory Files
abbrev M := EStateM StepError
inductive Operation where | read | write | pread | pwrite | close | dup | dup2 | openPath | openat deriving DecidableEq, Repr
inductive ArgType where | i32 | pointer | usize | offT | isize deriving DecidableEq, Repr
structure Signature where
  args : Array ArgType
  ret : ArgType
  variadic : Bool := false

def parse : String → Option Operation
  | "read" => some .read | "write" => some .write | "pread" => some .pread | "pwrite" => some .pwrite
  | "close" => some .close | "dup" => some .dup | "dup2" => some .dup2
  | "open" => some .openPath | "openat" => some .openat | _ => none

def signature : Operation → Signature
  | .read | .write => ⟨#[.i32,.pointer,.usize],.isize,false⟩
  | .pread | .pwrite => ⟨#[.i32,.pointer,.usize,.offT],.isize,false⟩
  | .close | .dup => ⟨#[.i32],.i32,false⟩
  | .dup2 => ⟨#[.i32,.i32],.i32,false⟩
  | .openPath => ⟨#[.pointer,.i32],.i32,true⟩
  | .openat => ⟨#[.i32,.pointer,.i32],.i32,true⟩
structure Hooks (S H D O E Meta Path : Type) where
  file : UnixOpen.Hooks S H D O E Meta Path
  /-- Query the exact invoked symbol; aliases may have distinct compiler ABI rows. -/
  expectedAbi : String → Signature → M S (FnAbi Miri.MIR.TyId)
  argumentCompat : ArgAbi Miri.MIR.TyId → ArgAbi Miri.MIR.TyId → M S Bool
  checkSymbolClash : String → M S Unit
  transmute : OpTy Provenance → TyAndLayout Miri.MIR.TyId → M S (OpTy Provenance)
  readI32 : OpTy Provenance → M S Int32
  readUsize : OpTy Provenance → M S UInt64
  readOffset : OpTy Provenance → M S Int
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  readPath : Pointer (Option Provenance) → M S Path
  /-- Implements source check_varargs for mode_t (promoted to i32 if <4 bytes),
  including signed/unsigned C variadic value compatibility. No default mode. -/
  readMode : String → ShimSignatures.Varargs Provenance → UnixOpen.ModeUse → M S UInt32
  pollAndUnblockZero : M S Unit
private def checked (h : Hooks S H D O E Meta P) (op : Operation) (name : String)
    (caller : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance)) :
    M S (Array (OpTy Provenance) × ShimSignatures.Varargs Provenance) := do
  let request := signature op
  let callee ← h.expectedAbi name request
  if callee.conv != .C || callee.cVariadic != request.variadic || callee.args.size != request.args.size ||
      callee.fixedCount.toNat != request.args.size then throw (.invalidProgram "compiler Unix FD shim signature mismatch")
  if caller.conv != callee.conv then throw (.undefinedBehavior "Unix FD shim calling convention mismatch")
  if caller.cVariadic != callee.cVariadic then throw (.undefinedBehavior "Unix FD shim variadic signature mismatch")
  if caller.fixedCount != callee.fixedCount then throw (.undefinedBehavior "Unix FD shim argument count mismatch")
  if !(← h.argumentCompat caller.ret callee.ret) then throw (.undefinedBehavior "Unix FD shim return ABI mismatch")
  for (caller,callee) in caller.args.toList.zip callee.args.toList do
    if !(← h.argumentCompat caller callee) then throw (.undefinedBehavior "Unix FD shim argument ABI mismatch")
  h.checkSymbolClash name
  if args.size < request.args.size || (!request.variadic && args.size != request.args.size) then
    throw (.invalidProgram "Unix FD operands disagree with caller ABI")
  let fixed ← (args.extract 0 request.args.size).mapIdxM fun index operand => do
    let some expected := callee.args[index]? | throw (.invalidProgram "missing Unix FD ABI argument")
    h.transmute operand expected.layout
  return (fixed,⟨args.extract request.args.size args.size,request.args.size⟩)
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some value => pure value | none => throw (.invalidProgram "missing checked FD operand")

def dispatch (h : Hooks S H D O E Meta P) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult := do
  -- Unix foreign_items polls before *any* name dispatch with communication on.
  if h.file.fd.communicate then h.pollAndUnblockZero
  let some operation := parse name | return .NotSupported
  let (args,tail) ← checked h operation name abi args
  match operation with
  | .read | .write | .pread | .pwrite =>
    let number ← h.readI32 (← arg args 0)
    let pointer ← h.readPointer (← arg args 1)
    let count ← h.readUsize (← arg args 2)
    let offset ← if operation == .pread || operation == .pwrite then
        (h.readOffset (← arg args 3)).map some else pure none
    UnixFd.readWrite h.file.fd number pointer count offset (operation == .write || operation == .pwrite) dest
  | .close => h.file.fd.writeInt (← UnixFd.close h.file.fd (← h.readI32 (← arg args 0))).toInt dest
  | .dup => h.file.fd.writeInt (← UnixFd.dup h.file.fd (← h.readI32 (← arg args 0))).toInt dest
  | .dup2 =>
    let old ← h.readI32 (← arg args 0)
    let new ← h.readI32 (← arg args 1)
    h.file.fd.writeInt (← UnixFd.dup2 h.file.fd old new).toInt dest
  | .openPath | .openat =>
    let directory ← if operation == .openat then (h.readI32 (← arg args 0)).map some else pure none
    let pointer ← h.readPointer (← arg args (if operation == .openat then 1 else 0))
    let flags ← h.readI32 (← arg args (if operation == .openat then 2 else 1))
    let path ← h.readPath pointer
    let file := { h.file with readMode := h.readMode name tail }
    h.file.fd.writeInt (← UnixOpen.openPath file directory path flags.toUInt32).toInt dest
  return .NeedsReturn

/-- This must be the outer Unix entry wrapper: its poll is the source's one
entry poll. Remaining handlers supplied as base.unix must not poll again. -/
def bindUnix (h : Hooks S H D O E Meta P)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B I) :
    ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B I := {
  base with unix := fun name abi args dest => do
    if base.family != .unix || base.os != h.file.fd.os then throw (.invalidProgram "Unix FD dispatcher target mismatch")
    let result ← dispatch h name abi args dest
    if result != .NotSupported then return result
    base.unix name abi args dest }
end Miri.Interpreter.UnixFdDispatch
