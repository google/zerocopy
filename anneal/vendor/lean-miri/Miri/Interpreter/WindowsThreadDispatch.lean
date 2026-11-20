import Miri.Interpreter.WindowsThreadMachine
import Miri.Interpreter.ForeignItems

/-! Windows thread/TLS foreign arms, with compiler system ABI checking. -/
namespace Miri.Interpreter.WindowsThreadDispatch
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Operation where
  | create | wait | tlsAlloc | flsAlloc | tlsGet | tlsSet | tlsFree | flsFree
  | isFiber | setDescription | getDescription | getId | currentId
  deriving DecidableEq, Repr
inductive ArgType where | pointer | handle | usize | u32 | bool | i32 | flsCallback deriving DecidableEq, Repr
structure Signature where
  args : Array ArgType
  ret : ArgType

def parse : String → Option Operation
  | "CreateThread" => some .create | "WaitForSingleObject" => some .wait
  | "TlsAlloc" => some .tlsAlloc | "FlsAlloc" => some .flsAlloc
  | "TlsGetValue" | "FlsGetValue" => some .tlsGet
  | "TlsSetValue" | "FlsSetValue" => some .tlsSet
  | "TlsFree" => some .tlsFree | "FlsFree" => some .flsFree
  | "IsThreadAFiber" => some .isFiber
  | "SetThreadDescription" => some .setDescription | "GetThreadDescription" => some .getDescription
  | "GetThreadId" => some .getId | "GetCurrentThreadId" => some .currentId
  | _ => none

def signature : Operation → Signature
  | .create => ⟨#[.pointer,.usize,.pointer,.pointer,.u32,.pointer],.handle⟩
  | .wait => ⟨#[.handle,.u32],.u32⟩
  | .tlsAlloc | .currentId => ⟨#[],.u32⟩
  | .flsAlloc => ⟨#[.flsCallback],.u32⟩
  | .tlsGet => ⟨#[.u32],.pointer⟩
  | .tlsSet => ⟨#[.u32,.pointer],.bool⟩
  | .tlsFree | .flsFree => ⟨#[.u32],.bool⟩
  | .isFiber => ⟨#[],.bool⟩
  | .setDescription | .getDescription => ⟨#[.handle,.pointer],.i32⟩
  | .getId => ⟨#[.handle],.u32⟩
structure Hooks (S F : Type) where
  thread : WindowsThread.Hooks S F
  systemConvention : M S CanonAbi
  /-- The exact shim symbol is part of the compiler query identity. -/
  expectedAbi : String → Signature → M S (FnAbi Miri.MIR.TyId)
  argumentCompat : ArgAbi Miri.MIR.TyId → ArgAbi Miri.MIR.TyId → M S Bool
  checkSymbolClash : String → M S Unit
  transmute : OpTy Provenance → TyAndLayout Miri.MIR.TyId → M S (OpTy Provenance)
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
  writePointer : Pointer (Option Provenance) → MPlaceTy Provenance → M S Unit
  writeInt : Int → MPlaceTy Provenance → M S Unit
private def checked (h : Hooks S F) (operation : Operation) (name : String)
    (caller : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance)) : M S (Array (OpTy Provenance)) := do
  let signature := signature operation
  let callee ← h.expectedAbi name signature
  if callee.conv != (← h.systemConvention) || callee.cVariadic || callee.args.size != signature.args.size ||
      callee.fixedCount.toNat != signature.args.size then throw (.invalidProgram "compiler Windows thread signature mismatch")
  if caller.conv != callee.conv then throw (.undefinedBehavior "Windows thread calling convention mismatch")
  if caller.cVariadic != callee.cVariadic then throw (.undefinedBehavior "Windows thread variadic ABI mismatch")
  if caller.fixedCount != callee.fixedCount then throw (.undefinedBehavior "Windows thread argument count mismatch")
  if !(← h.argumentCompat caller.ret callee.ret) then throw (.undefinedBehavior "Windows thread return ABI mismatch")
  for (actual,expected) in caller.args.toList.zip callee.args.toList do
    if !(← h.argumentCompat actual expected) then throw (.undefinedBehavior "Windows thread argument ABI mismatch")
  h.checkSymbolClash name
  if args.size != signature.args.size then throw (.invalidProgram "Windows thread operands disagree with ABI")
  args.mapIdxM fun index op => do
    let some expected := callee.args[index]? | throw (.invalidProgram "compiler Windows thread ABI argument missing")
    h.transmute op expected.layout
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some value => pure value | none => throw (.invalidProgram "checked Windows thread argument missing")

def dispatch (h : Hooks S F) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult := do
  let some operation := parse name | return .NotSupported
  let args ← checked h operation name abi args
  let scalar := fun value => h.writeScalar value dest
  match operation with
  | .create =>
    let id ← WindowsThread.create h.thread (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3) (← arg args 4) (← arg args 5)
    scalar (← WindowsHandles.toScalar h.thread.handles (.thread id))
  | .wait => WindowsThread.wait h.thread (← arg args 0) (← arg args 1) dest
  | .tlsAlloc => scalar (← WindowsThread.tlsAlloc h.thread none dest.layout.layout.size)
  | .flsAlloc => scalar (← WindowsThread.tlsAlloc h.thread (some (← arg args 0)) dest.layout.layout.size)
  | .tlsGet => h.writePointer (← WindowsThread.tlsGet h.thread (← arg args 0)) dest
  | .tlsSet =>
    WindowsThread.tlsSet h.thread (← arg args 0) (← arg args 1)
    h.writeInt 1 dest
  | .tlsFree | .flsFree =>
    WindowsThread.tlsFree h.thread (operation == .flsFree) (← arg args 0)
    h.writeInt 1 dest
  | .isFiber => h.writeInt 0 dest
  | .setDescription =>
    WindowsThread.setDescription h.thread (← arg args 0) (← arg args 1)
    h.writeInt 0 dest
  | .getDescription =>
    WindowsThread.getDescription h.thread (← arg args 0) (← arg args 1)
    h.writeInt 0 dest
  | .getId | .currentId =>
    let op ← if operation == .getId then (arg args 0).map some else pure none
    h.writeInt (Int.ofNat (← WindowsThread.getId h.thread op).toNat) dest
  return .NeedsReturn

def bindWindows (h : Hooks S F)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B Inst) :
    ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B Inst := {
  base with windows := fun name abi args dest => do
    if base.family != .windows then throw (.invalidProgram "Windows thread dispatcher on non-Windows target")
    let result ← dispatch h name abi args dest
    if result != .NotSupported then return result
    base.windows name abi args dest }
end Miri.Interpreter.WindowsThreadDispatch
