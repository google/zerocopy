import Miri.Interpreter.WindowsSync
import Miri.Interpreter.ForeignItems

/-! Pinned windows/foreign_items.rs:782–824 exact synchronization entrypoints. -/
namespace Miri.Interpreter.WindowsSyncDispatch
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Operation where
  | beginInitialize | complete | waitOnAddress | wakeSingle | wakeAll
  deriving DecidableEq, Repr
inductive ArgType where | pointer | u32 | usize deriving DecidableEq, Repr
structure Signature where
  args : Array ArgType
  returnsBool : Bool
  deriving DecidableEq, Repr

def parse : String → Option Operation
  | "InitOnceBeginInitialize" => some .beginInitialize
  | "InitOnceComplete" => some .complete
  | "WaitOnAddress" => some .waitOnAddress
  | "WakeByAddressSingle" => some .wakeSingle
  | "WakeByAddressAll" => some .wakeAll
  | _ => none

def signature : Operation → Signature
  | .beginInitialize => ⟨#[.pointer,.u32,.pointer,.pointer],true⟩
  | .complete => ⟨#[.pointer,.u32,.pointer],true⟩
  | .waitOnAddress => ⟨#[.pointer,.pointer,.usize,.u32],true⟩
  | .wakeSingle | .wakeAll => ⟨#[.pointer],false⟩
structure Hooks (S R : Type) where
  windows : WindowsSync.Hooks S R
  /-- Exact target canonicalization of extern system (not a hardcoded Win64
  assumption); compiler construction must use winapi::BOOL or () as requested. -/
  systemConvention : M S CanonAbi
  /-- The exact shim symbol is part of the compiler query identity. -/
  expectedAbi : String → Signature → M S (FnAbi Miri.MIR.TyId)
  argumentCompat : ArgAbi Miri.MIR.TyId → ArgAbi Miri.MIR.TyId → M S Bool
  checkSymbolClash : String → M S Unit
  transmute : OpTy Provenance → TyAndLayout Miri.MIR.TyId → M S (OpTy Provenance)
private def checked (h : Hooks S R) (op : Operation) (name : String)
    (caller : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance)) : M S (Array (OpTy Provenance)) := do
  let request := signature op
  let callee ← h.expectedAbi name request
  if callee.conv != (← h.systemConvention) || callee.cVariadic ||
      callee.fixedCount.toNat != request.args.size || callee.args.size != request.args.size then
    throw (.invalidProgram "compiler Windows shim signature disagrees with requested system ABI")
  if caller.conv != callee.conv then throw (.undefinedBehavior "Windows synchronization calling convention mismatch")
  if caller.cVariadic != callee.cVariadic then throw (.undefinedBehavior "Windows synchronization variadic signature mismatch")
  if caller.fixedCount != callee.fixedCount then throw (.undefinedBehavior "Windows synchronization argument count mismatch")
  if !(← h.argumentCompat caller.ret callee.ret) then throw (.undefinedBehavior "Windows synchronization return ABI mismatch")
  for (caller,callee) in caller.args.toList.zip callee.args.toList do
    if !(← h.argumentCompat caller callee) then throw (.undefinedBehavior "Windows synchronization argument ABI mismatch")
  h.checkSymbolClash name
  if args.size != request.args.size then throw (.invalidProgram "Windows synchronization operand count disagrees with ABI")
  args.mapIdxM fun index operand => do
    let some expected := callee.args[index]? | throw (.invalidProgram "missing Windows synchronization ABI argument")
    h.transmute operand expected.layout
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some value => pure value | none => throw (.invalidProgram "missing checked Windows sync operand")

def dispatch (h : Hooks S R) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult := do
  let some operation := parse name | return .NotSupported
  let args ← checked h operation name abi args
  let first ← arg args 0
  match operation with
  | .beginInitialize => WindowsSync.beginInitialize h.windows first (← arg args 1) (← arg args 2) (← arg args 3) dest
  | .complete =>
    let result ← WindowsSync.complete h.windows first (← arg args 1) (← arg args 2)
    h.windows.once.runtime.writeScalar result dest
  | .waitOnAddress => WindowsSync.waitOnAddress h.windows first (← arg args 1) (← arg args 2) (← arg args 3) dest
  | .wakeSingle => WindowsSync.wakeByAddress h.windows first false
  | .wakeAll => WindowsSync.wakeByAddress h.windows first true
  return .NeedsReturn

def bindWindows (h : Hooks S R)
    (base : ForeignItems.Hooks Provenance S D (MPlaceTy Provenance) Ptr B I) :
    ForeignItems.Hooks Provenance S D (MPlaceTy Provenance) Ptr B I := {
  base with windows := fun name abi args dest => do
    if base.family != .windows then throw (.invalidProgram "Windows sync dispatcher requires Windows target")
    let result ← dispatch h name abi args dest
    if result != .NotSupported then return result
    base.windows name abi args dest }
end Miri.Interpreter.WindowsSyncDispatch
