import Miri.Interpreter.WindowsEnvironment
import Miri.Interpreter.ForeignItems

namespace Miri.Interpreter.WindowsEnvironmentDispatch
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Operation where
  | getVariable | setVariable | getStrings | freeStrings | cwd | chdir | profile | pid | temp
  deriving DecidableEq, Repr
inductive ArgType where | pointer | handle | u32 | bool deriving DecidableEq, Repr
structure Signature where
  args : Array ArgType
  ret : ArgType
def signature : Operation → Signature
  | .getVariable => ⟨#[.pointer,.pointer,.u32],.u32⟩
  | .setVariable => ⟨#[.pointer,.pointer],.bool⟩
  | .getStrings => ⟨#[],.pointer⟩
  | .freeStrings | .chdir => ⟨#[.pointer],.bool⟩
  | .cwd | .temp => ⟨#[.u32,.pointer],.u32⟩
  | .profile => ⟨#[.handle,.pointer,.pointer],.bool⟩
  | .pid => ⟨#[],.u32⟩
def parse : String → Option Operation
  | "GetEnvironmentVariableW" => some .getVariable | "SetEnvironmentVariableW" => some .setVariable
  | "GetEnvironmentStringsW" => some .getStrings | "FreeEnvironmentStringsW" => some .freeStrings
  | "GetCurrentDirectoryW" => some .cwd | "SetCurrentDirectoryW" => some .chdir
  | "GetUserProfileDirectoryW" => some .profile | "GetCurrentProcessId" => some .pid
  | "GetTempPathW" => some .temp | _ => none
structure Hooks (S O E K : Type) where
  env : WindowsEnvironment.Hooks S O E K
  systemConvention : M S CanonAbi
  /-- The exact shim symbol is part of the compiler query identity. -/
  expectedAbi : String → Signature → M S (FnAbi Miri.MIR.TyId)
  argumentCompat : ArgAbi Miri.MIR.TyId → ArgAbi Miri.MIR.TyId → M S Bool
  checkSymbolClash : String → M S Unit
  transmute : OpTy Provenance → TyAndLayout Miri.MIR.TyId → M S (OpTy Provenance)
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
  writeInt : Int → MPlaceTy Provenance → M S Unit
  writePointer : Pointer (Option Provenance) → MPlaceTy Provenance → M S Unit
private def checked (h : Hooks S O E K) (operation : Operation) (name : String)
    (caller : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance)) : M S (Array (OpTy Provenance)) := do
  let signature := signature operation
  let callee ← h.expectedAbi name signature
  if callee.conv != (← h.systemConvention) || callee.cVariadic || callee.args.size != signature.args.size ||
      callee.fixedCount.toNat != signature.args.size then throw (.invalidProgram "compiler Windows environment signature mismatch")
  if caller.conv != callee.conv then throw (.undefinedBehavior "Windows environment calling convention mismatch")
  if caller.cVariadic != callee.cVariadic then throw (.undefinedBehavior "Windows environment variadic ABI mismatch")
  if caller.fixedCount != callee.fixedCount then throw (.undefinedBehavior "Windows environment argument count mismatch")
  if !(← h.argumentCompat caller.ret callee.ret) then throw (.undefinedBehavior "Windows environment return ABI mismatch")
  for (actual,expected) in caller.args.toList.zip callee.args.toList do
    if !(← h.argumentCompat actual expected) then throw (.undefinedBehavior "Windows environment argument ABI mismatch")
  h.checkSymbolClash name
  if args.size != signature.args.size then throw (.invalidProgram "Windows environment operands disagree with ABI")
  args.mapIdxM fun index op => do
    let some expected := callee.args[index]? | throw (.invalidProgram "compiler Windows environment ABI argument missing")
    h.transmute op expected.layout
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some value => pure value | none => throw (.invalidProgram "checked Windows environment argument missing")

def dispatch [DecidableEq O] (h : Hooks S O E K) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult := do
  let some operation := parse name | return .NotSupported
  let args ← checked h operation name abi args
  let u32 := fun (value : UInt32) => do
    match Scalar.fromUInt (BitVec.ofNat 128 value.toNat) (Size.ofBytes 4) with
    | .ok scalar => h.writeScalar scalar dest
    | .error _ => throw (.invalidProgram "Windows u32 construction failed")
  match operation with
  | .getVariable =>
    let name ← h.env.readPointer (← arg args 0)
    let buf ← h.env.readPointer (← arg args 1)
    let size ← h.env.readU32 (← arg args 2)
    u32 (← EnvVars.getEnvironmentVariableW h.env.env name buf size)
  | .setVariable =>
    let name ← h.env.readPointer (← arg args 0)
    let value ← h.env.readPointer (← arg args 1)
    let success ← EnvVars.setEnvironmentVariableW h.env.env name value
    h.writeScalar (← h.env.windows (if success then "TRUE" else "FALSE")) dest
  | .getStrings => h.writePointer (← EnvVars.getEnvironmentStringsW h.env.env) dest
  | .freeStrings => h.writeInt (← EnvVars.freeEnvironmentStringsW h.env.env (← h.env.readPointer (← arg args 0))).toInt dest
  | .cwd => u32 (← WindowsEnvironment.getcwd h.env (← arg args 0) (← arg args 1))
  | .chdir => h.writeScalar (← WindowsEnvironment.chdir h.env (← arg args 0)) dest
  | .profile => h.writeInt (if ← WindowsEnvironment.profile h.env (← arg args 0) (← arg args 1) (← arg args 2) then 1 else 0) dest
  | .pid => u32 (← EnvVars.getPid h.env.process)
  | .temp => u32 (← WindowsEnvironment.tempPath h.env (← arg args 0) (← arg args 1))
  return .NeedsReturn

def bindWindows [DecidableEq O] (h : Hooks S O E K)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B Inst) :
    ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B Inst := {
  base with windows := fun name abi args dest => do
    if base.family != .windows || h.env.env.family != .windows || h.env.process.family != .windows then
      throw (.invalidProgram "Windows environment dispatcher target mismatch")
    let result ← dispatch h name abi args dest
    if result != .NotSupported then return result
    base.windows name abi args dest }
end Miri.Interpreter.WindowsEnvironmentDispatch
