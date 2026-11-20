import Miri.Interpreter.UnixEnvironment

/-! Matching pinned Unix environment/system-information foreign-item arms. -/
namespace Miri.Interpreter.UnixEnvironmentDispatch
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Operation where
  | getenv | setenv | unsetenv | cwd | hostname | chdir | pid | uname | xuname | sysconf | strerror | uid | passwd | environ
  deriving DecidableEq, Repr
inductive ArgType where | i32 | pointer | sizeT | isize | pidT | uidT deriving DecidableEq, Repr
structure Signature where
  args : Array ArgType
  ret : ArgType
def signature : Operation → Signature
  | .getenv => ⟨#[.pointer],.pointer⟩
  | .setenv => ⟨#[.pointer,.pointer,.i32],.i32⟩
  | .unsetenv | .chdir | .uname => ⟨#[.pointer],.i32⟩
  | .cwd => ⟨#[.pointer,.sizeT],.pointer⟩
  | .hostname => ⟨#[.pointer,.sizeT],.i32⟩
  | .pid => ⟨#[],.pidT⟩ | .uid => ⟨#[],.uidT⟩ | .environ => ⟨#[],.pointer⟩
  | .xuname => ⟨#[.i32,.pointer],.i32⟩
  | .sysconf => ⟨#[.i32],.isize⟩
  | .strerror => ⟨#[.i32,.pointer,.sizeT],.i32⟩
  | .passwd => ⟨#[.uidT,.pointer,.pointer,.sizeT,.pointer],.i32⟩
structure Hooks (S O E K : Type) where
  env : UnixEnvironment.Hooks S O E K
  frameInStd : M S Bool
  /-- Exact compiler query keyed by the invoked foreign symbol. -/
  expectedAbi : String → M S (FnAbi Miri.MIR.TyId)
  argumentCompat : ArgAbi Miri.MIR.TyId → ArgAbi Miri.MIR.TyId → M S Bool
  checkSymbolClash : String → M S Unit
  transmute : OpTy Provenance → TyAndLayout Miri.MIR.TyId → M S (OpTy Provenance)
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
  writeInt : Int → MPlaceTy Provenance → M S Unit
  writePointer : Pointer (Option Provenance) → MPlaceTy Provenance → M S Unit

def parse (os name : String) : Option (Operation × Bool) :=
  match name with
  | "getenv" => some (.getenv,false) | "setenv" => some (.setenv,false)
  | "unsetenv" => some (.unsetenv,false) | "getcwd" => some (.cwd,false)
  | "gethostname" => some (.hostname,false) | "chdir" => some (.chdir,false)
  | "getpid" => some (.pid,false) | "sysconf" => some (.sysconf,false)
  | "strerror_r" => some (.strerror,false) | "getuid" | "geteuid" => some (.uid,false)
  | "getpwuid_r" | "__posix_getpwuid_r" => some (.passwd,true)
  | "uname" => if #["linux","android","macos","solaris","illumos"].contains os then some (.uname,false) else none
  | "__xuname" => if os == "freebsd" then some (.xuname,false) else none
  | "__sysconf_xpg7" => if os == "solaris" || os == "illumos" then some (.sysconf,true) else none
  | "__xpg_strerror_r" => if os == "linux" then some (.strerror,true) else none
  | "_NSGetEnviron" => if os == "macos" then some (.environ,true) else none
  | _ => none
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some value => pure value | none => throw (.invalidProgram "checked Unix environment operand missing")
private def checked (h : Hooks S O E K) (operation : Operation) (legacy : Bool) (name : String)
    (caller : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance)) : M S (Array (OpTy Provenance)) := do
  let signature := signature operation
  if legacy then
    h.checkSymbolClash name
    if caller.conv != .C then throw (.undefinedBehavior "Unix environment calling convention mismatch")
    if caller.cVariadic then throw (.undefinedBehavior "Unix environment variadic signature mismatch")
    if args.size != signature.args.size then throw (.undefinedBehavior "Unix environment argument count mismatch")
    return args
  let callee ← h.expectedAbi name
  if callee.conv != .C || callee.cVariadic || callee.fixedCount.toNat != signature.args.size || callee.args.size != signature.args.size then
    throw (.invalidProgram "compiler Unix environment signature mismatch")
  if caller.conv != callee.conv then throw (.undefinedBehavior "Unix environment calling convention mismatch")
  if caller.cVariadic != callee.cVariadic then throw (.undefinedBehavior "Unix environment variadic signature mismatch")
  if caller.fixedCount != callee.fixedCount then throw (.undefinedBehavior "Unix environment argument count mismatch")
  if !(← h.argumentCompat caller.ret callee.ret) then throw (.undefinedBehavior "Unix environment return ABI mismatch")
  for (actual,expected) in caller.args.toList.zip callee.args.toList do
    if !(← h.argumentCompat actual expected) then throw (.undefinedBehavior "Unix environment argument ABI mismatch")
  h.checkSymbolClash name
  if args.size != signature.args.size then throw (.invalidProgram "Unix environment operands disagree with ABI")
  args.mapIdxM fun index op => do
    let some expected := callee.args[index]? | throw (.invalidProgram "compiler Unix environment ABI operand missing")
    h.transmute op expected.layout

def dispatch (h : Hooks S O E K) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult := do
  let some (operation,legacy) := parse h.env.os name | return .NotSupported
  if operation == .passwd && !(← h.frameInStd) then return .NotSupported
  let args ← checked h operation legacy name abi args
  let int := fun (value : Int32) => h.writeInt value.toInt dest
  match operation with
  | .getenv => h.writePointer (← EnvVars.getenv h.env.env (← h.env.readPointer (← arg args 0))) dest
  | .unsetenv => int (← EnvVars.unsetenv h.env.env (← h.env.readPointer (← arg args 0)))
  | .setenv =>
    let _ ← h.env.readI32 (← arg args 2)
    let name ← h.env.readPointer (← arg args 0)
    let value ← h.env.readPointer (← arg args 1)
    int (← EnvVars.setenv h.env.env name value)
  | .cwd => h.writePointer (← UnixEnvironment.getcwd h.env (← arg args 0) (← arg args 1)) dest
  | .hostname => int (← UnixEnvironment.gethostname h.env (← arg args 0) (← arg args 1))
  | .chdir => int (← UnixEnvironment.chdir h.env (← arg args 0))
  | .pid =>
    let pid ← EnvVars.getPid h.env.process
    match Scalar.fromUInt (BitVec.ofNat 128 pid.toNat) (Size.ofBytes 4) with
    | .ok value => h.writeScalar value dest
    | .error _ => throw (.invalidProgram "pid u32 scalar construction failed")
  | .uid => h.writeInt 1000 dest
  | .uname => int (← UnixEnvironment.uname h.env (← arg args 0) none)
  | .xuname => int (← UnixEnvironment.uname h.env (← arg args 1) (some (← arg args 0)))
  | .sysconf => h.writeInt (← UnixEnvironment.sysconf h.env (← arg args 0)).toInt dest
  | .strerror => int (← UnixEnvironment.strerror h.env (← arg args 0) (← arg args 1) (← arg args 2))
  | .passwd => h.writeScalar (← UnixEnvironment.getpwuid h.env (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3) (← arg args 4)) dest
  | .environ =>
    match ← h.env.env.get with
    | .unix vars => h.writePointer vars.environ dest
    | _ => throw (.invalidProgram "Unix environment is uninitialized")
  return .NeedsReturn
def bindUnix (h : Hooks S O E K)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B Inst) :
    ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B Inst := {
  base with unix := fun name abi args dest => do
    if base.family != .unix || base.os != h.env.os then
      throw (.invalidProgram "Unix environment dispatcher target mismatch")
    let result ← dispatch h name abi args dest
    if result != .NotSupported then return result
    base.unix name abi args dest }
end Miri.Interpreter.UnixEnvironmentDispatch
