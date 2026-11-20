import Miri.Interpreter.CpuAffinityMachine

/-! Exact modern Unix and legacy FreeBSD affinity shim wrappers. -/
namespace Miri.Interpreter.CpuAffinityDispatch
open Miri.ABI Miri.Memory Miri.MIR
abbrev M := EStateM StepError
structure Hooks (P S D MD B I : Type) where
  affinity : CpuAffinity.Hooks P S MD
  foreign : ForeignItems.Hooks P S D MD (Pointer (Option P)) B I
  /-- Exact shim_sig Cfn(libc::pid_t,usize,*_)->i32 for the requested name. -/
  expectedAbi : String → M S (FnAbi TyId)

/-- Source-call adapter over the already adapted common Core. The Unix source
assembly has converted foreign destinations to `MPlaceTy` before reaching
this dispatcher, while its original full Hooks record still uses
`RuntimePlace`; requiring only Core avoids manufacturing unrelated callback
arms merely to run the affinity shim. -/
structure CoreHooks (P S D MD B I : Type) where
  affinity : CpuAffinity.Hooks P S MD
  foreign : ForeignItems.Core P S D MD (Pointer (Option P)) B I
  expectedAbi : String → M S (FnAbi TyId)
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "checked CPU affinity operand missing")

def emulateCore (h : CoreHooks P S D MD B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD) : M S (Option ForeignItems.EmulateItemResult) := do
  if name == "cpuset_getaffinity" then
    if h.foreign.os != "freebsd" then return none
    h.foreign.checkSymbolClash name
    if abi.conv != .C then throw (.undefinedBehavior "cpuset_getaffinity calling convention mismatch")
    if abi.cVariadic then throw (.undefinedBehavior "cpuset_getaffinity variadic signature")
    if args.size != 5 then throw (.undefinedBehavior "cpuset_getaffinity argument count mismatch")
    CpuAffinity.freeBsdGetAffinity h.affinity (← arg args 0) (← arg args 1)
      (← arg args 2) (← arg args 3) (← arg args 4) dest
    return some .NeedsReturn
  unless name == "sched_getaffinity" || name == "sched_setaffinity" do return none
  unless #["linux","freebsd","android"].contains h.foreign.os do
    throw (.unsupported "sched affinity unavailable on target OS")
  let callee ← h.expectedAbi name
  unless callee.conv == .C && !callee.cVariadic && callee.args.size == 3 do
    throw (.invalidProgram "CPU affinity compiler shim signature query mismatch")
  ForeignItems.Core.checkAbi h.foreign abi callee
  h.foreign.checkSymbolClash name
  unless args.size == 3 do throw (.invalidProgram "CPU affinity checked argument count")
  let args ← args.mapIdxM fun index value => do
    let expected ← arg callee.args index
    h.foreign.transmute value expected.layout
  let pid ← arg args 0
  let size ← arg args 1
  let mask ← arg args 2
  if name == "sched_getaffinity" then CpuAffinity.getAffinity h.affinity pid size mask dest
  else CpuAffinity.setAffinity h.affinity pid size mask dest
  return some .NeedsReturn

def emulate (h : Hooks P S D MD B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD) : M S (Option ForeignItems.EmulateItemResult) :=
  emulateCore ⟨h.affinity,h.foreign.toCore,h.expectedAbi⟩ name abi args dest

def bind (h : Hooks P S D MD B I) : ForeignItems.Hooks P S D MD (Pointer (Option P)) B I :=
  {h.foreign with unix := fun name abi args dest => do
    if let some result ← emulate h name abi args dest then return result
    h.foreign.unix name abi args dest}
end Miri.Interpreter.CpuAffinityDispatch
