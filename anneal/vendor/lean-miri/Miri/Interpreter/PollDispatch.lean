import Miri.Interpreter.EpollShims
import Miri.Interpreter.ForeignItems

/-! unix/foreign_items.rs poll and Linux/Android foreign_items.rs epoll arms.
No select/pselect/ppoll or epoll_pwait aliases occur in the pinned dispatch. -/
namespace Miri.Interpreter.PollDispatch
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Operation where | poll | create | control | wait deriving DecidableEq, Repr
structure Hooks (S F Iter : Type) where
  epoll : EpollShims.Hooks S F Iter
  os : String
  communicate : Bool
  pollAndUnblockZero : M S Unit
  /-- Compiler construction of extern C fn(pointer,nfds_t,i32)->i32. -/
  pollAbi : M S (FnAbi Miri.MIR.TyId)
  argumentCompat : ArgAbi Miri.MIR.TyId → ArgAbi Miri.MIR.TyId → M S Bool
  checkSymbolClash : String → M S Unit
  transmute : OpTy Provenance → TyAndLayout Miri.MIR.TyId → M S (OpTy Provenance)

def parse (os name : String) : Option Operation :=
  if name == "poll" then some .poll
  else if os == "linux" || os == "android" then
    match name with
    | "epoll_create1" => some .create
    | "epoll_ctl" => some .control
    | "epoll_wait" => some .wait
    | _ => none
  else none
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some value => pure value | none => throw (.invalidProgram "checked poll operand missing")

private def checked (h : Hooks S F I) (operation : Operation) (name : String)
    (caller : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance)) : M S (Array (OpTy Provenance)) := do
  if operation != .poll then
    -- Source deprecated checker: clash FIRST, then convention, variadic, arity.
    h.checkSymbolClash name
    if caller.conv != .C then throw (.undefinedBehavior "epoll shim calling convention mismatch")
    if caller.cVariadic then throw (.undefinedBehavior "epoll shim called with variadic signature")
    let count := if operation == .create then 1 else 4
    if args.size != count then throw (.undefinedBehavior "incorrect number of epoll arguments")
    return args
  let callee ← h.pollAbi
  if callee.conv != .C || callee.cVariadic || callee.args.size != 3 || callee.fixedCount.toNat != 3 then
    throw (.invalidProgram "compiler poll signature mismatch")
  if caller.conv != callee.conv then throw (.undefinedBehavior "poll calling convention mismatch")
  if caller.cVariadic != callee.cVariadic then throw (.undefinedBehavior "poll variadic signature mismatch")
  if caller.fixedCount != callee.fixedCount then throw (.undefinedBehavior "poll argument count mismatch")
  if !(← h.argumentCompat caller.ret callee.ret) then throw (.undefinedBehavior "poll return ABI mismatch")
  for (actual,expected) in caller.args.toList.zip callee.args.toList do
    if !(← h.argumentCompat actual expected) then throw (.undefinedBehavior "poll argument ABI mismatch")
  h.checkSymbolClash name
  if args.size != 3 then throw (.invalidProgram "poll operand count disagrees with ABI")
  args.mapIdxM fun index operand => do
    let some expected := callee.args[index]? | throw (.invalidProgram "poll compiler argument missing")
    h.transmute operand expected.layout

/-- Does not perform the Unix entry poll. Use bindUnix as the outer entry once,
or compose dispatch behind another existing outer entry-poll wrapper. -/
def dispatch (budget : Nat) (h : Hooks S F I) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult := do
  let some operation := parse h.os name | return .NotSupported
  let args ← checked h operation name abi args
  let first ← arg args 0
  match operation with
  | .poll => PollShims.poll budget h.epoll.poll first (← arg args 1) (← arg args 2) dest
  | .create => h.epoll.writeI32 (← EpollShims.create h.epoll first) dest
  | .control => h.epoll.writeI32 (← EpollShims.control budget h.epoll first (← arg args 1) (← arg args 2) (← arg args 3)) dest
  | .wait => EpollShims.wait budget h.epoll first (← arg args 1) (← arg args 2) (← arg args 3) dest
  return .NeedsReturn

def bindUnix (budget : Nat) (h : Hooks S F I)
    (base : ForeignItems.Hooks Provenance S P (MPlaceTy Provenance) Ptr B Inst) :
    ForeignItems.Hooks Provenance S P (MPlaceTy Provenance) Ptr B Inst := {
  base with unix := fun name abi args dest => do
    if base.family != .unix || base.os != h.os then throw (.invalidProgram "poll dispatcher target mismatch")
    if h.communicate then h.pollAndUnblockZero
    let result ← dispatch budget h name abi args dest
    if result != .NotSupported then return result
    base.unix name abi args dest }
end Miri.Interpreter.PollDispatch
