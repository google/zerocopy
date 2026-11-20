import Miri.Interpreter.EpollShims
import Miri.Interpreter.EventFd
import Miri.Interpreter.ShimSignatures
import Miri.Interpreter.IoError

/-! Remaining solarish/foreign_items.rs operations. Existing thread/socket/
__sysconf wrappers are dispatched by their canonical shared modules. -/
namespace Miri.Interpreter.SolarishForeign
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
def dynamicSymbol (name : String) : Bool := name == "pthread_setname_np"
structure Hooks (S F Iter D E B I : Type) where
  foreign : ForeignItems.Hooks Provenance S D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I
  errors : IoError.Hooks S E
  epoll : EpollShims.Hooks S F Iter
  event : EventFd.Hooks S F
  pollBudget : Nat
  readI32 : OpTy Provenance → M S Int32
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  isNull : Pointer (Option Provenance) → M S Bool
  libcI32 : String → M S Int32
  derefStack : OpTy Provenance → M S (MPlaceTy Provenance)
  derefU32 : OpTy Provenance → M S (MPlaceTy Provenance)
  projectNamed : MPlaceTy Provenance → String → M S (MPlaceTy Provenance)
  writeInt : Int → MPlaceTy Provenance → M S Unit
  stackAddress : UInt64
  stackSize : UInt64
  numCpus : UInt32

/-- Narrow source constructor interface for the Solarish arms. Their shim
semantics use only the shared nonrecursive foreign-item core, so callers that
build a platform arm must not fabricate unrelated math/Unix/Windows dispatch
callbacks just to provide symbol checking and pointer writes. -/
structure CoreHooks (S F Iter D E B I : Type) where
  foreign : ForeignItems.Core Provenance S D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I
  errors : IoError.Hooks S E
  epoll : EpollShims.Hooks S F Iter
  event : EventFd.Hooks S F
  pollBudget : Nat
  readI32 : OpTy Provenance → M S Int32
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  isNull : Pointer (Option Provenance) → M S Bool
  libcI32 : String → M S Int32
  derefStack : OpTy Provenance → M S (MPlaceTy Provenance)
  derefU32 : OpTy Provenance → M S (MPlaceTy Provenance)
  projectNamed : MPlaceTy Provenance → String → M S (MPlaceTy Provenance)
  writeInt : Int → MPlaceTy Provenance → M S Unit
  stackAddress : UInt64
  stackSize : UInt64
  numCpus : UInt32
private def arg (args : Array A) (i : Nat) : M S A :=
  match args[i]? with | some a => pure a | none => throw (.invalidProgram "checked solarish operand missing")

def emulateCore (h : CoreHooks S F Iter D E B I) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S (Option ForeignItems.EmulateItemResult) := do
  if !(#["solaris","illumos"].contains h.foreign.os) then return none
  let count := match name with
    | "___errno" => some 0 | "stack_getbounds" | "epoll_create1" => some 1
    | "pset_info" | "epoll_ctl" | "epoll_wait" => some 4 | "eventfd" => some 2 | _ => none
  let some count := count | return none
  if #["epoll_create1","epoll_ctl","epoll_wait","eventfd"].contains name && h.foreign.os != "illumos" then
    throw (.invalidProgram "Illumos-only synchronization shim on Solaris")
  h.foreign.checkSymbolClash name
  if abi.conv != .C then throw (.undefinedBehavior "solarish legacy calling convention mismatch")
  if abi.cVariadic then throw (.undefinedBehavior "solarish legacy variadic signature")
  if args.size != count then throw (.undefinedBehavior "solarish legacy argument count mismatch")
  let write32 := fun (value : Int32) => h.writeInt value.toInt dest
  if name == "___errno" then h.foreign.writePointer (← IoError.lastErrorPlace h.errors).mplace.ptr dest
  else if name == "epoll_create1" then write32 (← EpollShims.create h.epoll (← arg args 0))
  else if name == "epoll_ctl" then write32 (← EpollShims.control h.pollBudget h.epoll (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3))
  else if name == "epoll_wait" then EpollShims.wait h.pollBudget h.epoll (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3) dest
  else if name == "eventfd" then write32 (← EventFd.create h.event (← arg args 0) (← arg args 1))
  else if name == "stack_getbounds" then
    let stack ← h.derefStack (← arg args 0)
    for (field,value) in #[("ss_sp",h.stackAddress),("ss_size",h.stackSize),("ss_flags",0)] do
      h.writeInt (Int.ofNat value.toNat) (← h.projectNamed stack field)
    h.writeInt 0 dest
  else
    let pset ← h.readI32 (← arg args 0)
    let tpe ← h.readPointer (← arg args 1)
    let list ← h.readPointer (← arg args 3)
    let myId ← h.libcI32 "PS_MYID"
    if pset != myId then throw (.unsupported "pset_info requires PS_MYID")
    if !(← h.isNull tpe) then throw (.unsupported "pset_info requires type NULL")
    if !(← h.isNull list) then throw (.unsupported "pset_info requires list NULL")
    h.writeInt (Int.ofNat h.numCpus.toNat) (← h.derefU32 (← arg args 2))
    h.writeInt 0 dest
  return some .NeedsReturn

/-- Compatibility entry point for the legacy complete foreign-item record.
The actual Solarish arms project only its common source Core. -/
def emulate (h : Hooks S F Iter D E B I) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S (Option ForeignItems.EmulateItemResult) := do
  let core : CoreHooks S F Iter D E B I := {
    foreign := h.foreign.toCore
    errors := h.errors
    epoll := h.epoll
    event := h.event
    pollBudget := h.pollBudget
    readI32 := h.readI32
    readPointer := h.readPointer
    isNull := h.isNull
    libcI32 := h.libcI32
    derefStack := h.derefStack
    derefU32 := h.derefU32
    projectNamed := h.projectNamed
    writeInt := h.writeInt
    stackAddress := h.stackAddress
    stackSize := h.stackSize
    numCpus := h.numCpus }
  emulateCore core name abi args dest
end Miri.Interpreter.SolarishForeign
