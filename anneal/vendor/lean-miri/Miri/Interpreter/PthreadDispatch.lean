import Miri.Interpreter.PthreadSync
import Miri.Interpreter.ForeignItems

/-! Pinned unix/foreign_items.rs pthread synchronization dispatch. ABI records
are compiler-produced, compared via source LayoutCompat and argument transmute. -/
namespace Miri.Interpreter.PthreadDispatch
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
inductive ArgType where | pointer | i32 | u32 deriving DecidableEq, Repr
inductive Operation where
  | mutexattrInit | mutexattrSettype | mutexattrDestroy | mutexInit | mutexLock
  | mutexTrylock | mutexUnlock | mutexDestroy | rwlockRead | rwlockTryread
  | rwlockWrite | rwlockTrywrite | rwlockUnlock | rwlockDestroy
  | condattrInit | condattrSetclock | condattrGetclock | condattrDestroy
  | condInit | condSignal | condBroadcast | condWait | condTimedwait | condDestroy
  | semInit | semWait | semTimedwait | semPost | semDestroy
  deriving DecidableEq, Repr

def parse (name : String) : Option Operation :=
  (#[ ("pthread_mutexattr_init",.mutexattrInit), ("pthread_mutexattr_settype",.mutexattrSettype),
    ("pthread_mutexattr_destroy",.mutexattrDestroy), ("pthread_mutex_init",.mutexInit),
    ("pthread_mutex_lock",.mutexLock), ("pthread_mutex_trylock",.mutexTrylock),
    ("pthread_mutex_unlock",.mutexUnlock), ("pthread_mutex_destroy",.mutexDestroy),
    ("pthread_rwlock_rdlock",.rwlockRead), ("pthread_rwlock_tryrdlock",.rwlockTryread),
    ("pthread_rwlock_wrlock",.rwlockWrite), ("pthread_rwlock_trywrlock",.rwlockTrywrite),
    ("pthread_rwlock_unlock",.rwlockUnlock), ("pthread_rwlock_destroy",.rwlockDestroy),
    ("pthread_condattr_init",.condattrInit), ("pthread_condattr_setclock",.condattrSetclock),
    ("pthread_condattr_getclock",.condattrGetclock), ("pthread_condattr_destroy",.condattrDestroy),
    ("pthread_cond_init",.condInit), ("pthread_cond_signal",.condSignal),
    ("pthread_cond_broadcast",.condBroadcast), ("pthread_cond_wait",.condWait),
    ("pthread_cond_timedwait",.condTimedwait), ("pthread_cond_destroy",.condDestroy),
    ("sem_init",.semInit), ("sem_wait",.semWait), ("sem_timedwait",.semTimedwait),
    ("sem_post",.semPost), ("sem_destroy",.semDestroy) ] : Array (String × Operation)).find? (·.1 == name) |>.map (·.2)

def argumentTypes : Operation → Array ArgType
  | .mutexattrSettype | .condattrSetclock => #[.pointer,.i32]
  | .mutexInit | .condattrGetclock | .condInit | .condWait | .semTimedwait => #[.pointer,.pointer]
  | .condTimedwait => #[.pointer,.pointer,.pointer]
  | .semInit => #[.pointer,.i32,.u32]
  | _ => #[.pointer]
structure Hooks (S R Duration : Type) where
  pthread : PthreadSync.Hooks S R Duration
  /-- Exact nonvariadic extern C signature, returning i32; pointer entries are
  shim_sig wildcard-pointee raw pointers, not arbitrary pointer-sized integers. -/
  expectedAbi : Array ArgType → M S (FnAbi Miri.MIR.TyId)
  argumentCompat : ArgAbi Miri.MIR.TyId → ArgAbi Miri.MIR.TyId → M S Bool
  checkSymbolClash : String → M S Unit
  transmute : OpTy Provenance → TyAndLayout Miri.MIR.TyId → M S (OpTy Provenance)
  readI32 : OpTy Provenance → M S Int32
  readU32 : OpTy Provenance → M S UInt32

private def check (h : Hooks S R T) (operation : Operation) (name : String)
    (caller : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance)) : M S (Array (OpTy Provenance)) := do
  let types := argumentTypes operation
  let callee ← h.expectedAbi types
  if callee.conv != .C || callee.cVariadic || callee.fixedCount.toNat != types.size || callee.args.size != types.size then
    throw (.invalidProgram "compiler pthread shim signature disagrees with requested C signature")
  if caller.conv != callee.conv then throw (.undefinedBehavior "pthread shim calling convention mismatch")
  if caller.cVariadic != callee.cVariadic then throw (.undefinedBehavior "pthread shim variadic ABI mismatch")
  if caller.fixedCount != callee.fixedCount then throw (.undefinedBehavior "pthread shim argument count mismatch")
  if !(← h.argumentCompat caller.ret callee.ret) then throw (.undefinedBehavior "pthread shim return ABI mismatch")
  for (caller,callee) in caller.args.toList.zip callee.args.toList do
    if !(← h.argumentCompat caller callee) then throw (.undefinedBehavior "pthread shim argument ABI mismatch")
  h.checkSymbolClash name
  if args.size != types.size then throw (.invalidProgram "pthread operand count disagrees with caller ABI")
  args.mapIdxM fun index operand => do
    let some arg := callee.args[index]? | throw (.invalidProgram "missing pthread ABI argument")
    h.transmute operand arg.layout
private def argument (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some value => pure value | none => throw (.invalidProgram "missing checked pthread argument")

def dispatch (budget : Nat) (h : Hooks S R T) (name : String)
    (abi : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance))
    (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult := do
  let some operation := parse name | return .NotSupported
  let args ← check h operation name abi args
  let a ← argument args 0
  let p := h.pthread
  let write := p.objects.runtime.writeScalar
  match operation with
  | .mutexattrInit => PthreadSync.mutexattrInit p a; write 0 dest
  | .mutexattrSettype => write (← PthreadSync.mutexattrSettype p a (← h.readI32 (← argument args 1))) dest
  | .mutexattrDestroy => PthreadSync.mutexattrDestroy p a; write 0 dest
  | .mutexInit => PthreadSync.mutexInit p a (← argument args 1); write 0 dest
  | .mutexLock => PthreadSync.mutexLock p a dest
  | .mutexTrylock => write (← PthreadSync.mutexTrylock p a) dest
  | .mutexUnlock => write (← PthreadSync.mutexUnlock p a) dest
  | .mutexDestroy => PthreadSync.mutexDestroy p a; write 0 dest
  | .rwlockRead => PthreadSync.rwlockRead p a dest
  | .rwlockTryread => write (← PthreadSync.rwlockTryread p a) dest
  | .rwlockWrite => PthreadSync.rwlockWrite p a dest
  | .rwlockTrywrite => write (← PthreadSync.rwlockTrywrite p a) dest
  | .rwlockUnlock => PthreadSync.rwlockUnlock p a; write 0 dest
  | .rwlockDestroy => PthreadSync.rwlockDestroy p a; write 0 dest
  | .condattrInit => PthreadSync.condattrInit p a; write 0 dest
  | .condattrSetclock => write (← PthreadSync.condattrSetclock p a (← h.readI32 (← argument args 1))) dest
  | .condattrGetclock => PthreadSync.condattrGetclock p a (← argument args 1); write 0 dest
  | .condattrDestroy => PthreadSync.condattrDestroy p a; write 0 dest
  | .condInit => PthreadSync.condInit p a (← argument args 1); write 0 dest
  | .condSignal => PthreadSync.condSignal p a; write 0 dest
  | .condBroadcast => PthreadSync.condBroadcast budget p a; write 0 dest
  | .condWait => PthreadSync.condWait p a (← argument args 1) dest
  | .condTimedwait => PthreadSync.condTimedwait p a (← argument args 1) (← argument args 2) dest false
  | .condDestroy => PthreadSync.condDestroy p a; write 0 dest
  | .semInit =>
    let pshared ← h.readI32 (← argument args 1)
    let value ← h.readU32 (← argument args 2)
    PthreadSync.semInit p a pshared value dest
  | .semWait => PthreadSync.semWait budget p a dest
  | .semTimedwait => PthreadSync.semTimedwait budget p a (← argument args 1) dest
  | .semPost => PthreadSync.semPost p a dest
  | .semDestroy => PthreadSync.semDestroy p a dest
  return .NeedsReturn
/-- Install this family ahead of the remaining required Unix handlers, keeping
ForeignItems native/math/allocator/return/MIR-fallback ordering unchanged. -/
def bindUnix (budget : Nat) (h : Hooks S R T)
    (base : ForeignItems.Hooks Provenance S D (MPlaceTy Provenance) Ptr B I) :
    ForeignItems.Hooks Provenance S D (MPlaceTy Provenance) Ptr B I := {
  base with unix := fun name abi args dest => do
    if base.family != .unix || base.os != h.pthread.objects.os then
      throw (.invalidProgram "pthread dispatcher target disagrees with foreign-item target")
    let result ← dispatch budget h name abi args dest
    if result != .NotSupported then return result
    base.unix name abi args dest }
end Miri.Interpreter.PthreadDispatch
