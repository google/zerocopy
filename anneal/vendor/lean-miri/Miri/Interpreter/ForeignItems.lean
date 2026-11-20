import Miri.ABI.FnAbi
import Miri.Interpreter.Rvalue

/-! Source port of Miri shims/{mod,foreign_items,alloc,env}.rs. OS-specific,
compiler signature construction, allocation and host effects remain mandatory
queries; dispatch, ABI checks, allocation policy and control ordering are here. -/
namespace Miri.Interpreter.ForeignItems
open Miri.ABI Miri.MIR
abbrev M := EStateM StepError
inductive EmulateItemResult where
  | NeedsReturn | NeedsUnwind | AlreadyJumped | NotSupported
  deriving DecidableEq, Repr
inductive Family where | unix | windows | other deriving DecidableEq, Repr
inductive Init where | uninit | zero deriving DecidableEq, Repr
inductive AllocationKind where | rust | c | miri | mmap deriving DecidableEq, Repr
inductive SignatureType where
  | unit | usize | isize | i32 | u32 | pointer | unitPointer | alignment | never
  | u64 | u8 | bool | byteSlice | functionPointer
  deriving DecidableEq, Repr
structure Signature where
  conv : CanonAbi
  args : Array SignatureType
  ret : SignatureType
  deriving DecidableEq, Repr
inductive SpecialAllocatorMethod where
  | Alloc | AllocZeroed | Dealloc | Realloc
  deriving DecidableEq, Repr
inductive AllocatorSymbol (Instance : Type) where
  | redirect (symbol : String)
  | special (method : SpecialAllocatorMethod)

/-- Target architecture spellings are compiler target names, not host names. -/
def mallocAlign (arch os : String) (size : UInt64) : Except StepError Align := do
  let maximum : UInt64 ←
    if (arch == "riscv32" && (os == "espidf" || os == "zkvm")) ||
        (arch == "xtensa" && os == "espidf") then pure 4
    else if #["x86","arm","m68k","csky","loongarch32","mips","mips32r6",
        "powerpc","powerpc64","sparc","wasm32","hexagon","riscv32","xtensa"].contains arch then pure 8
    else if #["x86_64","aarch64","arm64ec","loongarch64","mips64","mips64r6",
        "s390x","sparc64","riscv64","wasm64"].contains arch then pure 16
    else throw (.invalidProgram s!"unsupported target architecture for malloc: {arch}")
  let bytes := if size >= maximum then maximum else if size >= 8 then 8
    else if size >= 4 then 4 else if size >= 2 then 2 else 1
  match Align.fromBytes bytes with
  | .ok align => pure align
  | .error error => throw (.invalidProgram (toString error))

def checkRustAllocRequest (maximum size align : UInt64) : Except StepError Align := do
  if size == 0 then throw (.undefinedBehavior "creating allocation with size 0")
  if size > maximum then throw (.undefinedBehavior "creating an allocation larger than half the address space")
  match Align.fromBytes align with
  | .ok value => pure value
  | .error (.tooLarge _) => throw (.unsupported "allocation alignment exceeds rustc maximum")
  | .error _ => throw (.undefinedBehavior "creating allocation with non-power-of-two alignment")

structure SymbolCandidate (Instance : Type) where
  fnInstance : Instance
  crateId : Nat
  weak : Bool
  explicitSymbol : Bool
  symbol : String
  spanOrder : Nat × Nat

/-- Weak definitions lose to strong definitions; two equally weak definitions
are an error, including two weak definitions. Compiler iteration order is kept. -/
def lookupSymbol (name : String) (symbols : Array (SymbolCandidate I)) :
    Except StepError (Option I) := do
  let mut chosen : Option (SymbolCandidate I) := none
  for candidate in symbols do
    if candidate.explicitSymbol && candidate.symbol == name then
      if let some original := chosen then
        match candidate.weak, original.weak with
        | false, true => chosen := some candidate
        | true, false => pure ()
        | _, _ =>
          let (first,second) := if original.spanOrder.1 < candidate.spanOrder.1 ||
              (original.spanOrder.1 == candidate.spanOrder.1 && original.spanOrder.2 < candidate.spanOrder.2) then
            (original,candidate) else (candidate,original)
          throw (.machineStop s!"multiple symbol definitions `{name}` in crates {first.crateId} and {second.crateId}")
      else chosen := some candidate
  return chosen.map (·.fnInstance)

inductive ExportKind where
  | function | associatedFunction | staticItem | other
  deriving DecidableEq, Repr

/-- Compiler definition-kind checks precede MIR loading. A data export with a
matching name must never become a callable fallback. -/
def lookupFunctionFromSymbols (name : String) (symbols : Array (SymbolCandidate I))
    (definitionKind : I → M S ExportKind) (loadMir : I → M S B) : M S (Option (B × I)) := do
  let found ← match lookupSymbol name symbols with
    | .ok found => pure found | .error error => throw error
  let some fnInstance := found | return none
  let kind ← definitionKind fnInstance
  if kind != .function && kind != .associatedFunction then
    throw (.undefinedBehavior "attempt to call an exported symbol that is not defined as a function")
  return some (← loadMir fnInstance,fnInstance)

def lookupStaticFromSymbols (name : String) (symbols : Array (SymbolCandidate I))
    (definitionKind : I → M S ExportKind) : M S (Option I) := do
  let found ← match lookupSymbol name symbols with
    | .ok found => pure found | .error error => throw error
  if let some fnInstance := found then
    if (← definitionKind fnInstance) != .staticItem then
      throw (.undefinedBehavior "attempt to access an exported symbol not defined as a static")
  return found

structure Core (P S D MD Ptr Body Instance : Type) where
  family : Family
  os : String
  arch : String
  maximumSize : UInt64
  noAllocShimSymbol : String
  allocatorSymbol : String → M S (Option (AllocatorSymbol Instance))
  lookupFunction : String → M S (Option (Body × Instance))
  forceAllocation : D → M S MD
  returnToBlock : Option BasicBlockId → M S Unit
  unwindToBlock : UnwindAction → M S Unit
  nativeEnabled : Bool
  callNative : String → MD → Array (OpTy P) → M S Bool
  expectedAbi : Signature → M S (FnAbi TyId)
  argumentCompat : ArgAbi TyId → ArgAbi TyId → M S Bool
  checkSymbolClash : String → M S Unit
  transmute : OpTy P → TyAndLayout TyId → M S (OpTy P)
  readUsize : OpTy P → M S UInt64
  readPointer : OpTy P → M S Ptr
  readI32 : OpTy P → M S Int32
  isNull : Ptr → M S Bool
  allocate : UInt64 → Align → Init → AllocationKind → M S Ptr
  deallocate : Ptr → Option (UInt64 × Align) → AllocationKind → M S Unit
  reallocate : Ptr → Option (UInt64 × Align) → UInt64 → Align → AllocationKind → M S Ptr
  writePointer : Ptr → MD → M S Unit
  writeNull : MD → M S Unit
  setEnomem : M S Unit
  startExit : Int32 → M S Unit
  specialDestination : D → M S MD

/-- Dispatch is separate from the nonrecursive source primitive dictionary.
Portable/platform factories need only Core while constructing their bodies. -/
structure Hooks (P S D MD Ptr Body Instance : Type) extends Core P S D MD Ptr Body Instance where
  math : String → FnAbi TyId → Array (OpTy P) → MD → M S EmulateItemResult
  unix : String → FnAbi TyId → Array (OpTy P) → MD → M S EmulateItemResult
  windows : String → FnAbi TyId → Array (OpTy P) → MD → M S EmulateItemResult
  /-- Other top-level arms (memory/string/Miri diagnostics) are required typed
  operations; NotSupported is reserved for names absent from the source table. -/
  otherPortable : String → FnAbi TyId → Array (OpTy P) → MD → M S (Option EmulateItemResult)

instance : CoeOut (Hooks P S D MD Ptr B I) (Core P S D MD Ptr B I) := ⟨Hooks.toCore⟩

private def lift (r : Except StepError A) : M S A :=
  match r with | .ok a => pure a | .error e => throw e

namespace Core
def checkAbi (h : Core P S D MD Ptr B I) (caller callee : FnAbi TyId) : M S Unit := do
  if caller.conv != callee.conv then throw (.undefinedBehavior "shim calling convention mismatch")
  if caller.cVariadic != callee.cVariadic then throw (.undefinedBehavior "shim variadic ABI mismatch")
  if caller.fixedCount != callee.fixedCount then throw (.undefinedBehavior "shim argument count mismatch")
  if !(← h.argumentCompat caller.ret callee.ret) then throw (.undefinedBehavior "shim return ABI mismatch")
  for (caller,callee) in caller.args.toList.zip callee.args.toList do
    if !(← h.argumentCompat caller callee) then throw (.undefinedBehavior "shim argument ABI mismatch")

def checkSignature (h : Core P S D MD Ptr B I) (name : String)
    (signature : Signature) (caller : FnAbi TyId) (args : Array (OpTy P)) : M S (Array (OpTy P)) := do
  let callee ← h.expectedAbi signature
  if callee.cVariadic then throw (.invalidProgram "nonvariadic shim signature constructed variadic")
  checkAbi h caller callee
  h.checkSymbolClash name
  if args.size != signature.args.size || callee.args.size != args.size then
    throw (.invalidProgram "shim arguments disagree with compiler ABI")
  args.mapIdxM fun index arg => do
    let some expected := callee.args[index]? | throw (.invalidProgram "missing shim ABI argument")
    h.transmute arg expected.layout

end Core

private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some a => pure a | none => throw (.invalidProgram "missing checked shim argument")
private def align (value : UInt64) : M S Align :=
  match Align.fromBytes value with | .ok a => pure a | .error e => throw (.invalidProgram (toString e))

/-- Compatibility entry points project the lawful nonrecursive dictionary. -/
def checkAbi (h : Hooks P S D MD Ptr B I) (caller callee : FnAbi TyId) : M S Unit :=
  Core.checkAbi h.toCore caller callee
def checkSignature (h : Hooks P S D MD Ptr B I) (name : String)
    (signature : Signature) (caller : FnAbi TyId) (args : Array (OpTy P)) : M S (Array (OpTy P)) :=
  Core.checkSignature h.toCore name signature caller args

def specialAllocator (h : Hooks P S D MD Ptr B I) (method : SpecialAllocatorMethod)
    (name : String) (abi : FnAbi TyId) (args : Array (OpTy P)) (dest : D) : M S Unit := do
  let signature := match method with
    | .Alloc | .AllocZeroed => Signature.mk .Rust #[.usize,.alignment] .unitPointer
    | .Dealloc => ⟨.Rust,#[.unitPointer,.usize,.alignment],.unit⟩
    | .Realloc => ⟨.Rust,#[.unitPointer,.usize,.alignment,.usize],.unitPointer⟩
  let args ← checkSignature h name signature abi args
  match method with
  | .Alloc | .AllocZeroed =>
    let size ← h.readUsize (← arg args 0)
    let alignment ← h.readUsize (← arg args 1)
    let alignment ← lift (checkRustAllocRequest h.maximumSize size alignment)
    let pointer ← h.allocate size alignment (if method == .AllocZeroed then .zero else .uninit) .rust
    h.writePointer pointer (← h.specialDestination dest)
  | .Dealloc =>
    let pointer ← h.readPointer (← arg args 0)
    let size ← h.readUsize (← arg args 1)
    let alignment ← h.readUsize (← arg args 2)
    h.deallocate pointer (some (size,← align alignment)) .rust
  | .Realloc =>
    let pointer ← h.readPointer (← arg args 0)
    let old ← h.readUsize (← arg args 1)
    let alignment ← h.readUsize (← arg args 2)
    let size ← h.readUsize (← arg args 3)
    let alignment ← lift (checkRustAllocRequest h.maximumSize size alignment)
    let pointer ← h.reallocate pointer (some (old,alignment)) size alignment .rust
    h.writePointer pointer (← h.specialDestination dest)

def inner (h : Hooks P S D MD Ptr B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD) : M S EmulateItemResult := do
  if h.nativeEnabled then
    if ← h.callNative name dest args then return .NeedsReturn
  if name == h.noAllocShimSymbol then
    let _ ← checkSignature h name ⟨.Rust,#[],.unit⟩ abi args
    return .NeedsReturn
  if name == "malloc" || name == "calloc" || name == "realloc" || name == "free" then
    let signature : Signature := if name == "malloc" then ⟨.C,#[.usize],.pointer⟩
      else if name == "calloc" then ⟨.C,#[.usize,.usize],.pointer⟩
      else if name == "realloc" then ⟨.C,#[.pointer,.usize],.pointer⟩
      else ⟨.C,#[.pointer],.unit⟩
    let args ← checkSignature h name signature abi args
    if name == "free" then
      let pointer ← h.readPointer (← arg args 0)
      if !(← h.isNull pointer) then h.deallocate pointer none .c
    else
      let old ← if name == "realloc" then (h.readPointer (← arg args 0)).map some else pure none
      let first ← h.readUsize (← arg args (if name == "realloc" then 1 else 0))
      let size ← if name == "calloc" then
          let second ← h.readUsize (← arg args 1)
          let product := first.toNat * second.toNat
          pure (if product <= h.maximumSize.toNat then some (UInt64.ofNat product) else none)
        else pure (if first <= h.maximumSize then some first else none)
      if let some size := size then
        let alignment ← lift (mallocAlign h.arch h.os size)
        let pointer ← if let some old := old then
            if ← h.isNull old then h.allocate size alignment .uninit .c
            else if size == 0 then throw (.undefinedBehavior "realloc with size zero")
            else h.reallocate old none size alignment .c
          else h.allocate size alignment (if name == "calloc" then .zero else .uninit) .c
        h.writePointer pointer dest
      else
        if h.family == .unix then h.setEnomem
        h.writeNull dest
    return .NeedsReturn
  if name == "exit" then
    let args ← checkSignature h name ⟨.C,#[.i32],.unit⟩ abi args
    h.startExit (← h.readI32 (← arg args 0))
    return .AlreadyJumped
  if name == "abort" then
    let _ ← checkSignature h name ⟨.C,#[],.unit⟩ abi args
    throw (.machineStop "the program aborted execution")
  if #["miri_alloc","miri_dealloc","miri_track_alloc","miri_start_unwind",
      "miri_run_provenance_gc","miri_get_alloc_id","miri_print_borrow_state",
      "miri_pointer_name","miri_static_root","miri_host_to_target_path",
      "miri_thread_spawn","miri_thread_join","miri_spin_loop","miri_backtrace_size",
      "miri_get_backtrace","miri_resolve_frame","miri_resolve_frame_names",
      "miri_write_to_stdout","miri_write_to_stderr","miri_promise_symbolic_alignment",
      "malloc_usable_size","memcmp","memchr","memrchr",
      "strlen","strnlen","wcslen","memcpy","strcpy","memset"].contains name then
    let some result ← h.otherPortable name abi args dest
      | throw (.unsupported s!"missing portable shim semantics for `{name}`")
    if result == .NotSupported then throw (.invalidProgram "recognized portable shim cannot fall through")
    return result
  let result ← h.math name abi args dest
  if result != .NotSupported then return result
  match h.family with
  | .unix => h.unix name abi args dest
  | .windows => h.windows name abi args dest
  | .other => pure .NotSupported

def emulate (h : Hooks P S D MD Ptr B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : D) (ret : Option BasicBlockId)
    (unwind : UnwindAction) : M S (Option (B × I)) := do
  if let some allocator ← h.allocatorSymbol name then
    match allocator with
    | .redirect symbol =>
      let some handler ← h.lookupFunction symbol | throw (.invalidProgram "missing alloc error handler symbol")
      return some handler
    | .special method =>
      specialAllocator h method name abi args dest
      h.returnToBlock ret
      return none
  let dest ← h.forceAllocation dest
  match ← inner h name abi args dest with
  | .NeedsReturn => h.returnToBlock ret; return none
  | .NeedsUnwind => h.unwindToBlock unwind; return none
  | .AlreadyJumped => return none
  | .NotSupported =>
    if let some body ← h.lookupFunction name then return some body
    throw (.machineStop s!"can't call foreign function `{name}` on OS `{h.os}`")

def emulateDynSym (h : Hooks P S D MD Ptr B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : D) (ret : Option BasicBlockId)
    (unwind : UnwindAction) : M S Unit := do
  if (← emulate h name abi args dest ret unwind).isSome then
    throw (.invalidProgram "DynSyms that delegate are not supported")

/-- OS strings are supplied as already-decoded target strings. Unix byte
encoding and Windows case rules belong to their separate OS modules. -/
def initialEnvironment (communicate : Bool) (forwarded : Array String)
    (environment overrides : Array (String × String)) : Array (String × String) := Id.run do
  let mut result := #[]
  for (name,value) in environment do
    if communicate || forwarded.contains name then
      result := (result.filter (·.1 != name)).push (name,value)
  for (name,value) in overrides do
    result := (result.filter (·.1 != name)).push (name,value)
  return result

def getPid (communicate : Bool) (hostPid : M S UInt32) : M S UInt32 :=
  if communicate then hostPid else pure 1000

def getTid (family : Family) (pid : UInt32) (thread : UInt32) : Except StepError UInt32 := do
  if family != .unix then throw (.invalidProgram "get_tid requires Unix target")
  if pid.toNat + thread.toNat >= 2^32 then throw (.invalidProgram "OS thread ID overflow")
  return pid + thread
end Miri.Interpreter.ForeignItems
