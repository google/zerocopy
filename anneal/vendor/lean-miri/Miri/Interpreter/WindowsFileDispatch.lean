import Miri.Interpreter.WindowsPaths
import Miri.Interpreter.ForeignItems

/-! Pinned windows/foreign_items.rs file and handle arms. All use modern
check_shim_sig with compiler system ABI and exact imported WinAPI types. -/
namespace Miri.Interpreter.WindowsFileDispatch
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Operation where
  | readFile | writeFile | create | getInformation | setInformation | flush | deleteFile | setPointer | moveFile
  | stdHandle | duplicate | close | currentProcess | currentThread | fullPath
  deriving DecidableEq, Repr
inductive ArgType where | pointer | handle | u32 | i64 | bool | i32 | fileInfoClass
  deriving DecidableEq, Repr
structure Signature where
  args : Array ArgType
  ret : ArgType

def parse : String → Option Operation
  | "NtReadFile" => some .readFile | "NtWriteFile" => some .writeFile
  | "CreateFileW" => some .create | "GetFileInformationByHandle" => some .getInformation
  | "SetFileInformationByHandle" => some .setInformation | "FlushFileBuffers" => some .flush
  | "DeleteFileW" => some .deleteFile | "SetFilePointerEx" => some .setPointer
  | "MoveFileExW" => some .moveFile | "GetStdHandle" => some .stdHandle
  | "DuplicateHandle" => some .duplicate | "CloseHandle" => some .close
  | "GetCurrentProcess" => some .currentProcess | "GetCurrentThread" => some .currentThread
  | "GetFullPathNameW" => some .fullPath | _ => none

def signature : Operation → Signature
  | .readFile | .writeFile => ⟨#[.handle,.handle,.pointer,.pointer,.pointer,.pointer,.u32,.pointer,.pointer],.i32⟩
  | .create => ⟨#[.pointer,.u32,.u32,.pointer,.u32,.u32,.handle],.handle⟩
  | .getInformation => ⟨#[.handle,.pointer],.bool⟩
  | .setInformation => ⟨#[.handle,.fileInfoClass,.pointer,.u32],.bool⟩
  | .flush | .close => ⟨#[.handle],.bool⟩
  | .deleteFile => ⟨#[.pointer],.bool⟩
  | .setPointer => ⟨#[.handle,.i64,.pointer,.u32],.bool⟩
  | .moveFile => ⟨#[.pointer,.pointer,.u32],.bool⟩
  | .stdHandle => ⟨#[.u32],.handle⟩
  | .duplicate => ⟨#[.handle,.handle,.handle,.pointer,.u32,.bool,.u32],.bool⟩
  | .currentProcess | .currentThread => ⟨#[],.handle⟩
  | .fullPath => ⟨#[.pointer,.u32,.pointer,.pointer],.u32⟩
structure Hooks (S F H D P HM T E K : Type) where
  paths : WindowsPaths.Hooks S F H D P HM T E K
  systemConvention : M S CanonAbi
  /-- The exact shim symbol is part of the compiler query identity. -/
  expectedAbi : String → Signature → M S (FnAbi Miri.MIR.TyId)
  argumentCompat : ArgAbi Miri.MIR.TyId → ArgAbi Miri.MIR.TyId → M S Bool
  checkSymbolClash : String → M S Unit
  transmute : OpTy Provenance → TyAndLayout Miri.MIR.TyId → M S (OpTy Provenance)
private def checked (h : Hooks S F H D P HM T E K) (operation : Operation) (name : String)
    (caller : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance)) : M S (Array (OpTy Provenance)) := do
  let signature := signature operation
  let callee ← h.expectedAbi name signature
  if callee.conv != (← h.systemConvention) || callee.cVariadic || callee.args.size != signature.args.size ||
      callee.fixedCount.toNat != signature.args.size then throw (.invalidProgram "compiler Windows file signature mismatch")
  if caller.conv != callee.conv then throw (.undefinedBehavior "Windows file calling convention mismatch")
  if caller.cVariadic != callee.cVariadic then throw (.undefinedBehavior "Windows file variadic ABI mismatch")
  if caller.fixedCount != callee.fixedCount then throw (.undefinedBehavior "Windows file argument count mismatch")
  if !(← h.argumentCompat caller.ret callee.ret) then throw (.undefinedBehavior "Windows file return ABI mismatch")
  for (actual,expected) in caller.args.toList.zip callee.args.toList do
    if !(← h.argumentCompat actual expected) then throw (.undefinedBehavior "Windows file argument ABI mismatch")
  h.checkSymbolClash name
  if args.size != signature.args.size then throw (.invalidProgram "Windows file operands disagree with ABI")
  args.mapIdxM fun index op => do
    let some expected := callee.args[index]? | throw (.invalidProgram "compiler Windows file ABI argument missing")
    h.transmute op expected.layout
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some value => pure value | none => throw (.invalidProgram "checked Windows file argument missing")

def dispatch (h : Hooks S F H D P HM T E K) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult := do
  let some operation := parse name | return .NotSupported
  let args ← checked h operation name abi args
  let files := h.paths.files
  let handles := files.handles
  let scalar := fun value => handles.writeScalar value dest
  match operation with
  | .currentProcess => scalar (← WindowsHandles.toScalar handles (.pseudo .currentProcess))
  | .currentThread => scalar (← WindowsHandles.toScalar handles (.pseudo .currentThread))
  | .stdHandle => scalar (← WindowsHandles.stdHandle handles (← arg args 0))
  | .close => scalar (← WindowsHandles.close handles (← arg args 0))
  | .duplicate => scalar (← WindowsHandles.duplicate handles (← arg args 0) (← arg args 1) (← arg args 2)
      (← arg args 3) (← arg args 4) (← arg args 5) (← arg args 6))
  | .create =>
    let handle ← WindowsFiles.create files (← arg args 0) (← arg args 1) (← arg args 2)
      (← arg args 3) (← arg args 4) (← arg args 5) (← arg args 6)
    scalar (← WindowsHandles.toScalar handles handle)
  | .getInformation => scalar (← WindowsFiles.getInformation files (← arg args 0) (← arg args 1))
  | .setInformation => scalar (← WindowsFiles.setInformation files (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3))
  | .flush => scalar (← WindowsFiles.flush files (← arg args 0))
  | .deleteFile => scalar (← WindowsFiles.deleteFile files (← arg args 0))
  | .moveFile => scalar (← WindowsFiles.moveFile files (← arg args 0) (← arg args 1) (← arg args 2))
  | .setPointer => scalar (← WindowsFiles.setPointer files (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3))
  | .readFile | .writeFile =>
    WindowsFiles.ntReadWrite files (operation == .writeFile) (← arg args 0) (← arg args 1)
      (← arg args 2) (← arg args 3) (← arg args 4) (← arg args 5) (← arg args 6) (← arg args 7) (← arg args 8) dest
  | .fullPath =>
    let value ← WindowsPaths.getFullPath h.paths (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3)
    match Scalar.fromInt value.toNat (Size.ofBytes 4) with
    | .ok value => scalar value
    | .error _ => throw (.invalidProgram "Windows full path u32 result construction failed")
  return .NeedsReturn

def bindWindows (h : Hooks S F H D P HM T E K)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B I) :
    ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) Ptr B I := {
  base with windows := fun name abi args dest => do
    if base.family != .windows || h.paths.files.os != "windows" then throw (.invalidProgram "Windows file dispatcher target mismatch")
    let result ← dispatch h name abi args dest
    if result != .NotSupported then return result
    base.windows name abi args dest }
end Miri.Interpreter.WindowsFileDispatch
