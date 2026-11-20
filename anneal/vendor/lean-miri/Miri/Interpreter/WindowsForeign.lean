import Miri.Interpreter.WindowsExitMachine
import Miri.Interpreter.WindowsFileDispatch
import Miri.Interpreter.WindowsThreadDispatch
import Miri.Interpreter.WindowsEnvironmentDispatch
import Miri.Interpreter.TimeShimDispatch
import Miri.Interpreter.WindowsSyncDispatch
import Miri.Interpreter.WindowsRandomDispatch
import Miri.Interpreter.StdOnlyShims

/-! One Windows platform foreign-item chain. All handlers execute on the same
S; direct dispatch avoids captured older platform fallback chains. -/
namespace Miri.Interpreter.WindowsForeign
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
structure Hooks (S Place F H D Os HM T E Kind R Host System TZ Timestamp B I : Type) where
  environment : WindowsEnvironmentDispatch.Hooks S Os E Kind
  files : WindowsFileDispatch.Hooks S F H D Os HM T E Kind
  thread : WindowsThreadDispatch.Hooks S F
  time : TimeShimDispatch.Hooks S Host System TZ Timestamp
  sync : WindowsSyncDispatch.Hooks S R
  random : WindowsRandomDispatch.Hooks S Place B I
  platform : WindowsPlatformDispatch.Hooks S Os E Kind F
  stdOnly : StdOnlyShims.WindowsHooks Provenance S Place (MPlaceTy Provenance) B I

/-- Inventory-specific direct dispatch. Each nonmatching handler returns before
operand reads/ABI queries, and each matching handler's actual errors propagate. -/
def dispatch [DecidableEq Os] (h : Hooks S Place F H D Os HM T E Kind R Host System TZ Timestamp B I)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I)
    (name : String) (abi : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance))
    (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult := do
  if base.family != .windows || base.os != "windows" || h.environment.env.env.family != .windows ||
      h.environment.env.process.family != .windows || h.time.time.family != .windows || h.time.time.os != "windows" then
    throw (.invalidProgram "Windows foreign chain target mismatch")
  let environment := h.environment
  let handles := h.files.paths.files.handles
  let platform := {h.platform with platform := {h.platform.platform with
    environment := environment.env, handles := handles}}
  let thread := {h.thread with thread := {h.thread.thread with handles := handles}}
  let result ← WindowsEnvironmentDispatch.dispatch environment name abi args dest
  if result != .NotSupported then return result
  let result ← WindowsFileDispatch.dispatch h.files name abi args dest
  if result != .NotSupported then return result
  let result ← WindowsThreadDispatch.dispatch thread name abi args dest
  if result != .NotSupported then return result
  let result ← TimeShimDispatch.dispatch h.time name abi args dest
  if result != .NotSupported then return result
  let result ← WindowsSyncDispatch.dispatch h.sync name abi args dest
  if result != .NotSupported then return result
  let random := {h.random with signatures := {h.random.signatures with foreign := base.toCore}}
  if let some result ← WindowsRandomDispatch.emulate random name abi args dest then return result
  let result ← WindowsPlatformDispatch.dispatch platform name abi args dest
  if result != .NotSupported then return result
  StdOnlyShims.windowsCore {h.stdOnly with foreign := base.toCore} name abi args dest

/-- Terminal platform handler: unknown Windows names return NotSupported to the
canonical foreign-item dispatcher, which owns unsupported/native/MIR policy. -/
def bind [DecidableEq Os] (h : Hooks S Place F H D Os HM T E Kind R Host System TZ Timestamp B I)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I) :=
  {base with windows := dispatch h base}

/-- Source DynSym dispatch uses the same chain, ABI queries and current state.
The canonical FunctionPointers Other registry must embed/recover this symbol. -/
def dynamic [DecidableEq Os] (h : Hooks S Place F H D Os HM T E Kind R Host System TZ Timestamp B I)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I)
    (symbol : WindowsPlatform.DynamicSymbol) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : Place) (ret : Option Miri.MIR.BasicBlockId)
    (unwind : Miri.MIR.UnwindAction) : M S Unit :=
  ForeignItems.emulateDynSym (bind h base) symbol.name abi args dest ret unwind
end Miri.Interpreter.WindowsForeign
