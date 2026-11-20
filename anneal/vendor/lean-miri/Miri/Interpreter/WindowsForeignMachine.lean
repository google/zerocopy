import Miri.Interpreter.ForeignSyncMachine
import Miri.Interpreter.WindowsForeign

/-! Production composition on the canonical full ThreadStacks machine state.
Main startup, ExitCalled, FLS/TLS destructors and function-pointer resolution
share the same registries, memory and actual thread stacks. -/
namespace Miri.Interpreter.WindowsForeignMachine
open Miri.ABI Miri.Memory Miri.Concurrency

/-- Select canonical typed init-once/futex objects in the actual Windows
foreign dispatcher; no legacy function registry is supplied. -/
def bindSynchronization (objects : ForeignSyncMachine.Objects S)
    (h : WindowsForeign.Hooks S Place FD H D Os HM T E Kind TypedSyncRuntime.Ref Host System TZ Timestamp B I) :=
  {h with sync := {h.sync with windows := ForeignSyncMachine.windows objects h.sync.windows}}

def bind [DecidableEq Os]
    (exit : WindowsExitMachine.Hooks U C Other X FnABI ArgABI Aff P)
    (choice : C) (systemAbi : X) (reuseClock : Option VectorIdx) (winLocal : Kind)
    (unwind : Unwind.Hooks MiriMemoryKind (ThreadStacks.Storage U) C Other)
    (embedDynamic : WindowsPlatform.DynamicSymbol → Other)
    (h : WindowsForeign.Hooks (MainMachine.State U) Place FD H D Os HM T E Kind R Host System TZ Timestamp B I)
    (base : ForeignItems.Hooks Provenance (MainMachine.State U) Place (MPlaceTy Provenance)
      (Pointer (Option Provenance)) B I) := Id.run do
  let tls := exit.main.termination.tls
  let thread := WindowsThreadMachine.bind tls.thread choice systemAbi reuseClock h.thread.thread
  let thread := WindowsThreadMachine.bindTls tls thread
  let thread := WindowsThreadMachine.bindNames h.environment.env.strings winLocal thread
  let platform := WindowsExitMachine.bindPlatform exit h.platform
  let platform := WindowsPlatformDispatch.bindUnwind unwind choice platform
  let platform := {platform with platform := {platform.platform with functionPointer := fun symbol => do
    return (← FunctionPointers.functionPointer exit.main.functions (.Other (embedDynamic symbol))).withOptionalProvenance}}
  let handles := {h.files.paths.files.handles with threads := return (← get).machine.threads}
  let files := {h.files with paths := {h.files.paths with files := {h.files.paths.files with handles}}}
  let h := {h with thread := {h.thread with thread}, platform, files}
  return WindowsForeign.bind h base

/-- Pair the composed foreign chain with this scheduler adapter. Its callback
sum includes main startup, ordinary TLS and ExitCalled; no callback stage is
reconstructed from a different memory-only snapshot. -/
def bindLoop (exit : WindowsExitMachine.Hooks U C Other X FnABI ArgABI Aff P)
    (base : RunLoopHooks (MainMachine.State U) C WindowsExitMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind U) :=
  WindowsExitMachine.bindLoop exit base scheduler
end Miri.Interpreter.WindowsForeignMachine
