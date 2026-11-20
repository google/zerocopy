import Miri.Interpreter.BlockingIo

/-! Source blocking_io.rs::block_thread_for_io on typed owned callback data.
Immediate readiness executes the FnOnce directly. Only actually blocked calls
consume a shared callback token; no function-valued registry is requested. -/
namespace Miri.Interpreter.OwnedBlockingIo
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
structure Hooks (S F C Poll Host : Type) where
  source : BlockingIo.Hooks S F Poll Host
  register : C → M S Nat
  take : Nat → M S C
  dropCapture : C → M S Unit
private def onError (action : M S A) (cleanup : M S Unit) : M S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state => match cleanup state with
    | .ok _ state => .error error state | .error next state => .error next state

/-- Owns the source_fd argument and callback environment. Source removes the IO
interest in its callback body, not in this helper. Registration follows the
source add-interest and immediate-readiness check. -/
def block (h : Hooks S F C P H) (fd : F) (interest : BlockingIo.Interest)
    (deadline : Option ThreadDeadline) (capture : C)
    (invoke : C → UnblockKind → M S Unit) : M S Unit :=
  Files.withDrop (do
    let runtime := h.source.readiness.runtime
    let ready ← onError (do
      BlockingIo.addBlockedThread h.source (h.source.readiness.id fd) (← runtime.threads).activeThread interest
      pure (interest.fulfilled (← h.source.sourceReadiness fd))
    ) (h.dropCapture capture)
    if ready then invoke capture .Ready
    else
      let token ← onError (h.register capture) (h.dropCapture capture)
      try
        let manager ← runtime.threads
        let manager ← match manager.blockThreadWithRuntimeConstraints .IO deadline token runtime.communicate with
          | .ok manager => pure manager
          | .error error => throw (runtime.error (.blockThreadSource error))
        runtime.putThreads manager
      catch error =>
        unless (← runtime.threads).threads.any (fun thread => match thread.state with
            | .Blocked _ _ actual => actual == token | _ => false) do
          h.dropCapture (← h.take token)
        throw error
  ) (h.source.readiness.dropFd fd)
end Miri.Interpreter.OwnedBlockingIo
