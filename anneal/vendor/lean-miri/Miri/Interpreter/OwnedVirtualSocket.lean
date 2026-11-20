import Miri.Interpreter.VirtualSocket
import Miri.Interpreter.OwnedSocketCompletion

/-! Source virtual_socket.rs read/write retry execution with exact data captures.
Uses the existing canonical socket buffers, clock policies and readiness state.
Future retries are queued environments, not recursive closure calls or fuel. -/
namespace Miri.Interpreter.OwnedVirtualSocket
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
inductive Capture (F : Type) where
  | read (socket : F) (pointer : Pointer (Option Provenance)) (length : Nat)
      (nonblock : Bool) (finish : OwnedSocketCompletion.Bytes)
  | write (socket : F) (pointer : Pointer (Option Provenance)) (length : Nat)
      (nonblock : Bool) (finish : OwnedSocketCompletion.Bytes)
structure Hooks (S F E Iter : Type) where
  source : VirtualSocket.Hooks S F E
  completion : OwnedSocketCompletion.Hooks S E Iter
  register : Capture F → M S Nat
  take : Nat → M S (Capture F)
private def onError (action : M S A) (cleanup : M S Unit) : M S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state => match cleanup state with
    | .ok _ state => .error error state | .error next state => .error next state
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def peer (value : VirtualSocket.State) : M S Files.WeakRef :=
  match value.peer with | some value => pure value | none => throw (.invalidProgram "virtual socket peer OnceCell uninitialized")
private def clockAcquire (h : VirtualSocket.Hooks S F E) (clock : VClock) : M S Unit := do
  let runtime := h.readiness.runtime
  match runtime.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.acquire (← runtime.global) (← runtime.threads) clock with
    | .ok global => runtime.putGlobal global
    | .error error => throw (runtime.error (SyncError.ofClock error))
private def clockRelease (h : VirtualSocket.Hooks S F E) (clock : VClock) (put : VClock → M S Unit) : M S Unit := do
  let runtime := h.readiness.runtime
  match runtime.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.prepareRelease (← runtime.global) (← runtime.threads) with
    | .error error => throw (runtime.error (SyncError.ofClock error))
    | .ok (snapshot,finish) =>
      put (clock.join snapshot)
      match finish with
      | .error error => throw (runtime.error (SyncError.ofClock error))
      | .ok global => runtime.putGlobal global

private inductive WriteStage (F E : Type) where
  | done (result : Files.Result E Nat)
  | peerDone (peer : F) (result : Files.Result E Nat)
  | blocked (peer : F)
  | written (peer : F) (count : Nat)
private def prepareWrite (h : VirtualSocket.Hooks S F E) (socket : F) (pointer : Pointer (Option Provenance))
    (length : Nat) (nonblock : Bool) : M S (WriteStage F E) := do
  if length == 0 then return .done (.ok 0)
  let current ← h.get socket
  let some other ← h.readiness.upgrade (← peer current)
    | return .done (.error (.host (← h.errors.hostFromKind .BrokenPipe)))
  onError (do
    let otherValue ← h.get other
    let some buffer := otherValue.readbuf | return .peerDone other (.error (.libc "EBADF"))
    if buffer.bytes.size > VirtualSocket.capacity then throw (.invalidProgram "virtual buffer capacity strict_sub underflow")
    let available := VirtualSocket.capacity-buffer.bytes.size
    if available == 0 then
      if current.nonblock || nonblock then
        return .peerDone other (.error (.host (← h.errors.hostFromKind .WouldBlock)))
      let current ← h.get socket
      h.put socket { current with blockedWrite := current.blockedWrite.push (← h.readiness.runtime.threads).activeThread }
      return .blocked other
    clockRelease h buffer.clock fun clock =>
      h.put other {otherValue with readbuf := some {buffer with clock := clock}}
    let count := min length available
    let bytes ← h.readBytes pointer count
    if bytes.size != count then throw (.invalidProgram "virtual write_to_host byte count mismatch")
    let currentOther ← h.get other
    let some currentBuffer := currentOther.readbuf | throw (.invalidProgram "virtual peer read buffer disappeared")
    h.put other { currentOther with readbuf := some { currentBuffer with bytes := currentBuffer.bytes ++ bytes }, blockedRead := #[] }
    for thread in currentOther.blockedRead do h.readiness.unblock thread .VirtualSocket
    return .written other count
  ) (h.readiness.dropFd other)

private inductive ReadStage (E : Type) where
  | done (result : Files.Result E Nat)
  | blocked
  | read (count : Nat) (empty : Bool)
private def prepareRead (h : VirtualSocket.Hooks S F E) (socket : F) (pointer : Pointer (Option Provenance))
    (length : Nat) (nonblock : Bool) : M S (ReadStage E) := do
  if length == 0 then return .done (.ok 0)
  let value ← h.get socket
  let some buffer := value.readbuf | throw (.unsupported "reading from write end of pipe")
  if buffer.bytes.isEmpty then
    let other ← h.readiness.upgrade (← peer value)
    if let some other := other then h.readiness.dropFd other
    if other.isNone then return .done (.ok 0)
    if value.nonblock || nonblock then return .done (.error (.host (← h.errors.hostFromKind .WouldBlock)))
    h.put socket { value with blockedRead := value.blockedRead.push (← h.readiness.runtime.threads).activeThread }
    return .blocked
  clockAcquire h buffer.clock
  let count := min length buffer.bytes.size
  let bytes := buffer.bytes.extract 0 count
  let remaining := buffer.bytes.extract count buffer.bytes.size
  h.put socket { value with readbuf := some { buffer with bytes := remaining } }
  h.writeBytes pointer bytes
  return .read count remaining.isEmpty
def dropCapture (h : Hooks S F E I) : Capture F → M S Unit
  | .read fd .. | .write fd .. => h.source.readiness.dropFd fd
private def block (h : Hooks S F E I) (capture : Capture F) : M S Unit := do
  let token ← onError (h.register capture) (dropCapture h capture)
  let runtime := h.source.readiness.runtime
  try
    let manager ← runtime.threads
    let manager ← match manager.blockThreadWithRuntimeConstraints .VirtualSocket none token runtime.communicate with
      | .ok manager => pure manager
      | .error error => throw (runtime.error (.blockThreadSource error))
    runtime.putThreads manager
  catch error =>
    unless (← runtime.threads).threads.any (fun thread => match thread.state with
        | .Blocked _ _ actual => actual == token | _ => false) do
      dropCapture h (← h.take token)
    throw error

def write (h : Hooks S F E I) (socket : F) (pointer : Pointer (Option Provenance))
    (length : Nat) (nonblock : Bool) (finish : OwnedSocketCompletion.Bytes) : M S Unit := do
  let source := h.source
  let stage ← onError (prepareWrite source socket pointer length nonblock) (source.readiness.dropFd socket)
  match stage with
  | .done result => Files.withDrop (OwnedSocketCompletion.bytes h.completion finish result) (source.readiness.dropFd socket)
  | .peerDone other result =>
    Files.withDrop (Files.withDrop (OwnedSocketCompletion.bytes h.completion finish result)
      (source.readiness.dropFd other)) (source.readiness.dropFd socket)
  | .blocked other =>
    onError (block h (.write socket pointer length nonblock finish)) (source.readiness.dropFd other)
    source.readiness.dropFd other
  | .written other count =>
    onError (Readiness.updateFd source.wakeBudget source.readiness socket {}) (source.readiness.dropFd other)
    Readiness.updateFd source.wakeBudget source.readiness other {forceEdge := true}
    OwnedSocketCompletion.bytes h.completion finish (.ok count)

def read (h : Hooks S F E I) (socket : F) (pointer : Pointer (Option Provenance))
    (length : Nat) (nonblock : Bool) (finish : OwnedSocketCompletion.Bytes) : M S Unit := do
  let source := h.source
  let stage ← onError (prepareRead source socket pointer length nonblock) (source.readiness.dropFd socket)
  match stage with
  | .done result => Files.withDrop (OwnedSocketCompletion.bytes h.completion finish result) (source.readiness.dropFd socket)
  | .blocked => block h (.read socket pointer length nonblock finish)
  | .read count empty =>
    let other ← onError (do
      let other ← source.readiness.upgrade (← peer (← source.get socket))
      if let some other := other then
        onError (do
          let value ← source.get other
          source.put other {value with blockedWrite := #[]}
          for thread in value.blockedWrite do source.readiness.unblock thread .VirtualSocket
        ) (source.readiness.dropFd other)
      pure other
    ) (source.readiness.dropFd socket)
    if let some other := other then
      onError (Readiness.updateFd source.wakeBudget source.readiness other {forceEdge := empty}) (source.readiness.dropFd socket)
    Readiness.updateFd source.wakeBudget source.readiness socket {}
    OwnedSocketCompletion.bytes h.completion finish (.ok count)

/-- The canonical dispatcher has already consumed Box<Self> before this call. -/
def invoke (h : Hooks S F E I) (capture : Capture F) (reason : UnblockKind) : M S Unit := do
  unless reason == .Ready do
    Files.withDrop (throw (.invalidProgram "virtual socket timeout impossible")) (dropCapture h capture)
  match capture with
  | .read socket ptr length nonblock finish => read h socket ptr length nonblock finish
  | .write socket ptr length nonblock finish => write h socket ptr length nonblock finish
end Miri.Interpreter.OwnedVirtualSocket
