import Miri.Interpreter.ForeignSyncMachine
import Miri.Interpreter.UnixForeign
import Miri.Interpreter.UnixThreadDispatchMachine
import Miri.Interpreter.UnixFsMachine
import Miri.Interpreter.PollMachine
import Miri.Interpreter.EventFdMachine
import Miri.Interpreter.SocketMachine
import Miri.Interpreter.FreeBsdSyncMachine
import Miri.Interpreter.MacOsForeignMachine
import Miri.Interpreter.UnixTlsMachine
import Miri.Interpreter.LinuxForeignMachine

/-! Connected Unix dispatch on canonical ThreadStacks state. Shared owned FD,
readiness/event/poll registries and thread lifecycle effects remain authoritative. -/
namespace Miri.Interpreter.UnixForeignMachine
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev FD H D O := UnixForeign.FD H D O

/-- Install actual HostRuntime-backed synchronization objects into every source
Unix OS subchain before dispatch, including the macOS pthread aliases. -/
def bindSynchronization (objects : ForeignSyncMachine.Objects S)
    (h : UnixForeign.Hooks S Place H D Other Os HM Time E Kind ReadDir DirEntry
      TypedSyncRuntime.Ref Duration PollIter AddrIter Host System TZ Timestamp B I) :=
  let pthread := {h.pthread with pthread := ForeignSyncMachine.pthread objects h.pthread.pthread}
  let macos := {h.macos with
    sync := ForeignSyncMachine.mac objects h.macos.sync
    pthread := ForeignSyncMachine.pthread objects h.macos.pthread}
  let freebsd := {h.freebsd with sync := ForeignSyncMachine.freeBsd objects h.freebsd.sync}
  {h with pthread, macos, freebsd}

/-- The outer poll executes actual blocking/readiness work in real thread
contexts; all source family dispatchers then reuse this one result prefix. -/
def bindIo [DecidableEq K]
    (machine : ReadinessMachine.Hooks K (ThreadStacks.Storage U) H D Other)
    (io : BlockingIo.Hooks (ThreadStacks.State K U) (FD H D Other) Poll Host)
    (deadline : DeadlineMachine.Hooks K (ThreadStacks.Storage U) Host System)
    (epoll : PollMachine.DescriptorHooks Other)
    (directories : UnixFsMachine.DirectoryStore (ThreadStacks.Storage U) ReadDir)
    (events : EventFdMachine.Store (ThreadStacks.Storage U) Other)
    (access : PlaceMachine.AccessConfig K (ThreadStacks.Storage U))
    (place : PlaceHooks Provenance (ThreadStacks.State K U) C MachineHooks.FrameExtra)
    (choice : C) (budget : Nat)
    (otherMetadata : Other → ThreadStacks.M K U (Sum (Except (IoError.HostError E) HM) String))
    (errorFromKind : IoError.ErrorKind → ThreadStacks.M K U (IoError.Error E))
    (h : UnixForeign.Hooks (ThreadStacks.State K U) Place H D Other Os HM Time E Kind ReadDir DirEntry R Duration PollIter AddrIter Host System TZ Timestamp B I) := Id.run do
  let io := ReadinessMachine.bindBlockingThreadStacks io
  let readiness := ReadinessMachine.bindThreadStacks (ReadinessMachine.bind machine io.readiness)
  let event := EventFdMachine.bind events machine readiness budget access place choice h.event.event
  let files := EventFdMachine.bindFiles events event budget errorFromKind h.fd.file.fd.files
  let fd := ReadinessMachine.bindFiles machine readiness {h.fd.file.fd with files}
  let fs := UnixFsMachine.bindAll machine files otherMetadata directories readiness fd h.fs
  let paths := UnixFsMachine.bindRawWrites access ⟨access.runtime.pointerSize⟩ fs.directories.paths
  let fs := {fs with directories := {fs.directories with paths}, times := {fs.times with fd := {fs.times.fd with paths}}, temporary := {fs.temporary with paths}}
  let poll := {h.poll with epoll := PollMachine.bind machine epoll deadline h.poll.epoll}
  let poll := {poll with epoll := {poll.epoll with poll := {poll.epoll.poll with readiness}}}
  return {h with
    pollAndUnblockZero := BlockingIo.pollAndUnblock budget io (some ⟨0,0,by decide⟩)
    fd := {h.fd with file := {h.fd.file with fd}}
    fs := fs
    poll := poll
    event := EventFdDispatch.bindWrite place choice {h.event with event}
    linux := {h.linux with event}
    macos := {h.macos with sync := MacOsForeignMachine.bindTime h.time.time deadline h.macos.sync}
    freebsd := {h.freebsd with sync := FreeBsdSyncMachine.bindReads access (FreeBsdSyncMachine.bindTime h.time.time deadline h.freebsd.sync)} }

/-- Build socket protocol closures before the IO/FD adapter captures their
actual vtable operations. Returns the bound TCP hooks so the caller can reuse
that same BlockingIo manager for the single outer poll. -/
def bindSockets
    (machine : ReadinessMachine.Hooks K (ThreadStacks.Storage U) H D Other)
    (descriptor : SocketMachine.Descriptor Other)
    (store : SocketMachine.Store (ThreadStacks.Storage U) Receiver Listener Tcp E)
    (blocking : ReadinessMachine.BlockingStore (ThreadStacks.Storage U) Poll)
    (budget : Nat)
    (tcp : TcpSocket.Hooks (ThreadStacks.State K U) (FD H D Other) Receiver Listener Tcp E Poll Host)
    (options : SocketOptions.Hooks (ThreadStacks.State K U) (FD H D Other) E AddrIter)
    (h : UnixForeign.Hooks (ThreadStacks.State K U) Place H D Other Os HM Time E Kind ReadDir DirEntry R Duration PollIter AddrIter Host System TZ Timestamp B I) := Id.run do
  let (virtual,tcp) := SocketMachine.bindFullStacks h.socket.virtual tcp
  let (virtual,tcp,socket) := SocketMachine.bind machine descriptor store blocking budget h.fd.file.fd.asUnix virtual tcp options h.socket.socket
  let files := SocketMachine.bindFiles budget descriptor virtual tcp h.fd.file.fd.files
  let fd := {h.fd with file := {h.fd.file with fd := {h.fd.file.fd with files}}}
  return ({h with socket := {h.socket with socket, virtual}, fd},tcp)

/-- Thread create/join/detach and current IDs bind real frames/clock state.
System C ABI and optional reuse-clock choice are required source inputs. -/
def bindThread [DecidableEq K]
    (thread : ThreadMachine.Hooks K U C O X FnABI ArgABI Aff)
    (access : PlaceMachine.AccessConfig K (ThreadStacks.Storage U))
    (place : PlaceHooks Provenance (ThreadStacks.State K U) C MachineHooks.FrameExtra)
    (choice : C) (cAbi : X) (reuseClock : Option VectorIdx)
    (misalignment : Pointer (Option Provenance) → Align → ThreadStacks.M K U (Option Misalignment))
    (h : UnixForeign.Hooks (ThreadStacks.State K U) Place H D Other Os HM Time E Kind ReadDir DirEntry R Duration PollIter AddrIter Host System TZ Timestamp B I) := Id.run do
  let policy := UnixThreadMachine.bind thread access choice cAbi reuseClock misalignment h.thread.thread
  let dispatch := UnixThreadDispatchMachine.bind place choice policy h.thread
  let process := {h.environment.env.process with
    activeThread := do return UInt32.ofNat (← get).machine.threads.activeThread.toNat
    threadIdTryFrom := fun raw => do
      return ((← get).machine.threads.threadIdTryFrom raw.toNat).toOption.map fun id => UInt32.ofNat id.toNat}
  let environment := {h.environment with env := {h.environment.env with process}}
  return {h with thread := dispatch, environment, linux := {h.linux with thread := policy, unixGettid := fun name => do
      let scalar ← dispatch.unixGettid name
      match scalar.toUInt32 with
      | .ok value => pure value | .error error => throw (ScalarOps.scalarError error)} }

/-- Canonical affinity masks, physical guest memory and actual Linux TID
lookup share the thread adapter's PID communication policy. -/
def bindAffinity [DecidableEq K]
    (runtime : CpuAffinityMachine.Runtime U)
    (access : PlaceMachine.AccessConfig K (ThreadStacks.Storage U))
    (place : PlaceHooks Provenance (ThreadStacks.State K U) C MachineHooks.FrameExtra)
    (choice : C)
    (h : UnixForeign.Hooks (ThreadStacks.State K U) Place H D Other Os HM Time E Kind ReadDir DirEntry R Duration PollIter AddrIter Host System TZ Timestamp B I) :=
  let affinity := CpuAffinityMachine.bind runtime access place choice h.communicate h.environment.env.process.hostPid h.affinity.affinity
  {h with affinity := {h.affinity with affinity}}

/-- Actual macOS argc/argv cells, function-pointer resolution and late TLS
atexit registration share the existing initialized MainMachine configuration. -/
def bindMain (main : MainMachine.Hooks U C O X FnABI ArgABI Aff P)
    (h : UnixForeign.Hooks (MainMachine.State U) Place H D Other Os HM Time E Kind ReadDir DirEntry R Duration PollIter AddrIter Host System TZ Timestamp B I) :=
  {h with macos := MacOsForeignMachine.bindTls main h.macos}

/-- Common pthread keys and macOS atexit use the same initialized TLS arena,
actual source spans, compiler function identities and physical guest writes. -/
def bindTls (main : MainMachine.Hooks U C O X FnABI ArgABI Aff P)
    (place : PlaceHooks Provenance (MainMachine.State U) C MachineHooks.FrameExtra)
    (choice : C)
    (misalignment : Pointer (Option Provenance) → Align → MainMachine.M U (Option Misalignment))
    (h : UnixForeign.Hooks (MainMachine.State U) Place H D Other Os HM Time E Kind ReadDir DirEntry R Duration PollIter AddrIter Host System TZ Timestamp B I) :=
  let tls := UnixTlsMachine.hooks (UnixTlsMachine.threadData main.termination.tls) main.access place choice
    main.functions main.termination.tls.thread.spans misalignment h.tls.signatures h.tls.signature h.tls.keyLayout
  {h with tls, macos := MacOsForeignMachine.bindTls main h.macos}

/-- Dynamic functions, statics and unwind use the same function registry,
initialized extern-static map and actual thread payload stack as execution. -/
def bindDynamic (main : MainMachine.Hooks U C O X FnABI ArgABI Aff P)
    (unwind : Unwind.Hooks MiriMemoryKind (ThreadStacks.Storage U) C O) (choice : C)
    (embed : UnixDynamic.Symbol → O) (statics : U → ExternStatic.State)
    (strings : MemoryShims.Hooks Provenance (MainMachine.State U) Place (MPlaceTy Provenance) B I)
    (scanBudget : Nat)
    (h : UnixForeign.Hooks (MainMachine.State U) Place H D Other Os HM Time E Kind ReadDir DirEntry R Duration PollIter AddrIter Host System TZ Timestamp B I) :=
  let dynamic := UnixDynamic.bindStrings strings scanBudget h.dynamic
  let dynamic := UnixDynamic.bindFunctions main.functions embed dynamic
  let dynamic := UnixDynamic.bindStatics (fun user => statics user.user) dynamic
  let dynamic := UnixDynamic.bindUnwind unwind choice dynamic
  {h with dynamic, linuxPlatform := LinuxForeignMachine.bindTls main statics h.linuxPlatform}

/-- Linux-specific Zero-growth realloc closes on the same physical address
and allocation state through a checked, lawful user-record embedding. -/
def bindLinuxMemory (lens : FunctionPointers.AddressLens (ThreadStacks.Storage U) Payload)
    (allocation : UnixMemoryMachine.Hooks Payload C Host Extra) (choices : UnixMemoryMachine.Choices)
    (h : UnixForeign.Hooks (ThreadStacks.State MiriMemoryKind U) Place H D Other Os HM Time E Kind ReadDir DirEntry R Duration PollIter AddrIter Host System TZ Timestamp B I) :=
  {h with linuxPlatform := {h.linuxPlatform with memory := LinuxForeignMachine.bindReallocateVia lens allocation choices h.linuxPlatform.memory}}

/-- Final canonical chain; callers apply IO/thread/socket/compiler bindings
before this operation, so no dispatcher captures an obsolete fallback chain. -/
def bind (h : UnixForeign.Hooks (ThreadStacks.State K U) Place H D Other Os HM Time E Kind ReadDir DirEntry R Duration PollIter AddrIter Host System TZ Timestamp B I)
    (base : ForeignItems.Hooks Provenance (ThreadStacks.State K U) Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I) :=
  UnixForeign.bind h base
end Miri.Interpreter.UnixForeignMachine
