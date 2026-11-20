import Miri.Interpreter.UnixFdDispatch
import Miri.Interpreter.UnixFsDispatch
import Miri.Interpreter.PollDispatch
import Miri.Interpreter.PthreadDispatch
import Miri.Interpreter.SocketDispatch
import Miri.Interpreter.UnixEnvironmentDispatch
import Miri.Interpreter.UnixMemory
import Miri.Interpreter.UnixThreadDispatch
import Miri.Interpreter.CpuAffinityDispatch
import Miri.Interpreter.EventFdDispatch
import Miri.Interpreter.LinuxSyscallDispatch
import Miri.Interpreter.UnixRandomDispatch
import Miri.Interpreter.TimeShimDispatch
import Miri.Interpreter.StdOnlyShims
import Miri.Interpreter.FreeBsdForeign
import Miri.Interpreter.SolarishForeign
import Miri.Interpreter.NetBsdForeign
import Miri.Interpreter.MacOsForeign
import Miri.Interpreter.UnixTlsDispatch
import Miri.Interpreter.UnixFdControlDispatch
import Miri.Interpreter.UnixVectoredDispatch
import Miri.Interpreter.UnixDynamic
import Miri.Interpreter.LinuxForeign
import Miri.Interpreter.AndroidForeign

/-! Source unix/foreign_items.rs outer poll and connected Unix/OS shim chain.
Unknown arms remain NotSupported, with no invented fallback OS implementation. -/
namespace Miri.Interpreter.UnixForeign
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
abbrev FD H D O := Files.Ref (Files.Description H D O)
structure Hooks (S Place H D Other Os HM Time E Kind ReadDir DirEntry R Duration PollIter AddrIter Host System TZ Timestamp B I : Type) where
  communicate : Bool
  /-- Source poll_and_unblock(Some(Duration::ZERO)), exactly once per entry. -/
  pollAndUnblockZero : M S Unit
  pthreadBudget : Nat
  pollBudget : Nat
  environment : UnixEnvironmentDispatch.Hooks S Os E Kind
  fdControl : UnixFdControlDispatch.Hooks S H D Other E HM Place B I
  vector : UnixVectoredDispatch.Hooks S H D Other E HM Place B I
  dynamic : UnixDynamic.Hooks S Place B I
  fd : UnixFdDispatch.Hooks S H D Other E HM Os
  fs : UnixFsDispatch.Hooks S (FD H D Other) D Os HM Time E Kind H ReadDir DirEntry
  poll : PollDispatch.Hooks S (FD H D Other) PollIter
  pthread : PthreadDispatch.Hooks S R Duration
  socket : SocketDispatch.Hooks S (FD H D Other) E AddrIter
  memory : UnixMemory.Hooks Provenance S Place (MPlaceTy Provenance) B I
  tls : UnixTlsDispatch.Hooks S Place B I
  thread : UnixThreadDispatch.Hooks S Place B I
  affinity : CpuAffinityDispatch.Hooks Provenance S Place (MPlaceTy Provenance) B I
  event : EventFdDispatch.Hooks S (FD H D Other) Place (MPlaceTy Provenance) B I
  linuxPlatform : LinuxForeign.Hooks S Place H D Other E HM Os B I
  linux : LinuxSyscall.Hooks S R (FD H D Other) Place B I
  random : UnixRandomDispatch.Hooks S Place B I
  time : TimeShimDispatch.Hooks S Host System TZ Timestamp
  macos : MacOsForeign.Hooks S R Duration Os E Kind
  freebsd : FreeBsdForeign.Hooks S R Place E B I
  solarish : SolarishForeign.Hooks S (FD H D Other) PollIter Place E B I
  netbsd : NetBsdForeign.Hooks S Os E Kind Place B I
  stdOnly : StdOnlyShims.Hooks Provenance S Place (MPlaceTy Provenance) B I

/-- The FD standalone dispatcher contains its own entry poll. Inside this
source outer dispatcher that exact poll has already run; suppress only that
redundant adapter, without changing communicate or any file-operation policy. -/
private def outerPollAlreadyPerformed : M S Unit := pure ()

abbrev Handler (S : Type) := String → FnAbi Miri.MIR.TyId → Array (OpTy Provenance) →
  MPlaceTy Provenance → M S ForeignItems.EmulateItemResult
abbrev OptionalHandler (S : Type) := String → FnAbi Miri.MIR.TyId → Array (OpTy Provenance) →
  MPlaceTy Provenance → M S (Option ForeignItems.EmulateItemResult)

/-- Source-owned ordered dispatch actions. The legacy complete `Hooks` record
is one producer; the runtime source constructor can instead populate supported
components and install exact-name unavailable arms without inventing the
static fields of unrelated subsystems. -/
structure SourceDispatchers (S : Type) where
  os : String
  communicate : Bool
  validate : M S Unit
  pollAndUnblockZero : M S Unit
  environment : Handler S
  fd : Handler S
  fdControl : OptionalHandler S
  vector : OptionalHandler S
  fs : Handler S
  poll : Handler S
  pthread : Handler S
  socket : Handler S
  memory : OptionalHandler S
  thread : OptionalHandler S
  tls : OptionalHandler S
  affinity : OptionalHandler S
  event : OptionalHandler S
  linux : OptionalHandler S
  random : OptionalHandler S
  time : Handler S
  linuxPlatform : OptionalHandler S
  androidPlatform : OptionalHandler S
  dynamic : OptionalHandler S
  macos : OptionalHandler S
  freebsd : OptionalHandler S
  solarish : OptionalHandler S
  netbsd : OptionalHandler S
  stdOnly : Handler S

/-- Recognized source arms whose operation bodies have not yet been connected
to the runtime factory. The matcher is kept here beside the source-order
dispatcher so a missing port cannot silently fall through to native/MIR
resolution. These are temporary, demand-local coverage boundaries. -/
inductive SourceGap where
  | fd | fdControl | vector | fs | poll | pthread | socket | memory | thread | tls | affinity | event | linux
  | random | time | linuxPlatform | androidPlatform | dynamic | macos | freebsd
  | solarish | netbsd
  deriving DecidableEq, Repr

def gapRecognizes (group : SourceGap) (os env name : String) : Bool :=
  match group with
  | .fd => (UnixFdDispatch.parse name).isSome
  | .fdControl => name == "fcntl" || name == "ioctl"
  | .vector => #["readv","writev","preadv","pwritev"].contains name
  | .fs => (UnixFsDispatch.parse os name).isSome
  | .poll => (PollDispatch.parse os name).isSome
  | .pthread => (PthreadDispatch.parse name).isSome
  | .socket => (SocketDispatch.parseTarget os name).isSome
  | .memory => #["mmap","munmap","aligned_alloc","mprotect","madvise",
      "posix_memalign","reallocarray"].contains name
  | .thread =>
      #["pthread_create","pthread_join","pthread_detach","pthread_self","sched_yield"].contains name ||
      ((os == "linux" && name == "gettid") ||
        (os == "freebsd" && name == "pthread_getthreadid_np") ||
        (os == "macos" && name == "pthread_threadid_np") ||
        ((#["linux","freebsd","solaris","illumos","macos"].contains os) &&
          #["pthread_setname_np","pthread_getname_np"].contains name))
  | .tls => #["pthread_key_create","pthread_key_delete","pthread_getspecific",
      "pthread_setspecific","pthread_atfork"].contains name
  | .affinity => name == "sched_getaffinity" || name == "sched_setaffinity" ||
      (os == "freebsd" && name == "cpuset_getaffinity")
  | .event => (os == "linux" || os == "android") && name == "eventfd"
  | .linux => (os == "linux" || os == "android") && #["syscall","prctl"].contains name
  | .random => #["getentropy","getrandom","arc4random_buf"].contains name
  | .time => match TimeShimDispatch.parse name with
      | none => false
      | some operation =>
        let request := TimeShimDispatch.signature operation
        if operation == .machAbsolute || operation == .machTimebase || operation == .machWait then
          os == "macos"
        else if request.systemAbi then false
        else os != "windows"
  | .linuxPlatform => os == "linux" &&
      (#["pread64","pwrite64","open64","openat64","mmap64","mremap","__errno_location",
      "__libc_current_sigrtmin","__libc_current_sigrtmax"].contains name
        || (env == "gnu" && name == "__cxa_thread_atexit_impl"))
  | .androidPlatform => os == "android" && #["pread64","pwrite64","__errno","gettid"].contains name
  | .dynamic => name == "dlsym" || name == "_Unwind_RaiseException"
  | .macos => os == "macos" && #["__error","close$NOCANCEL","CCRandomGenerateBytes",
      "_NSGetArgc","_NSGetArgv","_NSGetExecutablePath","_tlv_atexit","confstr",
      "pthread_get_stackaddr_np","pthread_get_stacksize_np","pthread_cond_timedwait_relative_np",
      "os_sync_wait_on_address","os_sync_wait_on_address_with_deadline",
      "os_sync_wait_on_address_with_timeout","os_sync_wake_by_address_any",
      "os_sync_wake_by_address_all","os_unfair_lock_lock","os_unfair_lock_trylock",
      "os_unfair_lock_unlock","os_unfair_lock_assert_owner","os_unfair_lock_assert_not_owner",
      "dispatch_semaphore_create","dispatch_semaphore_wait","dispatch_semaphore_signal",
      "dispatch_release","dispatch_time"].contains name
  | .freebsd => os == "freebsd" && #["__error","_umtx_op"].contains name
  | .solarish => #["solaris","illumos"].contains os &&
      (#["___errno","stack_getbounds","pset_info"].contains name ||
        (os == "illumos" && #["epoll_create1","epoll_ctl","epoll_wait","eventfd"].contains name) ||
        (os == "solaris" && #["epoll_create1","epoll_ctl","epoll_wait","eventfd"].contains name))
  | .netbsd => os == "netbsd" && #["__errno","__unsetenv13"].contains name

def unavailableError (os env : String) (group : SourceGap) (name : String) : StepError :=
  if group == .solarish && os == "solaris" &&
      #["epoll_create1","epoll_ctl","epoll_wait","eventfd"].contains name then
    .invalidProgram "Illumos-only synchronization shim on Solaris"
  else .unsupported s!"source Unix {reprStr group} shim `{name}` is not connected to the runtime factory"

def unavailableHandler (os env : String) (group : SourceGap) : Handler S :=
  fun name _ _ _ =>
    if gapRecognizes group os env name then
      throw (unavailableError os env group name)
    else pure .NotSupported

def unavailableOptional (os env : String) (group : SourceGap) : OptionalHandler S :=
  fun name _ _ _ =>
    if gapRecognizes group os env name then
      throw (unavailableError os env group name)
    else pure none

/-- The sole source-order implementation. Both complete interpreter records
and source-owned component/gap assemblies route through this exact function. -/
def dispatchSource (h : SourceDispatchers S)
    (base : ForeignItems.Core Provenance S Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I)
    (name : String) (abi : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance))
    (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult := do
  if base.family != .unix || base.os != h.os then
    throw (.invalidProgram "Unix foreign chain target mismatch")
  h.validate
  if h.communicate then h.pollAndUnblockZero
  let result ← h.environment name abi args dest
  if result != .NotSupported then return result
  let result ← h.fd name abi args dest
  if result != .NotSupported then return result
  if let some result ← h.fdControl name abi args dest then return result
  if let some result ← h.vector name abi args dest then return result
  let result ← h.fs name abi args dest
  if result != .NotSupported then return result
  let result ← h.poll name abi args dest
  if result != .NotSupported then return result
  let result ← h.pthread name abi args dest
  if result != .NotSupported then return result
  let result ← h.socket name abi args dest
  if result != .NotSupported then return result
  if let some result ← h.memory name abi args dest then return result
  if let some result ← h.thread name abi args dest then return result
  if let some result ← h.tls name abi args dest then return result
  if let some result ← h.affinity name abi args dest then return result
  if let some result ← h.event name abi args dest then return result
  if let some result ← h.linux name abi args dest then return result
  if let some result ← h.random name abi args dest then return result
  let result ← h.time name abi args dest
  if result != .NotSupported then return result
  if let some result ← h.linuxPlatform name abi args dest then return result
  if let some result ← h.androidPlatform name abi args dest then return result
  if let some result ← h.dynamic name abi args dest then return result
  if let some result ← h.macos name abi args dest then return result
  if let some result ← h.freebsd name abi args dest then return result
  if let some result ← h.solarish name abi args dest then return result
  if let some result ← h.netbsd name abi args dest then return result
  h.stdOnly name abi args dest

/-- Assemble a source-ordered resolver when only the environment and std-only
families are currently connected. Every known Unix group is still matched at
its original source position and fails closed on demand; unrecognized symbols
continue to the ordinary foreign resolver. The initial pre-entry poll remains
an explicit Unsupported boundary whenever communication is enabled. -/
def environmentStdOnlySource
    (os targetEnv : String) (communicate : Bool)
    (environment : Handler S)
    (stdOnly : Handler S) : SourceDispatchers S :=
  let unavailable := fun group => unavailableHandler os targetEnv group
  let unavailableOptional := fun group => unavailableOptional os targetEnv group
  { os, communicate
    validate := pure ()
    pollAndUnblockZero := if communicate then
      throw (.unsupported "source Unix entry poll is not connected to the runtime factory") else pure ()
    environment
    fd := unavailable .fd
    fdControl := unavailableOptional .fdControl
    vector := unavailableOptional .vector
    fs := unavailable .fs
    poll := unavailable .poll
    pthread := unavailable .pthread
    socket := unavailable .socket
    memory := unavailableOptional .memory
    thread := unavailableOptional .thread
    tls := unavailableOptional .tls
    affinity := unavailableOptional .affinity
    event := unavailableOptional .event
    linux := unavailableOptional .linux
    random := unavailableOptional .random
    time := unavailable .time
    linuxPlatform := unavailableOptional .linuxPlatform
    androidPlatform := unavailableOptional .androidPlatform
    dynamic := unavailableOptional .dynamic
    macos := unavailableOptional .macos
    freebsd := unavailableOptional .freebsd
    solarish := unavailableOptional .solarish
    netbsd := unavailableOptional .netbsd
    stdOnly }

private def completeDispatchers
    (h : Hooks S Place H D Other Os HM Time E Kind ReadDir DirEntry R Duration PollIter AddrIter Host System TZ Timestamp B I)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I) :
    SourceDispatchers S := Id.run do
  let fd := {h.fd with pollAndUnblockZero := outerPollAlreadyPerformed}
  -- Thread/TLS only need the primitive signature operations. Keep their
  -- source-provided primitive view intact; the general ForeignItems hook is
  -- used for the other Unix families below.
  let thread := h.thread
  let memory := {h.memory with foreign := base}
  let affinity := {h.affinity with foreign := base}
  let event := {h.event with foreign := base}
  let random := {h.random with signatures := {h.random.signatures with foreign := base.toCore}}
  let linuxBase := {h.linux with signatures := {h.linux.signatures with foreign := base}}
  let linuxRandom := {linuxBase with random := h.random.random}
  let linuxEvent := {linuxRandom with event := h.event.event}
  let linux := {linuxEvent with accept4 := SocketDispatch.syscallAccept4 h.socket}
  let controlBase := {h.fdControl with signatures := {h.fdControl.signatures with foreign := base}}
  let control := {controlBase with control := {h.fdControl.control with fd := h.fd.file.fd}}
  let vectorBase := {h.vector with signatures := {h.vector.signatures with foreign := base}}
  let vector := {vectorBase with vector := {h.vector.vector with fd := h.fd.file.fd}}
  let tls := h.tls
  let linuxPlatformBase := {h.linuxPlatform with signatures := {h.linuxPlatform.signatures with foreign := base}}
  let linuxPlatformFd := {linuxPlatformBase with fd := h.fd}
  let linuxPlatformMemory := {linuxPlatformFd with memory := {h.linuxPlatform.memory with memory := h.linuxPlatform.memory.memory}}
  let linuxPlatformErrors := {linuxPlatformMemory with errors := h.environment.env.errors}
  let linuxPlatformThread := {linuxPlatformErrors with unixGettid := thread.unixGettid}
  let linuxPlatform := {linuxPlatformThread with targetEnv := h.dynamic.targetEnv}
  let dynamicSignatures : ShimSignatures.PrimitiveHooks Provenance S := {
    family := base.family
    os := base.os
    checkAbi := ForeignItems.Core.checkAbi base.toCore
    checkSymbolClash := base.checkSymbolClash
    transmute := base.transmute }
  let dynamic : UnixDynamic.Hooks S Place B I := {h.dynamic with signatures := dynamicSignatures}
  let macosSignatures : ShimSignatures.PrimitiveHooks Provenance S := dynamicSignatures
  let macosBase := {h.macos with signatures := macosSignatures, writePointer := base.writePointer}
  let macosEnv := {macosBase with environment := h.environment.env}
  let macosRandom := {macosEnv with random := h.random.random}
  let macosClose := {macosRandom with closeFd := UnixFd.close h.fd.file.fd}
  let macosPthread := {macosClose with pthread := h.pthread.pthread}
  let macosSync := {h.macos.sync with runtime := h.pthread.pthread.objects.runtime}
  let macos := {macosPthread with sync := macosSync}
  let freebsdForeign := {h.freebsd with foreign := base}
  let freebsdErrors := {freebsdForeign with errors := h.environment.env.errors}
  let freebsdSync := {h.freebsd.sync with runtime := h.pthread.pthread.objects.runtime}
  let freebsd := {freebsdErrors with sync := freebsdSync}
  let solarishForeign := {h.solarish with foreign := base}
  let solarishErrors := {solarishForeign with errors := h.environment.env.errors}
  let solarishEpoll := {solarishErrors with epoll := h.poll.epoll}
  let solarish := {solarishEpoll with event := h.event.event}
  let netbsdBase := {h.netbsd with signatures := {h.netbsd.signatures with foreign := base}}
  let netbsd := {netbsdBase with environment := h.environment.env}
  let random := {random with signatures := {random.signatures with foreign := base.toCore}}
  return {
    os := h.environment.env.os
    communicate := h.communicate
    validate := do
      if h.environment.env.env.family != .unix || h.environment.env.os != base.os ||
          h.time.time.family != .unix || h.time.time.os != base.os || h.socket.socket.os != base.os ||
          h.poll.os != base.os || h.fd.file.fd.os != base.os then
        throw (.invalidProgram "Unix foreign chain target mismatch")
      if h.communicate != h.fd.file.fd.communicate || h.communicate != h.fs.communicate ||
          h.communicate != h.socket.socket.communicate || h.communicate != h.poll.communicate ||
          h.communicate != h.environment.env.process.communicate || h.communicate != h.random.random.communicate then
        throw (.invalidProgram "Unix foreign chain communication policy mismatch")
    pollAndUnblockZero := h.pollAndUnblockZero
    environment := UnixEnvironmentDispatch.dispatch h.environment
    fd := UnixFdDispatch.dispatch fd
    fdControl := fun name abi args dest => UnixFdControlDispatch.emulate control name abi args dest
    vector := fun name abi args dest => UnixVectoredDispatch.emulate vector name abi args dest
    fs := UnixFsDispatch.dispatch h.fs
    poll := PollDispatch.dispatch h.pollBudget h.poll
    pthread := PthreadDispatch.dispatch h.pthreadBudget h.pthread
    socket := SocketDispatch.dispatch h.socket
    memory := fun name abi args dest => UnixMemory.emulate memory name abi args dest
    thread := fun name abi args dest => UnixThreadDispatch.emulate thread name abi args dest
    tls := fun name abi args dest => UnixTlsDispatch.emulate tls name abi args dest
    affinity := fun name abi args dest => CpuAffinityDispatch.emulate affinity name abi args dest
    event := fun name abi args dest => EventFdDispatch.emulate event name abi args dest
    linux := fun name abi args dest => LinuxSyscallDispatch.emulate linux name abi args dest
    random := fun name abi args dest => UnixRandomDispatch.emulate random name abi args dest
    time := TimeShimDispatch.dispatch h.time
    linuxPlatform := fun name abi args dest => LinuxForeign.emulate linuxPlatform name abi args dest
    androidPlatform := fun name abi args dest => AndroidForeign.emulate linuxPlatform name abi args dest
    dynamic := fun name abi args dest =>
      @UnixDynamic.emulate Place S B I dynamic name abi args dest
    macos := fun name abi args dest => MacOsForeign.emulate macos name abi args dest
    freebsd := fun name abi args dest => FreeBsdForeign.emulate freebsd name abi args dest
    solarish := fun name abi args dest => SolarishForeign.emulate solarish name abi args dest
    netbsd := fun name abi args dest => NetBsdForeign.emulate netbsd name abi args dest
    stdOnly := StdOnlyShims.unix {h.stdOnly with foreign := base.toCore} }

def dispatch (h : Hooks S Place H D Other Os HM Time E Kind ReadDir DirEntry R Duration PollIter AddrIter Host System TZ Timestamp B I)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I)
    (name : String) (abi : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance))
    (dest : MPlaceTy Provenance) : M S ForeignItems.EmulateItemResult :=
  dispatchSource (completeDispatchers h base) base.toCore name abi args dest

/-- Bind a source-owned ordered dispatch chain while preserving the common
ForeignItems core and all non-Unix callback arms. This is the construction
boundary used by canonical runtime factories. -/
def bindSource (h : SourceDispatchers S)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance)
      (Pointer (Option Provenance)) B I) :
    ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance)
      (Pointer (Option Provenance)) B I :=
  {base with unix := fun name abi args dest =>
    dispatchSource h base.toCore name abi args dest}

/-- No nested fallback chain; the outer foreign resolver owns missing/native/MIR
behavior after a terminal NotSupported platform response. -/
def bind (h : Hooks S Place H D Other Os HM Time E Kind ReadDir DirEntry R Duration PollIter AddrIter Host System TZ Timestamp B I)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I) :=
  {base with unix := dispatch h base}
/-- Resolve FnVal::Other through this same source foreign dispatcher, including
normal return/unwind control transfer. Dynamic symbols cannot delegate to MIR. -/
def dynamicCall (h : Hooks S Place H D Other Os HM Time E Kind ReadDir DirEntry R Duration PollIter AddrIter Host System TZ Timestamp B I)
    (base : ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I)
    (symbol : UnixDynamic.Symbol) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : Place) (ret : Option Miri.MIR.BasicBlockId)
    (unwind : Miri.MIR.UnwindAction) : M S Unit :=
  ForeignItems.emulateDynSym (bind h base) symbol.name abi args dest ret unwind
end Miri.Interpreter.UnixForeign
