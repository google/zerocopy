# POSIX processes, signals, `fork`, and the flat address space: historical contingency versus real constraint

## Summary

The POSIX process bundles five things that later systems separate: an address space, a table of untyped integer descriptors, a table of signal dispositions, a set of process-wide mutable cells (working directory, `umask`, environment), and the user's whole authority. Each was cheap and adequate for one single-threaded C program on a small machine. Each collides with a modern process that hosts several threads and several language runtimes.

What to retain:

- `fork()` copies one thread and the whole address space, including mutexes held by threads that do not exist in the child. POSIX.1-2024 says the child of a multi-threaded process may only perform async-signal-safe operations until `exec`, marks `pthread_atfork` obsolescent, and adds `_Fork()`. Mature runtimes examined here no longer fork freely: glibc `posix_spawn`, Go, and OpenJDK use `clone(CLONE_VM|CLONE_VFORK)` or `posix_spawn`; CPython warns and changed its `multiprocessing` default.
- Signal dispositions are per process; masks are per thread. There is no kernel arbiter between two runtimes that both need `SIGSEGV`. Each runtime publishes its own chaining convention.
- `SA_RESTART` changes exactly one of Linux's four internal restart codes. It removes many `EINTR` results but never short counts, so every caller still needs an offset-advancing retry loop.
- One address space has no reservation protocol. Runtimes with fixed layouts (sanitizer shadows) and runtimes with preferred addresses (Go heap hints, JVM compressed-oops bases, V8 cages) are reconciled only by start-up order and hint fallback.
- `openat(dirfd, …)` is a starting point, not a boundary; `O_NOFOLLOW` protects one path component. Confinement needs `RESOLVE_BENEATH`-style resolution or a handle-only namespace.
- On macOS, Windows, OpenBSD, illumos and Fuchsia the documented stable interface is a library, not the trap instruction. Linux documents the syscall interface itself as stable.
- Plan 9, Capsicum, Zircon, Singularity and WASI each remove a different subset of the bundle. None removes all of it while keeping POSIX compatibility.

How far the evidence goes: the specification and source statements were read at the pinned revisions listed under Evidence. The support probe observed 25 behaviours on one Linux x86-64 host and computed 33 results from small models. Every claim about two runtimes sharing one process (JVM with Go, a sanitizer with Go or the JVM) is derived from each side's source; no such combination was executed.

## Applicability

Scope: the process, signal, descriptor, path and address-space interfaces of POSIX.1-2024 and their realisation in Linux (pinned development tree, `Makefile` version 7.4-rc3), with comparison points in FreeBSD, OpenBSD, illumos, Plan 9, Fuchsia and WASI, and with consumer-side evidence from glibc, Go, OpenJDK HotSpot, CPython, LLVM compiler-rt sanitizers and V8.

How the subjects in `REPORT.json` relate:

- POSIX.1-2024 is the normative text. Linux, FreeBSD, OpenBSD and illumos sources show what kernels implement. The language runtimes show what consumers do about it.
- The papers (Ritchie; Baumann et al.; Pike et al.; Watson et al.; Hunt & Larus; Gabriel) supply history and design rationale. Their measurements are theirs and were not reproduced.
- Two WASI revisions are listed: tag `v0.2.12` (the 0.2 "Preview 2" line, `wasi:filesystem@0.2.12`) and the default branch (`wasi:filesystem@0.3.2`). The capability statements quoted here are present in both; `docs/DesignPrinciples.md` and `proposals/filesystem/path-resolution.md` are byte-identical between them.

Limits on applicability:

- Architecture-specific facts (signal restart code, ASan layout, Go heap hints, syscall number 437) are for Linux x86-64 unless stated. Other architectures use different sanitizer offsets and Go hint formulas.
- Live observations come from one host: Linux 7.1.6 x86-64, CPython 3.13.15, glibc. They are not evidence about macOS, the BSDs or other kernels.
- The man-pages mirror is from 2021-09-01, five years older than the kernel revision. Its per-syscall restart lists are documentation of that period, not a statement about the pinned kernel.
- The glibc and man-pages repositories are GitHub mirrors of projects hosted elsewhere.

Related packages in this corpus, not repeated here: `os-syscall-interfaces-asynchronous-signals-and-environment-models` covers the Rust standard library's syscall and signal mechanics and verified-compiler environment models; `sfi-foundational-extensible-kernels-1993-2011` covers software fault isolation and exokernels; `metal-typechain-language-isolated-kernels-1995-2026` covers Singularity's channel contracts and exchange heap in type-system detail. This report supplies the OS-interface history and cross-runtime collisions those packages take as given.

## Findings

### 1. `fork()`: why it was cheap, and what it now copies

Origin. Ritchie records that process control "in its modern form was designed and implemented within a couple of days", that the system "already handled multiple (i.e. two) processes" by swapping, and that "the PDP-7's fork call required precisely 27 lines of assembly code". A combined fork-exec "would have been considerably more complicated, if only because exec as such did not exist". The first PDP-11 system had "24K bytes of core memory (16K for the system, 8K for user programs)". The 27-line figure is for the PDP-7, not the PDP-11.

Current normative text (POSIX.1-2024 `fork`):

> A process shall be created with a single thread. If a multi-threaded process calls fork(), the new process shall contain a replica of the calling thread and its entire address space, possibly including the states of mutexes and other resources. Consequently, the application shall ensure that the child process only executes async-signal-safe operations until such time as one of the exec functions is successful.

and, for locks not marked process-shared, "any attempt by the child process to perform any operation on the lock results in undefined behavior (regardless of whether the calling process is single-threaded or multi-threaded)".

Issue 8 changes recorded on that page: `_Fork()` added (equivalent to `fork()` but runs no atfork handlers and is async-signal-safe); the requirement that `fork()` be async-signal-safe removed; `FD_CLOFORK` added. `forkall()` was considered and rejected. `vfork` has no entry in the Issue 8 function index.

`pthread_atfork` is marked obsolescent. Its rationale states the intended pattern (prepare locks everything, parent and child unlock) and why it fails: "Each and every mutex and lock in the process must be located and locked. Every component of a program including third-party components must participate"; the unlocking functions are not async-signal-safe; and if the forking thread already holds a stream lock "the process will deadlock". Reinitialising mutexes in the child "does not resolve the question about how to correct or otherwise deal with the inconsistent state".

Linux implementation at the pinned revision (`kernel/fork.c`):

| Entry | Flags | Lines |
| --- | --- | --- |
| `fork` | none, `exit_signal = SIGCHLD`; returns `-EINVAL` without an MMU ("can not support in nommu mode") | 2879-2892 |
| `vfork` | `CLONE_VFORK \| CLONE_VM` | 2895-2904 |
| `copy_mm` | shares the `mm` under `CLONE_VM`, otherwise `dup_mm` | 1575-1611 |
| `copy_sighand` | shares the handler table under `CLONE_SIGHAND`, otherwise copies it | 1707-1730 |
| flag constraints | `CLONE_THREAD` requires `CLONE_SIGHAND`, which requires `CLONE_VM` | 2052-2065 |

What consumers do at the pinned revisions:

| Consumer | Mechanism | Source |
| --- | --- | --- |
| glibc `fork` | multi-threaded case takes stdio and malloc arena locks before `_Fork()`, re-initialises them in the child | `posix/fork.c:40-100`, `malloc/arena.c:166-210` |
| glibc `posix_spawn` | `clone` with `CLONE_VM \| CLONE_VFORK` on a separately allocated stack, all signals blocked in the child | `sysdeps/unix/sysv/linux/spawni.c:31-45, 389-407` |
| Go `syscall.forkExec` | adds `CLONE_VFORK \| CLONE_VM` unless a user namespace is requested; child code "must not acquire any locks … no rescheduling, no malloc calls, and no new stack segments" | `src/syscall/exec_linux.go:138-143, 318-320` |
| OpenJDK | `posix_spawn` of a helper binary by default "on all Unices including Linux"; `FORK` kept as backup; `VFORK` mode removed (comment says JDK 27) | `ProcessImpl_md.c:56-123`, `ProcessImpl.java:82-109` |
| CPython | `os.fork()` in a multi-threaded process raises `DeprecationWarning`; `multiprocessing` default is `forkserver` on POSIX since 3.14 and `spawn` on macOS since 3.8 | `Modules/posixmodule.c:8502-8560`, `Doc/library/multiprocessing.rst:139-194` |
| illumos libc | `posix_spawn` calls a `spawn` system call that "creates a brand-new child process that does not share the parent's address space"; `forkall()` exists and replicates every thread | `usr/src/lib/libc/port/threads/spawn.c:280-338`, `usr/src/man/man2/fork.2:358-381` |

illumos shows that the replicate-all-threads semantics POSIX rejected is implementable; its manual still warns that `fork()` followed by more than `exec` risks deadlock.

Baumann et al. list the structural objections: `fork` is no longer simple (they count 25 special cases in the then-current POSIX text), does not compose with user-level buffering, is not thread-safe, inherits everything by default, defeats ASLR when not followed by `exec`, and cannot be implemented in a single address space. Their Figure 1 reports `posix_spawn` at about 0.5 ms independent of parent size against `fork`+`exec` growing with parent size on their test machine. Those numbers were not re-measured here.

Probe results. Model: with two workers inside library critical sections and a third thread forking, 21 of 25 fork snapshots leave a child that blocks forever if it touches those libraries; a child restricted to lock-free operations completes in 25 of 25; forcibly reinitialising mutexes removes the deadlocks but exposes a half-updated structure in 9 of 25; atfork handlers for one of two libraries still deadlock in 6 of 10; handlers for every lock in one global order are safe (4 of 4); a prepare order that disagrees with one library's nesting deadlocks the parent; forking from inside a registered critical section never reaches `fork`. Live: the forked child had one thread, could not acquire a lock held by another parent thread within 0.4 s, and had the same libc base and stack range as the parent; CPython emitted the warning; a `posix_spawn` child started single-threaded and with a different layout.

Basis: normative (POSIX.1-2024) + documentation (Ritchie; Baumann et al.; illumos manual) + source (Linux, glibc, Go, OpenJDK, CPython, illumos) + execution (six live rows on one Linux host) + derived (model rows; the model's lock programs are illustrative, not extracted from any library).

### 2. Copy-on-write, overcommit, and allocation failure

`dup_mmap` walks every VMA of the parent. For each accountable mapping it charges the full length against the commit policy before copying page tables (`mm/mmap.c:1708-1818`, charge at 1749-1755). The policy function `__vm_enough_memory` (`mm/util.c:972-1010`) returns success unconditionally under `OVERCOMMIT_ALWAYS`; under `OVERCOMMIT_GUESS`, the compiled-in default (`mm/util.c:794`), it refuses only a single request larger than RAM plus swap; only `OVERCOMMIT_NEVER` compares against a commit limit. `Documentation/mm/overcommit-accounting.rst` describes mode 0 as "Obvious overcommits of address space are refused" and mode 2 as the one where "a process will not be killed while accessing pages but will receive errors on memory allocation".

Baumann et al. argue that copy-on-write `fork` "strongly encourages" overcommit, because conservative accounting must fail a `fork` whose worst case cannot be backed even when the child immediately `exec`s. The kernel source confirms the accounting hook exists on the fork path and that the default policy does not enforce a commit limit. It does not by itself show that `fork` was the reason for that default.

Consequence for language semantics: under the default policy an allocation can succeed and the failure surface later as a kill at first touch. No out-of-memory condition was provoked in this investigation.

Basis: source (Linux) + documentation (kernel overcommit document; Baumann et al.) + derived (the consequence for allocation-failure semantics).

### 3. Signals: process-wide dispositions, per-thread masks, a small safe set

POSIX.1-2024 XSH 2.4.1: "Each process has an action to be taken in response to each signal" and "Each thread has a 'signal mask'". Signals caused by a thread's own fault are generated for that thread; those tied to a process ID or an asynchronous event are generated for the process and delivered to "exactly one" eligible thread.

Linux mirrors this: `struct sighand_struct` holds `action[_NSIG]` and is shared by every task created with `CLONE_SIGHAND` (`include/linux/sched/signal.h:22-27`); `exec` resets handlers through `flush_signal_handlers` (`kernel/signal.c:526-540`, called at `fs/exec.c:1298`).

Async-signal-safe set. The table in XSH 2.4.3 contains 231 function names in the Issue 8 HTML edition; the XSH function index lists 1,227. Both counts were taken twice by independent text extraction from the fetched pages and agree, but they are counts over a rendered page, not over the standard's source. `_Fork`, `execve`, `write`, `sem_post`, `sigaction` are in the table; `fork`, `malloc`, `free`, `printf`, `pthread_mutex_lock`, `pthread_mutex_unlock`, `posix_spawn` are not. After a handler interrupts an unsafe function and calls an unsafe function, "the behavior is undefined".

Restart behaviour. Linux kernel code returns one of four internal codes (`include/linux/errno.h:14-18`), translated on the way out (`arch/x86/kernel/signal.c:255-281` with a handler, `333-359` without):

| Internal code | Handler, no `SA_RESTART` | Handler, `SA_RESTART` | No handler runs |
| --- | --- | --- | --- |
| `ERESTARTSYS` | `EINTR` | restart | restart |
| `ERESTARTNOINTR` | restart | restart | restart |
| `ERESTARTNOHAND` | `EINTR` | `EINTR` | restart |
| `ERESTART_RESTARTBLOCK` | `EINTR` | `EINTR` | restart via `restart_syscall` |

"Restart" is `regs->ax = regs->orig_ax; regs->ip -= 2`: the user program counter is moved back over the two-byte syscall instruction. That is the back-out strategy Gabriel's essay calls "PC loser-ing" and attributes to ITS, contrasted with the Unix choice that "sometimes an error code would be returned". Linux thus implements the back-out for some calls and the error code for others. This reading of the essay against the kernel code is this report's, not a statement found in either.

The 2021 `signal(7)` text lists calls that restart under `SA_RESTART` (reads and writes on slow devices, `wait*`, socket calls without a timeout, `flock`, `FUTEX_WAIT`, others) and calls that "are never restarted … regardless of the use of SA_RESTART" (socket calls with a timeout set, `pause`, `sigsuspend`, `poll`, `select`, `epoll_wait`, System V IPC, `nanosleep`, `io_getevents`). It also states that an I/O call that already transferred data returns the count transferred.

Runtime evidence that the flag is insufficient: Go installs its handlers with `SA_RESTART` (`src/runtime/os_linux.go:481`) and still wraps calls in a retry loop, with the comment "This appears to be required even though we install all signal handlers with SA_RESTART … it seems that we can't avoid an EINTR loop" (`src/os/file_posix.go:254-268`). CPython installs handlers with `SA_ONSTACK` and without `SA_RESTART` (`Python/pylifecycle.c:4039-4048`).

Probe results. Live: `SigCgt` was identical in two tasks of one process while `SigBlk` differed after one thread blocked `SIGUSR1`; `sa_flags` for a CPython-installed handler read `0x0c000000` and `siginterrupt(sig, False)` changed it to `0x1c000000`; a blocking `read(2)` on an empty pipe returned `EINTR` in the first configuration and was restarted in the second. This observes the `ERESTARTSYS` row only. The other three rows of the table are source reading; the probe's copy of the table is a transcription and is reported as such, not as a check. Model: a handler that takes the interrupted code's lock deadlocks at 3 of 5 interruption points; with a recursive lock it reads a half-updated structure at 1 of 5; a handler limited to a flag write completes at 5 of 5. For a 4-byte write over all 35 kernel schedules of depth 3, a single call loses data in 31 schedules with or without `SA_RESTART`; the offset-advancing loop loses none.

Basis: normative (POSIX.1-2024) + source (Linux; Go; CPython) + documentation (`signal(7)` as of 2021; Gabriel) + execution (six live rows, one host) + derived (model rows; the PC loser-ing comparison).

### 4. Several runtimes, one disposition table

Each runtime examined claims signals for its own correctness and documents what co-tenants must do.

| Runtime | Signals it depends on (from the cited source) | Demand on other code |
| --- | --- | --- |
| HotSpot | `SIGSEGV` for safepoint polls and implicit null checks; `SIGFPE` for implicit divide checks; `SIGUSR2` as suspend/resume signal (`os_linux_x86.cpp:258-285`, `signals_posix.cpp:178`) | Aborts on an "unexpected pre-existing sigaction handler" unless chaining or `AllowUserSignalHandlers` is enabled (`signals_posix.cpp:1286-1306`); chaining works by `libjsig` interposing `sigaction()` (`libjsig/jsig.c`). User code "would be making a serious error if it tried to handle an exception … that the VM was generating for its own correct operation" (`signals_posix.cpp:525-542`). |
| Go | `SIGURG` for goroutine preemption (`signal_unix.go:44-74`); `SIGSEGV`, `SIGBUS`, `SIGFPE` for run-time panics | Non-Go handlers "must use the SA_ONSTACK flag"; a non-Go handler for a synchronous signal "should record the existing Go signal handler" and call it when the faulting PC is in Go code; non-Go code "should not change the signal mask on any threads created by the Go runtime" (`os/signal/doc.go:113-172`). |
| CPython | whatever the program registers | Sets `SA_ONSTACK` because that "is friendlier to other C/C++/Golang-VM code" (`pylifecycle.c:4042-4045`). |

Go's choice of `SIGURG` is explained in source as a search for a signal that debuggers pass through, libc does not use internally, can occur spuriously without harm, and exists without real-time signals; the comment opens "There's no good way to choose this signal".

Finding: these are bilateral conventions. HotSpot's chaining relies on symbol interposition of `sigaction`; Go's relies on the other party saving and forwarding to the previous handler based on PC range; each assumes it can identify its own faults. Nothing in POSIX or the kernel multiplexes one signal number among several owners. Whether a given pair of runtimes composes depends on load order and on both following the other's convention.

This finding is derived from reading each runtime's contract. No process embedding two of these runtimes was built or run, so no specific failure is claimed.

Basis: source (OpenJDK, Go, CPython) + derived (the composition argument).

### 5. One address space, no reservation protocol

Fixed layouts and preferred addresses at the pinned revisions (Linux x86-64 unless noted):

| Tenant | Demand | Source |
| --- | --- | --- |
| ASan | `LowMem [0, 0x7fff7fff]`, `LowShadow [0x7fff8000, 0x8fff6fff]`, `ShadowGap [0x8fff7000, 0x02008fff6fff]`, `HighShadow [0x02008fff7000, 0x10007fff7fff]`, `HighMem [0x10007fff8000, 0x7fffffffffff]` | `compiler-rt/lib/asan/asan_mapping.h:21-26` |
| TSan with Go | heap must lie in `[0x00c000000000, 0x00e000000000)`; shadow at `0x200000000000` | `compiler-rt/lib/tsan/rtl/tsan_platform.h:506-523` |
| Go heap | 128 hints `(i << 40) \| 0x00c000000000`, tried in order until the kernel returns exactly the hinted address; race mode restricts to the TSan window | `src/runtime/malloc.go:477-592, 740-751` |
| HotSpot compressed oops | mode 0 needs the heap end below 4 GiB, mode 1 below 32 GiB (zero base), mode 2 a 32 GiB-aligned base, mode 3 an arbitrary base | `src/hotspot/share/oops/compressedOops.hpp:55-72` |
| V8 | 4 GiB pointer-compression cage with 4 GiB alignment; sandbox of 2^40 bytes by default, 2^37 where user address space is 39 bits, 2^34 on iOS | `include/v8-internal.h:167-168, 218-251` |

The Go window appears in two repositories: the Go comment says "The TSAN runtime requires the heap to be in the range [0x00c000000000, 0x00e000000000)" and the TSan header's Go mapping lists `00c0 0000 0000 - 00e0 0000 0000: heap`. The agreement is maintained by hand on both sides. The Go source also records a collision directly: "0x00c0 causes conflicts with AddressSanitizer which reserves all memory up to 0x0100."

Derived arithmetic from those constants (computed by the probe; the probe does not read upstream, so it cannot detect drift in the constants):

- The five ASan regions tile `[0, 2^47)` exactly; shadow plus gap is 2^44 bytes (16 TiB).
- Go's first default hint, `0x00c000000000`, is inside `ShadowGap`. Hints 0 through 15 fall in `ShadowGap` or `HighShadow`; hint 16 (`0x10c000000000`) is the first in `HighMem`.
- The race-mode window lies entirely inside ASan's `ShadowGap`.
- Of the 32 GiB window that zero-based compressed oops need, only `LowMem` (2 GiB minus 32 KiB, 6.25%) is application memory under the ASan layout.
- In a first-come interval model, if the fixed-layout tenant initialises first the hinting runtime lands on hint 16; if the hinting runtime initialises first the fixed-layout tenant cannot place its shadow.

These are statements about address ranges. No Go, JVM or V8 binary was run under a sanitizer, so the actual behaviour of those combinations (for example whether a given build disables a mode or picks another base) is not established here.

When the kernel's layout randomisation changes, a fixed-layout runtime has one remedy in source: ASan's `TryReExecWithoutASLR` prints "memory layout is incompatible, possibly due to high-entropy ASLR", sets `ADDR_NO_RANDOMIZE` with `personality`, and re-executes the process (`compiler-rt/lib/asan/asan_linux.cpp:122-151`). The same message strings appear in the TSan and MSan Linux platform files.

Live observations: mappings in `/proc/self/maps` were disjoint and sorted with the highest address using 47 bits; program, libraries, heap, stack and `[vdso]` shared the range; a second thread saw the same file-backed and stack ranges. An `mmap` hint at an occupied address was relocated without error; `MAP_FIXED_NOREPLACE` returned `EEXIST`; `MAP_FIXED` replaced the existing pages (a byte written earlier read back as zero).

Basis: source (LLVM, Go, OpenJDK, V8) + execution (six live rows about `/proc` and `mmap` only) + derived (all cross-tenant arithmetic and the ordering model).

### 6. Paths, descriptors, and completion-based I/O

Process-wide cells. The working directory and `umask` are single values per process. Two threads that each `chdir` and then open a relative name interfere in 4 of 6 interleavings in the probe's model; per-thread directory handles with `openat` do not.

Path confinement. Linux `openat2` defines `RESOLVE_BENEATH` as "Block 'lexical' trickery like '..', symlinks, and absolute paths which escape the dirfd" (`include/uapi/linux/openat2.h:39-41`). The walker returns `-EXDEV` on a jump to the root and `-EAGAIN` when "there was a racing rename or mount along our path" so that `..` cannot be shown to stay inside (`fs/namei.c:1138-1141, 2254-2267`). The WASI filesystem notes say the same of the plain call: "Plain `openat` doesn't perform any sandboxing … It has an `O_NOFOLLOW` flag, however this flag only applies to the last component".

Live on one Linux host: `openat(dirfd, "../secret.txt")` succeeded; `O_NOFOLLOW` returned `ELOOP` for a final-component symlink but followed a directory symlink in a non-final component; `openat2` with `RESOLVE_BENEATH` returned `EXDEV` for all five escape attempts and succeeded for `inside.txt` and `sub/../inside.txt`. Model over 41,580 enumerated paths on a ten-entry tree: plain resolution escapes for 272, `O_NOFOLLOW` for 215, beneath-style resolution for none (67 successes), and a component-by-component `O_NOFOLLOW` walk with a directory stack gives the same result as beneath-style resolution on every path. The model has no concurrent renames; the kernel's `-EAGAIN` path exists because that case is not equivalent.

Check-then-use. Checking a path and then using the path admits one bad interleaving of three against a single rename; opening first and checking the descriptor admits none of four.

Descriptors. Numbers are allocated lowest-free from a starting point (`fs/file.c:621-641`, `find_next_fd`; observed live: closing a descriptor and opening again returned the same number), so a stale integer silently names a different object. `ioctl` takes `(fd, unsigned int cmd, unsigned long arg)` and dispatches on the file's type (`fs/ioctl.c:584-601`); the meaning of `arg` is fixed only by convention between caller and driver.

Completion-based I/O. `struct io_rings` "is shared with the application through the mmap"; "The kernel controls head of the sq ring and the tail of the cq ring, and the application controls tail of the sq ring and the head of the cq ring" (`include/linux/io_uring_types.h:188-203`). The UAPI enum has 65 opcodes before `IORING_OP_LAST`. For zero-copy send the liburing manual states "The user must not modify the data buffer until the notification is posted". A buffer handed to an in-flight operation is therefore borrowed by the kernel until a completion arrives, not until the submitting call returns. In the probe's five-event model, freeing the buffer at scope exit after requesting cancellation allows one interleaving in which the kernel writes into freed memory; waiting for the completion allows none. That model is a reasoning aid; no `io_uring` instance was created.

Basis: source (Linux) + documentation (WASI notes; liburing manual) + execution (seven live rows, one host) + derived (model rows).

### 7. Where the stable interface actually is

| System | Documented position | Evidence |
| --- | --- | --- |
| Linux | "The kernel syscall interface … will only be added to over time, and not have things removed from it" | `Documentation/ABI/stable/syscalls` |
| macOS | "A statically linked binary assumes binary compatibility at the kernel system call interface, and we do not make any guarantees on that front" | Apple QA1118 (2011) |
| Windows | "The functions and structures in Winternl.h are internal to the operating system and subject to change from one release of Windows to the next … you should use the equivalent public functions instead" | Microsoft Learn, Calling Internal APIs |
| OpenBSD | each syscall number must be entered from one registered address, else `SIGABRT`; `pinsyscalls` "first appeared in OpenBSD 7.5" | `sys/sys/syscall_mi.h:55-125`, `lib/libc/sys/pinsyscalls.2` |
| illumos | "A system call is a C library function that requests a service from the system" | `usr/src/man/man2/Intro.2:19-22` |
| Fuchsia | "The vDSO entry points are the only means to enter the kernel … `syscall` on x86 … are not part of the system ABI" | `docs/concepts/kernel/vdso.md:207-211` |

The Windows statement concerns the native API declared in `Winternl.h` (implemented in `ntdll.dll`). Microsoft documents that layer as internal and directs applications to the public Win32 functions. So the stable layer on Windows is above `ntdll`, not `ntdll` itself.

Go follows these rules at the pinned revision: it imports from `/usr/lib/libSystem.B.dylib` on Darwin (`runtime/sys_darwin.go:579-599`), calls libc through trampolines on OpenBSD (`runtime/sys_openbsd.go`), imports from `libc.so` on Solaris and illumos (`runtime/os3_solaris.go:18-25`), and from `kernel32.dll` on Windows (`runtime/os_windows.go`).

Consequence: outside Linux, a language runtime inherits the platform C library's process-global state (its allocator, its atfork handlers, its signal use) whether or not it is written in C.

Basis: documentation (kernel ABI file; Apple; Microsoft; OpenBSD and illumos manuals; Fuchsia docs) + source (OpenBSD `pin_check`; Go) + derived (the consequence).

### 8. Designs that unbundle the process

| System | What it changes | What it keeps | Evidence |
| --- | --- | --- | --- |
| Plan 9 | `rfork(flags)` chooses per resource (name space, environment, descriptor table, note group, memory) whether the child shares, copies or starts clean; name spaces are per process; "Plan 9 has no super-user" | Creation still starts from the caller ("Forking is the only way new processes are created"); `fork` is `rfork(RFFDG\|RFREND\|RFPROC)`; asynchronous *notes* with handlers remain | `sys/man/2/fork`, `sys/include/libc.h:592-603`, `sys/src/9/port/sysproc.c:25-55`, `sys/man/2/notify`; Pike et al. |
| Capsicum | `cap_enter` sets a credential flag after which "Access to global name spaces … is prevented"; rights on a descriptor can only be reduced; lookups must start from a real descriptor with a relative path | The Unix process, `fork`, signals and descriptors; it is opt-in per program | `sys/kern/sys_capability.c:38-59, 101-134, 252-282`, `sys/kern/vfs_lookup.c:380-406`, `cap_enter(2)`; Watson et al. |
| Zircon | objects are reached "almost exclusively via Handles" carrying rights; `zx_process_create(job, …)` returns an empty process and its root address-space handle; "There is no ambient authority"; faults arrive as messages on an exception channel | 32-bit integer handle values in user space; a vDSO as the mandatory call path | `docs/concepts/kernel/concepts.md`, `namespaces.md:33-76`, `exceptions.md:15-28`, `zircon/vdso/process.fidl:52-153` |
| Singularity | software-isolated processes are "closed object spaces" and "sealed code spaces"; communication transfers exclusive ownership over contract-typed channels; processes may share ring 0 with the kernel | A kernel ABI (192 functions in the paper's Table 2) | Hunt & Larus |
| WASI 0.2 | "WASI has no *ambient authorities*"; every path operation takes a `descriptor` and a relative path and fails with `not-permitted` on escape; initial directories come from `preopens.get-directories` | POSIX-shaped file operations; path strings within a subtree | `proposals/filesystem/wit/types.wit:15-25, 300, 543-552`, `preopens.wit:10`, `docs/DesignPrinciples.md:5-23` |

Details that matter when borrowing from these:

- Plan 9 is a counterexample for name spaces and for explicit inheritance, not for asynchronous notification. `rfork` still runs caller code in the child.
- Capsicum's paper (2010) describes rejecting paths that contain `..` as "a conservative design". The pinned FreeBSD source enables `..` by default (`lookup_cap_dotdot = 1`) and rejects only a `..` that would walk over the starting directory (`nameicap_check_dotdot`, `vfs_lookup.c:268-308`). The paper reports "roughly 60 possible mask rights", about ten lines to sandbox `tcpdump` and about 100 for Chromium; those figures are the authors'.
- `cap_enter` stops the process's other threads while it runs and returns `EBUSY` if the descriptor table or working directory is shared with another process.
- Singularity's cost figures (Table 1: process creation 388,000 cycles against 719,000 for Linux; the WebFiles slowdowns of 6.3%, 18.9%, 33% and 37.7% as hardware isolation is added) are measurements from 2007 hardware in the authors' own system.
- The WASI `cli` world at `v0.2.12` imports clocks, filesystem, sockets, random, I/O, environment, exit and standard streams. A text search of the 0.2.12 WIT files found no process-creation or signal interface.

None of these systems was run. The table records what their documentation and source say.

Basis: documentation (papers; manuals; Fuchsia and WASI documents) + source (Plan 9, FreeBSD, Fuchsia FIDL, WASI WIT).

### 9. Contingent versus still-required

| Inherited feature | Contingent origin | Requirement any replacement must still meet |
| --- | --- | --- |
| `fork` as the creation primitive | Easy to add to a swapping PDP-7 kernel (Ritchie) | Cheap creation; a way to configure the child before it runs; snapshotting where wanted |
| Inherit everything by default | Follows from copying the image | Explicit, enumerable delegation of descriptors and authority |
| Process-wide signal table | One C program per process | Synchronous faults must reach a handler; blocked threads must be interruptible |
| `EINTR` | Simpler kernel exit path (Gabriel) | Cancellation and timeouts with defined partial-progress results |
| Global path strings, cwd, `umask` | Single-user-per-process protection model | Human-meaningful naming; delegation of subtrees |
| Lowest-free integer descriptors, `ioctl` | Uniform byte-stream simplification | Language-neutral object references; typed operations |
| Trap numbers as ABI | Linux-specific choice | Vendors need a boundary they can evolve |
| Flat address space with ad-hoc reservations | No concept of multiple runtimes per process | Large sparse reservations are useful; they need an owner |

The right-hand column is this report's synthesis from the findings above; it is an argument, not a result.

Basis: derived (from sections 1 through 8).

## Boundaries

Not examined:

- No two language runtimes were run in one process. JVM with Go, Go under ASan, the JVM under ASan and V8 under any sanitizer are analysed from constants and documented contracts only.
- No out-of-memory kill, `fork` latency or page-table copy cost was measured. Figures from Baumann et al. and Hunt & Larus are quoted, not reproduced.
- `io_uring` was not exercised. No ring was created and no buffer-lifetime bug was triggered.
- FreeBSD, OpenBSD, illumos, Plan 9, Fuchsia and any WASI host were not run. Capsicum's `cap_enter`, OpenBSD's `pin_check` and Zircon's vDSO enforcement are source and documentation readings.
- Oracle Solaris itself. Only illumos manual pages and Go's Solaris port were read. Whether Oracle documents the trap interface as private was not confirmed from an Oracle source.
- Windows system-call numbering across builds. Only Microsoft's statement about `Winternl.h` was read.
- macOS behaviour of `fork` with Objective-C or system frameworks, GPU driver state across `fork`, and garbage-collector safepoint locks. These are commonly cited hazards; no source for them was pinned here.
- `clone3`, `CLONE_PIDFD`, `pidfd`, `signalfd`, `userfaultfd` and restartable sequences as mitigations.
- Architectures other than x86-64 for the restart code, sanitizer layout and Go hint formulas.

Unknown:

- Whether the per-syscall restart lists in the 2021 `signal(7)` text still describe the pinned kernel. The mechanism was read in current source; the per-call classification was not re-derived.
- How Go built with its ASan mode, or HotSpot started under ASan, actually selects addresses. The interval arithmetic shows which ranges conflict, not what each runtime then does.
- The DOI string for Hunt & Larus could not be resolved through the fetch path used; volume, issue and pages were confirmed on the publisher-side publication page.
- Whether the count of 25 special cases in Baumann et al. matches the Issue 8 `fork` page; it was not recounted.

Known not to apply:

- "`SA_RESTART` makes `EINTR` handling unnecessary." Three of four restart codes ignore the flag, short counts are unaffected, and Go's source documents that the loop is still needed.
- "`openat` with a directory descriptor confines access." Observed false on Linux; `..` and intermediate symlinks escape.
- "`pthread_atfork` makes `fork` safe in threaded programs." POSIX.1-2024 marks it obsolescent and explains why it cannot work in general.
- "`ntdll.dll` is Windows' stable ABI." Microsoft documents that layer as internal and subject to change.
- "Ritchie's 27 lines describe PDP-11 `fork`." The figure is for the PDP-7.

Unsupported:

- `fork` on Linux without an MMU: the syscall returns `-EINVAL`.
- `vfork` in POSIX.1-2024: absent from the function index.

Stronger conclusions the evidence does not support: that any particular pair of runtimes fails to compose; that overcommit exists because of `fork`; that capability systems are free of the hazards listed (Plan 9 keeps asynchronous notes; Capsicum keeps `fork` and signals); that a passing probe confirms the upstream constants are current.

## Evidence

All material was acquired on 2026-11-19.

Specifications and papers (fetched as rendered text; quotations are from the fetched text):

- POSIX.1-2024, Issue 8 HTML edition, `https://pubs.opengroup.org/onlinepubs/9799919799/`: `functions/fork.html`, `functions/pthread_atfork.html`, `functions/posix_spawn.html`, `functions/sigaction.html`, `functions/V2_chap02.html` (2.4.1, 2.4.3), `idx/functions.html`. A request for `functions/vfork.html` returned no page.
- Baumann, Appavoo, Krieger, Roscoe, "A fork() in the road", HotOS '19, DOI 10.1145/3317550.3321435 (author-hosted PDF; DOI and venue printed on its first page).
- Ritchie, "The Evolution of the Unix Time-sharing System", as hosted at the Bell Labs page in `REPORT.json`; bibliographic note quoted from that page.
- Pike et al., "Plan 9 from Bell Labs", Computing Systems 8(3), Summer 1995; page footers 221 through 254 read from the USENIX scan; text also read at `https://9p.io/sys/doc/9.html`.
- Watson, Anderson, Laurie, Kennaway, "Capsicum: Practical Capabilities for UNIX", USENIX Security 2010. The paper and the USENIX page list these four authors.
- Hunt, Larus, "Singularity: Rethinking the Software Stack", ACM SIGOPS OSR 41(2), April 2007, pp. 37-49 (venue from the Microsoft Research publication page; full text from the author-hosted PDF; DOI not independently resolved).
- Gabriel, "The Rise of Worse is Better"; Apple QA1118 (revised 2011-09-20); Microsoft Learn "Calling Internal APIs".

Source at pinned revisions (repository, commit, paths as cited inline):

- `torvalds/linux` `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`: `kernel/fork.c`, `kernel/signal.c`, `arch/x86/kernel/signal.c`, `include/linux/errno.h`, `include/linux/sched/signal.h`, `mm/mmap.c`, `mm/util.c`, `fs/namei.c`, `fs/exec.c`, `fs/file.c`, `fs/ioctl.c`, `include/uapi/linux/openat2.h`, `include/uapi/linux/io_uring.h`, `include/linux/io_uring_types.h`, `Documentation/mm/overcommit-accounting.rst`, `Documentation/ABI/stable/syscalls`.
- `freebsd/freebsd-src` `d1e14cba4a79c0b4fe7cff3c0afcc0ffb50f54b3`; `openbsd/src` `974c1b36016e2479cd10e81aa8a4266ae9284751`; `illumos/illumos-gate` `21c9b825915a5d29ae49ee734ccef95e94d8aded`; `plan9foundation/plan9` `ed1a9c21e3297d7497a48053d33683375c75fbb4`.
- `fuchsia.googlesource.com/fuchsia` `d953ee3f076256b292cd85e449124d655cc8bf43`; `WebAssembly/WASI` `281ba75fafcd50961ef55f9e52747afcc9b71ede` and `463701e0f6c575a5d24ae31c2ec1e0ebf09d28e1`.
- `golang/go` `b496a3044e1dcdc3eed0af3e0e89db92f740d764`; `openjdk/jdk` `4f33273115381cd7697082fcb1bb2642dae19043`; `python/cpython` `6c9f2b691aaf0cf88cf2c3ba862f5de237a17344`; `llvm/llvm-project` `36f1fd30c75dc97c58a2350b6c7646206b30a0aa`; `v8/v8` `e88118f63dd96f24a9acb8bd0665e7880063f5c0`; `bminor/glibc` `04e750e75b73957cf1c791535a3f4319534a52fc`; `axboe/liburing` `a10946dc51eeababc48ee10baf0d17489f647a80`; `mkerrisk/man-pages` `ae6b221882ce71ba82fcdbe02419a225111502f0`.

Line numbers are for those commits. Only the files named were read; no claim is made about the rest of each tree.

Execution: `support/verify_posix_runtime_hazards.py`, Python 3.10+, standard library only. Reference run on Linux 7.1.6 x86-64, CPython 3.13.15:

```text
RESULT: PASS (58 passed, 0 failed, 0 skipped, 4 by-definition rows not counted as verification)
```

Of the 58, 25 are live observations (fork/spawn 6, signals 6, paths 7, address space 6) and 33 are model computations. The 4 `DEF` rows restate a table or constants transcribed from source, or a model arm fixed by its own definition (the spawn control arm, the restart table, the Go/TSan window, the V8 sizes); they cannot contradict upstream and are not evidence. Negative control: replacing the flag-write handler in the signal model with one that takes the interrupted lock turns that row into a failure (2 of 5 interruption points complete) and the probe exits 1.

The model rows depend on small programs chosen to illustrate each hazard. Their counts (for example 21 of 25) are properties of those programs, not measurements of real libraries.

## Revalidation

Cheapest checks first.

1. Run `python3 -B support/verify_posix_runtime_hazards.py`. It needs no network and writes only to a temporary directory. `--model-only` skips live checks; `--json` gives structured output. A pass re-establishes the 25 live behaviours on the host where it runs and the internal consistency of the models. It does not re-read any upstream file.
2. Constants and tables. For each transcribed item, diff the cited region at a newer revision: `arch/x86/kernel/signal.c` `handle_signal` and `arch_do_signal_or_restart`; `asan_mapping.h` lines 21-26; `tsan_platform.h` Go mapping; `runtime/malloc.go` hint loop; `compressedOops.hpp` mode comment; `v8-internal.h` cage and sandbox sizes. If any changed, update the constants at the top of the probe's address-space section and rerun; the hint-collision counts will change with them.
3. Runtime policy drift. Re-read the block comment in OpenJDK `ProcessImpl_md.c`, Go `forkAndExecInChild1` flag selection, glibc `spawni.c` header comment, and CPython `multiprocessing.rst` start-method notes. These are short and state the current default directly.
4. POSIX. Check the CHANGE HISTORY of `fork` and the status marker of `pthread_atfork` in any later issue; recount the async-signal-safe table if the number matters.
5. For another OS, the live sections report `SKIP` where a facility is missing. A `FAIL` there is information about that OS, not a probe defect; the accepted `O_NOFOLLOW` error codes already include the FreeBSD and NetBSD variants but were not exercised on those systems.

To turn the derived multi-runtime claims into observations, the investigation that was not done here must be done: build a process that embeds two of the runtimes (or one under a sanitizer), record `/proc/<pid>/maps` and the installed `sigaction` table after start-up in both load orders, and compare with sections 4 and 5.
