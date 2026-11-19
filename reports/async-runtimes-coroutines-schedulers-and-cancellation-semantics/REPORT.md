# Async Runtimes, Coroutines, Work-Stealing Schedulers, and Cancellation Semantics

## Summary

Concurrent language runtimes trade off across three coupled axes: **frame representation** (stackless state machines vs. stackful movable/segmented stacks), **cancellation semantics** (synchronous future dropping vs. cooperative cancel scopes), and **M:N scheduling discipline** (Chase-Lev deques vs. bounded SPMC FIFO rings + 1-slot LIFO locality caches, cooperative poll budgets, and preemption).

Direct inspection of twelve pinned upstream runtimes/verifiers (`golang/go`, `openjdk/jdk`, `erlang/otp`, `tokio-rs/tokio`, `python-trio/trio`, `ocaml/ocaml`, `ocaml-multicore/eio`, `Kotlin/kotlinx.coroutines`, `rust-lang/rust`, `llvm/llvm-project`, `tokio-rs/loom`, `awslabs/shuttle`), four primary specifications/papers, and an executable probe (`support/verify_cancellation_and_scheduler_semantics.py`) establishes four core invariants:

1. **Frame Representation Governs FFI Overhead vs. Function Coloring**: Rust `Future::poll(self: Pin<&mut Self>, cx: &mut Context<'_>)` guarantees zero intermediate heap allocation and zero stack-switch cost on synchronous C FFI calls, at the expense of function coloring, non-reentrant borrows across `.await`, and opaque backtraces. C++20 coroutines allocate frames dynamically by default; LLVM `CoroElide` (HALO, `P0981R0`) elides heap allocation only when ramp inlining succeeds and every exit path destroys the handle (`DT.dominates` or `canCoroBeginEscape == false`). Stackful runtimes eliminate coloring but pay at the native FFI boundary: Go switches from `2048`-byte copying stacks onto the OS `g0` stack on every `cgo` call; OpenJDK virtual threads eliminated `synchronized` pinning in JDK 24 (`JEP 491`) yet still pin carriers on `Pinned.NATIVE` (JNI/FFM), `CRITICAL_SECTION`, and `EXCEPTION`; Erlang/OTP BEAM preempts every `CONTEXT_REDS = 4000` reductions on isolated per-process heaps but requires Dirty CPU/IO NIF schedulers or `enif_consume_timeslice` for long native calls; OCaml 5 segmented fibers cannot capture effects across native C frames (`Effect.Unhandled`).
2. **Synchronous Drop Cancellation Causes "Cancel Safety" Data Loss**: Dropping a paused Rust future at `.await` destroys intermediate state stored inside `self` (such as `ReadExact<'a, A>`'s `ReadBuf<'a>`), silently desynchronizing byte streams when raced in `tokio::select!` (`45/45` wire bytes lost across `9` mid-frame drops in our probe, vs. `0` bytes lost with an external buffer or `mpsc::Sender::reserve` + `Permit::send`). Trio, Kotlin, Java `StructuredTaskScope`, and Eio use cooperative checkpoints with shielded cleanup scopes, whereas Rust's unstable `AsyncDrop` (`#126482`) conflicts with synchronous generics, `core::mem::forget`, panic unwinding, and bounded-stack guarantees.
3. **Production Async Queues Are Bounded SPMC FIFO Rings + 1-Slot LIFO, Not Classic Chase-Lev Deques**: Both Go (`p.runq`) and Tokio (`queue::Local`) use fixed `256`-slot SPMC FIFO circular rings with half-queue batch stealing (`n - n/2`), half-queue overflow spilling (`128` tasks + incoming), Acquire/Release atomics (avoiding Chase-Lev's `SeqCst` fence in `pop_bottom`), and a 1-slot LIFO locality slot (`runnext` / `lifo_slot`). Unbounded LIFO chaining starves FIFO, global, and I/O queues completely (`0` polls in our probe); Go guards `runnext` with `sysmon` `10ms` preemption (disabling `runnext` if `!haveSysmon`) and `schedtick % 61 == 0`, while Tokio enforces `MAX_LIFO_POLLS_PER_TICK = 3`, `Budget(128)`, self-tuned `global_queue_interval`, and `event_interval = 61`.
4. **Cooperative Budgets Cannot Preempt Synchronous CPU Loops**: Tokio's `coop::poll_proceed` triggers only inside instrumented async primitives; an unyielding CPU loop inside `Future::poll` stalls FIFO tasks and I/O reactor polling (`503`-step stall, `0` I/O polls in our probe), unlike Go's `sigPreempt` and BEAM's `4000`-reduction quantum (`14`-step max wait, `5` I/O polls). `Loom` (DPOR + `preemption_bound`) and `Shuttle` (PCT) validate concurrent schedules deterministically without wall-clock dependence.

## Applicability

This report characterizes twelve pinned upstream repository revisions and four specifications/papers listed in `REPORT.json`, all observed on `2026-11-19`:

- **Subject relationships**: Compares stackless poll/resume coroutines (`rust-lang/rust`, `tokio-rs/tokio`, `llvm/llvm-project` / `P0981R0`) with stackful/effectful runtimes (`golang/go`, `openjdk/jdk`, `erlang/otp`, `ocaml/ocaml`, `ocaml-multicore/eio`) and structured-concurrency frameworks (`python-trio/trio`, `Kotlin/kotlinx.coroutines`, `openjdk/jdk` `StructuredTaskScope`), interpreting production schedulers against Chase & Lev (2005), Lê et al. (2013), `tokio-rs/loom`, and `awslabs/shuttle`.
- **OpenJDK version split**: Explicitly separates **JDK 21 (`JEP 444`)** (`synchronized`/`Object::wait` carrier pinning via `Pinned.MONITOR`) from **JDK 24+ (`JEP 491`)** and the examined **`openjdk/jdk` revision (`4f33273115381cd7697082fcb1bb2642dae19043`, JDK 28 tip)**, where Java monitor pinning is removed (`VirtualThread` unmounts in `BLOCKING`/`BLOCKED`/`WAITING`) and `StructuredTaskScope` (iterated through `JEP 453`/`480`/`499`/`505`) is a finalized `public sealed interface` (`@since 28`) using `open(Joiner)`.
- **Adjacent corpus packages**: Does **not** duplicate `rustc` MIR `StateTransform` enum layouts, `Pin` Tree Borrows retagging, or LLVM SROA field-slicing mechanics; consult companion packages `rustc-statetransform-coroutines-async-gen-and-pin-mir-semantics` and `self-referential-unpin-coroutine-field-slicing-and-sroa`.
- **Probe scope**: Metrics from `support/verify_cancellation_and_scheduler_semantics.py` model discrete-event protocol and scheduler invariants calibrated to exact upstream constants (`256`, `3`, `128`, `61`, `n - n // 2`), not hardware wall-clock nanosecond distributions.

## Findings

### 1. Stackless Poll State Machines vs. Stackful Movable Green Threads and Virtual Threads

Basis: normative + documentation + source + derived

High-concurrency runtimes multiplexing $10^5$–$10^7$ tasks onto $O(\text{cores})$ OS threads split between **stackless compiler-lowered state machines** and **stackful movable/segmented stacks**.

#### 1.1 Architectural Comparison Matrix

| Dimension | Rust (`async`/`Future`) | C++20 Coroutines + LLVM | Go (`G-M-P` runtime) | OpenJDK Virtual Threads | Erlang/OTP BEAM | OCaml 5 + Eio |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Execution model** | Stackless state machine (`Future::poll`) | Stackless resume/destroy frame (`coroutine_handle`) | Stackful movable goroutine stack | Stackful heap-chunked continuation (`StackChunk`) | Stackful isolated actor process | Stackful segmented fiber stacks + 1-shot effects |
| **Per-task allocation** | 0 for nested `.await` (inline enum); 1 per root spawn | 1 heap alloc/call unless HALO (`CoroElide`) elides | `stackMin = 2048` B contiguous; `2x` grow, `1/2` shrink if `< 1/4` used | Lazy heap `StackChunk` on unmount (park/yield) | Isolated contiguous heap+stack (`htop`/`stop`) | Pooled power-of-2 segments (`NUM_STACK_SIZE_CLASSES = 5`) |
| **Function coloring** | Yes (`async fn` vs `fn`; calling conventions diverge) | Yes (`co_await` returns awaitable/task) | No (transparent runtime suspension) | No (transparent JDK blocking suspension) | No (transparent reduction preemption) | No for normal fns under Eio handler (dynamic per domain) |
| **Preemption** | Cooperative (`Poll::Pending` + Tokio `Budget(128)`) | Cooperative (`co_await` / `co_yield`) | Prologue checks + `sysmon` `10ms` (`forcePreemptNS`) `sigPreempt` | Cooperative unmount at JDK blocking points (incl. monitors post-JEP 491) | Deterministic reduction counter (`CONTEXT_REDS = 4000`, `p->fcalls`) | Cooperative via `Effect.perform` to domain scheduler |
| **Synchronous C FFI** | 0 stack-switch cost; blocking C stalls worker thread | 0 stack-switch cost; blocking C stalls caller thread | `cgocall` -> `entersyscall` -> `asmcgocall` onto OS `g0` -> `exitsyscall`; detaches `P` | Pins carrier OS thread (`Pinned.NATIVE`); JNI/FFM cannot freeze | Normal NIFs invisible to `4000` reds; use Dirty CPU/IO NIFs or `enif_consume_timeslice` | Switches to domain C stack; `Effect.perform` across C raises `Effect.Unhandled` |
| **Backtraces** | No native stack across `.await` | Only via custom promise links / debugger plugins | Native runtime `traceback` over goroutine stack | Full Java stack traces across `StackChunk`s | Full per-process BEAM traces (`process_info`) | Full OCaml traces within OCaml segments |
| **Pointer stability** | `Pin<&mut Self>` for immovable self-borrows | Stable heap address (or caller stack under HALO) | Stack pointers adjusted during `copystack` via GC maps | GC relocates oops in `StackChunk` | Immutable terms; no cross-process mutable aliasing | GC scans `struct stack_info`; values on GC heap |

#### 1.2 Rust Stackless Futures, Function Coloring, and Cross-Reference Boundary

Basis: normative + source + derived

In `rust-lang/rust` (`library/core/src/future/future.rs:111-114`), asynchronous computation lowers to one pull-based trait:

```rust
#[lang = "poll"]
pub trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

Nested `async fn` calls pack cross-`.await` locals and child futures into a flat concrete enum whose size is known statically, executing directly on the OS worker thread's native stack with zero stack-switch cost when calling synchronous C FFI. (For exact `rustc` MIR `StateTransform` enum layout, `Pin` Tree Borrows rules, and LLVM SROA slicing, see companion reports `rustc-statetransform-coroutines-async-gen-and-pin-mir-semantics` and `self-referential-unpin-coroutine-field-slicing-and-sroa`.)

Four structural costs follow directly from this representation:
1. **Infectious function coloring** (Nystrom 2015, *"What Color is Your Function?"*): synchronous callers cannot `.await` without a nested executor (which panics/deadlocks inside an active runtime), and higher-order combinators (`Iterator::map`, trait methods) cannot abstract seamlessly over pure vs. suspending callees because their **calling conventions diverge** (direct value return vs. returning an unboxed `Future` polled via `Pin<&mut Self>`).
2. **Non-reentrant borrows across `.await`**: holding a `std::sync::MutexGuard` or `&mut T` across `.await` embeds that guard inside the state machine, risking same-worker deadlock and making OS lock guards `!Send`.
3. **Opaque backtraces**: suspended tasks retain only an enum discriminant and captured locals on the heap, not OS stack frames.
4. **Blocking-call hazard**: per `future.rs:91-96`, `poll` must return quickly; blocking syscalls or CPU loops stall the executor OS worker thread.

#### 1.3 C++20 Coroutines and LLVM `CoroElide` (HALO) Fragility

Basis: normative + documentation + source + derived

C++20 coroutines (ISO/IEC 14882:2020 `[dcl.fct.def.coroutine]`) erase the frame type behind `std::coroutine_handle<>` allocated via `operator new`, relying on **HALO (Heap Allocation eLision Optimization)** (Smith & Nishanov 2018, WG21 `P0981R0`) to convert frames back to caller stack `alloca`s.

Direct inspection of `llvm/llvm-project` (`llvm/lib/Transforms/Coroutines/CoroElide.cpp:355-425`) establishes the three strict static preconditions of `CoroIdElider::attemptElide()`:
1. **Caller-side ramp inlining**: `CoroElide` operates intraprocedurally on post-split `coro.id`/`coro.begin` intrinsics inside `FEI.ContainingFunction` (`L386-408`); separate compilation without LTO, virtual/indirect dispatch, or inliner limits silently disable elision.
2. **Non-escaping lifetime on all exit paths**: `lifetimeEligibleForElide()` (`L355-384`) requires every terminator (including unwind pads) to be dominated by `coro.destroy`/`coro.dead` (`DT.dominates`) or proven unreachable without passing through destroy/dead via `canCoroBeginEscape`.
3. **Constant frame layout**: `getFrameLayout(cast<Function>(ResumeAddrConstant))` must yield static size and alignment (`L405-411`).

Thus C++20 zero-allocation coroutines are an **optimization-dependent property**—moving a handle into a container, type-erasing it, or compiling at `-O0` silently reintroduces per-call heap allocations—whereas Rust's unboxed `impl Future` guarantees zero intermediate heap allocation semantically.

#### 1.4 Go `G-M-P` Contiguous Copying Stacks, Signal Preemption, and `cgo` Trampolines

Basis: source + documentation + derived

Go avoids coloring by assigning each goroutine (`g`, `src/runtime/runtime2.go`) a movable contiguous stack multiplexed across OS threads (`m`) and logical processors (`p`):

- **Stack sizing & relocation (`src/runtime/stack.go`)**: Stacks start at `stackMin = 2048` bytes (`L78`, plus platform `stackSystem`, `L75-82`). Prologue overflow checks against `gp.stackguard0` invoke `newstack()` (`L1080`), doubling size (`newsize := oldsize * 2` until `newsize - used >= needed`, `L1204-1214`) and relocating via `copystack` (`L954`) using precise GC pointer maps. During GC, `shrinkstack` (`L1311-1360`) halves stacks when `used < avail / 4` and `newsize >= fixedStack`.
- **Signal-based asynchronous preemption (`src/runtime/proc.go`, `preempt.go`)**: Alongside cooperative prologue checks (`stackPreempt = uintptrMask & -1314`, `stack.go:133`), `sysmon` invokes `retake(now)` (`proc.go:6727`) to preempt any `G` (or `runnext` chain) exceeding `forcePreemptNS = 10 * 1000 * 1000 // 10ms` (`proc.go:6725, 6753-6756`) via `preemptM` -> `sigPreempt`. The signal handler verifies `isAsyncSafePoint` (`preempt.go:442`) and injects `asyncPreempt`/`asyncPreempt2` (`preempt.go:357-373`), switching to the system stack via `mcall` to yield even tight call-free loops.
- **`cgo` stack-switch boundary (`src/runtime/cgocall.go:7-28`)**: Because C lacks Go stack-split prologues and assumes an immovable OS stack, every `cgo` invocation runs `entersyscall` (detaching `P` so GC/goroutines proceed), `asmcgocall` (switching from `m->curg` to OS stack `m->g0`), the C function, stack restoration, and `exitsyscall` (reacquiring `P` under `GOMAXPROCS`). This non-inlinable trampoline adds per-call overhead (commonly tens of nanoseconds in Go runtime practice, vs. direct C calls in Rust) and causes `sysmon` to spawn extra OS threads `M` whenever C blocks.

#### 1.5 OpenJDK Virtual Threads and the JEP 444 -> JEP 491 Pinning Boundary

Basis: normative + source + derived

OpenJDK Project Loom (`JEP 444`, JDK 21) executes `VirtualThread` continuations (`jdk.internal.vm.Continuation`) on a FIFO work-stealing `ForkJoinPool` (`VirtualThread.java:1330-1356`: `boolean asyncMode = true; // FIFO`, `parallelism = availableProcessors()`, default `maxPoolSize = max(parallelism, 256)`). Active virtual threads mount onto carrier OS stacks (`enterSpecial`/`enter`, `Continuation.java:302-317`); blocking calls `doYield()`, freezing Java frames into GC-managed heap `StackChunk` objects (`stackChunkOop.cpp`, `continuationFreezeThaw.cpp`) and thawing them onto an arbitrary carrier on unpark.

- **JDK 21 (`JEP 444`) vs. JDK 24+ (`JEP 491`)**: Under JDK 21, `synchronized` blocks and `Object::wait` tied `ObjectMonitor` ownership to the carrier thread, causing `Pinned.MONITOR` starvation. In JDK 24 (`JEP 491`, *"Synchronize Virtual Threads without Pinning"*), confirmed directly in `openjdk/jdk` @ `4f33273115381cd7697082fcb1bb2642dae19043`, virtual threads unmount cleanly on monitor contention and `Object::wait` (`VirtualThread.java:142-152` states `BLOCKING = 12`, `BLOCKED = 13`, `UNBLOCKED = 14`, `WAITING = 15..18`).
- **Remaining structural pinning causes (`Continuation.java:58-62, 82-89`)**: `Pinned.MONITOR` has been deleted, leaving:
  ```java
  public enum Pinned {
      /** Native frame on stack */ NATIVE,
      /** In critical section */   CRITICAL_SECTION,
      /** Exception (OOME/SOE) */  EXCEPTION
  }
  ```
  (`continuationFreezeThaw.cpp:937, 949, 1378, 1971, 2027, 2054, 2068` returning `freeze_pinned_native` and `freeze_pinned_cs`). HotSpot cannot relativize or copy opaque native C/C++/Rust JNI or FFM stack frames (which may hold raw stack interior pointers or C++ RAII state) onto heap `StackChunk`s, so native frames permanently pin carrier threads.

#### 1.6 Erlang/OTP BEAM Reduction Scheduling, Isolated Heaps, and Dirty NIFs

Basis: source + documentation + derived

Erlang/OTP's BEAM VM (`erlang/otp`) optimizes for deterministic soft-real-time latency and fault isolation:

- **Per-process isolated heap+stack (`erts/emulator/beam/erl_process.h:1043-1067`)**: `struct process` pairs `Eterm *htop` (heap growing up) and `Eterm *stop` (stack growing down) inside a private contiguous allocation. Message passing copies terms (except ref-counted off-heap binaries), enabling per-process GC without global pauses, selective mailbox receive, and crash-only OTP supervision where one failing process never tears down shared mutable invariants.
- **Deterministic 4,000-reduction preemption (`erl_vm.h:47`, `erl_process.h:1062`)**: Every function call, BIF, and loop decrements `p->fcalls`, initialized to `#define CONTEXT_REDS 4000` (`erl_vm.h:47`; older 2,000-reduction figures reflect pre-R16B ERTS). Exhaustion yields deterministically to `erts_schedule` (`erl_process.c:9607`), with per-scheduler priority run queues (`ErtsRunQueue`, `erl_process.h:472-511`), periodic load balancing (`check_balance` every `2000 * CONTEXT_REDS` reductions, `erl_process.c:63, 4894, 9813`), and idle work stealing (`try_steal_task`, `erl_process.c:4468-4711, 9907`).
- **Native NIF blindspot & Dirty Schedulers (`erl_nif.h:42-47, 239-243`, `erl_process.h:111-112`)**: Native C/Rust NIFs bypass BEAM reduction counting and stall the scheduler OS thread if they exceed ~1 ms. Developers must explicitly mark blocking or heavy NIFs with `ERL_NIF_DIRTY_JOB_CPU_BOUND` or `ERL_NIF_DIRTY_JOB_IO_BOUND` (`erl_nif.h:241-242`) for separate dirty scheduler pools, or yield manually via `enif_consume_timeslice` + `enif_schedule_nif`.

#### 1.7 OCaml 5 Segmented Fiber Stacks and the C FFI Effect Barrier

Basis: source + documentation + derived

OCaml 5 (Sivaramakrishnan et al. 2021, PLDI '21, DOI `10.1145/3453483.3454039`) allocates small pooled fiber stack segments (`ocaml/ocaml`, `runtime/fiber.c:95, 537-615`, `NUM_STACK_SIZE_CLASSES = 5`; `runtime/caml/fiber.h:28-92`) bounded by `struct stack_info` at the bottom and `struct stack_handler` (`handle_value`, `handle_exn`, `handle_effect`, `parent`) at the top. Libraries like **Eio** (`ocaml-multicore/eio`, `lib_eio/core/fiber.ml:8-9`) suspend fibers in $O(1)$ pointer swaps via `Effect.perform`. Because native C calls switch onto the domain's OS C stack (`caml_c_call`), an OCaml callback invoked from C has a `NULL` handler parent above the C frame: performing an effect handled above that C frame raises `Stdlib.Effect.Unhandled`. Multi-shot resumption is likewise disallowed (`Effect.Continuation_already_resumed`), preventing double-finalization of linear resources.

---

### 2. Structured Concurrency, Synchronous Drop Cancellation ("Cancel Safety"), and `AsyncDrop`

Basis: normative + documentation + source + execution + derived

Structured concurrency (Smith 2018) enforces lexical task lifetimes: every child task spawned inside a scope terminates before control leaves that scope. How a runtime delivers cancellation across suspended coroutines determines whether multi-step protocols preserve their invariants.

#### 2.1 Comparative Matrix of Cancellation Models

| System | Scope Construct | Cancellation Mechanism | Interruptible Points | Cleanup Shielding | Structural Failure Mode |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Rust (`tokio`)** | No built-in nursery; `tokio::select!`, `JoinSet`, `TaskTracker` | **Synchronous `Drop`** of paused `Future` (no `.await` in `Drop::drop`) | **Every `.await`** inside a dropped future | None at language level; hoist state outside future or spawn detached task | **Silent mid-protocol state loss** ("cancel safety" bugs); UAF on borrowed `io_uring` DMA buffers |
| **Python `Trio`** | `trio.open_nursery()`, `CancelScope` (`_run.py:543, 1183`) | Hierarchical `CancelStatus` tree (`effectively_cancelled`, `_run.py:379, 472-475`); raises `Cancelled(BaseException)` (`_exceptions.py:52`) | Explicit **checkpoints** (`checkpoint()`, `_run.py:3019, 3057`) | `CancelScope(shield=True)` (`_run.py:382, 473, 512`) | Missing checkpoints delay cancel; unbounded `shield=True` hangs exit; scope misnesting (`_run.py:517`) |
| **Kotlin (`kotlinx.coroutines`)** | `coroutineScope`, `supervisorScope`, `Job` tree (`Job.kt:50-88`) | `Job.cancel()` (`Active -> Cancelling -> Cancelled`); throws `CancellationException` | Cancellable suspend functions (`CancellableContinuation`, `ensureActive`) | `withContext(NonCancellable)` in `finally` (`NonCancellable.kt:9-40`) | Catching `Exception` swallows `CancellationException`; `launch(NonCancellable)` severs parent-child tree (`NonCancellable.kt:19-22`) |
| **Java (`OpenJDK`)** | `StructuredTaskScope.open(Joiner)` (`StructuredTaskScope.java:380, 573, 1275`, `@since 28`) | Scope shutdown calls `Thread.interrupt()` on unfinished subtasks; `close()` awaits all children | Interruptible blocking JDK ops (`InterruptedException`) | Standard `finally` cleanup (non-interruptible unless re-blocking) | Subtasks ignoring interrupts or blocked in uninterruptible JNI delay `close()` indefinitely |
| **OCaml `Eio`** | `Switch.run`, `Fiber.fork ~sw`, `Fiber.first` (`switch.ml`, `fiber.ml:11-33`) | Per-domain `Cancel.t` tree (`On -> Cancelling -> Finished`, `cancel.ml:3-30`); invokes `fiber.cancel_fn`, raises `Cancelled` | Cancellable `Effect.perform` points | `Cancel.protect` (`protected = true`, `cancel.ml:21, 40`) | Domain-confined tree (`domain : Domain.id`, `cancel.ml:22`); cross-domain ops need atomic `cancel_fn` (`cancel.ml:13-15`) |

#### 2.2 Mechanical Root Cause of Rust's "Cancel Safety" Bugs

Basis: documentation + source + execution + derived

In `tokio-rs/tokio/tokio/src/macros/select.rs:152-158`, Tokio defines cancellation safety strictly in prose (no compiler check):

> *"If you have a future that has not yet completed, then it must be a no-op to drop that future and recreate it. This definition is motivated by the situation where a `select!` is used in a loop. Without this guarantee, you would lose your progress when another branch completes and you restart the `select!` by going around the loop."*

Inspecting `tokio/src/io/util/read_exact.rs:34-65` shows the exact hazard:

```rust
pub struct ReadExact<'a, A: ?Sized> {
    reader: &'a mut A,
    buf: ReadBuf<'a>, // advances cursor across Poll::Pending returns
    #[pin]
    _pin: PhantomPinned,
}
```

When `ReadExact::poll` reads partial bytes from the kernel socket into `me.buf` and returns `Poll::Pending`, the socket cursor has already advanced. If a competing `tokio::select!` branch completes, `select!` synchronously drops `ReadExact`, destroying `me.buf`'s filled count without returning it—silently discarding consumed bytes and desynchronizing the framing protocol. The same failure hits channel preprocessing: dequeuing an item and racing `tx.send(item)` inside `select!` drops `item` if cancelled. Tokio's cancel-safe idiom (`tokio/src/sync/mpsc/bounded.rs:1087-1119`) splits capacity acquisition from message consumption: `let permit = tx.reserve().await?;` (cancelling loses only FIFO waiter order, never an owned message), followed by synchronous `permit.send(item)`.

#### 2.3 Executable Verification: Sync-Drop Loss vs. External-Buffer & Cancel-Scope Recovery

Basis: execution

Running `python3 -B support/verify_cancellation_and_scheduler_semantics.py` over a deterministic 4-frame, 45-byte length-prefixed `ChunkedByteStream` (`max_chunk = 3`, heartbeat winning every 3rd tick) yields:

| Strategy in Probe | Decoded Frames (of 4) | Matches Expected? | Mid-Frame Drops | Bytes Silently Discarded | Conservation |
| :--- | :---: | :---: | :---: | :---: | :--- |
| **Rust-style sync-drop `select!` on 2-stage `ReadFrameFuture`** | `0` | `false` | `9` | **`45 / 45`** | Broken (stream desynchronized & exhausted) |
| **Rust-style cancel-safe external buffer (`BytesMut` + `poll_one_chunk`)** | `4` | `true` | `0` | **`0`** | Exact (`45 / 45` bytes decoded) |
| **Trio/Kotlin-style `CancelScope` (checkpoint + `shield=True` cleanup)** | `1` (pre-cancel) | N/A (cancelled) | `0` | **`0`** | Exact (`10` committed + `5` recovered = `15` consumed) |
| **Channel handoff: naive dequeue-then-`send` vs. `reserve` + `Permit::send`** | Naive: `0` / Permit: `1` | Naive dropped `1` msg | — | Naive: `1` msg / Permit: `0` | Permit pattern loses `0` messages |

This demonstrates that cancel-safety bugs arise whenever non-idempotent pre-`.await` side effects store progress inside a droppable future. Trio (`CancelScope(shield=True)`) and Kotlin (`withContext(NonCancellable)`) avoid silent destruction via cooperative checkpoints and shielded `finally` rollback—trading instantaneous drop cancellation for teardown latency and deadlock risk if a shielded cleanup awaits a dead peer without a deadline.

#### 2.4 Why `AsyncDrop` Collides with Rust's Core Language Guarantees

Basis: source + documentation + derived

In `rust-lang/rust/library/core/src/future/async_drop.rs:1-58`, `AsyncDrop` remains unstable (`#![unstable(feature = "async_drop", issue = "126482")]`):

```rust
#[lang = "async_drop"]
pub trait AsyncDrop {
    #[allow(async_fn_in_trait)]
    async fn drop(self: Pin<&mut Self>);
}
#[lang = "async_drop_in_place"]
pub async unsafe fn async_drop_in_place<T: ?Sized>(_to_drop: &mut T) { /* compiler intrinsic */ }
```

Five structural conflicts prevent `AsyncDrop` from cleanly resolving async cancellation and linear teardown:
1. **Generic synchronous code & color pollution**: Synchronous generics (`drop<T>`, `mem::replace`, `Vec::pop`, `Option::take`) assume synchronous destruction. Passing an `AsyncDrop` type into synchronous code either silently runs sync `Drop` (defeating cleanup) or splits the standard library across a new `?SyncDrop`/`AsyncDestruct` bound.
2. **Safe destructor skipping (`core::mem::forget` & `Rc`/`Arc` cycles)**: Rust is affine, not linear; memory safety can never rely on `Drop` or `AsyncDrop` running. Thus `AsyncDrop` cannot make borrowed-stack-buffer `io_uring` operations sound on cancellation—completion I/O still requires heap-owned buffer handoff (`tokio-uring`/`compio`) or linear (`!Leak`) types.
3. **Synchronous stack unwinding (`panic = "unwind"`)**: Native DWARF/SEH unwinding has no `Context<'_>`/`Waker` and cannot return `Poll::Pending`, while panicking inside `AsyncDrop::drop` triggers double-panic abort hazards.
4. **Cancellation-of-`AsyncDrop` paradox**: Dropping the future returned by `AsyncDrop::drop` reintroduces synchronous drop cancellation unless async destructors run uninterruptibly (risking deadlock).
5. **State-machine & stack-size growth**: Every `.await` point with live `AsyncDrop` locals introduces async-drop transitions and embedded drop-future storage inside the enclosing coroutine enum, inflating `size_of` and codegen size.

---

### 3. Work-Stealing Deques, LIFO-Slot Starvation, Cooperative Budgets, and Formal Progress

Basis: normative + source + execution + derived

#### 3.1 Textbook Chase-Lev Deque vs. Production Fixed-Ring SPMC FIFO + 1-Slot LIFO Schedulers

Direct source inspection reveals that neither Go's `p.runq` nor Tokio's `queue::Local` implements the textbook **Chase-Lev deque** (Chase & Lev 2005, SPAA '05, DOI `10.1145/1073970.1073974`; weak-memory proof in Lê, Pop, Cohen & Zappa Nardelli 2013, PPoPP '13, DOI `10.1145/2442516.2442524`):

| Property | Classic Chase-Lev (2005) / Lê et al. (2013) | Go `p.runq` (`proc.go`, `runtime2.go`) | Tokio `queue::Local` (`multi_thread/queue.rs`) |
| :--- | :--- | :--- | :--- |
| **Owner pop order** | **LIFO** from `bottom` (`pop_bottom`) | **FIFO** from `runqhead` (`runqget`, `proc.go:7713-7723`) | **FIFO** from `head` (`pop`, `queue.rs:361-399`) |
| **Locality fast path** | Inherent in LIFO `pop_bottom` | Separate 1-slot **`p.runnext`** (`runtime2.go:906`, `proc.go:7599-7711`) | Separate 1-slot **`core.lifo_slot`** (`worker.rs:125, 750-786`) |
| **Array sizing** | Dynamically resizable circular buffer (epoch/GC reclamation) | Fixed **`[256]guintptr`** (`runtime2.go:893`); overflow spills `128` + new `G` to global `sched.runq` | Fixed **`LOCAL_QUEUE_CAPACITY = 256`** (`queue.rs:63`); overflow spills `128` + new task to inject queue (`queue.rs:300-358`) |
| **Stealer granularity** | Single task per `steal_top` CAS | Batch-steals **half** (`n - n/2`) via `runqgrab` (`proc.go:7767-7775`) | Batch-steals **half** (`n - n/2`) via `steal_into2` (`queue.rs:420-495`) |
| **Memory-ordering protocol** | Concurrent stealers; owner `pop_bottom` requires **`SeqCst` fence** between `bottom--` and `top` load (Lê et al. 2013) | `LoadAcq` on `runqhead`/`runqtail`, `CasRel` on `runqhead` (`proc.go:7714-7720, 7769-7770`) | Packs `(steal_head, real_head)` into one `AtomicUnsignedLong` (`queue.rs:37-50`); rejects concurrent stealers (`L482`); uses **`Acquire`/`Release`/`AcqRel`** CAS (`L390, 465, 473`), eliminating per-pop `SeqCst` fences |

Whereas fork-join parallel frameworks (Cilk, Blumofe & Leiserson 1999, JACM DOI `10.1145/324133.324234`; Rayon) use LIFO owner popping to bound stack depth, server/I/O runtimes use FIFO local queues to prevent tail-latency inversion on independent requests—pairing a FIFO ring with a single 1-slot LIFO cache (`runnext`/`lifo_slot`) for message-passing locality. OpenJDK's `VirtualThread.createDefaultScheduler()` similarly configures `ForkJoinPool` in FIFO mode (`asyncMode = true`, `VirtualThread.java:1353-1355`).

#### 3.2 LIFO-Slot Ping-Pong Starvation, Fairness Intervals, and Cooperative Budget Blindspots

Basis: source + execution + derived

If Task `A` and Task `B` repeatedly wake each other via the 1-slot LIFO cache, an unguarded worker loops between `A` and `B` forever, starving the 256-slot FIFO ring, global queue, and I/O reactor. Both runtimes codify explicit mitigations:

- **Go (`golang/go/src/runtime/proc.go`)**: `runqget` returns `inheritTime = true` for `runnext` (`L7709-7710`), so chained `runnext` goroutines share one `10ms` `forcePreemptNS` slice (`L6725, 6753-6756`) preempted by `sysmon`. When `!haveSysmon`, `runqput` **disables `runnext` completely** (`L7584-7594`). Global-queue starvation is bounded by `pp.schedtick%61 == 0` (`L3496`).
- **Tokio (`tokio-rs/tokio/tokio/src/runtime/scheduler/multi_thread/worker.rs` & `tokio/src/task/coop/mod.rs`)**:
  1. **LIFO cap**: `const MAX_LIFO_POLLS_PER_TICK: usize = 3;` (`worker.rs:272`). After 3 consecutive LIFO polls (`L773-786`), `core.lifo_enabled = false` forces subsequent local wakes onto the FIFO `run_queue`.
  2. **Cooperative budget**: `run_task` runs under `coop::budget` (`worker.rs:718`) initialized to `Budget::initial() = Budget(Some(128))` (`coop/mod.rs:115-117`). LIFO tasks inherit the parent's remaining budget (`worker.rs:704-705, 758-770`); exhaustion pushes the LIFO task to `run_queue` and makes `coop::poll_proceed(cx)` (`coop/mod.rs:343-345, 397, 413-427`) defer the waker and return `Poll::Pending` (while dropping `RestoreOnPending` reverts the decrement if the underlying op naturally returned `Pending`, `L295-305`).
  3. **Global & I/O intervals**: `Core::next_task` checks the global queue every dynamically self-tuned `global_queue_interval` ticks (`worker.rs:1079-1086, 1321-1328`); `maintenance` invokes `park_yield` every `event_interval = 61` ticks (`builder.rs:283, 295`, noting origin in Go; `worker.rs:828-835`). Unstable `enable_eager_driver_handoff` (`worker.rs:692-700`) eagerly wakes a parked worker whenever the driver-holding worker begins polling a task.
- **Cooperative blindspot**: `coop::Budget(128)` bounds only ready-yielding Tokio primitives. A synchronous CPU loop or blocking syscall inside `Future::poll` never calls `coop::poll_proceed`, stalling local FIFO tasks (until stolen) and blocking the I/O/timer driver if held by that worker.

#### 3.3 Executable Verification: Scheduler Starvation, Mitigation, and Queue Conservation

Basis: execution

Running `python3 -B support/verify_cancellation_and_scheduler_semantics.py` over `1,000` steps (`event_interval = 61`, `global_queue_interval = 31`, `MAX_LIFO_POLLS_PER_TICK = 3`, `Budget = 128`) produces:

| Scheduler Regime (1,000-step horizon) | Ticks | Ping + Pong Polls | Polls / FIFO Task (4) | Max FIFO Wait (steps) | Global Polls | I/O Reactor Polls | Max I/O Gap (steps) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **`unbounded_lifo`** (no LIFO cap, no preemption) | `1` | `500 + 500` | `0, 0, 0, 0` | **`1000`** | **`0`** | **`0`** | **`1000`** |
| **`tokio_bounded`** (`MAX_LIFO = 3`, `Budget = 128`, `31`/`61`) | `631` | `246 + 246` | `122, 122, 122, 122` | **`8`** | `20` | `10` | `97` |
| **`coop_cpu_hog`** (500-step unyielding sync `poll`) | `6` | `0 + 0` | `1, 1, 1, 1` | **`503`** | **`0`** | **`0`** | **`1000`** |
| **`preemptive_cpu_hog`** (10-step quantum, BEAM/Go model) | `362` | `0 + 0` | `70, 70, 70, 70` | **`14`** | `11` | `5` | `169` |

The probe's `BoundedLocalRunQueue` check (`300` pushed tasks) also verifies exact conservation: push `#256` spills `128 + 1 = 129` tasks to `global_q` (leaving `171` in `w0` after `#299`); `w1.steal_into` steals `171 - 85 = 86` tasks (leaving `85` in `w0`); draining all queues recovers all `300` unique IDs without loss or duplication.

#### 3.4 Formal Progress, Fairness Assumptions, and Concurrency Model Checking (`Loom` & `Shuttle`)

Basis: normative + source + derived

Finite-prefix safety proofs (linearizability, race freedom, task conservation) fit standard separation logics and weak-memory verification (Lê et al. 2013), whereas starvation-freedom is a $\Pi^0_2$ liveness property that fails under adversarial scheduling unless paired with explicit fairness axioms and bounded step-cost contracts per poll (often requiring transfinite step-indexing). In Rust runtime engineering, two systematic verifiers check concrete scheduler and atomic code directly:

- **`tokio-rs/loom`** (`src/model.rs:17-43, 108-127`, wired into Tokio via `#[cfg(loom)]` in `queue.rs:62-65` and `builder.rs:279-280`, shrinking capacity and `EVENT_INTERVAL = 4`): combines **Dynamic Partial-Order Reduction (DPOR)** (Flanagan & Godefroid 2005, POPL '05, DOI `10.1145/1040305.1040315`) with **preemption bounding** (`preemption_bound` / `LOOM_MAX_PREEMPTIONS`) to exhaustively explore C11 weak-memory interleavings of small lock-free queues.
- **`awslabs/shuttle`** (`shuttle/src/scheduler/mod.rs:8-10`, `shuttle-schedulers/src/pct.rs:21-33`): scales to larger multi-task async programs via **Probabilistic Concurrency Testing (PCT)** (Burckhardt, Kothari, Musuvathi & Nagarakatte 2010, ASPLOS '10, DOI `10.1145/1735970.1736040`), using `PctScheduler` (`max_depth - 1` random `change_points`) for a $1 / (n \cdot k^{d-1})$ discovery lower bound on depth-$d$ bugs, alongside `DfsScheduler`, `RandomScheduler`, and `ReplayScheduler`.

## Boundaries

- **Not examined**:
  - `rustc` MIR `StateTransform` enum discriminant synthesis, `Pin` Tree Borrows retagging, and LLVM SROA field-slicing (covered in companion reports `rustc-statetransform-coroutines-async-gen-and-pin-mir-semantics` and `self-referential-unpin-coroutine-field-slicing-and-sroa`).
  - Linux `io_uring` kernel cancellation (`IORING_OP_ASYNC_CANCEL`) and completion-based Rust runtimes (`tokio-uring`, `compio`), beyond the structural borrowed-buffer UAF hazard under synchronous `Drop`.
  - GHC Haskell RTS (`safe`/`unsafe` FFI, `throwTo`/`mask`), Swift Concurrency (`TaskGroup`), and WebAssembly Stack Switching / WASI Preview 3 async ABI internals.
  - Hardware wall-clock nanosecond latency benchmarks across specific x86-64 / AArch64 microarchitectures.
- **Unknown**:
  - Final stabilization design of Rust's unstable `AsyncDrop` (`#126482`) regarding generic `?SyncDrop`/`AsyncDestruct` bounds vs. fallback sync drops.
  - Production tail-latency crossover points between Tokio's self-tuned `global_queue_interval` + `enable_eager_driver_handoff` and Go's `schedtick % 61` + `10ms` `sysmon` preemption across varying core counts and poll-time distributions.
- **Known not to apply**:
  - JDK 21 (`JEP 444`) carrier pinning on Java `synchronized` / `Object::wait` (`Pinned.MONITOR`) **no longer applies** to JDK 24+ (`JEP 491`) or examined `openjdk/jdk` (`4f33273115381cd7697082fcb1bb2642dae19043`).
  - Go's `cgo` `g0` stack-switch overhead **does not apply** to Go-to-Go calls or Rust/C++ stackless coroutines calling synchronous C FFI directly.
  - Tokio's `coop::Budget(128)` **does not apply** to unyielding synchronous CPU loops, blocking syscalls, or non-coop third-party futures.
  - Classic Chase-Lev `pop_bottom` `SeqCst` fence requirements (Lê et al. 2013) **do not directly apply** to Go's `runqget` or Tokio's `queue::Local::pop`, which pop FIFO from `head` via Acquire/Release CAS.
- **Unsupported**:
  - Performing OCaml 5 algebraic effects across an interleaved native C FFI frame is explicitly unsupported (`Stdlib.Effect.Unhandled`).
  - Multi-shot continuation resumption is explicitly unsupported in OCaml 5 (`Effect.Continuation_already_resumed`) and OpenJDK `Continuation`.
  - Unmounting OpenJDK virtual threads with active native JNI/FFM frames on the stack is explicitly unsupported (`freeze_pinned_native` / `Pinned.NATIVE`).
  - Stable Rust `AsyncDrop` is explicitly unsupported on stable toolchains as of `rust-lang/rust` @ `b0b600668bb9b4a897e2299b0a44289d42276545`.

## Evidence

All primary sources and probe outputs below were directly resolved and verified on `2026-11-19`:

### Pinned Upstream Source Inspections

| Repository & 40-char Revision | Inspected Files, Line Ranges & Verified Symbols |
| :--- | :--- |
| **`golang/go`** `b496a3044e1dcdc3eed0af3e0e89db92f740d764` | `src/runtime/stack.go:75-82,133,954,1080,1204-1214,1311-1360` (`stackMin=2048`, `stackPreempt`, `copystack`, `newstack` `2x`, `shrinkstack` `<1/4`); `runtime2.go:891-906` (`runq [256]guintptr`, `runnext`); `proc.go:3496-3501,6725-6756,7583-7610,7703-7724,7767-7775` (`schedtick%61`, `forcePreemptNS=10ms`, `!haveSysmon`, `runqget` `inheritTime`, `runqgrab`); `preempt.go:357-373,426-446` (`asyncPreempt2`, `isAsyncSafePoint`); `cgocall.go:7-28` (`entersyscall`, `asmcgocall` onto `g0`, `exitsyscall`). |
| **`openjdk/jdk`** `4f33273115381cd7697082fcb1bb2642dae19043` | `src/java.base/share/classes/jdk/internal/vm/Continuation.java:58-89,298-355` (`enum Pinned { NATIVE, CRITICAL_SECTION, EXCEPTION }`, `doYield`, `enterSpecial`); `src/hotspot/share/runtime/continuationFreezeThaw.cpp:937,949,1378,1971,2027,2054,2068` (`freeze_pinned_native`, `freeze_pinned_cs`); `src/hotspot/share/oops/stackChunkOop.cpp`; `src/java.base/share/classes/java/lang/VirtualThread.java:125-175,1330-1356` (`BLOCKING..TIMED_WAIT`, `ForkJoinPool` `asyncMode=true`, `maxPoolSize=max(p,256)`); `src/java.base/share/classes/java/util/concurrent/StructuredTaskScope.java:378-395,573,1275-1277` (`@since 28`, `sealed interface`, `open(Joiner)`). |
| **`erlang/otp`** `2f60d1b6a246b3f7ae997fd93a9af067fab7f981` | `erts/emulator/beam/erl_vm.h:47` (`CONTEXT_REDS 4000`); `erl_process.h:111-112,472-511,1043-1067` (dirty CPU/IO counts, `ErtsRunQueue_`, `struct process` `htop`/`stop`/`fcalls`); `erl_process.c:59-65,4468-4711,4894,9607,9813,9907` (`ERTS_RUNQ_CHECK_BALANCE_REDS_PER_SCHED`, `try_steal_task`, `check_balance`, `erts_schedule`); `erl_nif.h:42-47,239-243` (`enif_consume_timeslice`, `ERL_NIF_DIRTY_JOB_{CPU,IO}_BOUND`). |
| **`tokio-rs/tokio`** `fc0d151753b5fb10125ecef2d48f29b192c9abcf` | `tokio/src/runtime/scheduler/multi_thread/worker.rs:125-129,272,672-786,827-841,1078-1110,1321-1328` (`lifo_slot`, `MAX_LIFO_POLLS_PER_TICK=3`, `enable_eager_driver_handoff`, `maintenance`, `next_task`); `builder.rs:278-296` (`event_interval=61`, `4` on loom); `queue.rs:37-65,300-358,361-399,420-495` (`LOCAL_QUEUE_CAPACITY=256`, packed `head`, FIFO `pop`, single-stealer `steal_into2` `n - n/2`); `task/coop/mod.rs:115-126,291-345,396-427` (`Budget(Some(128))`, `poll_proceed`, `RestoreOnPending`); `macros/select.rs:73-83,101-163`; `io/util/read_exact.rs:34-65`; `sync/mpsc/bounded.rs:67,1087-1119`. |
| **`python-trio/trio`** `c327959a7175c86e1801b4ee8a17920c82b415e5` | `src/trio/_core/_run.py:353-390,472-520,543,632,928,1183,3019,3057` (`CancelStatus`, `shield`, `CancelScope`, `Nursery`, `checkpoint`); `_exceptions.py:52` (`Cancelled(BaseException)`); `_ki.py:1-55`. |
| **`ocaml/ocaml`** `d921d1e86c56baa7b30e890ced455c12255793f5` | `runtime/caml/fiber.h:28-92` (`stack_handler`, `stack_info`, fiber stack layout); `runtime/fiber.c:53-105,537-615` (`NUM_STACK_SIZE_CLASSES=5`, `caml_try_realloc_stack`). |
| **`ocaml-multicore/eio`** `07069de0954fd2d991d7b2f6ea555f28c7abc2d4` | `lib_eio/core/cancel.ml:1-60,174-220` (`Cancel.t`, `protected`, `cancel_fn`, `Domain.id`); `fiber.ml:8-33` (`Effect.perform (Fork ...)`); `switch.ml`. |
| **`Kotlin/kotlinx.coroutines`** `7f4d6cf2414937b50291df6169a69afbaf9c5a20` | `kotlinx-coroutines-core/common/src/Job.kt:50-95` (`Job` lifecycle state machine); `NonCancellable.kt:8-45` (`withContext(NonCancellable)` and `launch(NonCancellable)` warning). |
| **`rust-lang/rust`** `b0b600668bb9b4a897e2299b0a44289d42276545` | `library/core/src/future/future.rs:45-114` (`Future::poll`); `library/core/src/future/async_drop.rs:1-58` (`#![unstable(feature = "async_drop", issue = "126482")]`, `AsyncDrop`, `async_drop_in_place`). |
| **`llvm/llvm-project`** `d56bc48c9c0ea19b58427b3c6f114bd669710cbd` | `llvm/lib/Transforms/Coroutines/CoroElide.cpp:355-425` (`lifetimeEligibleForElide`, `DT.dominates`, `canCoroBeginEscape`, `attemptElide`, `elideHeapAllocations`). |
| **`tokio-rs/loom`** `9d549cd5357a5485900f4c53951fc1726319659f` | `src/model.rs:17-43,108-127` (`Builder::preemption_bound`, `LOOM_MAX_PREEMPTIONS`). |
| **`awslabs/shuttle`** `72bdbdb612c2311905c84bbc73d59f12a5b17e43` | `shuttle/src/scheduler/mod.rs:8-10`; `shuttle-schedulers/src/pct.rs:21-33` (`PctScheduler`, `change_points`). |

### Primary Literature and Specifications

- David Chase & Yossi Lev (2005), *"Dynamic Circular Work-Stealing Deque"*, SPAA '05, DOI `10.1145/1073970.1073974`.
- Nhat Minh Lê, Antoniu Pop, Albert Cohen & Francesco Zappa Nardelli (2013), *"Correct and Efficient Work-Stealing for Weak Memory Models"*, PPoPP '13, pp. 69–80, DOI `10.1145/2442516.2442524`.
- Robert D. Blumofe & Charles E. Leiserson (1999), *"Scheduling Multithreaded Computations by Work Stealing"*, JACM 46(5), DOI `10.1145/324133.324234`.
- Richard Smith & Gor Nishanov (2018-03-18), *"Halo: coroutine Heap Allocation eLision Optimization: the joint response"*, WG21 `P0981R0`.
- Bob Nystrom (2015-02-01), *"What Color is Your Function?"*.
- Nathaniel J. Smith (2018-04-25), *"Notes on structured concurrency, or: Go statement considered harmful"*, `https://vorpus.org/blog/notes-on-structured-concurrency-or-go-statement-considered-harmful/`.
- KC Sivaramakrishnan, Stephen Dolan, Leo White, Tom Kelly, Sadiq Jaffer & Anil Madhavapeddy (2021), *"Retrofitting Effect Handlers onto OCaml"*, PLDI '21, DOI `10.1145/3453483.3454039`.
- Cormac Flanagan & Patrice Godefroid (2005), *"Dynamic Partial-Order Reduction for Model Checking Software"*, POPL '05, DOI `10.1145/1040305.1040315`.
- Sebastian Burckhardt, Pravesh Kothari, Madanlal Musuvathi & Santosh Nagarakatte (2010), *"A Randomized Scheduler with Probabilistic Guarantees of Finding Bugs"*, ASPLOS '10, pp. 167–178, DOI `10.1145/1735970.1736040`.
- OpenJDK JEPs: `JEP 444` (Virtual Threads, JDK 21), `JEP 491` (Synchronize Virtual Threads without Pinning, JDK 24), and Structured Concurrency (`JEP 453` JDK 21 -> `JEP 480` JDK 23 -> `JEP 499` JDK 24 -> `JEP 505` JDK 25 -> finalized `@since 28` API in examined `openjdk/jdk`).

### Executable Probe Artifact

- **Script**: `support/verify_cancellation_and_scheduler_semantics.py` (Python 3.10+ stdlib only, zero external dependencies).
- **Invocation**: `python3 -B reports/async-runtimes-coroutines-schedulers-and-cancellation-semantics/support/verify_cancellation_and_scheduler_semantics.py` — exited `0` on `2026-11-19`, verifying all cancellation, LIFO-starvation, cooperative-blindspot, and 256-slot work-stealing conservation assertions reported in Sections 2.3 and 3.3.

## Revalidation

To verify these findings against newer upstream releases without repeating a broad survey:

1. **Re-run the standalone executable probe**:
   ```console
   python3 -B reports/async-runtimes-coroutines-schedulers-and-cancellation-semantics/support/verify_cancellation_and_scheduler_semantics.py
   ```
   A `0` exit code confirms all modeled cancellation, LIFO-starvation, preemption, and queue-conservation assertions still hold.
2. **Diff narrow upstream anchors**:
   - **Tokio**: `worker.rs` (`MAX_LIFO_POLLS_PER_TICK`, `enable_eager_driver_handoff`), `queue.rs` (`LOCAL_QUEUE_CAPACITY`, single-stealer `steal_into2`), `builder.rs` (`event_interval`), and `task/coop/mod.rs` (`Budget::initial()`).
   - **Go**: `src/runtime/stack.go` (`stackMin`, `newstack`, `shrinkstack`) and `proc.go` (`forcePreemptNS`, `schedtick%61`, `!haveSysmon` `runnext` guard).
   - **OpenJDK**: `Continuation.java` (`enum Pinned`), `continuationFreezeThaw.cpp` (`freeze_pinned_*`), and `StructuredTaskScope.java`.
   - **Erlang/OTP**: `erts/emulator/beam/erl_vm.h` (`CONTEXT_REDS`) and `erl_nif.h` (`ERL_NIF_DIRTY_JOB_*`).
   - **Rust & LLVM**: `library/core/src/future/async_drop.rs` (stabilization or `?SyncDrop`/`AsyncDestruct` changes) and `CoroElide.cpp` (`lifetimeEligibleForElide`).
   - **OCaml 5**: `runtime/caml/fiber.h` and `runtime/fiber.c` (whether effects across native C frames remain unsupported).

If a future runtime alters its fundamental execution contract (e.g., Rust stabilizing linear `!Leak` / `AsyncDrop` types or OpenJDK unpinning FFM native frames), repeat a full source review of that runtime rather than relying solely on the constant checks above.
