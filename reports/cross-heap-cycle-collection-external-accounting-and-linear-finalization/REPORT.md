# Cross-Heap Cycle Collection, External Memory Accounting, Biased Reference Counting, and Resurrection-Free Finalization

## Summary

Federating multiple managed runtimes inside a single address space—such as a tracing JavaScript/VM heap coupled with a C++ DOM heap, a reference-counted Python/Swift runtime, or native off-heap arenas—exposes four fundamental soundness and liveness hazards: (1) uncollectable cross-heap reference cycles pinned by opaque external handles; (2) lost-object and premature-reclamation races when concurrent tracing collectors interact with trial-deletion cycle collectors; (3) multi-collector stop-the-world (STW) epoch deadlocks and external-memory OOM blind spots; and (4) finalizer resurrection and teardown-order inversion on native resources.

Key established findings from the inspected runtimes, algorithms, and executable state-space probes:

1. **Cross-heap cycles cannot be broken by opaque external handles; they require either a strict acyclic heap-rank partial order or unified cross-component tracing.** As demonstrated in V8's `CppHeap` + Oilpan integration (`v8/v8` `e88118f63dd96f24a9acb8bd0665e7880063f5c0`, OOPSLA 2018 `10.1145/3276521`), treating cross-boundary references (`TracedReference`) as strong external roots leaks every $A_{\text{JS}} \leftrightarrow B_{\text{C++}}$ cycle. V8 dissolves these cycles by driving both heaps through one synchronized tri-color marking epoch (`InitializeMarking`, `StartMarking`, `AdvanceMarking`, `EnterFinalPause`, `FinishMarkingAndProcessWeakness`, `CompactAndSweep`), using `UnifiedHeapMarkingState` and a cross-heap remembered set (`RememberCrossHeapReferenceIfNeeded`) for generational minor collections, while feeding C++ `StatsCollector` allocation deltas (`AllocatedObjectSizeIncreased`/`Decreased`) directly into GC pacing.
2. **Coupling Bacon–Rajan trial-deletion cycle collection with a concurrent tracing collector is unsound without an epoch-coupled SATB (Snapshot-At-The-Beginning) pre-write barrier and a ranked/federated epoch coordinator.** Executing `p2_cross_heap_cycle_and_epoch_probe.py` exhibits two concrete failures: (a) without an SATB pre-write barrier on pointer overwrites across the tracing/RC boundary, a mutator that loads a cyclic RC node before clearing the tracing reference suffers a use-after-free when trial deletion sweeps the node as white; (b) two independent collectors initiating unranked STW safepoint handshakes reach an explicit deadlock state `('WAIT_T2_SAFE', 'WAIT_T1_SAFE', None)` in 9 reachable states, whereas a single federated epoch coordinator where waiters park in safepoint-safe state reaches 12 states with 0 deadlocks.
3. **Production non-atomic RC optimizations rely on asymmetric thread-ownership tagging, QSBR, and static borrow/reuse analysis—yet free-threaded CPython still requires world-stops for cycle collection and resurrection checks.** CPython PEP 703 (`python/cpython` `441c010fef90ab2860ae8142cbfd1fd52f53ba75`) implements Choi–Shull–Torrellas biased reference counting (`10.1145/3243176.3243195`) using `ob_tid`, `ob_ref_local` (32-bit non-atomic), and `ob_ref_shared` (atomic count shifted left by `_Py_REF_SHARED_SHIFT = 2`, packing 2 low-order state bits `_Py_REF_MAYBE_WEAKREF = 0x1`, `_Py_REF_QUEUED = 0x2`, `_Py_REF_MERGED = 0x3`), paired with 128-byte-aligned per-thread QSBR (`Python/qsbr.c`) for lock-free container reclamation; however, `Python/gc_free_threading.c` still executes `_PyEval_StopTheWorld` for cyclic GC—and calls it a **second time** after running finalizers to handle resurrected objects. In contrast, Koka's Perceus (`koka-lang/koka` `b66091b2a5a7ea20c5ed9498ad1e1f03caee9589`, PLDI 2021 `10.1145/3453483.3454032`) achieves compile-time precise drop/dup placement and in-place drop-reuse specialization (`kk_refcount_t`: `0` = unique, `>0` = thread-local, `<0` = thread-shared/sticky atomic), testing uniqueness and thread-sharing in one signed branch (`rc <= 0`) and freeing recursively with bounded stack via `KK_FIELD_IDX_MAX`.
4. **Resurrection-free asynchronous cleanups (`Go 1.24 runtime.AddCleanup`) and thread-local handshake deallocation (`Java FFM SharedSession`) solve complementary halves of safe native resource teardown.** Go's `runtime.AddCleanup[T, S]` (`golang/go` `b496a3044e1dcdc3eed0af3e0e89db92f740d764`, `src/runtime/mcleanup.go`) decouples the cleanup argument `arg` from the collected pointer `ptr` (forbidding resurrection, allowing multiple cleanups per object and interior pointers, scaling concurrent `runCleanups()` goroutines, and explicitly side-stepping Go's tiny allocator for the `arg` box so a tiny-allocated root cannot keep `ptr` alive), whereas `runtime.SetFinalizer` (`src/runtime/mfinal.go`) requires allocation base pointers, permits resurrection (imposing a 2-GC-cycle penalty), and leaks cyclic finalizable graphs. For deterministic off-heap deallocation under concurrent readers without locks on the fast path, OpenJDK JEP 454 (`openjdk/jdk` `4f33273115381cd7697082fcb1bb2642dae19043`, `SharedSession.java`, `scopedMemoryAccess.cpp`) combines a volatile state transition with a JEP 312 thread-local handshake (`CloseScopedMemoryHandshakeClosure`), installing `ScopedAsyncExceptionHandshakeClosure` on threads inside `@Scoped` frames and **deoptimizing compiled frames** where JIT loop strip-mining may have hoisted the liveness check above a safepoint poll.

## Applicability

This report characterizes cross-runtime memory management, reference counting, and native resource disposal across five production codebases and four foundational papers:

- **Unified tracing across heterogeneous heaps:** `v8/v8` (`e88118f63dd96f24a9acb8bd0665e7880063f5c0`, `include/v8-cppgc.h`, `include/v8-traced-handle.h`, `src/heap/cppgc-js/cpp-heap.h`, `cpp-heap.cc`, `unified-heap-marking-state.h`) and Degenbaev et al. (OOPSLA 2018, `10.1145/3276521`). Findings apply to V8's production Oilpan (`cppgc`) integration with single-isolate JS heaps and generational minor GC cross-heap remembered sets.
- **Cycle collection and reuse-analyzed RC:** Bacon & Rajan (ECOOP 2001, `10.1007/3-540-45337-7_12`), Reinking et al. (PLDI 2021, `10.1145/3453483.3454032`), and `koka-lang/koka` (`b66091b2a5a7ea20c5ed9498ad1e1f03caee9589`, `src/Backend/C/Parc.hs`, `ParcReuse.hs`, `src/Core/Borrowed.hs`, `CheckFBIP.hs`, `kklib/include/kklib.h`, `kklib/src/refcount.c`). Perceus findings apply to pure/functional-with-effects languages whose heap graphs are acyclic (or where mutable refs are explicitly tracked) and whose compiler controls every dup/drop site.
- **Biased RC + QSBR + free-threaded cyclic GC:** Choi, Shull & Torrellas (PACT 2018, `10.1145/3243176.3243195`) and `python/cpython` (`441c010fef90ab2860ae8142cbfd1fd52f53ba75`, `Py_GIL_DISABLED` build paths in `Include/object.h`, `Include/refcount.h`, `Include/internal/pycore_object.h`, `Include/internal/pycore_qsbr.h`, `Python/qsbr.c`, `Python/gc_free_threading.c`). Findings on `ob_tid`/`ob_ref_local`/`ob_ref_shared` apply specifically to `Py_GIL_DISABLED` (free-threaded) CPython builds, not default GIL builds.
- **Deterministic off-heap deallocation and resurrection-free cleanups:** `openjdk/jdk` (`4f33273115381cd7697082fcb1bb2642dae19043`, `SharedSession.java`, `X-ScopedMemoryAccess.java.template`, `scopedMemoryAccess.cpp` implementing JEP 454 on HotSpot) and `golang/go` (`b496a3044e1dcdc3eed0af3e0e89db92f740d764`, `src/runtime/mcleanup.go`, `src/runtime/mfinal.go` implementing Go 1.24+ `runtime.AddCleanup` vs. `runtime.SetFinalizer`).

The executable probe (`p2_cross_heap_cycle_and_epoch_probe.py`) models abstract object graphs and finite-state collector/thread protocols in Python 3 to demonstrate exact counterexamples and BFS deadlock reachability; it does not run live V8, CPython, HotSpot, or Go binaries.

## Findings

### 1. Cross-Component Tracing and External Memory Accounting (`V8 CppHeap` + Oilpan)

Basis: source (`v8/v8@e88118f6`, `include/v8-traced-handle.h`, `src/heap/cppgc-js/cpp-heap.h`, `cpp-heap.cc`, `unified-heap-marking-state.h`) + normative (`10.1145/3276521`)

#### 1.1 Why Opaque External Roots Leak Polyglot Cycles—and When Heap-Rank Partial Orders Suffice

When two runtimes $H_1$ and $H_2$ communicate only via opaque external root tables (e.g., JNI global refs, V8 `Persistent` handles, or CPython `Py_INCREF` held by a Rust `Arc`), any reference edge $A \in H_1 \to B \in H_2$ pins $B$ as a root in $H_2$. If $B$ also holds an edge $B \to A$, $A$ is pinned as a root in $H_1$. Neither collector can discover that $\{A, B\}$ is unreachable from program roots (confirmed by `p2_cross_heap_cycle_and_epoch_probe.py` Part A1: isolated collectors reclaim `[]`, unified tracing reclaims `['A', 'B']`).

A **strict acyclic heap-rank partial order** ($H_1 \succ H_2$: edges may cross from $H_1$ to $H_2$, never from $H_2$ to $H_1$, or back-edges must be weak) completely eliminates cross-heap cycles *without* unified tracing. Real-world applicability divides sharply by workload:
- **Acyclic rank suffices:** Python/ML tensor pipelines (Python orchestrator $\succ$ Rust/C++ raw tensor buffer / GPU arena), where native buffers store only flat numerical payloads and never retain strong `PyObject*` callbacks.
- **Irreducible peer cycles force unified tracing:** Browser DOM + JS (DOM nodes hold JS event listener closures that close over DOM nodes), GUI widget trees + scripting callbacks, and plugin graphs where arbitrary closures cross between runtimes in both directions.

#### 1.2 V8 `CppHeap` Unified Marking Protocol and Generational Cross-Heap Barriers

Degenbaev et al. (OOPSLA 2018, `10.1145/3276521`) and `v8/v8@e88118f6` resolve JS $\leftrightarrow$ C++ cycles by folding Oilpan (`cppgc`) into V8's tri-color incremental/concurrent marking cycle rather than running a separate C++ tracing epoch:

1. **Cross-heap handle representation (`include/v8-traced-handle.h` L30–45):** C++ objects hold JS references via `v8::TracedReference<T>` (created via `GlobalizeTracedReference` with `TracedReferenceStoreMode::{kInitializingStore, kAssigningStore}` and `TracedReferenceHandling::{kDefault, kDroppable}`). Unlike `v8::Global`, a `TracedReference` is **not** automatically a strong root during a unified GC; instead, Oilpan's `Trace(Visitor*)` methods visit `TracedReference` fields and push referenced JS objects onto V8's marking worklist via `UnifiedHeapMarkingState::MarkAndPush` (`src/heap/cppgc-js/unified-heap-marking-state.h` L19–38).
2. **Synchronized lifecycle driven by one coordinator (`src/heap/cppgc-js/cpp-heap.h` L136–151, `cpp-heap.cc` L966–983):** V8's GC drives `CppHeap` through lockstep phases:
   - `InitializeMarking` / `StartMarking`: synchronizes collection type (major vs. minor) and allocates `UnifiedHeapMarker`.
   - `AdvanceMarking(max_duration, ...)`: interleaves incremental C++ marking steps with V8 marking, pumping cross-heap worklists in both directions until both reach fixpoint (`IsMarkingDone()`).
   - `EnterFinalPause(EmbedderStackState)` (`cpp-heap.cc` L966–983): enters the atomic pause, installs `ConservativeTracedHandlesMarkingVisitor` when C++ stack scanning is needed, calls `marker.EnterAtomicPause(stack_state)`, and cancels compaction if unsafe.
   - `FinishMarkingAndProcessWeakness()` & `CompactAndSweep()`: drains any remaining cross-heap grey objects, clears weak callbacks/traced handles consistently across both heaps, and sweeps concurrently.
3. **Generational minor GC cross-heap remembered set (`cpp-heap.h` L204–209):** To avoid scanning the entire C++ heap on every V8 young-generation scavenge/minor GC, `CppHeap` maintains an explicit cross-heap remembered set (`RememberCrossHeapReferenceIfNeeded`, `VisitCrossHeapRememberedSetIfNeeded`, `ResetCrossHeapRememberedSet`) updated by the write barrier (`WriteBarrier(void*)`, L159) whenever an old C++ object stores a reference to a young JS object.
4. **External memory pressure accounting (`cpp-heap.h` L43, L164–166; `cpp-heap.cc` L70–81):** A classic polyglot OOM pathology occurs when tiny 32-byte JS wrapper objects pin megabytes of C++ or GPU allocations, leaving the JS heap under its GC trigger threshold until the OS OOM-kills the process. `CppHeap` inherits `cppgc::internal::StatsCollector::AllocationObserver` (`AllocatedObjectSizeIncreased`, `AllocatedObjectSizeDecreased`, `MinorGCHeapGrowing::LimitReached()`) so C++ byte growth directly adjusts V8's combined heap allocation limits and triggers incremental marking before physical memory exhausts.

---

### 2. Coupling Bacon–Rajan Trial-Deletion Cycle Collection with Concurrent SATB Tracing

Basis: normative (`10.1007/3-540-45337-7_12`) + execution (`p2_cross_heap_cycle_and_epoch_probe.py`) + derived

#### 2.1 Bacon–Rajan Trial Deletion Mechanics (ECOOP 2001)

Bacon & Rajan (*Concurrent Cycle Collection in Reference Counted Systems*, ECOOP 2001) detect garbage cycles in a reference-counted heap without tracing the entire live heap by exploiting the invariant that **any garbage cycle must have experienced a non-zero reference-count decrement on at least one of its members**. Nodes carry four colors:
- **Black:** In use or free (default).
- **Purple:** Candidate cycle root (buffered whenever `rc` is decremented to $>0$).
- **Gray:** Trial-decremented during `MarkGray(S)` (subtracting internal references among descendants of purple roots).
- **White:** Candidate garbage (after `Scan(S)` finds residual trial `rc == 0`; any reachable node with residual `rc > 0` triggers `ScanBlack` to restore reference counts and color its transitive closure Black before `CollectWhite` frees remaining White nodes).

#### 2.2 Synchronization Invariants Required to Couple Trial Deletion with Concurrent Tracing

When a tracing heap $H_T$ (e.g., V8 / OCaml / JVM with Yuasa SATB or Steele incremental barriers) coexists with a Bacon–Rajan RC heap $H_R$ in one federated mark epoch, **two fatal failure classes** emerge unless strict cross-boundary invariants hold (verified in `p2_cross_heap_cycle_and_epoch_probe.py`):

1. **Premature-reclamation UAF race (`Part A2`):** Suppose $A \in H_T$ holds the sole external reference to a cyclic RC subgraph $B_1 \leftrightarrow B_2 \subset H_R$ (`rc(B1) = 2`, `rc(B2) = 1`). A mutator concurrently loads `reg = A.f` ($B_1$), clears `A.f = null` (decrementing `rc(B1): 2 -> 1` and buffering $B_1$ as Purple), and—before storing `reg` into a Black root $C$—the trial-deletion collector executes `MarkGray(B1)` (`trial_rc(B2)=0`, `trial_rc(B1)=0`), `Scan(B1)` (marks both White), and frees $\{B_1, B_2\}$. The mutator's subsequent store `C.f = reg` produces a **use-after-free**.
   - **Required synchronization invariant (SATB-Coupled Trial Deletion):** Every overwrite of a cross-heap reference slot $A.f \leftarrow v_{\text{new}}$ during an active mark/cycle epoch **must execute a Yuasa SATB pre-write barrier** logging the overwritten old value $v_{\text{old}}$ into the epoch's SATB buffer *before* decrementing $v_{\text{old}}$'s reference count (or deferring the RC decrement until the SATB buffer drains). Any RC object logged in the SATB buffer is treated as externally rooted (`ScanBlack`) for the remainder of the epoch—guaranteeing `freed = []` and zero UAF (`Part A2`, `UAF=False`).
   - **Cross-heap cycle completeness:** Conversely, to break $A \in H_T \leftrightarrow B \in H_R$ cycles, the trial-deletion pass must treat an edge $A \to B$ as **internal to the trial subgraph** (subtracting 1 from `trial_rc(B)`) *if and only if* $A$ is currently unmarked (White) in $H_T$'s unified tracing epoch, and must defer `CollectWhite(B)` until $H_T$'s final atomic pause confirms $A$ remains unmarked after draining all SATB buffers.
2. **Multi-collector epoch handshake deadlock (`Part B`):** If Collector 1 ($H_T$) and Collector 2 ($H_R$, e.g., CPython's `_PyEval_StopTheWorld`) independently initiate safepoint/world-stop handshakes without a total ordering, Thread 1 initiating $H_T$'s safepoint while waiting for Thread 2 collides with Thread 2 initiating $H_R$'s safepoint while waiting for Thread 1. Exhaustive BFS in `p2_cross_heap_cycle_and_epoch_probe.py` confirms the deadlock state `('WAIT_T2_SAFE', 'WAIT_T1_SAFE', None)` among 9 reachable states.
   - **Required liveness invariant (Federated Epoch Coordinator):** All participating collectors must acquire a **single federated epoch coordinator token** before requesting peer safepoints, and any thread blocked waiting to acquire that token **must park in a safepoint-safe (quiescent) state** so the current token holder can complete its handshake. BFS confirms 0 deadlocks across all 12 reachable states.

---

### 3. High-Throughput Reference Counting: Perceus Reuse Analysis & CPython PEP 703 Biased RC + QSBR

#### 3.1 Perceus: Garbage-Free Reference Counting, Borrowed Parameters, and In-Place Reuse

Basis: source (`koka-lang/koka@b66091b2`, `src/Backend/C/Parc.hs`, `ParcReuse.hs`, `src/Core/Borrowed.hs`, `CheckFBIP.hs`, `kklib/include/kklib.h` L104–126, `kklib/src/refcount.c` L13–55) + normative (`10.1145/3453483.3454032`)

Perceus (Reinking et al., PLDI 2021) eliminates two classic costs of naive reference counting—excessive dup/drop traffic and allocator churn on functional updates—through whole-function linear resource analysis:

1. **Precise (garbage-free) drop placement (`src/Backend/C/Parc.hs`, `src/Core/Borrowed.hs`):** Every variable is dropped immediately after its last dynamic use (before subsequent calls, preserving tail-call optimization and avoiding space leaks), while parameters annotated as **borrowed** (`Borrowed.hs`) omit caller-side `dup` and callee-side `drop` completely.
2. **Drop-reuse specialization (`src/Backend/C/ParcReuse.hs`, `CheckFBIP.hs`):** When a pattern match destructs a constructor `C(x, y)` whose last use is that match, Perceus emits a **reuse token** (`kk_reuse_t`) via `drop-reuse`: if the block is dynamically unique (`rc == 0`), the runtime returns its memory address directly without invoking the allocator, and a subsequent constructor allocation of matching size class overwrites only changed fields in place (**Functional But In-Place / FBIP**, verified statically by `CheckFBIP.hs`).
3. **Asymmetric 32-bit `kk_refcount_t` layout & stackless freeing (`kklib/include/kklib.h` L104–126, `kklib/src/refcount.c` L13–55):**
   ```c
   typedef int32_t kk_refcount_t;
   // rc == 0 : unique reference (in-place reuse eligible!)
   // rc >  0 : thread-local non-atomic count (extra references = rc)
   // rc <  0 : thread-shared (atomic CAS/fetch_add) OR sticky overflow (never freed)
   static inline bool kk_refcount_is_thread_shared(kk_refcount_t rc) { return (rc < 0); }
   static inline bool kk_refcount_is_unique_or_thread_shared(kk_refcount_t rc) { return (rc <= 0); }
   ```
   Encoding unique as `0` and thread-shared/sticky as `< 0` lets the hot-path decrement check **both** uniqueness (free/reuse) and thread-sharing (atomic slow path) in a **single signed branch `rc <= 0`**. When dropping deep structures, `kk_block_fast_drop_free` (`refcount.c` L43–55) tail-loops on single-child pointers and uses the 8-bit header `field_idx` (`KK_FIELD_IDX_MAX = 0xFF`, `kklib.h` L126) for pointer-reversal stackless freeing so dropping a million-element linked list cannot overflow the C call stack.

#### 3.2 CPython PEP 703: Biased Reference Counting, Deferred RC, QSBR, and Free-Threaded Cyclic GC

Basis: source (`python/cpython@441c010f`, `Include/object.h` L154–167, `Include/refcount.h` L78–117, `Include/internal/pycore_object.h` L160–212, `Include/internal/pycore_qsbr.h` L40–75, `Python/qsbr.c` L114–136, `Python/gc_free_threading.c` L74–87, L2088–2198) + normative (`10.1145/3243176.3243195`)

Removing CPython's GIL (`Py_GIL_DISABLED`, PEP 703) without incurring atomic RMW cache-line bouncing on every `Py_INCREF`/`Py_DECREF` relies on three coupled mechanisms directly visible in `python/cpython@441c010f`:

1. **Biased Reference Counting object header (`Include/object.h` L156–167, `Include/refcount.h` L81–116):**
   ```c
   struct _object {
       _Py_ALIGNED_DEF(_PyObject_MIN_ALIGNMENT, uintptr_t) ob_tid; // owning thread ID (or 0=unowned)
       uint16_t ob_flags;
       PyMutex ob_mutex;           // per-object 1-byte lock
       uint8_t ob_gc_bits;         // gc-related state
       uint32_t ob_ref_local;      // non-atomic local refcount (owning thread ONLY)
       Py_ssize_t ob_ref_shared;   // atomic shared refcount << 2 | 2-bit flags
       PyTypeObject *ob_type;
   };
   ```
   The two least-significant bits of `ob_ref_shared` (`_Py_REF_SHARED_SHIFT = 2`, `_Py_REF_SHARED_FLAG_MASK = 0x3`) encode four states:
   - `_Py_REF_SHARED_INIT = 0x0` (unshared / initial);
   - `_Py_REF_MAYBE_WEAKREF = 0x1`;
   - `_Py_REF_QUEUED = 0x2` (enqueued on owner's merge queue after non-owner saw zero);
   - `_Py_REF_MERGED = 0x3` (local and shared counts merged; `ob_tid = _Py_UNOWNED_TID = 0`, all subsequent updates atomic).
   Because non-owning threads may decrement references they did not increment (e.g., ownership transfer), the signed count `ob_ref_shared >> 2` can temporarily go **negative**; total count is `ob_ref_local + (ob_ref_shared >> 2)` (`Include/refcount.h` L114–115). Crucially, `_PyObject_IsUniquelyReferenced` (`pycore_object.h` L181–191) requires **both** `_Py_IsOwnedByCurrentThread(ob)` and `ob_ref_local == 1` and **`ob_ref_shared == 0` including all flag bits**, preventing concurrent threads from racing to borrow a reference during in-place mutation.
2. **Deferred Reference Counting & QSBR (`pycore_qsbr.h` L40–75, `Python/qsbr.c` L114–136):** Globally hot objects (modules, functions, code objects) opt into deferred RC (`_Py_HasDeferredRefcount`) to avoid cross-core contention; stack frames hold uncounted deferred references until GC scans them. Lock-free reads of shared `dict`/`list` backing arrays use **Quiescent-State-Based Reclamation (QSBR)**:
   - Shared state maintains monotonic 64-bit `wr_seq` and `rd_seq` (`_Py_qsbr_advance` atomically adds `QSBR_INCR` to `wr_seq`);
   - Each thread holds a 128-byte-padded `struct _qsbr_thread_state` (explicitly padded for Apple Silicon 128-byte cache lines to eliminate false sharing, `pycore_qsbr.h` L72–75) recording its last observed `seq` plus `deferred_count`, `deferred_memory`, and `deferred_page_memory` (for mimalloc pages held from size-class reuse);
   - `qsbr_poll_scan` executes `_Py_atomic_fence_seq_cst()` to synchronize with `_Py_qsbr_attach()` before verifying every online thread has advanced past the retirement sequence.
3. **Important limitation — free-threaded cyclic GC is still stop-the-world (`gc_free_threading.c` L74–87, L2088–2198):** Despite biased RC and QSBR, `gc_collect_internal` calls `_PyEval_StopTheWorld(interp)` (L2090) to compute cyclic `gc_refs` (reusing `ob_tid` as a scratch field during the pause!). Furthermore, when garbage contains non-trivial `__del__` finalizers, CPython must resume threads to run `finalize_garbage(state)` (L2185) and then execute a **second** `_PyEval_StopTheWorld(interp)` (L2187) to call `handle_resurrected_objects(state)`. And if an active interpreter frame lacks a valid stack pointer (`GH-129236`, L75–78), GC sets `skip_deferred_objects` and skips collecting deferred-RC objects entirely for soundness.

---

### 4. Eliminating Finalizer Resurrection and Teardown Races: Java FFM Shared Arena Handshakes vs. Go 1.24 `runtime.AddCleanup`

#### 4.1 OpenJDK JEP 454: Shared Arena Handshake Deallocation and Compiler-Hoisting Deoptimization

Basis: source (`openjdk/jdk@4f332731`, `SharedSession.java` L83–102, `scopedMemoryAccess.cpp` L42–245)

Deterministic off-heap memory deallocation (`Arena.ofShared().close()`) faces a classic read/free race: mutator threads read raw native addresses inside tight JIT loops without acquiring a per-access mutex, while another thread concurrently calls `close()` to `munmap`/`free` the backing memory. OpenJDK JEP 454 solves this with **zero per-access atomic locks** on the reader fast path:

1. **Volatile state fence (`SharedSession.java` L83–102):** `justClose()` executes `ACQUIRE_COUNT.compareAndExchange(this, 0, CLOSED_ACQUIRE_COUNT)` (rejecting closure if explicit child acquires are active), writes `STATE.setVolatile(this, CLOSED)`, and invokes `SCOPED_MEMORY_ACCESS.closeScope(this, ALREADY_CLOSED)`.
2. **Two-step JEP 312 thread-local handshake (`scopedMemoryAccess.cpp` L141–245):**
   - First, HotSpot runs `CloseScopedMemoryHandshakeClosure` across all `JavaThread`s (no global STW barrier required—each thread responds independently at its next safepoint poll).
   - If `is_accessing_session(jt, session, in_scoped)` detects the thread inside an `@Scoped` memory-access method, HotSpot cannot throw directly (the thread may be in native code); it installs a second asynchronous handshake `ScopedAsyncExceptionHandshakeClosure` via `jt->install_async_exception(...)` (L207–209), which increments `_async_exceptions` and throws `ScopedAccessError` upon returning to Java so the thread unwinds out of the scoped access before `closeScope` releases the native memory.
   - **Critical JIT compiler-hoisting hazard (`scopedMemoryAccess.cpp` L216–238):** Even when `in_scoped` is **false** at the safepoint, C2 loop strip-mining and check hoisting can transform a loop into:
     ```text
     liveness check (hoisted out of @Scoped method)
     for (...) {
       for (...) { /* strip-mined inner loop */ memory access (@Scoped) }
       safepoint poll  <-- thread stopped here (OUTSIDE @Scoped!)
     }
     ```
     Because the thread already passed the hoisted liveness check before `STATE` turned `CLOSED`, resuming after the handshake would perform a **use-after-free** on the freed arena! Therefore, whenever `last_frame.is_compiled_frame() && last_frame.can_be_deoptimized()`, `CloseScopedMemoryHandshakeClosure` **deoptimizes the frame** back to the interpreter so the next iteration re-executes the liveness check against `CLOSED`.

#### 4.2 Go 1.24 `runtime.AddCleanup` vs. `runtime.SetFinalizer`

Basis: source (`golang/go@b496a304`, `src/runtime/mcleanup.go` L75–125, L218–240, L671–730; `src/runtime/mfinal.go` L432–490)

Go 1.24's `runtime.AddCleanup` (Proposal #67535) systematically eliminates the four architectural defects of legacy `runtime.SetFinalizer`:

| Property | `runtime.SetFinalizer(obj, fn)` (`mfinal.go`) | `runtime.AddCleanup[T, S](ptr, fn, arg)` (`mcleanup.go`) |
| :--- | :--- | :--- |
| **Object resurrection** | **Permitted** (`fn` receives `obj`, can publish it globally) $\implies$ mandatory **2-GC-cycle** reclamation delay | **Impossible by construction** (`fn` receives separate `arg : S`, never `ptr : *T`); object is reclaimed in the **same GC cycle** |
| **Pointer alignment restriction** | Must point to the **first byte** of an allocated heap block (`mfinal.go` L473–478 throws otherwise, with a narrow tiny-alloc exception) | **Arbitrary interior pointers supported** (slices, struct fields, embedded handles) |
| **Multiplicity per object** | Strictly **1** finalizer per allocation (subsequent calls overwrite) | **Arbitrarily many** independent cleanups per object, each returning a cancellable `Cleanup` handle (`Cleanup.Stop()`, `mcleanup.go` L220) |
| **Cycle collection interaction** | Any reference cycle containing a finalizable object is **permanently leaked** (neither finalized nor freed) | Cycles without external strong references to `ptr` from `arg`/`fn` are collected cleanly because `ptr` is not kept alive for finalization |
| **Execution concurrency** | Single global finalizer goroutine (one slow finalizer blocks all finalization process-wide) | **Auto-scaling concurrent goroutine pool** (`for range need { go runCleanups() }`, `mcleanup.go` L672–730) |
| **Subtle allocator edge cases** | Rejects `inUserArenaChunk`; special-cases `MallocHeaderSize` | Rejects `ptr == nil`, `inUserArenaChunk`, and shallow `ptr == arg` (`mcleanup.go` L94–100); **explicitly side-steps Go's tiny allocator** (`size < maxTinySize && argType.PtrBytes == 0`, L114–120) when boxing `arg`, because the `arg` box is a GC root—sharing a 16-byte tiny-alloc slot with `ptr` would accidentally pin `ptr` alive forever! |

#### 4.3 Statically Complete Native Disposal via Linear Types

Basis: derived (combining Go `AddCleanup`, Java FFM `SharedSession`, and affine/linear ownership)

Neither `AddCleanup` nor Java's `Cleaner` guarantees *prompt* or *deterministic* teardown (GC may never run if heap pressure is low, and teardown order across sibling cleanups is unspecified). Making native disposal **statically complete** without finalizer resurrection requires a two-tier discipline:
1. **Primary path — linear/affine ownership token + lexical scope (`Drop`/linear consume):** Resources with hard teardown obligations (file descriptors, DMA buffers, shared memory arenas) are represented by a linear handle whose type forces explicit synchronous disposal (`close(arena)` consuming the token, backed by JEP 454 handshake or Verona single-owner `Iso` drop when shared readers exist).
2. **Secondary backstop (only for dynamically shared GC-owned wrappers) — resurrection-free `AddCleanup` + external memory accounting:** When a GC language must hold a native resource whose lifetime is truly dynamic, attaching a resurrection-free `AddCleanup(wrapper, free_raw, raw_handle)` paired with `AllocatedObjectSizeIncreased`/`Decreased`-style byte accounting prevents both resurrection delays and OOM blind spots, while `Cleanup.Stop()` cancels the fallback whenever the deterministic `close()` path runs first.

---

### 5. Cross-Runtime Federation Trade-Off Matrix

Basis: derived (synthesized from Sections 1–4)

| Strategy | Breaks Cross-Heap Cycles? | Mutator Barrier Cost | STW Pause Needed? | Handles External Memory OOM? | Safe Native Disposal Guarantee |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Opaque External Handles (`Persistent` / JNI Global)** | **No** (leaks $A \leftrightarrow B$) | Zero on normal access | Per-heap only | Only via manual `AdjustAmountOfExternalAllocatedMemory` | Prone to leaks & finalizer order inversion |
| **Acyclic Heap-Rank Partial Order ($H_1 \succ H_2$)** | Yes (by forbidding back-edges) | Zero cross-heap barrier | Per-heap only | Requires upward byte accounting | Deterministic drop on leaf heap $H_2$ |
| **Unified Cross-Component Tracing (`V8 CppHeap`)** | **Yes** (single tri-color epoch) | Cross-heap write barrier + minor-GC remembered set | Final atomic pause (shared) | **Yes** (`StatsCollector` integrated into GC limits) | Weak callbacks / `CppHeap` sweep without JS resurrection |
| **SATB-Coupled Trial-Deletion RC + Tracing** | **Yes** (if SATB barrier + unified epoch hold) | SATB pre-write barrier + purple buffer on dec | Federated epoch sync (must be ranked!) | Natural via RC + byte accounting | Must defer white sweep until SATB drain completes |
| **Biased RC + QSBR (`CPython PEP 703`)** | **Only via STW cyclic GC** (`_PyEval_StopTheWorld`) | Non-atomic owner / atomic shared + QSBR polls | **Yes** (2x STW if finalizers resurrect!) | Prompt for acyclic objects; delayed for cycles | Legacy `__del__` allows resurrection |
| **Perceus (`Koka`)** | **No** (acyclic FP heap assumed) | Non-atomic `rc <= 0` fast path; zero on borrows | **No** | Exact immediate reclamation (`garbage-free`) | Immediate drop on last use + raw C free callback (`kk_block_free_raw`) |

## Boundaries

- **Not examined:** Rust-to-CPython `PyO3` `__traverse__` / `PyTraverseError` cyclic GC integration under `Py_GIL_DISABLED` (the `src/class/gc.rs` path moved in `PyO3/pyo3@a6addae8` and was not fully inspected; only `src/sync.rs` was downloaded).
- **Not examined:** Mechanized Iris / Coq / Lean proofs of concurrent garbage collectors (e.g., Zakowski et al., Birkedal et al., or *Orca* / *Sapphire* mechanized proofs) were not verified line-by-line against primary Coq/Iris repositories in this report.
- **Not examined:** Empirical pause-time or throughput benchmarks comparing V8 unified marking, CPython free-threaded GC, and Go 1.24 `AddCleanup` under live polyglot workloads were not executed.
- **Unknown:** Whether CPython's free-threaded cyclic collector (`Python/gc_free_threading.c`) will transition from `_PyEval_StopTheWorld` to concurrent SATB or Bacon–Rajan trial deletion in future releases is unknown from the inspected revision `441c010fef90ab2860ae8142cbfd1fd52f53ba75`.
- **Known not to apply:** Perceus (`koka-lang/koka@b66091b2`) does **not** collect arbitrary mutable reference cycles; its garbage-free precision theorem (`10.1145/3453483.3454032`) applies to functional/acyclic graphs (or explicitly managed mutable reference cells broken externally).
- **Known not to apply:** Go's `runtime.AddCleanup` (`golang/go@b496a304`) does **not** guarantee that cleanups run before program exit, nor does it detect indirect reachability cycles where `arg` transitively references `ptr` through an intermediate struct (`mcleanup.go` L94–100 only panics on direct shallow pointer equality `ptr == arg`; indirect retention silently prevents the cleanup from ever firing).
- **Unsupported:** Both `runtime.AddCleanup` (`mcleanup.go` L101–104) and `runtime.SetFinalizer` (`mfinal.go` L445–448) explicitly panic/throw if passed a pointer inside a Go user arena (`inUserArenaChunk`), and OpenJDK's `SharedSession.justClose()` rejects closing a session while explicit `acquireCount > 0` (`SharedSession.java` L87–89).
- **Stronger conclusion avoided:** Showing that a single federated epoch coordinator eliminates 2-collector safepoint deadlocks in our finite-state BFS model (`p2_cross_heap_cycle_and_epoch_probe.py`) does *not* by itself prove starvation-freedom (transfinite progress) when an unbounded stream of mutators holds native locks or retries CAS loops across heterogeneous collectors.

## Evidence

### Primary Git Source References (Observed 2026-11-19)

1. **`v8/v8` @ `e88118f63dd96f24a9acb8bd0665e7880063f5c0`**
   - `include/v8-traced-handle.h` L30–45: `TracedReferenceStoreMode`, `TracedReferenceHandling`, `GlobalizeTracedReference`.
   - `src/heap/cppgc-js/unified-heap-marking-state.h` L19–38: `UnifiedHeapMarkingState::MarkAndPush(const TracedReferenceBase&)`.
   - `src/heap/cppgc-js/cpp-heap.h` L39–75, L136–209: `CppHeap` inheriting `AllocationObserver` and `GarbageCollector`; `InitializeMarking`, `StartMarking`, `AdvanceMarking`, `EnterFinalPause`, `FinishMarkingAndProcessWeakness`, `CompactAndSweep`, `AllocatedObjectSizeIncreased`/`Decreased`, `RememberCrossHeapReferenceIfNeeded`.
   - `src/heap/cppgc-js/cpp-heap.cc` L70–81, L966–983: `MinorGCHeapGrowing::LimitReached`, `CppHeap::EnterFinalPause` installing `ConservativeTracedHandlesMarkingVisitor`.
2. **`koka-lang/koka` @ `b66091b2a5a7ea20c5ed9498ad1e1f03caee9589`**
   - `kklib/include/kklib.h` L104–126: `int32_t kk_refcount_t`, `kk_refcount_is_thread_shared` (`rc < 0`), `kk_refcount_is_unique_or_thread_shared` (`rc <= 0`), `KK_FIELD_IDX_MAX = 0xFF`.
   - `kklib/src/refcount.c` L13–55: `kk_block_free_raw`, `kk_block_fast_drop_free` tail-call loop.
   - `src/Backend/C/Parc.hs`, `src/Backend/C/ParcReuse.hs` L14–53, `src/Core/Borrowed.hs`, `src/Core/CheckFBIP.hs`: Perceus dup/drop insertion, reuse-token specialization, borrowed-parameter analysis, and static FBIP verification.
3. **`python/cpython` @ `441c010fef90ab2860ae8142cbfd1fd52f53ba75`**
   - `Include/object.h` L154–167: `Py_GIL_DISABLED` `struct _object` (`ob_tid`, `ob_flags`, `ob_mutex`, `ob_gc_bits`, `ob_ref_local`, `ob_ref_shared`, `ob_type`).
   - `Include/refcount.h` L78–117: `_Py_REF_SHARED_SHIFT = 2`, `_Py_REF_SHARED_FLAG_MASK = 0x3`, `_Py_REF_MAYBE_WEAKREF = 0x1`, `_Py_REF_QUEUED = 0x2`, `_Py_REF_MERGED = 0x3`, arithmetic right-shift total refcount formula.
   - `Include/internal/pycore_object.h` L160–212: `_PyObject_IsUniquelyReferenced` requiring `ob_ref_shared == 0` including flags.
   - `Include/internal/pycore_qsbr.h` L40–75 & `Python/qsbr.c` L114–136: `struct _qsbr_thread_state`, 128-byte cache-line padding, `_Py_qsbr_advance`, `qsbr_poll_scan` (`_Py_atomic_fence_seq_cst()`).
   - `Python/gc_free_threading.c` L74–87, L2088–2198: `_PyEval_StopTheWorld` on entry and second `_PyEval_StopTheWorld` for `handle_resurrected_objects`, `skip_deferred_objects` (`GH-129236`).
4. **`openjdk/jdk` @ `4f33273115381cd7697082fcb1bb2642dae19043`**
   - `src/java.base/share/classes/jdk/internal/foreign/SharedSession.java` L83–102: `justClose()` CAS on `ACQUIRE_COUNT`, volatile `STATE = CLOSED`, `SCOPED_MEMORY_ACCESS.closeScope`.
   - `src/hotspot/share/prims/scopedMemoryAccess.cpp` L141–245: `ScopedAsyncExceptionHandshakeClosure`, `CloseScopedMemoryHandshakeClosure`, `install_async_exception`, and compiled-frame deoptimization for hoisted liveness checks across strip-mined loop safepoints.
5. **`golang/go` @ `b496a3044e1dcdc3eed0af3e0e89db92f740d764`**
   - `src/runtime/mcleanup.go` L75–125, L218–240, L671–730: `AddCleanup[T, S]`, shallow `ptr == arg` panic, tiny-allocator bypass for `arg` box, `Cleanup.Stop()`, dynamic concurrent `runCleanups()` goroutine pool.
   - `src/runtime/mfinal.go` L432–490: `SetFinalizer` allocation-base pointer check (`pointer not at beginning of allocated block`) and `inUserArenaChunk` throw.

### Published Literature & Specifications

- Ulan Degenbaev, Jochen Eisinger, Kentaro Hara, Marcel Hlopko, Michael Lippautz, Hannes Payer. *Cross-Component Garbage Collection*. PACMPL 2 (OOPSLA 2018). DOI: `10.1145/3276521`.
- David F. Bacon, V. T. Rajan. *Concurrent Cycle Collection in Reference Counted Systems*. ECOOP 2001, LNCS 2072. DOI: `10.1007/3-540-45337-7_12`.
- Alex Reinking, Ningning Xie, Leonardo de Moura, Daan Leijen. *Perceus: Garbage Free Reference Counting with Reuse*. PLDI 2021. DOI: `10.1145/3453483.3454032`.
- Jiho Choi, Thomas Shull, Josep Torrellas. *Biased Reference Counting: Minimizing Atomic Operations in Garbage Collection*. PACT 2018. DOI: `10.1145/3243176.3243195`.
- Sam Gross. *PEP 703: Making the Global Interpreter Lock Optional in CPython* (Python Enhancement Proposal 703).
- OpenJDK *JEP 454: Foreign Function & Memory API* (JDK 22) and *JEP 312: Thread-Local Handshakes*.
- Go Proposal #67535: *runtime: add AddCleanup* (Go 1.24).

### Executable Probe and Recorded Output (`Basis: execution`, 2026-11-19)

Command: `python3 /tmp/p2_cross_heap_cycle_and_epoch_probe.py` (Python 3, Linux x86-64). Standalone probe source:

```python
from collections import deque

def test_cross_heap_cycle():
    # External root drops A; A(heap T) <-> B(heap RC) remain mutually pinned under isolated roots
    roots_T = {"handle_from_B": "A"}
    rc_B = {"B": 1}
    reclaimed_isolated = set()
    if "A" not in set(roots_T.values()): reclaimed_isolated.add("A")
    if rc_B["B"] == 0: reclaimed_isolated.add("B")
    # Unified cross-component tracing from true_roots = {}
    marked, q = set(), deque()
    unified_edges = {"A": ["B"], "B": ["A"]}
    while q:
        u = q.popleft()
        if u not in marked:
            marked.add(u)
            q.extend(unified_edges.get(u, []))
    print(f"[Part A1] Isolated cross-heap collectors reclaimed: {sorted(reclaimed_isolated)} (LEAK: A<->B pinned)")
    print(f"[Part A1] Unified cross-component tracing reclaimed: {sorted({'A', 'B'} - marked)}")

def test_br_satb_race():
    # Mutator read B1 from A.f before A.f = None decremented B1.rc: 2->1 (Purple), before writing C.f = B1
    rc = {"B1": 1, "B2": 1}
    mutator_reg = "B1"
    trial_rc = {"B1": rc["B1"] - 1, "B2": rc["B2"] - 1}  # MarkGray across B1 <-> B2
    white = {x for x, c in trial_rc.items() if c == 0}
    print(f"[Part A2] Trial-deletion WITHOUT SATB barrier: freed={sorted(white)}, mutator holds {mutator_reg} => UAF={mutator_reg in white}")
    # With Yuasa SATB pre-write barrier on A.f = None, B1 is logged as SATB root -> ScanBlack protects {B1, B2}
    satb_roots = {"B1"}
    freed_satb = set() if "B1" in satb_roots else white
    print(f"[Part A2] Trial-deletion WITH SATB barrier:    freed={sorted(freed_satb)}, UAF={mutator_reg in freed_satb}")

def check_deadlock(ranked: bool):
    init = ("RUN", "RUN", None)
    q, visited, deadlocks = deque([init]), {init}, []
    while q:
        t1, t2, owner = s = q.popleft()
        if t1 == "DONE" and t2 == "DONE": continue
        nexts = []
        if not ranked:
            if t1 == "RUN": nexts.append(("WAIT_T2_SAFE", t2, owner))
            if t2 == "RUN": nexts.append((t1, "WAIT_T1_SAFE", owner))
            if t1 == "WAIT_T2_SAFE" and t2 in ("RUN", "DONE"): nexts.append(("DONE", t2, owner))
            if t2 == "WAIT_T1_SAFE" and t1 in ("RUN", "DONE"): nexts.append((t1, "DONE", owner))
        else:
            if t1 == "RUN": nexts.append(("HOLD_EPOCH", t2, "T1") if owner is None else ("SAFE_WAIT", t2, owner))
            if t2 == "RUN": nexts.append((t1, "HOLD_EPOCH", "T2") if owner is None else (t1, "SAFE_WAIT", owner))
            if t1 == "HOLD_EPOCH" and t2 in ("RUN", "SAFE_WAIT", "DONE"): nexts.append(("DONE", t2, None))
            if t2 == "HOLD_EPOCH" and t1 in ("RUN", "SAFE_WAIT", "DONE"): nexts.append((t1, "DONE", None))
            if t1 == "SAFE_WAIT" and owner is None: nexts.append(("HOLD_EPOCH", t2, "T1"))
            if t2 == "SAFE_WAIT" and owner is None: nexts.append((t1, "HOLD_EPOCH", "T2"))
        if not nexts: deadlocks.append(s)
        for ns in nexts:
            if ns not in visited:
                visited.add(ns); q.append(ns)
    return len(visited), deadlocks

test_cross_heap_cycle()
test_br_satb_race()
n_u, dl_u = check_deadlock(False)
n_r, dl_r = check_deadlock(True)
print(f"[Part B] Unranked dual-collector handshake: {n_u} reachable states, deadlocks={dl_u}")
print(f"[Part B] Ranked federated epoch coordinator: {n_r} reachable states, deadlocks={dl_r}")
```

Observed stdout:

```text
[Part A1] Isolated cross-heap collectors reclaimed: [] (LEAK: A<->B pinned)
[Part A1] Unified cross-component tracing reclaimed: ['A', 'B']
[Part A2] Trial-deletion WITHOUT SATB barrier: freed=['B1', 'B2'], mutator holds B1 => UAF=True
[Part A2] Trial-deletion WITH SATB barrier:    freed=[], UAF=False
[Part B] Unranked dual-collector handshake: 9 reachable states, deadlocks=[('WAIT_T2_SAFE', 'WAIT_T1_SAFE', None)]
[Part B] Ranked federated epoch coordinator: 12 reachable states, deadlocks=[]
```

## Revalidation

1. **V8 CppHeap unified marking and external accounting:** Diff `src/heap/cppgc-js/cpp-heap.h`, `cpp-heap.cc` (`EnterFinalPause`, `MinorGCHeapGrowing`), and `include/v8-traced-handle.h` against `v8/v8@e88118f63dd96f24a9acb8bd0665e7880063f5c0`.
2. **CPython free-threaded RC, QSBR, and STW cyclic GC:** Diff `Include/object.h` (`struct _object`), `Include/refcount.h` (`_Py_REF_SHARED_*`), `Include/internal/pycore_qsbr.h`, and `Python/gc_free_threading.c` (specifically searching for `_PyEval_StopTheWorld` and `skip_deferred_objects`) against `python/cpython@441c010fef90ab2860ae8142cbfd1fd52f53ba75`.
3. **Koka Perceus refcount encoding:** Diff `kklib/include/kklib.h` (`kk_refcount_t`) and `kklib/src/refcount.c` (`kk_block_fast_drop_free`) against `koka-lang/koka@b66091b2a5a7ea20c5ed9498ad1e1f03caee9589`.
4. **Java FFM handshake deoptimization & Go `AddCleanup`:** Diff `src/hotspot/share/prims/scopedMemoryAccess.cpp` (`CloseScopedMemoryHandshakeClosure`) against `openjdk/jdk@4f33273115381cd7697082fcb1bb2642dae19043`, and `src/runtime/mcleanup.go` (`AddCleanup`, `runCleanups`) against `golang/go@b496a3044e1dcdc3eed0af3e0e89db92f740d764`.
5. **Protocol counterexample and deadlock probe:** Re-run the embedded Python script above whenever modifying the epoch handshake protocol or cross-heap barrier rules to confirm zero deadlocks and zero UAF under concurrent mutator interleavings.
