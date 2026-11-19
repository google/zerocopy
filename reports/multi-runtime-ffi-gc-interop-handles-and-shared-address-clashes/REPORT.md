# Multi-Runtime FFI, GC Interop, Handle Disciplines, and Shared-Process Resource Clashes

## Summary

Co-locating multiple managed and systems runtimes in one OS address space exposes three structural invariants that single-language type systems and ABIs do not enforce:

1. **The Zero-Copy Memory Triangle:** *Zero-copy shared mutable access*, *moving or barriered concurrent tracing GC*, and *exclusive aliasing (`&mut T` / LLVM `noalias`)* cannot hold simultaneously across an unchecked FFI boundary. Every runtime sacrifices or dynamically fences at least one vertex:
   - **OpenJDK** (`openjdk/jdk@4f332731`) routes `GetPrimitiveArrayCritical` through `CollectedHeap::pin_object`: `SerialHeap` and `ParallelScavengeHeap` still stall GC globally via `GCLocker`, `ZCollectedHeap` stalls relocation via `ZJNICritical`, while `G1CollectedHeap` (post-JEP 423) and `ShenandoahHeap` perform per-region pinning via thread-local caches. **Panama FFM (JEP 454)** avoids managed-heap pinning by placing shared buffers off-heap under confined or safepoint-handshake-closed shared `Arena` lifetimes, allowing temporary heap pointers only for short non-callback `Linker.Option.critical(true)` downcalls.
   - **CPython PEP 703 (`Py_GIL_DISABLED`)** replaces single-word non-atomic refcounts with biased local + atomic shared counters, immortalization (`UINT32_MAX`), suspendable per-object critical sections, and QSBR—turning legacy borrowed-reference APIs (`PyList_GetItem`) into concurrent UAF hazards unless replaced by owned lookups (`PyList_GetItemRef`), **HPy** opaque handles (`HPy`, `HPyField`, `HPy_Is`), or **PyO3** attachment-scoped lifetimes (`Python<'py>`, `Bound<'py, T>`).
   - **Go `cgo`** enforces transitive pointer checks rejecting Go pointers to unpinned Go memory (`cgoCheckPointer`); `runtime.Pinner` is strictly **shallow**, rejects user-arena objects, and panics via `pinnerLeakPanic` if finalized without `Unpin()`.
   - **OCaml 5** requires manual `CAMLparam`/`CAMLlocal` shadow roots, dual `caml_modify` barriers (SATB `caml_darken` + generational `major_ref`), and raises `Effect.Unhandled` when algebraic effects cross C callbacks. **Erlang/OTP BEAM** allows only read-only bitstring pinning (`enif_inspect_binary`) and enforces a `CONTEXT_REDS = 4000` (~1 ms) cooperative reduction budget (`enif_consume_timeslice`) outside dirty schedulers.
2. **Cross-Heap Reference Cycles:** Independent collectors (tracing GC ↔ RC or GC ↔ GC) treat incoming cross-heap handles as external strong roots and permanently leak every cycle crossing the boundary. Complete reclamation without premature wrapper loss requires **unified cross-component tracing** with cross-heap write barriers (`V8::CppHeap` + Oilpan `UnifiedHeapMarkingState`), complete foreign edge reporting (`tp_traverse`/`__traverse__` into a Bacon-Rajan-style cycle collector), or a strictly acyclic ownership DAG.
3. **Process-Global Resource Collisions and Bridge Trade-Offs:** Shared OS processes collide on POSIX single-slot signal handlers (`JVM` `SIGSEGV` implicit null/safepoint traps vs. `Go` `SIGURG` preemption, imperfectly mediated by `libjsig`), GIL × native-mutex ABBA deadlocks (prevented by `PyO3` `MutexExt::lock_py_attached`) and CPython 3.13t suspendable critical sections, Rust destructive bitwise moves vs. C++ self-referential move constructors (`CXX` `Pin` / `IsRelocatable`), DRF-UB (`C++11`/`Rust`) vs. defined-racy buffers (`Java`, `JS` `SharedArrayBuffer`, `OCaml 5`), and M:N carrier pinning (which persists for JNI/FFM native frames even after JDK 24 JEP 491). Bridge generators (**CXX**, **Diplomat**, **UniFFI**) trade zero-copy borrowing, serialization (`RustBuffer`), handle tagging, and mandatory `Send + Sync` differently.

## Applicability

This report documents shared-address-space interoperability across co-resident runtimes inside a single OS process. The 16 durable `subjects` in `REPORT.json` form three linked groups:

- **Eleven pinned upstream runtime and bridge repositories** (`openjdk/jdk`, `python/cpython`, `hpyproject/hpy`, `PyO3/pyo3`, `golang/go`, `ocaml/ocaml`, `erlang/otp`, `v8/v8`, `dtolnay/cxx`, `mozilla/uniffi-rs`, and `rust-diplomat/diplomat`), directly audited at immutable 40-character HEAD commits to compare memory-management, handle, barrier, concurrency, signal, and bridge invariants side by side (exact coordinates in `## Evidence`).
- **Five normative specifications and peer-reviewed papers** (OpenJDK JEP 454, Python PEP 703, Degenbaev et al. OOPSLA 2018, Bacon & Rajan ECOOP 2001, and Watt et al. PLDI 2020) establishing the formal semantics of off-heap scoped memory, free-threaded CPython, unified cross-component GC, RC cycle collection, and relaxed shared-buffer memory models.
- **One standalone executable state-space probe** (`support/verify_multiruntime_ffi_triangles.py`, Python 3.10+ stdlib only) verifying abstract invariant models extracted from these systems (not hardware benchmarks).

**Cross-references to adjacent corpus packages (not duplicated here):**
- Rust calling conventions, `FnAbi`, `extern "C-unwind"`, and platform unwind tables: `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`.
- Static linking, DWARF `.eh_frame`/LSDA, and CompCert/CakeML/VeriFFI open-module composition: `compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026`.
- General POSIX signal/syscall semantics and CPU weak-memory mappings: `os-syscall-interfaces-asynchronous-signals-and-environment-models` and `weak-memory-concurrency-models-hardware-mappings-and-optimizations`.

**Version and platform scope:** Collector-specific OpenJDK pinning (`G1` post-JEP 423 vs. `Serial`/`Parallel` `GCLocker`), CPython `Py_GIL_DISABLED` layouts, Go `runtime.Pinner` leak panics, OCaml 5 multicore SATB barriers, and Erlang `CONTEXT_REDS = 4000` are observed at the pinned revisions (post-JDK-22, post-Python-3.13, post-Go-1.21, OCaml 5.x, modern OTP); older releases diverge where noted inline. Signal-chaining rules (`libjsig`, `SIGURG`) apply to POSIX/Unix targets; Windows SEH/VEH behavior is outside scope (`## Boundaries`).

## Findings

### 1. The Zero-Copy Memory Triangle and Runtime Pinning/Handle Disciplines

Basis: normative + source + execution + derived

When systems code (`C`, `C++`, `Rust`) accesses heap memory managed by a tracing GC or reference-counted runtime without copying, three properties form an irreconcilable triangle across an unchecked FFI boundary:

1. **Zero-copy shared mutable access:** Foreign code dereferences raw machine pointers (`T*`, `&mut [u8]`) directly into managed backing storage in $O(1)$ time.
2. **Moving or barriered concurrent tracing GC:** The managed runtime freely relocates objects during compaction/minor GC and depends on compiler-emitted read/write barriers (remembered sets, SATB snapshots, colored-pointer load barriers) for tri-color soundness.
3. **Exclusive aliasing (`&mut T` / LLVM `noalias` / C99 `restrict`):** The native compiler assumes exclusive mutable provenance across the FFI call and any callbacks, enabling hoisted loads, dead-store elimination, and register caching.

**Derived trade-off structure:** Holding (1) + (2) without compiler-generated native stack maps and barrier emission breaks memory safety via **use-after-relocation**, **lost-object bugs** (skipped write barriers), and **`noalias` invalidation** on reentrancy. Holding (1) + (3) requires suspending or localizing (2) via **pinning**, **GC-locking**, or **off-heap arenas**. Holding (2) + (3) drops (1) via **copying/serialization** or **opaque handle indirection**.

#### Comparative Matrix Across Examined Runtimes

| Runtime / API | Pinned Commit | Handle / Reference Mechanism | Relocation / Pinning Strategy | Mandatory Barrier / Safety Discipline | Aliasing / Concurrency Guard | Primary Failure Modes |
|---|---|---|---|---|---|---|
| **OpenJDK JNI** | `openjdk/jdk@4f332731` | Indirect `jobject` local/global/weak refs; `GetPrimitiveArrayCritical` raw ptr | `CollectedHeap::pin_object`: `GCLocker` (Serial/Parallel), `ZJNICritical` (ZGC), per-region pin cache (G1 post-JEP 423, Shenandoah) | No JNI/Java callbacks or blocking inside critical section; pair with `Release*Critical` | None on native ptr; Java threads may alias concurrently | Global GC stalls/OOM (Serial/Parallel/ZGC); pinned-region fragmentation (G1/Shenandoah); UAF after release |
| **OpenJDK Panama FFM (JEP 454)** | `openjdk/jdk@4f332731` | Off-heap `MemorySegment` + `Arena`; heap ptr only via `Linker.Option.critical(true)` | Off-heap segments immovable; `critical(true)` pins transiently for call duration | `Arena.ofConfined` owner check; `Arena.ofShared` safepoint handshake close | Spatial + temporal bounds; off-heap segments still allow racy native/Java writes | `WrongThreadException` / `ScopedAccessError`; JVM crash if `critical(true)` blocks or upcalls |
| **CPython 3.13t+ (`Py_GIL_DISABLED`)** | `python/cpython@441c010f` | Direct `PyObject*`; biased local/shared RC + `ob_mutex` + QSBR | Non-moving `mimalloc` heap; stop-the-world cyclic GC | Replace borrowed APIs (`PyList_GetItem`) with owned (`PyList_GetItemRef`); attach thread | Suspendable per-object `PyCriticalSection` + atomic RC + QSBR | Concurrent UAF on legacy borrowed refs; torn invariants across suspended critical sections |
| **HPy** | `hpyproject/hpy@0a1d8791` | Opaque `HPy` (`struct { intptr_t _i; }`), `HPyField`, `HPyGlobal` | Decouples handle identity from object address; supports moving GCs (PyPy/GraalPy) | Close every handle independently (`HPy_Close`); test identity via `HPy_Is` | Zero-recompile debug mode tracks per-handle alloc/close provenance | Leak or double-close when porting `PyObject*` pointer-identity idioms |
| **PyO3** | `PyO3/pyo3@a6addae8` | `!Send` `Python<'py>`; owned `Bound<'py, T>`; lifetime-tied `Borrowed<'a, 'py, T>` | Delegates to CPython RC + opt-in `__traverse__`/`__clear__` | Detach (`MutexExt::lock_py_attached`) before blocking native locks | Rust borrow checker + interior mutability; `'py` ≠ mutual exclusion on `3.13t` | ABBA GIL/mutex deadlocks if blocking while attached; cross-heap Rust `Arc` cycles |
| **Go `cgo` + `runtime.Pinner`** | `golang/go@b496a304` | Call-pinned raw Go ptr or `cgo.Handle` integer map | Non-moving Go heap; `Pinner.Pin` sets per-span `pinnerBits` + `specialPinCounter` | Transitive `cgoCheckPointer`: no Go ptr to unpinned Go memory; shallow `Pinner` + `Unpin()` | Dynamic type-graph walk (`cgocheck`) on call entry; none statically in C | Panic on nested unpinned Go ptr; UAF if C retains unpinned ptr; `pinnerLeakPanic` on GC |
| **OCaml 5 C-FFI** | `ocaml/ocaml@d921d1e8` | `value` registered via `CAMLparam`/`CAMLlocal` shadow root blocks | Moving minor heap + concurrent non-moving SATB major heap | Mandatory `caml_modify` (SATB `caml_darken` + `major_ref`); `CAMLreturn` | Domain-local roots; `caml_callback` clears `Stack_parent` | Silent use-after-relocation on missed root; lost object on raw `*fp = v`; `Effect.Unhandled` |
| **Erlang/OTP BEAM NIFs** | `erlang/otp@2f60d1b6` | Opaque `ERL_NIF_TERM`; `enif_inspect_binary` read-only slice | Per-process copying GC + refcounted off-heap binaries (`ERTS_PIN_BITSTRING`) | Never mutate inspected binaries; call `enif_consume_timeslice` (`CONTEXT_REDS = 4000`) or use dirty schedulers | Immutable terms; unaligned bitstrings copied to `env->tmp_obj_list` | Cross-process corruption on mutation; scheduler freeze if ordinary NIF > ~1 ms |

---

#### 1.1 OpenJDK JNI Critical Regions, Collector-Specific Pinning, and Panama FFM (JEP 454)

Basis: normative + source

At `openjdk/jdk@4f33273115381cd7697082fcb1bb2642dae19043`, `jni_GetPrimitiveArrayCritical` (`src/hotspot/share/prims/jni.cpp:2872-2891`) resolves the `Handle`, enters JVM TI deferred suspension (`thread->enter_jni_deferred_suspension()`), calls `Universe::heap()->pin_object(thread, a())` (`src/hotspot/share/gc/shared/collectedHeap.hpp:486-487`), and returns `arrayOop(a())->base(type)` with `*isCopy = JNI_FALSE`; `jni_ReleasePrimitiveArrayCritical` (`L2894-2900`) symmetrically calls `unpin_object`. Auditing all five HotSpot collectors reveals **three distinct pinning implementations**:

1. **Heap-Wide GC Stalling (`SerialHeap`, `ParallelScavengeHeap`):** `SerialHeap::pin_object` (`serialHeap.cpp:159-164`) and `ParallelScavengeHeap::pin_object` (`parallelScavengeHeap.cpp:1242-1247`) delegate to `GCLocker::enter/exit`. Inside `gcLocker.cpp:81-144`, `GCLocker` uses a **Dekker duality** between `_is_gc_request_pending` and per-thread `in_critical_atomic()`, ordered by `OrderAccess::fence()` (`L96, L137`): `GCLocker::block()` acquires `JNICritical_lock`, sets `_is_gc_request_pending = true`, fences, and spin-yields until every critical thread exits, while newly arriving threads block in `enter_slow` (`L123-144`). Allocating inside a critical section or blocking on another thread waiting in `enter_slow` causes global stalls or `OutOfMemoryError`.
2. **Relocation-Phase Stalling (`ZCollectedHeap`):** `ZCollectedHeap::pin_object` (`zCollectedHeap.cpp:274-280`) invokes `ZJNICritical::enter/exit` (`zJNICritical.cpp:32-88`), using a signed atomic `_count` (`>= 0` normal, `-1` blocked, `< -1` block-in-progress via `compare_set(count, -(count + 1))`) that stalls incoming entries on `ZConditionLock` (`ZCriticalPhaseJNICriticalStall`) until active critical threads drain.
3. **Per-Region Pinning (`G1CollectedHeap` post-JEP 423, `ShenandoahHeap`):** Under JEP 423 (*Region Pinning for G1*, Hamlin Li / Thomas Schatzl, JDK 22), `G1CollectedHeap::pin_object` (`g1CollectedHeap.inline.hpp:251-266`) increments a thread-local per-region pin cache (`G1ThreadLocalData::pin_count_cache(thread).inc_count(obj_region_idx)`) without `GCLocker`. `ShenandoahHeap::pin_object` (`shenandoahHeap.cpp:2337-2363`) similarly caches `(pin_cache_region, pin_cache_count)` per thread and flushes to `get_region(idx)->record_pin(count)`. Other heap regions continue collecting normally, trading global GC stalls for **region-level evacuation suppression** while any array in that region remains pinned.

**Project Panama FFM (JEP 454, JDK 22)** escapes managed-heap pinning by allocating native off-heap `MemorySegment` regions bounded by an `Arena` (`java/lang/foreign/Arena.java`):
- `Arena.ofConfined()` enforces single-thread ownership with zero atomic synchronization on access and deterministic `close()`.
- `Arena.ofShared()` achieves **lock-free fast-path concurrent reads with deterministic `close()`**: `SharedSession::justClose` (`SharedSession.java:83-93`) CAS-transitions `ACQUIRE_COUNT` from `0` to `CLOSED_ACQUIRE_COUNT`, stores `STATE = CLOSED`, and invokes `SCOPED_MEMORY_ACCESS.closeScope`. Inside HotSpot (`scopedMemoryAccess.cpp:42-215`), `CloseScopedMemoryHandshakeClosure` executes a per-thread safepoint handshake, walking `@Scoped` `java.base` frames (`for_scoped_methods`, `L43-92`) to test `is_accessing_session` (`L94-118`). Any thread mid-access receives an asynchronous `ScopedAsyncExceptionHandshakeClosure` (`L135-209`) unwinding out before deallocation.
- When copying a Java primitive array off-heap is prohibitive, `Linker.Option.critical(boolean allowHeapAccess)` (`Linker.java:922-951`) exposes a temporary Java-heap native address strictly for short, non-callback downcalls; violating its contract (blocking or upcalling into Java) risks JVM crashes.

---

#### 1.2 CPython PEP 703 (`Py_GIL_DISABLED`), HPy Opaque Handles, and PyO3 Lifetimes

Basis: normative + source + documentation

CPython's legacy `Python.h` exposes direct `PyObject*` pointers and **borrowed references** (returned without incrementing refcounts), which relied on the GIL to remain alive until the thread yielded. Under **PEP 703** (Sam Gross, Python 3.13+), audited at `python/cpython@441c010fef90ab2860ae8142cbfd1fd52f53ba75`, removing the GIL reshapes the C-API boundary:

1. **Biased Reference Counting and Immortalization:** Under `Py_GIL_DISABLED`, `struct _object` (`Include/object.h:156-167`) carries:
   ```c
   struct _object {
       _Py_ALIGNED_DEF(_PyObject_MIN_ALIGNMENT, uintptr_t) ob_tid;
       uint16_t ob_flags;
       PyMutex ob_mutex;           // per-object lock
       uint8_t ob_gc_bits;         // gc-related state
       uint32_t ob_ref_local;      // local reference count
       Py_ssize_t ob_ref_shared;   // shared (atomic) reference count
       PyTypeObject *ob_type;
   };
   ```
   Immortal objects set `ob_ref_local = _Py_IMMORTAL_REFCNT_LOCAL` (`UINT32_MAX`, `Include/refcount.h:74`). `Py_INCREF` (`Include/refcount.h:271-284`) loads `local` relaxed, exits early if `local + 1 == 0`, updates `ob_ref_local` non-atomically when `_Py_IsOwnedByCurrentThread(op)`, and otherwise atomically adds `1 << _Py_REF_SHARED_SHIFT` to `ob_ref_shared`.
2. **Borrowed-Reference UAF vs. QSBR-Backed Owned Lookups:** `PyList_GetItem` (`Objects/listobject.c:413-425`) still returns `((PyListObject *)op)->ob_item[i]` unsynchronized—an immediate concurrent UAF if another thread pops or resizes the list before the caller increments the refcount. `PyList_GetItemRef` (`L428-441`) delegates to `list_get_item_ref` (`L376-400`), performing a lock-free atomic load of `op->ob_item` and `_Py_TryXGetRef(&ob_item[i])` (falling back to a critical section on contention), while **Quiescent-State-Based Reclamation (`QSBR`)** (`Include/internal/pycore_qsbr.h:23-42`, odd write sequence incrementing by `QSBR_INCR = 2`, `QSBR_OFFLINE = 0` for detached threads) defers freeing swapped-out `ob_item` arrays until every attached thread passes a quiescent state.
3. **HPy Opaque Handles (`hpyproject/hpy@0a1d8791`):** Replaces raw `PyObject*` with distinct value structs (`typedef struct { intptr_t _i; } HPy`, `HPyField`, `HPyGlobal`, `hpy/devel/include/hpy.h:189-203`). Every handle must be closed individually (`HPy_Close`), pointer comparison (`h1 == h2`) is a compile-time error in C (requiring `HPy_Is`), `HPyField` enables moving-GC relocation and write barriers (`docs/overview.rst:31-36`, `docs/api.rst:55-115`), and runtime debug mode pinpoints leaked or double-closed handles to their exact C-API call site without recompilation.
4. **PyO3 Lifetimes (`PyO3/pyo3@a6addae8`):** Uses the `!Send` zero-sized token `Python<'py>(PhantomData<&'py AttachGuard>, PhantomData<NotSend>)` (`src/marker.rs:358`), binding owned refs in `Bound<'py, T>` (`src/instance.rs:74`) and borrowed refs in `Borrowed<'a, 'py, T>` (`src/instance.rs:958`). Under `Py_GIL_DISABLED`, `'py` proves *only* interpreter thread attachment—not exclusive access over shared Python objects (`guide/src/free-threading.md:80-87`).

---

#### 1.3 Go `cgo` Transitive Pointer Rules, Shallow `runtime.Pinner`, and `cgo.Handle`

Basis: normative + source + execution

Go's concurrent tri-color GC never scans C memory (`C.malloc`) and reserves future object relocation (`golang/go@b496a304`, `src/runtime/cgocall.go:582-586`). `src/cmd/cgo/doc.go:347-415` defines dynamic allocation-origin rules enforced by `cgoCheckPointer` / `cgoCheckArg` (`src/runtime/cgocall.go:590-770`) unless `GODEBUG=cgocheck=0`:

1. **Transitive Unpinned-Pointer Prohibition:** A Go pointer passed directly at top level (`top = true`) is implicitly pinned for the call duration, provided the memory it points to **contains no Go pointer to unpinned Go memory** (`cmd/cgo/doc.go:383-384`). Recursing into fields, slices, interfaces, or nested pointers sets `top = false` and panics on `cgoIsGoPointer(p) && !top && !isPinned(p)` (`cgocall.go:709, 720, 735, 764`); `abi.Chan` and `abi.Map` always panic (`L681-685`).
2. **Struct-Field vs. Backing-Array Granularity:** `&s.field` checks *only* `field` (`cmd/cgo/doc.go:385-386`), whereas `&slice[0]` or `&arr[0]` checks the **entire array or slice backing array up to `s.cap`** (`L386-388`, `cgocall.go:617-639, 726-729`).
3. **Shallow `runtime.Pinner` and Leak Panic:** `Pinner.Pin` (`src/runtime/pinner.go:40-240`) marks per-span `mspan.pinnerBits` (promoting multi-pins to `specialPinCounter`, `L190-199`, refreshing across GC cycles in `refreshPinnerBits`, `L341-368`). It is strictly **shallow** (nested pointers must be pinned individually, `L42-44`), panics on user-arena allocations (`inUserArenaChunk`, `L134-137`), and registers a `SetFinalizer` (`L70-75`) that unpins and invokes `pinnerLeakPanic()` (`L444-446`: `panic("runtime.Pinner: found leaking pinned pointer; forgot to call Unpin()?")`) if an un-unpinned `Pinner` is garbage-collected.
4. **Opaque Indirection (`runtime/cgo.Handle`):** `src/runtime/cgo/handle.go:12-95` maps arbitrary Go values to non-zero `uintptr` integer handles inside a Go `sync.Map` so C stores only opaque integers without pinning.

**Executable verification (`support/verify_multiruntime_ffi_triangles.py`, Model B):** Verified all six invariants: nested unpinned Go pointer rejected, shallow `Pinner.Pin(outer)` alone still rejected, `&outer.flat_c` allowed while `&slice[0]` rejects unpinned `slice[2]`, arena pin rejected, C-retained unpinned Go pointer causes UAF upon Go GC sweep, and finalizing an un-unpinned `Pinner` triggers `PinnerLeakPanic`.

---

#### 1.4 OCaml 5 C-FFI Shadow Roots, Dual Write Barriers, and Fiber Effect Boundaries

Basis: source + derived

OCaml 5 (`ocaml/ocaml@d921d1e86c56baa7b30e890ced455c12255793f5`) pairs a per-domain **copying minor heap** with a concurrent non-moving **SATB major heap**, imposing three unchecked C-FFI disciplines:

1. **Shadow Root Chains (`runtime/caml/memory.h:290-345`):** `CAMLparam*`/`CAMLlocal*` chain stack-allocated `struct caml__roots_block` frames into `&CAML_LOCAL_ROOTS`, registering `&x` pointers so minor GC updates relocated slots in place. Returning without `CAMLreturn` leaves a dangling pointer into a popped C stack frame.
2. **Dual Generational + Concurrent SATB Write Barrier (`runtime/memory.c:312-354, 427-439`):** Mutating a managed field requires `caml_modify` (`L333-354`), which runs `write_barrier` (`L312-327`), `atomic_thread_fence(memory_order_acquire)`, and `atomic_store_release`. `write_barrier` performs both (a) `caml_darken(Caml_state, old_val, 0)` when `!Is_young(obj)` and `caml_marking_started()` (SATB barrier preserving overwritten major-heap targets) and (b) `Ref_table_add(&Caml_state->minor_tables->major_ref, ...)` when `Is_block_and_young(new_val)` (generational remembered set). Raw `*fp = val` bypasses both barriers; `caml_initialize` (`L427-439`) skips `caml_darken` and is valid only on freshly allocated uninitialized major blocks.
3. **Delimited-Continuation Boundary (`runtime/callback.c:46-70`, `runtime/fiber.c:779-794`):** Because segmented OCaml fibers cannot capture native C stack frames, `alloc_and_clear_stack_parent` moves `Stack_parent(current_stack)` into a GC-rooted block and clears it to `NULL` across C callbacks. Performing an effect handled above the C frame deterministically raises `Effect.Unhandled`.

---

#### 1.5 Erlang/OTP BEAM NIFs: Read-Only Binary Pinning and Cooperative Reduction Budgets

Basis: source + documentation

In `erlang/otp@2f60d1b6a246b3f7ae997fd93a9af067fab7f981`:
- **Read-Only Binary Pinning (`erts/emulator/beam/erl_nif.c:1343-1367`):** `enif_inspect_binary` uses `ERTS_PIN_BITSTRING` to expose an immutable byte view without copying (mutating inspected bytes corrupts shared cross-process Erlang terms); if `BIT_OFFSET(offset) != 0`, BEAM transparently allocates an aligned copy on `env->tmp_obj_list`, silently losing zero-copy behavior.
- **Reduction Budget (`CONTEXT_REDS = 4000`):** Ordinary BEAM schedulers preempt processes after `CONTEXT_REDS = 4000` reductions (`erts/emulator/beam/erl_vm.h:47`), approximated as ~1 ms (`erts/doc/references/erl_nif.md:394, 1094`). Uncooperative native loops freeze the OS scheduler thread unless they either call `enif_consume_timeslice(env, percent)` (`erl_nif.c:3362-3381`, debiting `((CONTEXT_REDS + 99) / 100) * percent` = 40 reductions/percent via `BUMP_REDS` and yielding via `enif_schedule_nif` on return `1`; a no-op returning `0` on dirty schedulers) or declare `ERL_NIF_DIRTY_JOB_CPU_BOUND` / `ERL_NIF_DIRTY_JOB_IO_BOUND`.

---

#### 1.6 Reentrant FFI Callbacks, `&mut`/`noalias` Violations, and Revocable Handle Indirection

Basis: derived + execution

Even in single-threaded non-moving runtimes, **synchronous reentrancy** (`Rust -> Foreign -> Rust`) breaks vertex (3) of the Zero-Copy Memory Triangle: holding `&mut [u8]` establishes an active Stacked/Tree Borrows protector and LLVM `noalias` contract across the call, so any reentrant foreign read or write through an aliased pointer triggers immediate **Undefined Behavior** and invalidates compiler-hoisted loads.

**Executable verification (`support/verify_multiruntime_ffi_triangles.py`, Model C):**
- **Unguarded `&mut` across callback:** Reentrant access via alias tag `2` while caller protector `(tag=1, "mut")` is active triggers `AliasingUB` (`unguarded_reentrant_mut_ub_detected = True`).
- **Dynamic borrow-token / `may_enter` guard:** Runtime borrow state deterministically rejects reentrant access with `ReentrantBorrowDenied` (`borrow_token_blocked_reentrancy = True`) before UB occurs.
- **Revocable generational handle indirection:** Releasing `&mut` before crossing FFI and exposing a `(slot, generation)` handle permits transient callback reads while bumping generation on scope exit—trapping stashed handles (`RevokedHandleTrap`, `stashed_handle_trapped_after_revoke = True`) and preventing escaped-borrow UAF and ABA reuse.

---

### 2. Cross-Heap Reference Cycles: Isolated Collectors vs. Unified Cross-Component Tracing

Basis: normative + source + execution + derived

#### 2.1 Structural Inevitability of Cross-Heap Leaks Under External-Root Isolation

When two independent memory managers $H_1$ and $H_2$ (e.g., tracing GC ↔ RC, or tracing GC ↔ tracing GC) lack a shared graph traversal protocol, every cross-boundary edge acts as an **opaque external strong root** (JNI `GlobalRef`, `Py<T>`, `cgo.Handle`, `Arc::into_raw`). For any directed cycle $v_0 \to \dots \to v_{k-1} \to v_0$ intersecting both $H_1$ and $H_2$, every $H_1$ entry node stays externally rooted while its $H_2$ predecessor survives, and every $H_2$ entry node keeps refcount $\ge 1$ (or external root support) while its $H_1$ predecessor survives. Alternating independent collections to fixpoint reclaims acyclic garbage (within $d + 1$ rounds for $d$ boundary hops) but **permanently leaks 100% of unreachable cross-heap cycles**.

Breaking cycles by blindly turning one direction (e.g., C++ DOM node → JS wrapper) into an untraced weak handle fails whenever ownership runs in both directions: dropping direct JS references while the C++ DOM stays live prematurely collects the wrapper, losing JS expando state, `WeakMap` entries, and object identity (`wrapper1 !== wrapper2` upon re-wrapping).

**Executable verification (`support/verify_multiruntime_ffi_triangles.py`, Model A):** `IsolatedMultiHeap.collect_to_fixpoint()` reclaims an unreachable acyclic pair (`gc_dead -> rc_dead`) in 3 rounds while leaking all 6 nodes of a 2-node cycle and a 4-node multi-hop cycle (`isolated_leaked_cycle_nodes == 6`). Switching `dom_node -> js_wrapper` to a weak back-edge prematurely reclaims `js_wrapper` while `dom_node` remains rooted (`weak_backedge_prematurely_reclaimed == ['js_wrapper']`).

---

#### 2.2 V8 ↔ Blink Oilpan (`CppHeap`) Unified Cross-Component Tracing

Basis: normative + source + execution

Degenbaev, Eisinger, Hara, Hlopko, Lippautz, and Payer (*Cross-Component Garbage Collection*, PACMPL / OOPSLA 2018, DOI `10.1145/3276521`) solved JS ↔ DOM cross-heap leaks via **unified cross-component tracing**, implemented in `v8/v8@e88118f63dd96f24a9acb8bd0665e7880063f5c0`:

1. **Bidirectional Worklist Forwarding:** V8 traces JS wrappers directly into `cppgc::GarbageCollected` C++ objects without external strong roots. Symmetrically, C++ objects reference JS via `v8::TracedReference<T>` (`include/v8-traced-handle.h:54-80`): when `UnifiedHeapMarkingVisitorBase` (`unified-heap-marking-visitor.cc:29-39`) visits a traced reference, `UnifiedHeapMarkingState::MarkAndPush` (`unified-heap-marking-state-inl.h:33-60`) resolves the slot via `BasicTracedReferenceExtractor::GetObjectSlotForMarking`, marks it via `TracedHandles::Mark`, filters Smis (`IsHeapObject`), and pushes the `HeapObject` onto V8's `MarkingWorklists::Local` (`MarkingHelper::TryMarkAndPush`, `L56-58`).
2. **Synchronized Lifecycle (`src/heap/cppgc-js/cpp-heap.cc:908-1055`):** `CppHeap::StartMarking()` (`L908-920`) shares V8's local marking worklist directly; `AdvanceMarking` (`L927-948`) interleaves incremental/concurrent slices; `EnterFinalPause` (`L966-984`) enters the coordinated atomic pause with `ConservativeTracedHandlesMarkingVisitor` (`L977-980`) to reach a joint marking fixpoint; only afterward do `ProcessCrossThreadWeakness` (`L1011-1020`) and `FinishMarkingAndProcessWeakness` (`L1022-1050`) clear weak/traced handles under `DisallowGarbageCollectionScope` + `WeakProcessingForGlobalHandlesScope`.
3. **Mandatory Cross-Heap Write Barrier (`cpp-heap.cc:996-1000`):** `CppHeap::WriteBarrier(void* object)` invokes `MarkerBase::WriteBarrierType::kDijkstra` so moving an unmarked C++ object into an already-black V8 object during incremental marking cannot lose live memory.

**Executable verification (`support/verify_multiruntime_ffi_triangles.py`, Model A):** `UnifiedCrossComponentHeap.unified_gc()` reclaims all 8 unreachable nodes (including both 2-node and 4-node cycles) while preserving all 4 live nodes (including a rooted cross-heap cycle). Omitting the Dijkstra cross-heap write barrier loses the live `cpp_payload` object (`missing_write_barrier_lost_object == True`), whereas firing it preserves soundness (`with_write_barrier_preserved == True`).

---

#### 2.3 Cross-Domain Cycle Collection Alternatives (`Bacon-Rajan`, `PyO3 __traverse__`, Acyclic Ownership DAGs)

Basis: normative + source + documentation + derived

| Strategy | Representative System | Cross-Heap Cycle Completeness | Coupling Cost | Residual Hazards |
|---|---|---|---|---|
| **Unified Cross-Component Tracing** | `V8` + `Blink` Oilpan (`CppHeap`) | Complete | Extreme (shared worklists, barriers, atomic pause, `v8::Locker` discipline `v8-cppgc.h:73-75`) | Missing write barriers lose live objects |
| **Host Cycle Collector Traversal Hooks** | `CPython` `tp_traverse`/`tp_clear` (`PyO3` `__traverse__`) + Bacon-Rajan trial deletion | Complete *iff* all foreign edges in every cycle are reported | Moderate (manual per-type traversal) | Opaque `Arc`/`Mutex`/closures leak; calling `Python::attach` in `__traverse__` panics (`PyO3/guide/src/class/protocols.md:473-474`) |
| **Strict Acyclic Cross-Heap Ownership DAG** | `Diplomat` (JS hidden owner refs), `UniFFI` (`Arc` ownership) | Cycles forbidden by architecture | Low (unmodified VMs) | Any accidental strong callback back-edge silently leaks |

Bacon & Rajan's concurrent RC cycle collector (ECOOP 2001, DOI `10.1007/3-540-45337-7_12`) reclaims isolated cycles via localized trial deletion (subtracting internal reference counts over candidate subgraphs and collecting those reaching zero). Across FFI (as in CPython `tp_traverse` / `PyO3` `__traverse__`, `guide/src/class/protocols.md:428-474`), trial deletion remains sound only if foreign types accurately report every outgoing managed handle—any edge hidden inside a Rust `Arc`, `Mutex`, or closure leaves the residual count non-zero and leaks the cycle permanently.

---

### 3. Process-Global Resource Collisions: Signals, Locks, Moves, Memory Models, and Runtime Budgets

Basis: normative + source + documentation + execution + derived

#### 3.1 POSIX Signal-Handler Hijacking (`JVM SIGSEGV` × `Go SIGURG` × Native Handlers & `libjsig`)

Basis: source + execution + derived

POSIX allows only **one** handler per signal number per process (`sigaction`), yet managed runtimes rely on hardware signals for routine execution:
- **OpenJDK HotSpot** (`openjdk/jdk@4f332731`, `os_linux_x86.cpp:258-295`) handles `SIGSEGV` for **safepoint polls** (`SafepointMechanism::is_poll_address`, `L258`) and **implicit null checks** (`MacroAssembler::uses_implicit_null_check`, `L282-285`), handles `SIGBUS` for truncated `MappedByteBuffer` recovery (`L260-273`), uses `SIGUSR2` for JFR sampling (`signals_posix.cpp:178`), and forbids blocking `SIGILL`/`SIGBUS`/`SIGFPE`/`SIGSEGV`/`SIGTRAP` (`L489-493`).
- **Go** (`golang/go@b496a304`, `signal_unix.go:74, 179-180, 395`) uses `const sigPreempt = _SIGURG` for asynchronous goroutine preemption and installs handlers for `_SigPanic` (`SIGSEGV`), `SIGPIPE`, and `sigPreempt` even in `-buildmode=c-shared` / `c-archive` libraries.
- **`libjsig` Chaining and Fragility (`src/java.base/unix/native/libjsig/jsig.c:143-230`):** Preloaded via `LD_PRELOAD`, `libjsig` interposes `signal`/`sigset`/`sigaction` over `dlsym(RTLD_NEXT, "sigaction")` (`L213`). Once HotSpot installs a handler (`jvm_signal_installed && sigismember(&jvmsigs, sig)`), `jsig.c:153-164` saves subsequent foreign registrations in `sact[sig]` without replacing the kernel handler, and `signals_posix.cpp:392-399` delegates unowned faults via `get_signal_action`.
- **Failure modes (verified in Model E):** (1) Without `libjsig` preloaded before `libjvm`, a late `sigaction(SIGSEGV)` overwrites HotSpot's handler so a routine Java implicit null check fatally crashes the process (`without_libjsig_jvm_null_check == 'NATIVE_FATAL_CRASH(jvm_implicit_null)'`), whereas preloaded `libjsig` handles Java faults and chains native faults cleanly; (2) Go's `SIGURG` causes `EINTR` in C libraries missing `SA_RESTART` retry loops; (3) `libjsig`'s two-tier design breaks when 3+ signal-handling runtimes (e.g., JVM + Go + Wasmtime) chain independently without a unified PC-range dispatcher.

---

#### 3.2 Global Locks, ABBA Deadlocks, and CPython 3.13t Suspendable Critical Sections

Basis: source + documentation + execution

1. **ABBA Lock-Order Inversion vs. `PyO3` `MutexExt::lock_py_attached`:** Acquiring `RustMutex -> GIL/attach` on Thread 1 while Thread 2 holds `GIL/attach -> RustMutex` deadlocks immediately. `PyO3/pyo3@a6addae8` (`src/sync.rs:278-291, 405-434`) avoids this in `MutexExt::lock_py_attached` by trying `self.try_lock()` first (`L419`), and on `WouldBlock` detaching via `unsafe { SuspendAttach::new() }` (`L429`) before blocking on `self.lock()`. Detaching before blocking native locks remains mandatory under `Py_GIL_DISABLED` so blocked threads do not stall stop-the-world GC pauses (`guide/src/free-threading.md:80-94`). **Model D1** exhaustively verifies deadlock reachability in the naive protocol (13 states, `naive_abba_deadlock_reachable == True`) and **0 deadlocks** across all 17 states of `lock_py_attached` (`pyo3_abba_deadlock_reachable == False`).
2. **CPython 3.13t Suspendable Critical Sections (`Python/critical_section.c:21-165`):** To avoid deadlocks during nested Python callbacks (`__hash__`/`__eq__`), `_PyCriticalSection_SuspendAll` (`L108-130`) walks `tstate->critical_section` and **unlocks every held `PyMutex`** on thread detach or incompatible nested lock acquisition, re-locking them in `_PyCriticalSection_Resume` (`L133-165`). Consequently, `Py_BEGIN_CRITICAL_SECTION` / `PyO3` `with_critical_section` (`src/sync/critical_section.rs:132`) does **not** guarantee atomic non-suspendable mutual exclusion across any call that can invoke Python or detach; **Model D2** reproduces a concurrent reader observing a torn pair `(1, 0)` mid-critical-section (`cpython_313t_cs_suspend_torn_pair == [1, 0]`).

---

#### 3.3 Destructive Bitwise Moves (`Rust`) vs. Self-Referential Move Constructors (`C++`)

Basis: source + documentation + derived

Rust moves are **destructive bitwise `memcpy`s** (source becomes uninitialized; `Drop` never runs on moved-from slots), whereas C++ moves run `T(T&&)` (updating internal self-pointers such as `std::string` SSO buffers or intrusive list sentinels) and still run `~T()` on the moved-from object. Bitwise-moving a self-referential C++ object into Rust creates dangling internal pointers; letting C++ `std::move` a Rust object without invalidating the source triggers double-free.

`dtolnay/cxx@4d19ca4eec78b2964035a3ea3cef5196515b13e7` resolves this statically (`src/extern_type.rs:151-224`, `include/cxx.h:1122-1136`, `book/src/extern-c++.md:43-50`):
- **`cxx::kind::Trivial`** types cross by value only if C++ passes `static_assert(rust::IsRelocatable<T>)`, which defaults to `std::is_trivially_move_constructible<T>::value && std::is_trivially_destructible<T>::value` (`include/cxx.h:1130-1136`) unless explicitly specialized.
- **`cxx::kind::Opaque`** types (such as `CxxString = "std::string"`, `extern_type.rs:222-223`) are forbidden by value in Rust, cross only behind indirection (`&T`, `UniquePtr<T>`), and require `Pin<&mut T>` for mutation specifically to prohibit `std::mem::swap`.

---

#### 3.4 Memory-Model Contagion: DRF-UB (`C++11`/`Rust`) vs. Defined-Racy Managed Buffers

Basis: normative + source + derived

`C11`, `C++11`, and `Rust` declare any unsynchronized conflicting access involving a non-atomic operation to be **instantaneous Undefined Behavior**, whereas Java (`ByteBuffer`/`VarHandle`), JavaScript `SharedArrayBuffer` (Watt et al., PLDI 2020, DOI `10.1145/3385412.3385973`), and OCaml 5 (Local DRF with explicit acquire/release fences in `runtime/memory.c:342-354, 448-504`) assign bounded, type-safe semantics even to racy reads/writes.

**Derived consequence:** Passing a concurrently writable `SharedArrayBuffer` or Java `MemorySegment` to Rust as `&[u8]`/`&mut [u8]` or C++ as non-atomic `uint8_t*` escalates a legal managed data race into **native compiler UB**. Sound zero-copy concurrent sharing requires native atomic accesses (`AtomicU8` / `std::atomic_ref` with `Relaxed`/`Acquire`/`Release`) unless external synchronization guarantees exclusivity.

---

#### 3.5 M:N Carrier Pinning, TLS Contexts, `fork()`, and Opaque External Memory Budgets

Basis: source + documentation + derived

- **Green-Stack Switching & Carrier Pinning:** Go `cgocall` (`golang/go@b496a304`, `cgocall.go:153-215`) calls `entersyscall()` (detaching `P`) and switches onto the OS thread's `g0` stack, spawning unbounded OS threads (`M`) when C calls block. In Java Virtual Threads, JDK 24 **JEP 491** eliminated `synchronized` pinning via heap-based monitors, but **JNI and Panama FFM native frames still pin carrier platform threads** because the JVM cannot unmount opaque native stacks.
- **TLS Context Corruption:** Runtimes store execution context in OS TLS (`JNIEnv*`, `PyThreadState*`, OCaml `Caml_state`, Go `g`). Calling into a runtime from an unattached foreign OS thread crashes; caching OS-TLS handles across M:N fiber migrations (without `!Send` tokens like `Python<'py>` or Go `runtime.LockOSThread()`) corrupts another carrier's context.
- **Opaque External Memory & `fork()` Deadlocks:** Tiny managed wrappers holding megabytes of native buffers trigger OS OOM kills unless external pressure is reported (e.g., OCaml's `caml_alloc_dependent_memory` / `caml_adjust_gc_speed`, `runtime/memory.c:365-415`, triggering major slices at `extra_heap_resources > 0.2` and minor GC at `> 1.0`). POSIX `fork()` inside multi-threaded mixed-runtime processes orphans every allocator, GC, and thread-pool lock held by vanished threads.

---

### 4. Multi-Language Bridge Generator Architecture Comparison (`CXX`, `Diplomat`, `UniFFI`, `PyO3`, `HPy`)

Basis: source + documentation + derived

| Bridge | Pinned Commit | Boundary | Value Crossing | Ownership & Lifetimes | Concurrency / Aliasing | GC & Cycle Posture |
|---|---|---|---|---|---|---|
| **CXX** | `dtolnay/cxx@4d19ca4e` | Rust ↔ C++ | Zero-copy by value (`IsRelocatable`); indirection (`&T`, `Pin<&mut T>`, `UniquePtr`) for `Opaque` | RAII both sides; `Pin<&mut T>` prevents bitwise swap | Opt-in `unsafe impl Send/Sync` (`extern-c++.md:51-70`) | No GC; acyclic RAII |
| **Diplomat** | `rust-diplomat/diplomat@71628f09` | Rust → C, C++, JS, Dart, Kotlin, `.NET`, Python | Zero-copy slices (`DiplomatSlice<'a, T>`) & `DiplomatWrite` sinks (`runtime/src/lib.rs:11-29`) | Opaque `Box<T>` / `&'a T`; **target-native lifetime lowering** (`book/src/lifetimes.md:6-53`) | Explicit non-elided Rust lifetimes `'a` on FFI signatures | C++ docs; **JS stashes hidden GC ref from borrowed wrapper to owner** (acyclic) |
| **UniFFI** | `mozilla/uniffi-rs@d5a18867` | Rust ↔ Kotlin, Swift, Python, Ruby | **Copy/serialize** strings, records, sequences via `RustBuffer` (`lifting_and_lowering.md:15-20`) | Rust `Arc::into_raw` **even** `u64` handles; foreign **odd** `u64` handle map (`handle.rs:12-39`) | Mandatory `Send + Sync` + interior mutability; **no `&mut self`** (`object_references.md:21-30`) | Foreign finalizers call Rust free; strong foreign callbacks can still cycle |
| **PyO3** | `PyO3/pyo3@a6addae8` | Rust ↔ CPython (GIL & `3.13t`) | Direct `PyObject*` primitives/buffers; explicit Rust extraction | `!Send` `Python<'py>`; `Bound<'py, T>`; detached `Py<T>` | `MutexExt::lock_py_attached`; `with_critical_section` | Manual `__traverse__`/`__clear__` hooking CPython cyclic GC |
| **HPy** | `hpyproject/hpy@0a1d8791` | C → CPython, PyPy, GraalPy | Opaque `HPy` handles + universal ABI context | Independent `HPy_Dup`/`HPy_Close`; `HPyField` | Debug-mode handle provenance checks | Moving-GC compatible; `HPyField` barrier support |

**Design-space synthesis:**
- **UniFFI (`mozilla/uniffi-rs@d5a18867`):** Packs Rust and foreign objects into one `#[repr(transparent)] struct Handle(u64)` (`handle.rs:7-39`), reserving `0` as invalid and partitioning bit 0 (`is_foreign() == ((self.0 & 1) == 1)`) using `Arc` pointer alignment $> 1$ for even Rust handles and odd foreign map keys. By serializing structured values (`RustBuffer`) and banning `&mut self` (`object_references.md:13-30`), UniFFI buys thread-safe foreign ergonomics at the expense of copy overhead (retaining `into_arc_borrowed`, `handle.rs:74-89`, only for async future polling where foreign lifetime stability is guaranteed).
- **Diplomat (`rust-diplomat/diplomat@71628f09`):** Targets zero-copy libraries (such as ICU4X) by restricting the ABI to FFI-safe slices, write sinks, and explicitly lifetime-annotated opaque types (`core/src/hir/lifetimes.rs`, `book/src/types.md:5-35`), then lowering lifetimes idiomatically per target (`book/src/lifetimes.md:6-53`: C++ lifetime documentation vs. JS hidden owner references keeping owning wrappers alive in JS GC without cross-heap tracing).
- **CXX (`dtolnay/cxx@4d19ca4e`):** Avoids GC handles and serialization completely via compile-time C++ `static_assert(rust::IsRelocatable<T>)`, `UniquePtr<T>`, and `Pin<&mut T>`.

## Boundaries

- **not examined:**
  - `.NET` CoreCLR `GCHandle`/`fixed`/managed interior pointer (`Span<T>`) GC brick tables; `GHC` Haskell RTS `safe`/`unsafe` FFI and `CApiFFI`; `Swift` C++ interop, `~Copyable`, and Objective-C toll-free bridging; `Ruby` GVL/Ractor C-API; `Lua`/`LuaJIT` `longjmp` C-frame unwinding;
  - `GraalVM Truffle` / `Sulong` polyglot VMs and the `WebAssembly Component Model` (`WIT` Canonical ABI / `WasmGC`), which form separate interop substrates;
  - Windows SEH / Vectored Exception Handling (`AddVectoredExceptionHandler`) analogs of POSIX `libjsig`;
  - Live hardware microbenchmark latencies (nanoseconds for `cgocall`, JNI vs. Panama FFM, `RustBuffer` copies); execution evidence tests abstract state-space invariant models only.
- **unknown:**
  - Whether a standardized, low-overhead unified cross-component tracing protocol can scale across 3+ independent production VMs (e.g., JVM + V8 + CPython) without regressing single-language JIT/GC throughput;
  - Whether modular static stack-bound and escape analysis can safely eliminate Go/OCaml/Loom native stack switches and carrier pinning for arbitrary third-party C/Rust libraries;
  - How compositional separation logics (Iris, Melocoton, DimSum) can specify CPython 3.13t's suspendable `PyCriticalSection` + `QSBR` + biased refcounting without whole-interpreter proofs.
- **known not to apply:**
  - Claims that OpenJDK `GetPrimitiveArrayCritical` universally stalls GC globally via `GCLocker` **do not apply** to `G1CollectedHeap` (post-JEP 423) or `ShenandoahHeap` at `openjdk/jdk@4f332731` (both use per-region pinning; `GCLocker` still applies to `SerialHeap`/`ParallelScavengeHeap`, and `ZJNICritical` stalls ZGC relocation).
  - Claims that forgetting `runtime.Pinner.Unpin()` in Go merely leaks memory silently **do not apply** at `golang/go@b496a304`: the `Pinner` finalizer invokes `pinnerLeakPanic()` (`pinner.go:70-75, 444-446`).
  - Claims that JDK 24 JEP 491 eliminated all Java Virtual Thread carrier pinning **do not apply** to JNI or Panama FFM native frames.
  - Claims that `PyO3`'s `Python<'py>` token enforces cross-thread mutual exclusion **do not apply** under `Py_GIL_DISABLED` (`guide/src/free-threading.md:85-87`).
  - Legacy claims of a `2000`-reduction BEAM timeslice **do not apply** to `erlang/otp@2f60d1b6`, which sets `CONTEXT_REDS = 4000` (`erl_vm.h:47`).
- **unsupported:**
  - Passing Go channels, maps, or Go pointers containing unpinned nested Go pointers to C (`cmd/cgo/doc.go:383-415`, `cgocall.go:681-769`), or pinning user-arena Go objects (`pinner.go:134-137`).
  - Performing OCaml 5 algebraic effects across an interleaved C callback frame (`runtime/callback.c:46-65`, raises `Effect.Unhandled`).
  - Holding `cxx::kind::Opaque` C++ types (e.g., `std::string`) by value or behind plain `&mut T` in Rust via `CXX` (`extern_type.rs:154-164`, `extern-c++.md:43-49`).
  - Calling `Python::attach` inside a `PyO3` `__traverse__` callback (`guide/src/class/protocols.md:473-474`, panics).
  - Exposing `&mut self` methods directly on `UniFFI` exported objects (`object_references.md:21-23`).

## Evidence

All primary-source inspections and probe executions were acquired on `2026-11-19`.

### Primary Source Code Coordinates (11 Pinned Upstream Repositories)

| Subject | Repository & Pinned Commit | Verified Paths, Symbols & Line Ranges |
|---|---|---|
| **OpenJDK** | `openjdk/jdk` @ `4f33273115381cd7697082fcb1bb2642dae19043` | `src/hotspot/share/prims/jni.cpp` (`jni_GetPrimitiveArrayCritical` L2872–2891, `jni_ReleasePrimitiveArrayCritical` L2894–2900); `collectedHeap.hpp` (`pin_object`/`unpin_object` L486–487); `gcLocker.cpp` (L81–144); `serialHeap.cpp` (L159–164); `parallelScavengeHeap.cpp` (L1242–1247); `g1CollectedHeap.inline.hpp` (L251–266); `shenandoahHeap.cpp` (L2337–2363); `zCollectedHeap.cpp` (L274–280) & `zJNICritical.cpp` (L32–88); `java/lang/foreign/Linker.java` (`Option.critical` L922–951); `SharedSession.java` (`justClose` L83–93); `scopedMemoryAccess.cpp` (L43–215); `libjsig/jsig.c` (L143–220); `signals_posix.cpp` (L178, L392–401, L489–493); `os_linux_x86.cpp` (L258–295) |
| **CPython** | `python/cpython` @ `441c010fef90ab2860ae8142cbfd1fd52f53ba75` | `Include/object.h` (L156–167); `Include/refcount.h` (L74, L271–284); `Objects/listobject.c` (`list_get_item_ref` L376–400, `PyList_GetItem` L413–425, `PyList_GetItemRef` L428–441); `Python/critical_section.c` (L21–62, L108–165); `Include/internal/pycore_qsbr.h` (L23–42); `Doc/howto/free-threading-extensions.rst` |
| **HPy** | `hpyproject/hpy` @ `0a1d8791dfb28ea7d928bd1aabe37cc40dfb8146` | `hpy/devel/include/hpy.h` (L189–203); `docs/overview.rst` (L31–36, L58–61, L301–315); `docs/api.rst` (L55–115) |
| **PyO3** | `PyO3/pyo3` @ `a6addae8948adedafd09b2832edf3fa23d282b16` | `src/marker.rs` (`Python<'py>` L358); `src/instance.rs` (`Bound` L74, `Borrowed` L958); `src/sync.rs` (`MutexExt` L278–291, `lock_py_attached` L405–434); `src/sync/critical_section.rs` (L132); `guide/src/free-threading.md` (L75–94); `guide/src/class/protocols.md` (L428–474) |
| **Go** | `golang/go` @ `b496a3044e1dcdc3eed0af3e0e89db92f740d764` | `src/cmd/cgo/doc.go` (L347–415); `src/runtime/pinner.go` (L40–99, L125–203, L341–368, L444–446); `src/runtime/cgocall.go` (L153–215, L590–770); `src/runtime/cgo/handle.go` (L12–95); `src/runtime/signal_unix.go` (L74, L179–180, L395) |
| **OCaml 5** | `ocaml/ocaml` @ `d921d1e86c56baa7b30e890ced455c12255793f5` | `runtime/caml/memory.h` (L290–345); `runtime/memory.c` (`write_barrier` L312–327, `caml_modify` L333–354, `caml_alloc_dependent_memory`/`caml_adjust_gc_speed` L365–415, `caml_initialize` L427–439, `caml_atomic_*` L441–505); `runtime/callback.c` (L46–70); `runtime/fiber.c` (L779–794) |
| **Erlang/OTP** | `erlang/otp` @ `2f60d1b6a246b3f7ae997fd93a9af067fab7f981` | `erts/emulator/beam/erl_vm.h` (`CONTEXT_REDS = 4000` L47); `erts/emulator/beam/erl_nif.c` (`enif_inspect_binary` L1343–1367, `enif_consume_timeslice` L3362–3381); `erts/doc/references/erl_nif.md` (L392–415, L1081–1107) |
| **V8 / Oilpan** | `v8/v8` @ `e88118f63dd96f24a9acb8bd0665e7880063f5c0` | `include/v8-cppgc.h` (L70–100); `include/v8-traced-handle.h` (L54–80); `src/heap/cppgc-js/unified-heap-marking-state-inl.h` (L33–60); `unified-heap-marking-visitor.cc` (L18–39); `cpp-heap.cc` (L908–1055) |
| **CXX** | `dtolnay/cxx` @ `4d19ca4eec78b2964035a3ea3cef5196515b13e7` | `src/extern_type.rs` (L151–224); `include/cxx.h` (L467–513, L1122–1136); `book/src/extern-c++.md` (L43–70) |
| **UniFFI** | `mozilla/uniffi-rs` @ `d5a18867e723852247ee9db61bc277f6243fe61d` | `uniffi_core/src/ffi/handle.rs` (L7–101); `docs/manual/src/internals/object_references.md` (L19–80); `lifting_and_lowering.md` (L1–25) |
| **Diplomat** | `rust-diplomat/diplomat` @ `71628f09c2969bc6e1013d50041f33b365e6cd81` | `runtime/src/lib.rs` (L11–85); `book/src/lifetimes.md` (L5–53); `book/src/types.md` (L1–35) |

### Normative Specifications and Peer-Reviewed Literature

- **JEP 454:** Maurizio Cimadamore, *Foreign Function & Memory API*, OpenJDK JDK 22 (GA March 2024), `https://openjdk.org/jeps/454` (with contextual JDK 22 **JEP 423**, Hamlin Li / Thomas Schatzl, *Region Pinning for G1*, and JDK 24 **JEP 491**, *Synchronize Virtual Threads without Pinning*).
- **PEP 703:** Sam Gross, *Making the Global Interpreter Lock Optional in CPython*, Python 3.13, `https://peps.python.org/pep-0703/`.
- **Cross-Component GC:** Ulan Degenbaev, Jochen Eisinger, Kentaro Hara, Marcel Hlopko, Michael Lippautz, and Hannes Payer, *Cross-Component Garbage Collection*, PACMPL Vol. 2, OOPSLA 2018, Article 151, DOI `10.1145/3276521`.
- **RC Cycle Collection:** David F. Bacon and V. T. Rajan, *Concurrent Cycle Collection in Reference Counted Systems*, ECOOP 2001 (LNCS 2072, pp. 207–235), DOI `10.1007/3-540-45337-7_12`.
- **JS Relaxed Memory Model:** Conrad Watt, Christopher Pulte, Anton Podkopaev, Guillaume Barbier, Stephen Dolan, Shaked Flur, Jean Pichon-Pharabod, and Shu-yu Guo, *Repairing and Mechanising the JavaScript Relaxed Memory Model*, PLDI 2020, DOI `10.1145/3385412.3385973`.

### Execution Evidence (`support/verify_multiruntime_ffi_triangles.py`)

Executed on Linux (`Python 3.13`, `python3 -B support/verify_multiruntime_ffi_triangles.py`, exit code `0`):

```text
[PASS] model_a_cross_heap_cycles: {'isolated_fixpoint_rounds': 3, 'isolated_leaked_cycle_nodes': 6, 'weak_backedge_prematurely_reclaimed': ['js_wrapper'], 'unified_reclaimed_unreachable_nodes': 8, 'unified_live_preserved': 4, 'missing_write_barrier_lost_object': True, 'with_write_barrier_preserved': True}
[PASS] model_b_go_cgo_pinner: {'caught_unpinned_nested_go_ptr': True, 'caught_shallow_pin_insufficiency': True, 'caught_slice_backing_unpinned_elem': True, 'caught_arena_pin_rejection': True, 'caught_c_retained_unpinned_uaf': True, 'caught_pinner_leak_panic': True}
[PASS] model_c_reentrant_aliasing: {'unguarded_reentrant_mut_ub_detected': True, 'borrow_token_blocked_reentrancy': True, 'handle_in_scope_read_ok': True, 'stashed_handle_trapped_after_revoke': True}
[PASS] model_d_locks_and_cs: {'naive_interleaving_states': 13, 'naive_abba_deadlock_reachable': True, 'pyo3_lock_py_attached_states': 17, 'pyo3_abba_deadlock_reachable': False, 'cpython_313t_cs_suspend_torn_pair': [1, 0]}
[PASS] model_e_signal_chaining: {'without_libjsig_jvm_null_check': 'NATIVE_FATAL_CRASH(jvm_implicit_null)', 'with_libjsig_jvm_null_check': 'JVM_HANDLED_NPE_OR_SAFEPOINT', 'with_libjsig_chained_native_fault': 'NATIVE_FATAL_CRASH(native_segfault)'}
ALL 5 MULTI-RUNTIME FFI INVARIANT MODELS VERIFIED.
```

## Revalidation

Use these narrow checks to revalidate key findings against newer upstream revisions without repeating the full multi-repository audit:

1. **Re-run the executable invariant probe (< 1 s):**
   ```console
   python3 -B reports/multi-runtime-ffi-gc-interop-handles-and-shared-address-clashes/support/verify_multiruntime_ffi_triangles.py
   ```
   A pass reconfirms the abstract cycle-leak, unified-tracing, write-barrier, `cgo`/shallow-`Pinner`, reentrant-aliasing, ABBA-deadlock, suspended-critical-section, and `libjsig` chaining invariants; it does not detect upstream source drift.
2. **Targeted upstream source diffs:**
   - **OpenJDK (`openjdk/jdk`):** Diff `pin_object` overrides in `serialHeap.cpp`, `parallelScavengeHeap.cpp`, `g1CollectedHeap.inline.hpp`, and `zJNICritical.cpp`; diff `scopedMemoryAccess.cpp` (`CloseScopedMemoryHandshakeClosure`) and `jsig.c`; check OpenJDK JEPs for any post-JEP-491 native-frame virtual-thread unpinning work.
   - **CPython (`python/cpython`) & PyO3 (`PyO3/pyo3`):** Diff `Include/object.h` (`Py_GIL_DISABLED`), `Python/critical_section.c` (`_PyCriticalSection_SuspendAll`), `Objects/listobject.c` (`PyList_GetItem` vs. `PyList_GetItemRef`), and `PyO3/src/sync.rs` (`MutexExt::lock_py_attached`).
   - **Go (`golang/go`):** Diff `src/cmd/cgo/doc.go`, `src/runtime/pinner.go` (`Pin`, `pinnerLeakPanic`), `src/runtime/cgocall.go` (`cgoCheckArg`), and `src/runtime/signal_unix.go` (`sigPreempt`).
   - **OCaml (`ocaml/ocaml`) & Erlang (`erlang/otp`):** Diff `runtime/memory.c` (`write_barrier`/`caml_modify`), `runtime/callback.c` (`alloc_and_clear_stack_parent`), `erts/emulator/beam/erl_vm.h` (`CONTEXT_REDS`), and `erl_nif.c` (`enif_consume_timeslice`).
   - **V8 (`v8/v8`) & Bridges (`dtolnay/cxx`, `mozilla/uniffi-rs`, `rust-diplomat/diplomat`):** Diff `v8/src/heap/cppgc-js/{unified-heap-marking-state-inl.h,cpp-heap.cc}`; check `cxx/include/cxx.h` (`IsRelocatable` vs. C++26 trivial relocation), `uniffi_core/src/ffi/handle.rs`, and `diplomat/book/src/lifetimes.md`.
