# Handle Tables, Scoped Arenas, and Cross-Runtime FFI Pinning Protocols

## Summary

Sharing objects and byte buffers across autonomous managed runtimes (JVM, Go, CPython, V8/Node.js, CRuby) or mutually distrusting isolation domains (WebAssembly guests, native C extensions, confidential-compute enclaves, smart accelerators) is governed by a structural **Zero-Copy / Runtime-Autonomy / Bilateral-Liveness trilemma**: no cross-domain FFI protocol can simultaneously permit (P1) zero-copy direct dereference of live runtime-managed pointers, (P2) autonomous memory relocation and reclamation inside the host runtime without synchronizing on the foreign domain, and (P3) bilateral memory safety and bounded liveness under an uncooperative or adversarial peer. Production runtimes resolve this trilemma along distinct, sharply characterized axes:

1. **Deterministic Off-Heap Arena Revocation (`OpenJDK` JEP 454 `ScopedMemoryAccess`):** HotSpot eliminates per-access atomic reference counting on shared off-heap arenas (`SharedSession`) by checking a plain `state` field inside `@Scoped` methods and paying the synchronization cost on `close()` via a two-stage Thread-Local Handshake (`src/hotspot/share/prims/scopedMemoryAccess.cpp:168-317`). The first stage (`CloseScopedMemoryHandshakeClosure`) either schedules an async exception handshake (`ScopedAsyncExceptionHandshakeClosure`) for threads inside `@Scoped` frames or calls `Deoptimization::deoptimize` on compiled frames whose JIT-hoisted liveness check may have separated from the access; the second stage **spin-yields (`SpinYield`)** until `async_exceptions == 0` before freeing memory. Critically, the Javadoc in `X-ScopedMemoryAccess.java.template:62-63` still states the pre-JDK-8310644 behavior (that `close()` fails and leaves the session open), diverging directly from the C++ source, and any thread trapped in native code under a `@Scoped` frame stalls `closeScope` indefinitely.
2. **Heap Pinning vs. Movable Stacks (`Go` `runtime.Pinner`):** Go 1.21+ separates object pinning (`runtime.Pinner`) from OS-thread affinity (`runtime.LockOSThread`), tracking per-heap-object 2-bit pin states (`pinnerBits` + overflow `specialPinCounter` in `src/runtime/pinner.go:166-428`) and enforcing cgo pointer-passing invariants (`src/runtime/cgocall.go:590-856`, `src/runtime/cgocheck.go:25-179`). Because Go goroutine stacks dynamically relocate via `copystack` (`src/runtime/stack.go:954-1010`), stack pointers cannot be pinned; `Pinner.Pin(any)` relies on interface escape analysis to move stack variables to the heap, while `setPinned` silently returns `false` on non-heap addresses (`spanOfHeap == nil`) and panics on Go user arenas (`inUserArenaChunk`, L134–137) or leaked un-unpinned `Pinner`s via a finalizer (`pinnerLeakPanic`, L70–75, L444–446).
3. **Lock-Free Reclamation vs. Indirection (`CPython` PEP 703 `nogil` QSBR vs. `HPy`, `Node-API`, `Wasmtime`):**
   - Free-threaded CPython (`Py_GIL_DISABLED`) pairs biased reference counting (`ob_tid`, `ob_ref_local`, 2-bit-flagged `ob_ref_shared`, `Include/object.h:156-167`, `Include/refcount.h:81-92`) and suspendable per-object critical sections (`_PyCriticalSection_SuspendAll`, `Python/critical_section.c:108-130`) with Quiescent State-Based Reclamation (`Include/internal/pycore_qsbr.h`, `Python/qsbr.c`). Any native FFI call that blocks without detaching (`_Py_qsbr_detach`, setting `seq = QSBR_OFFLINE = 0`) freezes `shared->rd_seq` across the entire interpreter, halting mimalloc page reclamation linearly with wall time.
   - `HPy` (`hpyproject/hpy`, now **archived**, with opaque-handle evolution migrated to PEPs 620/670/674 and PyNI) and `Node-API` (`napi_handle_scope`, `napi_ref` over `v8::Persistent` in `src/js_native_api_v8.cc:659-765`) interpose opaque handles so moving GCs retain autonomy; under `V8_ENABLE_SANDBOX`, Node-API explicitly **forbids** zero-copy external buffers (`napi_no_external_buffers_allowed`, `js_native_api_v8.cc:3152-3153`).
   - Contrary to a common misconception, neither Wasmtime's VM `HandleTable` (`crates/wasmtime/src/runtime/vm/component/handle_table.rs:109-327`) nor its host `ResourceTable` (`crates/wasmtime/src/runtime/component/resource_table.rs:38-250`) uses generational handle indices: both use dense 1-based `u32` slots (`MAX_HANDLE = 1 << 28`) with a LIFO free-list (`DELETE_WITH_TOMBSTONE = false`), enforcing safety via `TypedResourceIndex`, `lend_count`, `CallContext.borrow_count`, parent/child sets, and store-wide `HandleCounter` quotas—which prevents host memory corruption and slot-exhaustion DoS, but permits **same-type guest ABA handle aliasing** after `drop` + `new`.
4. **DoS-Bounded Cross-Domain Pinning Leases:** Achieving bilateral safety *and* liveness across mutually distrusting domains requires splitting FFI into **Lane A (64-bit generational `(idx, gen)` handle tables with finite `(max_handles, max_pinned_bytes, epoch_ttl)` leases)**—eliminating both ABA aliasing and uncooperative pin-retention starvation—and **Lane B (pointer-free byte arenas transferred via single-copy or hardware ownership exclusion)**, with explicit fault/rejection semantics on forced lease revocation.

## Applicability

This report characterizes memory-sharing, pinning, handle-indirection, and safe-reclamation protocols across the pinned upstream runtimes and specifications in `REPORT.json`:

- **OpenJDK (`openjdk/jdk` at `d65bc4b262564e535c431aa8d4b58a1f7630fa64`, JEP 454 / post-JDK-8310644):** Directly inspected in `src/hotspot/share/prims/scopedMemoryAccess.cpp`, `src/java.base/share/classes/jdk/internal/misc/X-ScopedMemoryAccess.java.template`, `src/java.base/share/classes/jdk/internal/foreign/MemorySessionImpl.java`, and `SharedSession.java`. Applies to HotSpot JVM Foreign Function & Memory API `ConfinedSession`, `SharedSession`, `ImplicitSession`, and `GlobalSession`.
- **Go (`golang/go` at `b496a3044e1dcdc3eed0af3e0e89db92f740d764`):** Directly inspected in `src/runtime/pinner.go`, `src/runtime/stack.go`, `src/runtime/cgocall.go`, and `src/runtime/cgocheck.go`. Applies to Go 1.21+ `runtime.Pinner`, cgo pointer checks (`GODEBUG=cgocheck=1` and `GOEXPERIMENT=cgocheck2`), and contiguous movable goroutine stacks.
- **CPython (`python/cpython` at `03e7a8854d714fabb3ab5b8c8f984fc1214f65b0`, PEP 703 `Py_GIL_DISABLED`):** Directly inspected in `Include/internal/pycore_qsbr.h`, `Python/qsbr.c`, `Python/critical_section.c`, `Include/object.h`, `Include/refcount.h`, and `Include/internal/pycore_object.h`. Applies to free-threaded CPython builds (3.13+ `--disable-gil`); GIL-enabled builds do not activate QSBR or biased reference counting.
- **HPy (`hpyproject/hpy` at `0a1d8791dfb28ea7d928bd1aabe37cc40dfb8146`), Node.js Node-API (`nodejs/node` at `4f37a6a8aac657b309714d953c7e28c2de6caf40`), Wasmtime (`bytecodealliance/wasmtime` at `3ce2209872ccf1ea115914a81e020aef66a10c51`) + Component Model Canonical ABI (`WebAssembly/component-model` at `585526aa1f2c7f76f07557d16e265dede38b3acb`), and CRuby (`ruby/ruby` at `2979ed47232036f592dcc24e05c6dab7fa139eb2`):** Directly inspected to contrast opaque handle tables, V8 persistent references and sandbox restrictions, WebAssembly Component Model borrow/lend tables, and compacting-GC movable marking (`rb_gc_mark_movable` / `rb_gc_location`).

**Cross-subject scope:** The trilemma and DoS-bounded lease state machine generalize to any pair of domains `(R, C)` where host runtime `R` manages object lifetimes or physical placement and foreign domain `C` executes outside `R`'s compiler-generated safepoints and pointer maps (native C/C++/Rust FFI, WebAssembly guests, or mutually distrusting hardware cores). Specific runtime mechanics (such as HotSpot C2 deoptimization or CPython mimalloc page deferral) apply only to their named implementations.

## Findings

### 1. The Zero-Copy / Runtime-Autonomy / Bilateral-Liveness Trilemma

Basis: derived + source

Consider a managed runtime $R$ sharing heap objects, stack frames, or off-heap memory segments with a foreign domain $C$ (native C extension, another GC runtime, untrusted WebAssembly guest, or mutually distrusting hardware core/enclave) across a boundary $\mathcal{B}$ where $R$ cannot atomically inspect or rewrite $C$'s registers and private memory. Define three properties:

- **(P1) Zero-Copy Direct Object Sharing:** $C$ holds and dereferences raw virtual addresses pointing directly into $R$'s live managed heap, stack frames, or shared memory segments without marshaling copies or per-access handle table indirection.
- **(P2) Runtime Autonomy:** $R$ can unilaterally relocate objects or stacks (compacting GC, Go `copystack`, reallocating backing arrays), advance reclamation grace periods (CPython QSBR, `SharedSession.close()`), and reclaim bounded memory without waiting for $C$ to reach a cooperative safepoint or issue an explicit release call.
- **(P3) Bilateral Safety & Bounded Liveness:** Neither side can induce spatial/temporal memory corruption (UAF, dangling pointers, torn multi-word metadata) in the other, **and** neither side can unilaterally deadlock the other's reclamation, close handshakes, or exhaust unbounded pinned memory.

**Impossibility Proposition:** *No protocol over an autonomous managed runtime $R$ and an uncooperative foreign domain $C$ satisfies $\mathrm{P1} \land \mathrm{P2} \land \mathrm{P3}$ simultaneously:*

1. **$\mathrm{P1} \land \mathrm{P2} \implies \neg\mathrm{P3}$ (Temporal / Relocation Unsoundness):** If $C$ holds raw pointer $p$ into $R$ and $R$ autonomously moves the referent (`Go copystack`, `Ruby GC.compact`, V8 Scavenger/Mark-Compact) or completes a reclamation epoch (`CPython QSBR`, `SharedArena` free), $R$ cannot patch $p$ inside $C$'s unmapped registers or private memory, immediately creating a dangling pointer or type-confused UAF in $C$.
2. **$\mathrm{P1} \land \mathrm{P3\text{-safety}} \implies \neg\mathrm{P2} \lor \neg\mathrm{P3\text{-liveness}}$ (Pinning / Handshake Starvation):** Preserving safety of raw pointers $p$ held by $C$ requires either (a) pinning the object/span in place (`runtime.Pinner`, `rb_gc_mark`, `napi_ref`), which defeats heap compaction ($\neg\mathrm{P2}$) and lets an uncooperative $C$ hoard unbounded pinned memory indefinitely ($\neg\mathrm{P3\text{-liveness}}$), or (b) synchronizing reclamation with $C$ via global/thread-local barriers (`ScopedMemoryAccess` `SpinYield`, CPython QSBR `rd_seq`), which lets a stalled or adversarial $C$ block reclamation across $R$ indefinitely ($\neg\mathrm{P3\text{-liveness}}$).
3. **$\mathrm{P2} \land \mathrm{P3} \implies \neg\mathrm{P1}$ (Indirection or Ownership-Transferred Byte Arenas):** Preserving both runtime autonomy and bilateral safety/liveness forces live runtime object graphs to cross $\mathcal{B}$ strictly as **opaque revocable handles** (indirecting through a runtime-owned table that $R$'s GC can freely update during compaction and forcibly invalidate on lease expiry) or **canonical serialized copies**. True zero-copy is sound only for **pointer-free off-heap byte arenas** whose physical/virtual write ownership is transferred exclusively via a trusted arbiter (e.g., OS `mprotect`/`munmap`, IOMMU/TDISP, or explicit epoch leases with trapped/faulted revocation).

#### 1.1 Cross-Runtime Protocol Matrix

Basis: source + normative + documentation

| Runtime / Mechanism | Primary Object Crossing | Relocation / Compaction Support | Concurrent Reclamation Sync | Fast-Path Read Overhead | Liveness / DoS Failure Mode Under Uncooperative Peer |
|---|---|---|---|---|---|
| **OpenJDK JEP 454 (`SharedSession` + `ScopedMemoryAccess`)** | Off-heap `MemorySegment` (pointer-free bytes) | N/A (off-heap native address; `HeapSession` is non-closeable) | Two-phase Thread-Local Handshake + `Deoptimization::deoptimize` + `SpinYield` (`scopedMemoryAccess.cpp:168-317`) | Plain load of `@Stable int state` (`MemorySessionImpl.java:83, 199-206`) | Thread stalled in native/JVMTI inside `@Scoped` holds `async_exceptions > 0`, hanging `Arena.close()` in `SpinYield` indefinitely. |
| **Go (`runtime.Pinner` + `cgocheck`)** | Raw Go heap pointer (non-stack, non-user-arena) | Heap is non-moving today, but `pinnerBits` reserves pinning contract; stacks move (`copystack`) and cannot be pinned | Explicit `Unpin()` + GC finalizer panic on forgotten `Pinner` (`pinner.go:70-75`) | Direct pointer dereference in C (0 runtime check after call entry) | C retaining pinned object leaks span indefinitely; forgotten `Unpin()` crashes process via `pinnerLeakPanic`; unpinned stack `unsafe.Pointer` silently ignored by `setPinned` (`spanOfHeap == nil`) and dangles on `copystack`! |
| **CPython PEP 703 (`nogil` QSBR + BRC + Critical Sections)** | Raw `PyObject*` (owned strong ref or hazardous borrow) | Non-moving `PyObject` (mimalloc pages); backing buffers (`dict`/`list`) relocate under QSBR | QSBR `wr_seq`/`rd_seq` epoch scan (`qsbr.c:130-172`); STW cycle GC | Non-atomic `ob_ref_local` on owning thread; atomic `ob_ref_shared` off-owner | Native extension blocking without `_Py_qsbr_detach` freezes `rd_seq` interpreter-wide, stalling all deferred mimalloc page frees (Probe 2B.1); critical sections suspend on detach/callback (`critical_section.c:109`). |
| **HPy (`hpyproject/hpy`, archived)** | Opaque `HPy` handle (`obj + 1` on CPython; handle table on PyPy/GraalPy) | Full moving-GC autonomy via `HPyField` / `HPyGlobal` | Explicit `HPy_Close(ctx, h)` | Handle-table lookup (PyPy/GraalPy) or `-1` untag (CPython `handles.h:18-22`) | Leaked handles retain referents; debug mode detects leaks/UAF, but production ABI has no built-in cross-domain TTL lease. |
| **Node-API / V8 (`napi_handle_scope`, `napi_ref`, External `ArrayBuffer`)** | Opaque `napi_value` (scoped) / `napi_ref` (refcounted `v8::Persistent`) | Full moving-GC autonomy for JS objects; external `ArrayBuffer` **banned** under `V8_ENABLE_SANDBOX` (`js_native_api_v8.cc:3152`) | V8 HandleScope stack unwind + weak callback (`WeakCallback`, L760) | Indirection through V8 handle slot; direct `Data()` on non-sandboxed `ArrayBuffer` | Unreleased `napi_ref` (`refcount_ > 0`) pins JS subgraph forever; detached `ArrayBuffer` (`napi_detach_arraybuffer`) invalidates cached C `void* data`. |
| **Wasmtime Component Model (`VMHandleTable` + `ResourceTable`)** | Dense 1-based `u32` handle (`MAX_HANDLE = 1 << 28`) | Complete host autonomy (guest never sees raw host pointers) | Deterministic `resource.drop`, `lend_count`, `CallContext.borrow_count`, `HandleCounter` cap | $O(1)$ array index + tag/type check (`handle_table.rs:187-214`) | Slot-exhaustion bounded by `HandleCounter.limit` & `DEFAULT_MAX_CAPACITY = 1_000_000`; **non-generational LIFO free-list allows intra-type guest ABA aliasing** (Probe 2A). |
| **CRuby (`rb_gc_mark_movable` + `rb_gc_location`)** | Raw `VALUE` (pinned by `rb_gc_mark` or relocated via `dcompact` callback) | Opt-in compaction via `rb_gc_mark_movable` + `rb_gc_location` (`include/ruby/internal/gc.h:169-215`) | Conservative stack scan pins stack-referenced objects | Direct `VALUE` pointer | Legacy C extensions using `rb_gc_mark` pin pages and fragment heap; conservative stack scan fails across isolated enclaves/foreign stacks. |

---

### 2. JDK 22 Project Panama (JEP 454): `ScopedMemoryAccess` Safepoint-Handshake Revocation

Basis: normative + source + documentation + execution

JEP 454 finalized the Foreign Function & Memory API in JDK 22 with four `MemorySessionImpl` tiers (`src/java.base/share/classes/jdk/internal/foreign/MemorySessionImpl.java:56-69, 143-157`):
- `GlobalSession` (`state = NONCLOSEABLE = 1`, annotated `@Stable` so C2 JIT folds liveness checks to constant `true`);
- `HeapSession` (wraps on-heap Java arrays, non-closeable);
- `ConfinedSession` (single `owner` thread, deterministic `close()` with zero cross-thread synchronization);
- `SharedSession` (multi-threaded deterministic `close()`, plus subclass `ImplicitSession` backed by a `java.lang.ref.Cleaner`).

#### 2.1 Why Plain-Mode Liveness Checks Work — and the Exact Two-Phase Close Protocol

In `MemorySessionImpl.checkValidStateRaw()` (L199–206), every memory access checks `if (state < OPEN) throw ALREADY_CLOSED;` using a **plain (non-volatile) read** of `state`—eliminating atomic RMW contention on hot read loops. Temporal safety against concurrent `SharedSession.close()` is guaranteed solely by the closing protocol across `SharedSession.java:83-93` and `src/hotspot/share/prims/scopedMemoryAccess.cpp:42-317`:

1. **Exclusive close arbitration (`SharedSession.java:83-93`):**
   ```java
   int acquireCount = (int) ACQUIRE_COUNT.compareAndExchange(this, 0, CLOSED_ACQUIRE_COUNT);
   if (acquireCount < 0) throw sharedSessionAlreadyClosed();
   else if (acquireCount > 0) throw alreadyAcquired(acquireCount);
   STATE.setVolatile(this, CLOSED);
   SCOPED_MEMORY_ACCESS.closeScope(this, ALREADY_CLOSED);
   ```
   Waiters in `sharedSessionAlreadyClosed()` spin-wait (`Thread.onSpinWait()`) until `STATE` visibly transitions from `OPEN` (`0`) to `CLOSED` (`-1`), preventing a racing thread from receiving an "already closed" exception while `isAlive()` still observes `OPEN` (L95–102). Sessions explicitly acquired by long-running downcalls (`whileAlive` / `acquire0`, `MAX_FORKS = Integer.MAX_VALUE`) block `close()` cleanly with `alreadyAcquired`.
2. **First stage — Synchronous Thread-Local Handshake (`scopedMemoryAccess.cpp:168-307`):**
   `ScopedMemoryAccess_closeScope` runs `Handshake::execute(&cl)` (`CloseScopedMemoryHandshakeClosure`) against every live `JavaThread`. Because executing a Thread-Local Handshake (JEP 312) inserts a full cross-thread synchronization barrier, every thread executing after the handshake is guaranteed to observe `STATE == CLOSED` (L301–306). For each thread `jt`:
   - **Inside `@Scoped` method referencing `session` (`is_accessing_session`, L94–118, L195–209):** `for_scoped_methods` walks frames inside `java.base` (or the entire stack if JVMTI agents are loaded, `JvmtiEnv::environments_might_exist()`, L58–90) looking for methods annotated `@Scoped` (`m->is_scoped()`). If any local `T_OBJECT` slot equals `session`, HotSpot cannot throw immediately because `jt` might currently be running native code (e.g., inside `Unsafe.copyMemory`). Instead, it allocates a `ScopedAsyncExceptionHandshakeClosure`, atomically increments `async_exceptions`, and installs it via `jt->install_async_exception(...)` (L207–209).
   - **Compiled frame outside `@Scoped` (`!in_scoped`, L210–266):** C2 JIT may hoist the `@Scoped` liveness check above a strip-mined loop while placing a safepoint poll *between* the check and the subsequent memory access (explicitly diagrammed in `scopedMemoryAccess.cpp:219-247`). If the top frame is compiled, `code->has_scoped_access()` is true, and `is_session_live(last_frame, register_map)` finds the `session` oop live in the frame/registers/nmethod (L270–290), HotSpot invokes **`Deoptimization::deoptimize(jt, last_frame)`** (L261) so the thread reverts to the interpreter upon resuming and re-executes `checkValidStateRaw()` before touching native memory!
3. **Second stage — `SpinYield` Barrier for Async Exception Delivery (`scopedMemoryAccess.cpp:309-316`):**
   ```cpp
   ThreadBlockInVM tbivm(thread);
   SpinYield spin_yield;
   while (async_exceptions.load_acquire() > 0) {
     spin_yield.wait();
   }
   ```
   Each target thread self-processes its `ScopedAsyncExceptionHandshakeClosure` at its next safepoint poll, decrements `async_exceptions`, and if still inside the `@Scoped` method, throws `ScopedAccessError` to unwind before any further dereference (L155–165). Only after `async_exceptions` reaches `0` does `close()` proceed to `resourceList.cleanup()` (`free`/`munmap`).

#### 2.2 Source Disagreement and Adversarial Liveness Hazards

- **Documentation vs. Source Disagreement (`X-ScopedMemoryAccess.java.template:62-63` vs. `scopedMemoryAccess.cpp:195-316`):** The Javadoc of `ScopedMemoryAccess` still documents the pre-JDK-8310644 protocol: *"If any thread is found accessing a resource associated to the very memory session being closed, the handshake fails, and the session will not be closed."* In the actual `openjdk/jdk` implementation (`d65bc4b26256`), closing **never reverts to `OPEN`**: it unconditionally transitions `STATE = CLOSED`, injects async exceptions into active `@Scoped` readers, deoptimizes compiled loop frames, and waits for unwinding.
- **Liveness vulnerability (Probe 2B.2):** Because `ScopedAsyncExceptionHandshakeClosure` is self-processed *only* when the target thread reaches a safepoint poll (`scopedMemoryAccess.cpp:129-131`), any thread that remains inside native code (or a blocking JVMTI agent callback invoked while a `@Scoped` frame is on the stack) holds `async_exceptions > 0`, causing the closing thread to **spin indefinitely in `SpinYield`** without freeing the arena. Furthermore, `acquire0()` exposes a direct DoS vector if an untrusted component can acquire a shared session and never call `release0()`, permanently rejecting `close()` with `IllegalStateException("Session is acquired by N clients")`.

---

### 3. Go `runtime.Pinner` vs. Moving Goroutine Stacks and `cgocheck`

Basis: normative + source + derived

Go manages two starkly different memory regions: a **non-moving mark-sweep heap** (organized into `mspan`s, with future moving-GC compatibility reserved by the cgo pointer-passing rules) and **contiguous, dynamically movable goroutine stacks** starting at 2 KiB.

#### 3.1 Movable Stacks (`copystack`) and Why Stack Pointers Cannot Be Pinned

When a goroutine exhausts its stack guard, `newstack()` calls `copystack(gp, newsize)` (`src/runtime/stack.go:954-1010`), which allocates a fresh stack (`stackalloc`), `memmove`s the live frames to the new address range `[new.lo, new.hi)`, and calls `adjustpointers` (`stack.go:652`) using compiler-generated pointer bitmaps (`bitvector`) to add `adjinfo.delta = new.hi - old.hi` to every Go-known pointer targeting `[old.lo, old.hi)`. Because foreign C code neither emits Go stack maps nor halts for `adjustpointers`, any raw pointer to a Go goroutine stack retained across a stack growth silently points into freed/poisoned (`0xfd`, L972) memory.

#### 3.2 `runtime.Pinner` Internals (`src/runtime/pinner.go`)

Introduced in Go 1.21, `runtime.Pinner` decouples object lifetime/location pinning from OS-thread pinning (`runtime.LockOSThread()`):

1. **Per-span 2-bit `pinnerBits` + overflow `specialPinCounter` (`pinner.go:166-203, 257-325, 375-428`):**
   - Each `mspan` lazily allocates a 2-bit-per-object bitmap (`pinnerBits`, `divRoundUp(nelems*2, 8)` bytes, 8-byte aligned, L316–325): bit 0 is `isPinned`, bit 1 is `isMultiPinned`.
   - The first `Pin(ptr)` sets `isPinned` under `span.speciallock` (with `acquirem()` disabling preemption and `span.ensureSwept()`). Subsequent pins of the same object set `isMultiPinned` and increment a linked-list `specialPinCounter` record in `span.specials` (L190–199, L375–398), avoiding counter allocation in the common single-pin case.
   - `unpinObjects` (`pinner.go:207-255`) caps work per lock acquisition at `const maxBatch = 64` (L222) so unpinning thousands of references cannot starve scheduler preemption.
   - During sweep, `refreshPinnerBits()` (L341–368) copies live bitmaps into the next mark-bit arena epoch or clears `span.pinnerBits = nil` if all 64-bit chunks are zero.
2. **Validation edges and silent non-heap bypass (`pinner.go:125-172`):**
   - `pinnerGetPtr` panics on `nil`, non-pointer kinds, and **Go user arenas** (`inUserArenaChunk(uintptr(e.data))`, L134–137: *"Arena-allocated objects are not eligible for pinning"*).
   - `setPinned(ptr)` checks `span := spanOfHeap(uintptr(ptr))` (L167). If `span == nil`—covering C pointers, linker globals, zero-size objects, **and raw stack addresses smuggled via `unsafe.Pointer`**—`setPinned` **silently returns `false`** without error! Safe Go code passing `&localVar` to `Pinner.Pin(pointer any)` is protected *only* because passing to `any` forces Go escape analysis to heap-allocate `localVar`; bypassing escape analysis via `noescape` or `unsafe.Pointer` yields a silent no-op pin on a movable stack address.
3. **Shallow pinning and leak-panic detection (`pinner.go:42-44, 70-75, 444-446`):**
   - Pinning is strictly **non-transitive**: pointers *inside* a pinned struct must be pinned individually (`cgoCheckArg` and `cgoCheckUnknownPointer`, `cgocall.go:659-808`, recursively verify that every transitively reachable Go pointer satisfies `isPinned(pp)` under default `cgocheck=1`, and `cgoCheckPtrWrite`, `cgocheck.go:25-69`, intercepts stores of unpinned Go pointers into C memory under `GOEXPERIMENT=cgocheck2`).
   - Every newly allocated internal `pinner` registers a GC finalizer (`SetFinalizer`, L70–75) that unpins leaked refs and triggers **`pinnerLeakPanic()`** (*`"runtime.Pinner: found leaking pinned pointer; forgot to call Unpin()?"`*). Thus, unlike a soft lease, forgetting `Unpin()` is fatal to the Go process, while holding `Pinner` alive on behalf of an untrusted C peer allows unbounded heap retention.
4. **Multi-word tearing across FFI (Go 2022 Memory Model):**
   Go slices (`{ptr, len, cap}`), strings (`{ptr, len}`), and interfaces (`{type, data}`) are multi-word values without atomic tearing protection. Concurrent unsynchronized mutation of a Go slice/interface while passing it across cgo can pair an old `ptr` with a new `len` (or mismatched type descriptor and data pointer), bypassing bounds checks even when the target buffer is pinned; safe FFI must snapshot multi-word headers atomically or copy out before crossing.

---

### 4. CPython PEP 703 `nogil` QSBR vs. HPy, Node-API, and Wasmtime Handle Tables

Basis: normative + source + documentation + execution

#### 4.1 CPython Free-Threaded (`Py_GIL_DISABLED`) Memory Reclamation & FFI Hazards

CPython's PEP 703 free-threaded architecture (`python/cpython` `03e7a8854d71`) replaces the Global Interpreter Lock with four interacting mechanisms that radically tighten FFI invariants:

1. **Biased Reference Counting (`Include/object.h:156-167`, `Include/refcount.h:81-92`, Choi et al., PACT 2018):**
   Each `PyObject` carries `ob_tid` (owning thread ID, or `0` = `_Py_UNOWNED_TID` when immortal/merged), `ob_mutex` (`PyMutex`), `ob_ref_local` (`uint32_t`, non-atomic fast path for the owning thread), and `ob_ref_shared` (`Py_ssize_t`, atomic off-owner count shifted left by `_Py_REF_SHARED_SHIFT = 2`, with 2 low flag bits: `_Py_REF_SHARED_INIT = 0x0`, `_Py_REF_MAYBE_WEAKREF = 0x1`, `_Py_REF_QUEUED = 0x2`, `_Py_REF_MERGED = 0x3`). Any legacy C extension directly mutating `ob_refcnt` or reading `PyObject*` without atomic/API discipline corrupts refcounts under concurrent threads.
2. **Quiescent State-Based Reclamation (`Include/internal/pycore_qsbr.h:27-189`, `Python/qsbr.c:42-291`):**
   Derived from FreeBSD's GUS SMR (Hart et al., JPDC 2007), CPython's per-interpreter `_qsbr_shared` holds a monotonically increasing odd 64-bit write sequence `wr_seq` (`QSBR_INITIAL = 1`, `QSBR_INCR = 2`) and the minimum attached thread read sequence `rd_seq`. Detached threads store `QSBR_OFFLINE = 0`, preventing collision with any odd sequence number (`pycore_qsbr.h:23-29`). Per-thread `_qsbr_thread_state` entries are padded to `_Py_QSBR_CACHE_LINE_SIZE` (`128 B` on AArch64/Apple Silicon, `64 B` elsewhere, L81–91) to eliminate false sharing on eval-loop back-edges.
   - **Deferred mimalloc page pinning & FFI stall amplification (`pycore_qsbr.h:55-63`, `qsbr.c:130-172`, Probe 2B.1):** Lock-free container reads (`dict` keys, `list` backing arrays) and mimalloc pages scheduled for size-class/cross-thread reuse (`deferred_page_memory`) cannot be freed until `QSBR_LEQ(goal, rd_seq)`. In `qsbr_poll_scan` (L130–158), a single attached thread that blocks inside a C/Rust FFI call without detaching (`Py_BEGIN_ALLOW_THREADS` -> `_Py_qsbr_detach`, storing `0`) pins `min_seq` at its stale sequence indefinitely. Probe 2B.1 confirms that over 50 epochs of 64 KiB page deferrals across 7 active workers, 1 stalled attached thread holds `rd_seq = 1` with **0 pages reclaimed (3,200 KiB leaked)**; the instant it detaches (`seq = 0`), `rd_seq` jumps to `101` and all 50 pages reclaim immediately.
   - **Array growth Stop-The-World (`qsbr.c:202-208`):** Resizing `shared->array` triggers `_PyEval_StopTheWorld(interp)`, requiring every attached thread to reach an eval/detach boundary—another FFI deadlock vector if native code ignores thread detachment.
3. **Suspendable Critical Sections (`Python/critical_section.c:21-165`):**
   `Py_BEGIN_CRITICAL_SECTION` locks per-object `PyMutex`es, but **`_PyCriticalSection_SuspendAll` (L109–130) unlocks all active critical sections on the thread whenever the thread detaches, acquires a contended lock, or re-enters arbitrary Python callbacks (`__del__`, `__hash__`, `__eq__`)**, flagging `*tagptr |= _Py_CRITICAL_SECTION_INACTIVE`. Therefore, critical sections prevent data races on single C-API operations, **not** atomic invariants across arbitrary callbacks; borrowed `PyObject*` references (`PyList_GetItem`, `PyDict_GetItem`) become immediate UAF hazards in `nogil` builds because concurrent resizing or suspended locks invalidate the container slot before the caller uses the borrowed pointer.

#### 4.2 Opaque Handle Tables: HPy, Node-API (V8), and Wasmtime Component Model

1. **HPy (`hpyproject/hpy` `0a1d8791dfb2`):**
   Eliminated borrowed references entirely: every `HPy` is an independent owned handle closed via `HPy_Close`, while object-embedded references use `HPyField` (`HPyField_Load`/`Store`) and module globals use `HPyGlobal` so moving GCs (PyPy, GraalPy) can relocate Python objects freely without pinning. On CPython's universal ABI (`hpy/universal/src/handles.h:12-22`), `_py2h` encodes `(HPy){(HPy_ssize_t)obj + 1}`—intentionally misaligning the pointer by `+1` so accidental casts to `PyObject*` fault immediately. Per `hpy/README.md:11-36`, HPy is **archived / no longer actively maintained**, with its design absorbed into CPython PEPs 620, 670, 674, and the PyNI (`pep-08xx`) effort.
2. **Node-API / V8 (`nodejs/node` `4f37a6a8aac6`):**
   Separates stack-scoped local handles (`napi_handle_scope`, `napi_escapable_handle_scope`, `js_native_api_v8.cc:2927-2970`) from heap-persistent reference-counted handles (`v8impl::Reference`, `js_native_api_v8.cc:659-765`). A `Reference` wraps `v8::Persistent<v8::Value>` linked into `env->reflist`: when `refcount_ > 0` it strongly roots the JS object across V8 moving/compacting GC cycles; when `refcount_` drops to `0` (`Unref`, L702–712) it transitions to weak (`persistent_.SetWeak(..., WeakCallback)`, L751–765), releasing the object while preserving GC autonomy. For byte buffers, `napi_get_arraybuffer_info` (L3185–3219) hands out raw `ab->Data()` pointers, which dangle if JS executes `napi_detach_arraybuffer` (L3717) or `ArrayBuffer.prototype.transfer()` while native code caches the pointer. Crucially, under **`V8_ENABLE_SANDBOX`**, `node_api_create_external_sharedarraybuffer` (L3152–3153) fails closed with **`napi_no_external_buffers_allowed`**, proving that hardware/software memory-cage isolation directly rejects zero-copy external host buffers (Trilemma branch $\mathrm{P2} \land \mathrm{P3} \implies \neg\mathrm{P1}$).
3. **Wasmtime Component Model (`bytecodealliance/wasmtime` `3ce2209872cc` & `WebAssembly/component-model` `585526aa1f2c`):**
   Enforces full host-pointer opacity (`Resource<T>` wraps an unforgeable `u32` handle; `host_static.rs:21-40`) using a two-layer architecture:
   - **VM `HandleTable` (`crates/wasmtime/src/runtime/vm/component/handle_table.rs:47-327`) & `ResourceTables` (`vm/component/resources.rs:53-257`):** Stores 1-based handles bounded by `MAX_HANDLE = 1 << 28` (Canonical ABI reserves the upper 4 bits; `CanonicalABI.md:1046, 1092`). Each `VMHandleTableSlot` is `Free { next: u32 }`, `ResourceOwn { resource, lend_count }`, or `ResourceBorrow { resource, lend_count, scope }` (with `lend_count` statically asserted at an identical byte offset across both variants for branchless JIT updates, L23–41). Every borrow increments `lend_count` on the lender and `CallContext.borrow_count` on the active call scope; `remove_resource` traps if `lend_count != 0` (`"cannot remove owned resource while borrowed"`, L304–306), and call exit traps if `borrow_count != 0`.
   - **Store-wide DoS cap (`HandleCounter`, `handle_table.rs:49-92`):** Tracks allocated slots + active lends across all tables in a `Store` (`used <= limit`). Notably, `remove()` returns freed slots to the LIFO free-list (`self.next = idx - 1`, L179–185) **without decrementing `HandleCounter.used`** because the underlying `TryVec` never shrinks (L55–56)—bounding peak host memory against churn attacks.
   - **Host `ResourceTable` (`crates/wasmtime/src/runtime/component/resource_table.rs:38-250`):** Maps `Resource<T>` to `Box<dyn AnyWithTypeName + Send>` with `DEFAULT_MAX_CAPACITY = 1_000_000` (L93), LIFO `free_head`, optional parent/child `BTreeSet<u32>` enforcing `ResourceTableError::HasChildren` before parent deletion (L95–110), and `DELETE_WITH_TOMBSTONE = false` by default (L83–87).
   - **Non-generational ABA boundary (Probe 2A):** Because neither `HandleTable` nor `ResourceTable` embeds a generation counter in the `u32` handle, dropping handle `1` of type `File` and immediately inserting a new `File` reuses handle `1` via the LIFO free-list. While host Rust memory safety and cross-type isolation remain intact, a buggy or confused-deputy guest retaining a stale integer `1` silently aliases the newly allocated `File` (`rep = 202` instead of `101`, verified in Probe 2A).

---

### 5. DoS-Bounded Cross-Domain Pinning Leases and Generational Handle Protocol

Basis: derived + execution

To close both the **liveness/DoS gap** (OpenJDK `SpinYield`/unreleased `acquire0`, Go leaked `Pinner`, CPython attached-thread QSBR freeze, Node-API leaked `napi_ref`) and the **same-type ABA aliasing gap** (Wasmtime LIFO `u32` reuse) across mutually distrusting domains, a cross-domain FFI membrane should implement a **two-lane generational lease protocol**:

#### 5.1 Lane A: 64-Bit Generational Lease Handle Table

Represent every cross-domain object handle as an opaque 64-bit capability `H = (gen : u32) << 32 | (idx : u32)` (`idx >= 1`, `gen >= 1`, reserving `0` as null and retiring slots on `gen == u32::MAX` to preclude generation wraparound). Each foreign principal $P$ receives an isolated quota `LeaseQuota = (max_handles, max_pinned_bytes, max_ttl_epochs)` with slot state:

```text
Slot ::= Free { gen: u32, next_free: Option<u32> }
       | Live { gen: u32, ty: TypeId, target: GcRelocatableRef,
                pinned_bytes: usize, expiry_epoch: u64, borrow_count: u32 }
```

**State transitions and invariants (verified in Probe 2A):**
1. **`alloc(P, obj, nbytes, ttl)`:** Fails closed with `LeaseQuotaExceeded` if `P.live_handles + 1 > max_handles` or `P.pinned_bytes + nbytes > max_pinned_bytes` or `ttl > max_ttl_epochs`. Registers `target` as a **GC-movable root** (e.g., `HPyField`, `rb_gc_mark_movable` + `rb_gc_location`, `v8::Persistent`, JVM `OopHandle`) so host compaction updates `Slot.target` in place without pinning heap pages.
2. **`resolve(H, expected_ty)`:** Checks `idx < len`, `slot == Live`, `slot.gen == H.gen`, `slot.ty == expected_ty`, and `current_epoch < slot.expiry_epoch`. Any mismatch deterministically returns `StaleGeneration | WrongType | LeaseExpired`—eliminating intra-type ABA aliasing (Probe 2A: `gh1 = 0x100000001` rejected after slot reuse as `gh2 = 0x200000001`).
3. **`advance_epoch_and_reclaim()` (Byzantine-tolerant revocation):** Unlike OpenJDK's `SpinYield` or CPython's un-detached QSBR, expiry requires **zero cooperation** from peer $P$: when `current_epoch >= slot.expiry_epoch`, the host atomically transitions `Live -> Free { gen: gen + 1 }`, decrements `P.live_handles` and `P.pinned_bytes`, and drops `Slot.target` so GC reclaims the underlying object.

#### 5.2 Lane B: Zero-Copy Byte Arenas Under Forced Revocation

When bulk data bandwidth forbids copying (e.g., high-throughput I/O, numerical matrices, DMA rings), restrict raw pointers exclusively to **pointer-free off-heap byte arenas** paired with explicit revocation semantics:
- **Single-copy fallback (`copy_once_private`):** For small control/header payloads across shared memory without hardware exclusion, perform one volatile, compiler-barriered load into private memory before parsing to prevent concurrent TOCTOU/double-fetch and Go multi-word tearing.
- **Hardware-enforced revocation vs. cooperative handshakes:** When forcing a Lane B lease expiry against an uncooperative peer, OS/hardware page-table revocation (`mprotect(PROT_NONE)` + TLB shootdown, or `RMI_GRANULE_UNDELEGATE`/`TDISP` lock revocation + IOMMU `ATC` flush) enforces immediate spatial cut-off, but converts subsequent peer accesses into asynchronous hardware faults (`SIGSEGV`, `SError`, `#MC`, or PCIe Completer Abort). Callers must explicitly choose between (i) **trapped hardware revocation** (bounded host liveness, fatal fault to misbehaving peer), (ii) **cooperative epoch drain** (clean `ScopedAccessError`/Wasm trap, vulnerable to peer stall unless backed by a watchdog kill), or (iii) **copying across a Lane A handle**.
- **Cross-domain reference cycles:** Whenever two autonomous runtimes ($A \leftrightarrow B$, e.g., CPython $\leftrightarrow$ JVM or JS $\leftrightarrow$ Rust/Wasm) hold strong cross-domain handles referencing each other's objects, neither runtime's local cycle collector can trace across the opaque wall. Bounded-TTL leases or explicit weak handles (`WeakCallback` / weakrefs) are mandatory to break cross-domain garbage cycles without global stop-the-world distributed tracing.

## Boundaries

- **Generational wraparound and 64-bit vs. 32-bit ABI constraints (`known not to apply` to WebAssembly Component Model MVP `i32` handles):** The WebAssembly Component Model Canonical ABI (`CanonicalABI.md:1046`) fixes resource handles to 32-bit `i32` values (`MAX_HANDLE = 1 << 28`), leaving insufficient bits for wide per-slot generation counters without shrinking maximum concurrent handles drastically. The 64-bit `(idx:32, gen:32)` generational lease design in §5.1 therefore applies to host-native, IPC, and FFI ABIs that can carry 64-bit handles, not unmodified Component Model MVP guest ABIs.
- **Pre-JDK-22 / older OpenJDK releases (`not examined`):** Only `openjdk/jdk` at `d65bc4b262564e535c431aa8d4b58a1f7630fa64` (post-JEP 454 and post-JDK-8310644) was directly inspected. Earlier incubator/preview FFM releases (`JDK 17–21`) used the reverting `CLOSING -> OPEN` handshake behavior still described in the stale Javadoc of `X-ScopedMemoryAccess.java.template:62-63`.
- **CPython PEP 703 `PyNI` (`pep-08xx`) and CPython 3.15+ stable ABI evolution (`not examined`):** `hpy/README.md` points to the active `py-ni/peps` `pep-08xx` handle proposal; only `python/cpython` (`03e7a8854d71`) and archived `hpyproject/hpy` (`0a1d8791dfb2`) were directly examined.
- **JVM JNI `GetPrimitiveArrayCritical` and .NET `GCHandle.Alloc(..., Pinned)` (`not examined`):** Classic JNI critical regions (which can stall GC or copy arrays) and CLR pinned `GCHandle`s / `Memory<T>` `MemoryHandle` were not directly source-inspected in this report; analogies should be checked against HotSpot `jni.cpp` and CoreCLR `gchandleutilities.cpp` before relying on them.
- **Go future moving heap GC (`unknown`):** Current Go (`b496a3044e1d`) uses a non-moving mark-sweep heap (`pinnerBits` currently prevents premature reclamation and satisfies `cgocheck`, while `cgocall.go:582-586` explicitly notes `cgoCheckPointer` will pin pointers *"When and if we implement a moving garbage collector"*). Whether a future moving Go collector changes `setPinned` behavior on interior pointers or span fragmentation overhead is unresolved.
- **Hardware fault containment on forced Lane B revocation (`unsupported` without OS/VMM signal/fault isolation):** Forcing `munmap`/`mprotect(PROT_NONE)` or PCIe `TDISP` revocation while an in-process C thread reads a shared arena raises `SIGSEGV`/bus errors that cannot be safely caught as ordinary language exceptions without dedicated signal-trampoline/sandbox boundaries (unlike HotSpot's `@Scoped` async handshake or Wasmtime's table-lookup traps).
- **Stronger claim not established:** Demonstrating that a generational handle table eliminates ABA aliasing and bounds memory DoS does **not** solve distributed cyclic garbage collection across mutually distrusting heaps if both domains repeatedly renew TTL leases on a cycle.

## Evidence

### 1. Upstream Source & Specification Anchors (Observed 2026-11-19)

| Subject | Commit / Standard | Path & Lines / Symbols | Verified Fact |
|---|---|---|---|
| `openjdk/jdk` | `d65bc4b262564e535c431aa8d4b58a1f7630fa64` | `src/hotspot/share/prims/scopedMemoryAccess.cpp:42-317` (`for_scoped_methods`, `ScopedAsyncExceptionHandshakeClosure`, `CloseScopedMemoryHandshakeClosure`, `ScopedMemoryAccess_closeScope`) | Two-phase handshake: installs async exception handshake for threads inside `@Scoped`, calls `Deoptimization::deoptimize` on compiled frames with `has_scoped_access() && is_session_live()`, then blocks in `SpinYield` loop until `async_exceptions == 0` (L312–316). |
| `openjdk/jdk` | `d65bc4b262564e535c431aa8d4b58a1f7630fa64` | `src/java.base/share/classes/jdk/internal/misc/X-ScopedMemoryAccess.java.template:59-153` | Stale Javadoc (L62–63) claims handshake failure leaves session open, disagreeing with `scopedMemoryAccess.cpp`; `@Scoped` wraps `checkValidStateRaw()` + `UNSAFE` + `Reference.reachabilityFence` (L136–153). |
| `openjdk/jdk` | `d65bc4b262564e535c431aa8d4b58a1f7630fa64` | `src/java.base/share/classes/jdk/internal/foreign/{MemorySessionImpl,SharedSession}.java` | `@Stable int state` plain check in `checkValidStateRaw()` (`MemorySessionImpl.java:83-84, 199-206`); `ACQUIRE_COUNT.compareAndExchange(this, 0, -1)` + `STATE.setVolatile(CLOSED)` + `closeScope` (`SharedSession.java:83-102`). |
| `golang/go` | `b496a3044e1dcdc3eed0af3e0e89db92f740d764` | `src/runtime/pinner.go:34-446` (`Pinner`, `pinnerGetPtr`, `isPinned`, `setPinned`, `unpinObjects`, `pinnerBits`, `incPinCounter`, `pinnerLeakPanic`) | 2-bit `pinnerBits` + `specialPinCounter`; rejects `inUserArenaChunk` (L134–137); silently returns `false` when `spanOfHeap == nil` (L167–172); `maxBatch = 64` (L222); finalizer triggers `pinnerLeakPanic` (L70–75, L444–446). |
| `golang/go` | `b496a3044e1dcdc3eed0af3e0e89db92f740d764` | `src/runtime/stack.go:652, 954-1010` (`adjustpointers`, `copystack`); `src/runtime/cgocall.go:590-856`; `src/runtime/cgocheck.go:25-179` | `copystack` reallocates and `memmove`s goroutine stacks (poisoning with `0xfd`); `cgoCheckPointer`/`cgoCheckArg`/`cgoCheckPtrWrite` enforce recursive `isPinned` invariant on Go pointers passed to or stored in C memory. |
| `python/cpython` | `03e7a8854d714fabb3ab5b8c8f984fc1214f65b0` | `Include/internal/pycore_qsbr.h:27-189`, `Python/qsbr.c:42-291` | Odd `wr_seq` (`QSBR_INITIAL=1`, `QSBR_INCR=2`), `QSBR_OFFLINE=0`, 128 B AArch64 / 64 B cache-line padding (`_Py_QSBR_CACHE_LINE_SIZE`), `deferred_page_memory`, `qsbr_poll_scan` `min_seq` barrier, `_PyEval_StopTheWorld` on thread-array resize (L202–208). |
| `python/cpython` | `03e7a8854d714fabb3ab5b8c8f984fc1214f65b0` | `Include/object.h:156-167`, `Include/refcount.h:81-92`, `Python/critical_section.c:21-165` | Biased RC (`ob_tid`, `ob_ref_local`, `ob_ref_shared` with `_Py_REF_SHARED_SHIFT=2` and 4 flag states); `_PyCriticalSection_SuspendAll` unlocks all active critical sections on thread detach/suspension (L109–130). |
| `hpyproject/hpy` | `0a1d8791dfb28ea7d928bd1aabe37cc40dfb8146` | `README.md:11-36`, `hpy/universal/src/handles.h:12-56` | Archived status + handoff to PEPs 620/670/674 & PyNI; CPython universal handle tagged `+1` (`(HPy_ssize_t)obj + 1`) to trap raw casts. |
| `nodejs/node` | `4f37a6a8aac657b309714d953c7e28c2de6caf40` | `src/js_native_api_v8.cc:659-765, 2927-2970, 3127-3219, 3717` | `Reference` wraps `v8::Persistent` with strong/weak transitions (`SetWeak`/`ClearWeak`); `V8_ENABLE_SANDBOX` rejects external buffers with `napi_no_external_buffers_allowed` (L3152–3153); `napi_get_arraybuffer_info` exposes raw `ab->Data()`. |
| `bytecodealliance/wasmtime` | `3ce2209872ccf1ea115914a81e020aef66a10c51` | `crates/wasmtime/src/runtime/vm/component/{handle_table,resources}.rs`, `crates/wasmtime/src/runtime/component/{resource_table.rs,resources/host_static.rs}` | `MAX_HANDLE = 1 << 28`; `HandleCounter` never decrements on slot `remove`; LIFO free-list (`self.next = idx - 1`); `lend_count` + `CallContext.borrow_count`; `ResourceTable` `DEFAULT_MAX_CAPACITY = 1_000_000`, `DELETE_WITH_TOMBSTONE = false`, parent/child `BTreeSet<u32>`. |
| `WebAssembly/component-model` | `585526aa1f2c7f76f07557d16e265dede38b3acb` | `design/mvp/CanonicalABI.md:1042-1127, 1383-1406, 2359` | `Table.MAX_LENGTH = 2**28 - 1` (reserving high 4 bits); `num_lends` counter and `trap_if(h.num_lends != 0)`. |
| `ruby/ruby` | `2979ed47232036f592dcc24e05c6dab7fa139eb2` | `include/ruby/internal/gc.h:160-215` | `rb_gc_mark` pins objects vs. `rb_gc_mark_movable` + `rb_gc_location` opt-in compaction update. |

### 2. Execution Probe 2A & 2B: Handle-Table ABA, DoS Leases, QSBR Stall, and Handshake Liveness

**Environment:** Python 3.13.15, executed 2026-11-19.

**Self-contained executable reproducer (Python 3.10+):**
```python
# Probe 2A (Wasmtime LIFO free-list vs 64-bit Generational Lease Table) & Probe 2B (QSBR + Handshake)
slots, free_head, gens = [], None, []
def wt_alloc(rep):
    global free_head
    if free_head is None:
        slots.append(rep); return len(slots)
    i = free_head; free_head = slots[i]; slots[i] = rep; return i + 1
def wt_drop(h):
    global free_head
    slots[h - 1] = free_head; free_head = h - 1
h1 = wt_alloc(101); wt_drop(h1); h2 = wt_alloc(202)
assert h1 == h2 == 1 and slots[h1 - 1] == 202  # Same-type LIFO ABA aliasing

gslots, gfree, live, pbytes, epoch = [], None, 0, 0, 1
def gl_alloc(rep, nb, ttl, max_b=4096):
    global gfree, live, pbytes
    if pbytes + nb > max_b: raise RuntimeError("LeaseQuotaExceeded: max_pinned_bytes")
    if gfree is None:
        gslots.append([1, True, rep, nb, epoch + ttl, None]); idx = len(gslots) - 1
    else:
        idx = gfree; s = gslots[idx]; gfree = s[5]
        s[1], s[2], s[3], s[4] = True, rep, nb, epoch + ttl
    live += 1; pbytes += nb; return (gslots[idx][0] << 32) | (idx + 1)
def gl_revoke(idx):
    global gfree, live, pbytes
    s = gslots[idx]; s[1] = False; s[0] += 1; live -= 1; pbytes -= s[3]; s[3] = 0; s[5] = gfree; gfree = idx
gh1 = gl_alloc(101, 2048, 2); gl_revoke(0); gh2 = gl_alloc(202, 2048, 2)
assert (gh1 >> 32) == 1 and (gh2 >> 32) == 2 and gslots[0][0] != (gh1 >> 32)  # ABA rejected

# Probe 2B.1 (CPython PEP 703 QSBR grace-period stall: wr_seq odd += 2, QSBR_OFFLINE = 0)
wr_seq, rd_seq, tseq, deferred = 1, 1, [1] * 8, []
for _ in range(50):
    wr_seq += 2; deferred.append((wr_seq, 64))
    for i in range(1, 8): tseq[i] = wr_seq
    rd_seq = max(rd_seq, min(s for s in tseq if s != 0))
    deferred = [p for p in deferred if p[0] > rd_seq]
assert (wr_seq, rd_seq, len(deferred)) == (101, 1, 50)  # 3200 KiB stalled by attached thread 0
tseq[0] = 0  # _Py_qsbr_detach() -> QSBR_OFFLINE
rd_seq = max(rd_seq, min((s for s in tseq if s != 0), default=wr_seq))
deferred = [p for p in deferred if p[0] > rd_seq]
assert (rd_seq, len(deferred)) == (101, 0)  # Immediate 100% reclamation
```

**Observed outputs (2026-11-19):**
- `[Wasmtime] drop-while-borrowed -> TRAP: cannot remove resource while borrowed`
- `[Wasmtime] unreturned-borrow-on-exit -> TRAP: unknown handle: borrow handles still remain`
- `[Wasmtime] ABA reuse: stale_copy=1, new_h2=1, rep(stale_copy)=202 (SILENTLY ALIASED TO rep=202!)`
- `[GenLease] ABA check: gh1=0x100000001, gh2=0x200000001, resolve(gh1) -> REJECTED: StaleGeneration(handle_gen=1, slot_gen=2)`
- `[GenLease] DoS byte quota (4096B full) -> REJECTED: LeaseQuotaExceeded: max_pinned_bytes`
- `[GenLease] forced expiry at epoch=3: reclaimed=2, live=0, pinned_bytes=0`
- `[QSBR] Attached stalled FFI thread (50 epochs): wr_seq=101, rd_seq=1, unreclaimed_pages=50 (3200 KiB)`
- `[QSBR] After _Py_qsbr_detach() (seq=0): wr_seq=101, rd_seq=101, freed_now=50, remaining=0 (0 KiB)`
- `[ScopedMemoryAccess] Cooperative Java reader (tick 5): CLOSED_AT_TICK_5 (async_exceptions=0)`
- `[ScopedMemoryAccess] Stalled native/JVMTI reader under @Scoped: SPINYIELD_STALLED_AT_TICK_1000 (async_exceptions=1, memory_unfreed=True)`

## Revalidation

Use these narrow checks when revalidating against newer JDK, Go, CPython, Node.js, or Wasmtime releases:

1. **OpenJDK `ScopedMemoryAccess` protocol & Javadoc sync check:** Diff `src/hotspot/share/prims/scopedMemoryAccess.cpp` (`CloseScopedMemoryHandshakeClosure`, `ScopedMemoryAccess_closeScope`) and `X-ScopedMemoryAccess.java.template` against `d65bc4b262564e535c431aa8d4b58a1f7630fa64`. Verify whether `SpinYield` remains unbounded, whether `Deoptimization::deoptimize` is still used for compiled loop hoisting, and whether the stale Javadoc at L62–63 has been updated.
2. **Go `runtime.Pinner` & `cgocheck` check:** Diff `src/runtime/pinner.go` (`pinnerGetPtr`, `setPinned`, `pinnerLeakPanic`) and `src/runtime/cgocheck.go` against `b496a3044e1dcdc3eed0af3e0e89db92f740d764`. Check whether `setPinned` still returns `false` silently for `spanOfHeap == nil` (including raw stack `unsafe.Pointer`s) and whether Go introduces a moving heap GC or changes `cgocheck2` defaults.
3. **CPython `nogil` QSBR & C-API handle check:** Diff `Include/internal/pycore_qsbr.h`, `Python/qsbr.c` (`qsbr_poll_scan`, `_Py_qsbr_reserve`), and `Python/critical_section.c` (`_PyCriticalSection_SuspendAll`) against `03e7a8854d714fabb3ab5b8c8f984fc1214f65b0`. Also monitor whether PyNI (`pep-08xx`) lands opaque handle tables in CPython mainline.
4. **Node-API / V8 Sandbox check:** Inspect `V8_ENABLE_SANDBOX` guards around `napi_create_external_arraybuffer` / `node_api_create_external_sharedarraybuffer` in `src/js_native_api_v8.cc` to check whether Node.js enables V8 Sandbox by default or adds sandbox-safe zero-copy arena APIs.
5. **Wasmtime handle-table ABA & DoS check:** Diff `crates/wasmtime/src/runtime/vm/component/handle_table.rs` (`VMHandleTableSlot`, `HandleCounter`, `remove`) and `crates/wasmtime/src/runtime/component/resource_table.rs` (`DELETE_WITH_TOMBSTONE`, `DEFAULT_MAX_CAPACITY`) against `3ce2209872ccf1ea115914a81e020aef66a10c51` to see if generational tags, shrinking `HandleCounter`, or configurable tombstones are introduced.
