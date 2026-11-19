# Garbage Collection Barriers, Safepoints, and Runtime Invariants

## Summary

Automatic memory management—precise moving/compacting collection, concurrent mark-and-sweep, generational collection, and compile-time reference counting with in-place reuse—imposes structural **compiler–runtime invariants** that scalar optimizations silently corrupt when GC semantics are bolted onto an untyped IR. Across seven pinned production codebases (`LLVM`, `OpenJDK HotSpot`, `Go`, `OCaml 5`, `MMTk`, `Lean 4`, `Koka`), thirteen foundational papers, and a standalone model-checking probe (`support/verify_gc_tricolor_and_derived_roots.py`), five contracts govern soundness:

1. **Precise stack maps and derived-pointer base pairing (`Diwan, Moss & Hudson PLDI 1992`, `LLVM Statepoints`)**: Moving collectors cannot infer object headers from raw addresses because loop strength reduction and GEP offsetting synthesize **exterior derived pointers** that fall outside the source object (and even inside adjacent objects) while making `base` appear dead to liveness analysis. Sound lowering separates GC references (e.g., LLVM non-integral `addrspace(1)`) from raw integers and pins `(base, derived)` pairs across safepoints (`gc.statepoint` / `gc.relocate`), reconstructing `derived' = base' + (derived - base)` after relocation.
2. **Safepoint polling and Time-To-Safepoint (TTSP)**: Removing polls from counted loops (`int` loops in HotSpot C2) or omitting non-call loop polls (pre-1.14 cooperative Go) causes multi-second stop-the-world stalls. Production runtimes bound TTSP via HotSpot C2 **counted-loop strip mining** (`OuterStripMinedLoop` + `LoopStripMiningIter`) with thread-local guard-page/watermark polling (`SafepointMechanism`), or via **asynchronous signal preemption** (`golang/go` `isAsyncSafePoint` + `PCDATA_UnsafePoint` exclusion + conservative async stack/register scanning).
3. **Concurrent tri-color completeness and x86-TSO ordering**: Under concurrent marking with un-barriered stack writes and no stack re-scanning, omitting *either* deletion shading (`Yuasa`) or insertion shading (`Dijkstra`) loses live white objects—verified by minimal 8-step and 7-step probe counterexamples—while Go's hybrid barrier (`shade(*slot); if stack is grey: shade(ptr)`) achieves 0 lost-object states across 38,010 exhaustively explored states without STW stack re-scans. Go shades *unconditionally* on object color to avoid an x86-TSO Dekker store-buffer race (`(r1=0, r2=0)` without `MFENCE`, verified in the probe). OpenJDK G1 and OCaml 5 instead pair Yuasa SATB deletion barriers with STW initial root scans and generational remembered sets.
4. **Colored-pointer load barriers and VM-binding traits (`OpenJDK Generational ZGC`, `MMTk`)**: Post-JEP 490 OpenJDK ZGC stores **16 low-order metadata bits** (`RRRRMMmmFFrr0000`) in `zpointer`, combining the x86-64 load-good check and unmasking into one speculative right-shift (`CF=1` good, `ZF=1` null, `ja` slowpath iff `CF==0 && ZF==0`) patched at nmethod entry, with monotonic CAS self-healing (`ZBarrier::self_heal`) and 32-entry `ZStoreBarrierBuffer` buffers offloading marking and remembered sets to store barriers. `MMTk`'s `VMBinding` traits formalize the collector–VM boundary and expose compiler hazards such as write-barrier elision failing across deoptimization safepoints (`Barrier::object_probable_write`).
5. **Compile-time reference counting, in-place reuse, and mechanized GC proofs**: Lean 4 (migrated from legacy `IR/RC.lean` to the `LCNF` impure pass pipeline) and Koka (`Perceus`) compile purely functional updates into `rc == 1` in-place mutation (`reset`/`reuse` tokens) with `rc > 1` copy fallback and borrow inference that excludes `reset` targets from derived borrows. Lean 4's C runtime (`lean.h`) encodes ST/MT/persistent/sticky 32-bit reference counts whose overflow saturation is formally verified in Lean (`tests/verif/Verif/runtime/RC.lean`). Mechanized tracing-GC proofs span Boogie/Z3 assembly collectors (`Hawblitzel & Petrank 2009`), Coq `GCminor` (`McCreight et al. 2007/2010`), HOL4 CakeML generational GC (`Sandberg Ericsson et al. 2019`), and Isabelle/HOL x86-TSO on-the-fly GC (`Gammie et al. 2015`).

## Applicability

This report synthesizes compiler–runtime GC contracts across seven pinned upstream source repositories and thirteen peer-reviewed papers listed in `REPORT.json`, all directly inspected or executed on `2026-11-19`:

- **Compiler safepoint and root-map infrastructure**: `llvm/llvm-project` (`4d369315c397296c4e3fdaff15b7e6500b533d16`, X86_64 and AArch64 statepoint lowering, `Statepoints.md`, `GarbageCollection.md`, `StackMaps.md`, `RewriteStatepointsForGC.cpp`, `PlaceSafepoints.cpp`), interpreted with `Diwan, Moss & Hudson (PLDI 1992)`.
- **Production tracing runtimes (comparative study)**:
  - `openjdk/jdk` (`4f33273115381cd7697082fcb1bb2642dae19043`) — **post-JEP 490 Generational ZGC** (non-generational JEP 333 multi-mapped ZGC has been removed upstream; the two layouts differ fundamentally), G1 dual SATB/card-table barriers, HotSpot `SafepointMechanism`, and C2 counted-loop strip mining (`loopnode.cpp`).
  - `golang/go` (`b496a3044e1dcdc3eed0af3e0e89db92f740d764`) — non-moving, non-generational concurrent mark-sweep (`mgc.go`), hybrid write barrier (`mbarrier.go`, `mwbbuf.go`), signal-based async preemption (`preempt.go`), and shallow FFI pinning (`pinner.go`).
  - `ocaml/ocaml` (`d921d1e86c56baa7b30e890ced455c12255793f5`) — OCaml 5 multicore STW parallel minor GC (`minor_gc.c`), concurrent major mark-sweep with domain-local pools (`major_gc.c`, `shared_heap.c`), SATB + generational write barrier (`memory.c`), and C FFI shadow-root macros (`caml/memory.h`), alongside `Sivaramakrishnan et al. (ICFP 2020)`.
  - `mmtk/mmtk-core` (`d154f4f0dcca27439b920165ce5c948ca18aef24`) — `VMBinding` traits (`src/vm/*`), `BarrierSelector`/`Barrier` (`src/plan/barriers.rs`), `PlanConstraints`, `LXR`, and `Concurrent Immix`.
- **Compile-time reference counting and reuse**:
  - `leanprover/lean4` (`8009d0a64d2860606c6a5ac5ff6702622b24921e`) — modern **LCNF impure-phase pipeline** (`src/Lean/Compiler/LCNF/{Passes,ResetReuse,InferBorrow,ExplicitRC,ExpandResetReuse,CoalesceRC}.lean`), C runtime (`src/include/lean/lean.h`), and in-tree formal RC model (`tests/verif/Verif/runtime/RC.lean`), superseding the earlier `IR/RC.lean` paths in `Ullrich & de Moura (IFL 2019)`.
  - `koka-lang/koka` (`facb7932ce6871fdb063f762a304bd8238f35fba`) — Perceus (`src/Backend/C/{Parc,ParcReuse,ParcReuseSpec}.hs`, `src/Core/Borrowed.hs`), corresponding to `Reinking et al. (PLDI 2021)`, contrasted with cyclic trial deletion (`Bacon & Rajan ECOOP 2001`).
- **Adjacent corpus cross-references**: Mechanized GC verification here complements—without duplicating—`pcc-tal-verve-foundational-certificate-kernels-1996-2016` (Verve's TAL/Boogie OS nucleus integrating Hawblitzel & Petrank's verified collector) and `compiler-correctness-theorem-shapes-and-end-to-end-chains` (CompCert/CompCertTSO and CakeML end-to-end simulation theorems).
- **Executable probe scope**: `support/verify_gc_tricolor_and_derived_roots.py` (Python 3.10+, stdlib-only) checks bounded finite-state models of the invariants analyzed below; it establishes exact counterexamples and exhaustive small-state safety for those models rather than full machine-code equivalence for upstream runtimes.

## Findings

### 1. Precise Stack Maps, Derived Interior/Exterior Pointers, and LLVM Statepoints

Basis: normative (LLVM IR statepoint contract) + documentation (`llvm/docs/Statepoints.md`, `GarbageCollection.md`, `StackMaps.md`, Diwan, Moss & Hudson PLDI 1992) + source (`llvm/lib/Transforms/Scalar/RewriteStatepointsForGC.cpp`) + execution (`support/verify_gc_tricolor_and_derived_roots.py`) + derived

#### 1.1 Conservative Scanning vs. Precise Moving Collection

Conservative collectors scan stack slots and registers for values falling inside heap address bounds and pin ambiguous targets, precluding object relocation because an integer masquerading as a pointer cannot safely be rewritten. A **precise moving collector** relocates live objects and therefore requires compiled code at every **safepoint** to guarantee (`llvm/docs/Statepoints.md:75-83, 474-500`):

1. Every live copy of a GC reference in registers or stack slots—including copies created by CSE, register allocation, or spilling—is listed in the stack map.
2. Each live pointer is associated with the allocation (base object) it belongs to.
3. Every copy can be updated after relocation, and no static path uses an unrelocated pre-safepoint SSA value observably after the safepoint.

#### 1.2 The Derived Interior and Exterior Pointer Hazard

Scalar optimizations (loop strength reduction, GEP reassociation, induction-variable canonicalization, struct-field CSE) rewrite `base[i]` into a derived pointer `p = base + offset` and eliminate subsequent uses of `base`. As formalized by Diwan, Moss, and Hudson (`PLDI 1992`, DOI `10.1145/143095.143140`, targeting GCC/Modula-3) and `llvm/docs/Statepoints.md:34-43, 297-323`, this creates two distinct moving-GC failure modes:

- **Dropped base on an interior derived pointer**: Standard liveness sees `base` as dead across a loop safepoint when only `derived = base + 16` is live afterward. If the collector requires base roots and the stack map omits `base`, the object is either left un-evacuated (dangling read) or relocated without updating `derived`.
- **Exterior derived pointers colliding with adjacent objects**: Loop strength reduction routinely creates out-of-bounds addresses—such as a one-past-end sentinel `p = arrA + len(arrA)` or a negative-biased base `p = arrA - 8` for 1-based indexing. At a safepoint, `derived` lies *outside* `arrA` and can fall directly inside adjacent live object `arrB`. Runtime address-range lookup (`find_base_by_address(derived)`) mis-attributes `derived` to `arrB` and shifts it by `arrB`'s relocation delta instead of `arrA`'s, silently corrupting subsequent dereferences.

Diwan, Moss, and Hudson's compiler rule—adopted by LLVM statepoints—treats every use of a derived pointer as a simultaneous use of its base pointer(s), pinning `(base, derived)` pairs live across safepoints so the runtime saves `offset = derived - base` pre-relocation and writes back `derived' = base' + offset` afterward.

Running `support/verify_gc_tricolor_and_derived_roots.py` (`verify_derived_pointer_relocation`) confirms all three cases on a two-space copying heap:
- Dropping `base` for `arrA + 16` yields a dangling read (`None`) after copying.
- A 1-past-end exterior pointer `arrA + 16` collides with adjacent `arrB`, causing address-range lookup to mis-attribute it to `arrB` and corrupt `*(derived - 8)` when `arrB` and `arrA` move to non-adjacent to-space addresses.
- Explicit `(base, derived)` statepoint pairs reconstruct both interior and exterior pointers (`('arrA', 200)`) identically regardless of evacuation order.

#### 1.3 LLVM Non-Integral Pointers and `RewriteStatepointsForGC`

LLVM splits mid-level optimization from explicit relocation (`llvm/docs/Statepoints.md:88-245, 513-635`):

1. **Abstract machine model**: Managed references use a **non-integral pointer address space** (`ptr addrspace(1)` in built-in `"statepoint-example"` and `"coreclr"` strategies, `Statepoints.md:547-553`). Having no defined pointer-to-integer bit mapping lets the runtime change addresses at safepoints without invalidating mid-level optimizations.
2. **Explicit relocation lowering (`RewriteStatepointsForGC`)**: Run late after `mem2ref` and scalar optimizations, `RS4GC` wraps every potentially safepointing call/invoke in a `token`-returning `llvm.experimental.gc.statepoint` carrying live references in its `"gc-live"` operand bundle, paired with `llvm.experimental.gc.result` and `llvm.experimental.gc.relocate(token, base_idx, derived_idx)` (`Statepoints.md:176-183, 539-545`).

Inspection of `RewriteStatepointsForGC.cpp` (`4d369315...`) shows four key mechanisms:
- **Optimistic `BDVState` PHI lattice (`RewriteStatepointsForGC.cpp:319-435, 679-809`)**: `findBaseDefiningValue` walks back through `GEP`, `FreezeInst`, and vector `BitCastInst` (treating heap loads, globals, arguments, call returns, and `null` as base pointers). Across `PHI`/`Select` merges, `findBasePointer` iterates over `BDVState::StatusTy = { Unknown, Base, Conflict }` and synthesizes parallel **base PHI nodes** for every `Conflict` merge so the base pointer remains live at downstream safepoints.
- **Derived-pointer rematerialization (`RewriteStatepointsForGC.cpp:190-198, 2221-2335`)**: `findRematerializableChainToBasePointer` and `chainToBasePointerCost` avoid spilling short `GEP` + no-op `CastInst` chains (`<= ChainLengthThreshold`), cloning the offset arithmetic after relocating the base alone.
- **GC-parseable atomic `memcpy`/`memmove` (`Statepoints.md:592-635`)**: Unless annotated `"gc-leaf-function"`, `RS4GC` lowers `llvm.memcpy.element.unordered.atomic.*` / `memmove` to safepoint-capable runtime calls (`__llvm_memcpy_element_unordered_atomic_safepoint_*`) with derived pointers split into `(dest_base, dest_offset, src_base, src_offset, length)`.
- **StackMap v3 vs. legacy `shadow-stack` (`Statepoints.md:411-470`, `GarbageCollection.md:380-396`)**: Statepoints emit two-location `(base_loc, derived_loc)` records in the StackMap section (`StackMaps.md`), superseding LLVM's portable but high-overhead, **non-thread-safe** `"shadow-stack"` `gcroot` linked list.

#### 1.4 Documented Upstream Holes in LLVM Statepoints

| Hazard / Limitation | Upstream Location (`4d369315...`) | Consequence |
| :--- | :--- | :--- |
| **Non-integral load speculation hole** | `Statepoints.md:109-115` | `ValueTracking.cpp` (`isSafeToSpeculate`) can unsoundly speculate loads changing memory type between non-integral GC pointer and non-pointer; requires a local workaround. |
| **No relocation-invariant verifier** | `Statepoints.md:502-507` | LLVM's IR `Verifier` checks local intrinsic syntax but does *not* check that unrelocated pointers are unreachable after a statepoint. |
| **`ptrtoint` / `inttoptr` breaks base inference** | `Statepoints.md:708-719` | Integer round-trips defeat `RS4GC` base tracking; mixed raw/managed code requires opaque intrinsics or explicit lowering. |
| **Exceptional-edge relocations broken** | `Statepoints.md:745-750` | Relocating live GC pointers across exception `rethrow` edges is documented as broken in upstream ToT. |
| **Narrow backend & `alloca` support** | `Statepoints.md:292-295, 699-702` | Only `X86_64` and `AArch64` support statepoint lowering; `RS4GC` does not rewrite stack `alloca`s in `"gc-live"`. |

---

### 2. Safepoint Polling Mechanisms, Counted-Loop Elision, and Time-To-Safepoint (TTSP)

Basis: source (`openjdk/jdk` `safepointMechanism.hpp/.inline.hpp`, `loopnode.cpp`; `golang/go` `preempt.go`; `llvm/llvm-project` `PlaceSafepoints.cpp`; `mmtk/mmtk-core` `collection.rs`) + documentation (`Go Proposal 24543`) + derived

Any stop-the-world phase or per-thread handshake must wait for mutators to reach a safepoint; the delay until the slowest mutator halts is **Time-To-Safepoint (TTSP)**. Because a backedge safepoint acts as an opaque call inhibiting vectorization and unrolling, HotSpot C2 historically removed safepoints from `int`-counted loops (`_iv_bt == T_INT`, up to $2^{31}$ iterations, while keeping them in `T_LONG` loops), and cooperative Go (pre-1.14) polled only at function prologues (overloading stack-bound checks, `preempt.go:27-33`), letting tight call-free loops stall global GC pauses indefinitely.

#### 2.1 Production Safepoint & Preemption Mechanisms Compared

| Runtime | Poll Mechanism | Loop / TTSP Bounding Strategy | Stack-Map Precision | Notable Edge Cases |
| :--- | :--- | :--- | :--- | :--- |
| **OpenJDK HotSpot** (`4f332731...`) | **Thread-local polling** (`SafepointMechanism::ThreadData { _polling_word, _polling_page }`, `safepointMechanism.hpp:70-78`): trapping load from `_polling_page` (`PROT_NONE` when armed); `_polling_word` carries `_poll_bit = 1` + JEP 376 `StackWatermark`. | **C2 counted-loop strip mining** (`loopnode.cpp:3524-3531, 3715-3720, 4518-4560, 5751-5757`): splits `T_INT` `CountedLoop` into an unpolled inner loop capped at `LoopStripMiningIter` iterations inside an `OuterStripMinedLoop` carrying one cloned `SafePointNode`; drops outer loop if `iter_estimate <= LoopStripMiningIterShortLoop * ABS(stride)`. | Precise OOP maps at every safepoint and deopt site. | `AtomicAccess::load_acquire(&_polling_word)` orders poll-page reads before handshake state (`safepointMechanism.inline.hpp:51-55`). |
| **Go** (`b496a304...`) | Synchronous stack-bound poisoning in prologues (`preempt.go:27-33`) + OS-signal (`SIGURG`) **asynchronous preemption** (`preempt.go:35-51`, rewriting signal context to call `asyncPreempt`). | Signals interrupt tight call-free loops asynchronously without emitting backedge polls. | Precise at blocked/sync safepoints; **conservative stack & register scan** at async points (`preempt.go:16-25`). | `isAsyncSafePoint` (`preempt.go:442-549`) rejects `PCDATA_UnsafePoint == UnsafePointUnsafe` (write barriers, `nosplit`), assembly lacking `FUNCDATA_LocalsPointerMaps`, `runtime.`/`internal/runtime/`/`reflect.`, and **`goexperiment.RuntimeSecret && gp.secret > 0`** (preventing conservative scanning / spill buffers from leaking secrets, `preempt.go:462-476`). Supports `UnsafePointRestart1/2/AtEntry`. |
| **LLVM `PlaceSafepoints`** (`4d369315...`) | Inlines module-defined `gc.safepoint_poll()` at entry and loop backedges (`Statepoints.md:653-689`). | Elides backedge polls when `containsUnconditionalCallSafepoint` holds or `ScalarEvolution` proves `FiniteExecution` (`PlaceSafepoints.cpp:79-82, 147-158`). | Precise after `RS4GC`. | Does not bound TTSP under heavy paging (`Statepoints.md:682-683`). |
| **MMTk** (`d154f4f0...`) | VM-owned via `Collection::stop_all_mutators` / `block_for_gc` (`src/vm/collection.rs:15-45`). | Owned by host VM; MMTk assumes pause holds once `stop_all_mutators` returns. | VM-owned (`Scanning`). | `Collection::out_of_memory` (`collection.rs:75-117`) warns against unwinding exceptions across Rust/C/C++ ABI boundaries, recommending `Address::ZERO`. |

#### 2.2 Guard-Page Traps vs. Conditional Branch Polls

Thread-local guard-page polls execute a single non-branching memory load in the disarmed common case (zero branch-predictor pressure) and trigger a `SIGSEGV` trap only when armed, enabling per-thread handshakes without stopping unrelated threads (unlike legacy global polling pages). Branch polls (`if (unlikely(*flag)) slow_path()`) avoid signal-handler overhead at the cost of a branch instruction per poll site. HotSpot combines both: JIT loops issue a trapping load against `ThreadData::_polling_page`, while runtime transitions and returns check `_polling_word` (simultaneously driving JEP 376 stack watermarks).

---

### 3. Tri-Color Marking Invariants, Write Barriers, and Weak-Memory Ordering

Basis: normative (Wilson 1992, Dijkstra et al. 1978, Yuasa 1990) + source (`golang/go` `mgc.go`, `mbarrier.go`, `mwbbuf.go`; `openjdk/jdk` `g1BarrierSet.inline.hpp`; `ocaml/ocaml` `memory.c`, `major_gc.c`, `minor_gc.c`, `shared_heap.c`, `caml/major_gc.h`) + execution (`support/verify_gc_tricolor_and_derived_roots.py`) + derived

#### 3.1 Wilson's Lost-Object Conditions and Single-Sided Barriers

In the tri-color abstraction (`Dijkstra et al. 1978`, DOI `10.1145/359642.359655`; `Yuasa 1990`, DOI `10.1016/0164-1212(90)90084-Y`; `Wilson IWMM 1992`, DOI `10.1007/BFb0017182`), **white** objects are unvisited (reclaimable), **grey** objects are discovered with unscanned outgoing slots, and **black** objects are fully scanned. A concurrent mutator causes a **lost live object** (sweeping reachable white $W$) iff both hold:
1. The mutator installs a pointer to white $W$ inside a black object $B$; **and**
2. All remaining paths from grey objects to $W$ are destroyed before traversal.

Negating (1) yields **Dijkstra's strong tri-color invariant** (insertion barrier `shade(new_ptr)` on `*slot = new_ptr`: no black→white edges). Negating (2) yields **Yuasa's weak tri-color / SATB invariant** (deletion barrier `shade(*slot)` on overwrite, with black allocation during mark: every white object live at the initial snapshot stays reachable from grey).

#### 3.2 Un-Barriered Stacks and Go's Hybrid Write Barrier

Compiled runtimes omit write barriers on current-frame stack writes (`golang/go` `src/runtime/mbarrier.go:96-101`). When stacks are scanned **concurrently** (one goroutine at a time rather than in one atomic STW root snapshot) with **no final STW stack re-scan**, *both* single-sided barriers lose reachable objects:

1. **Pure Dijkstra (`shade(new)`) without stack re-scan fails**: Already-scanned (black) stack $S_1$ loads white $C$ from grey heap slot $B.f$ into a register (no barrier), then writes $B.f = \text{nil}$ (Dijkstra shades `new = nil`, ignoring `old = C`). GC blackens $B$ without seeing $C$; since $S_1$ is never rescanned, sweep frees live $C$.
2. **Pure Yuasa (`shade(old)`) without STW stack snapshot fails**: Unscanned (grey) stack $S_1$ holding the sole reference to white $C$ writes $C$ into black heap slot $A.f$ (overwriting `nil`; Yuasa shades `old = nil`, ignoring `new = C`), then clears $C$ from $S_1$ (no barrier). When GC later scans $S_1$, $C$ is absent; sweep frees live $C$ even though $A.f \to C$.

Go (`src/runtime/mbarrier.go:24-64`, `mgc.go:24-82`, Proposal `17503`) eliminates STW stack re-scanning via its **hybrid write barrier**:

```text
writePointer(slot, ptr):
    shade(*slot)            // Yuasa: prevents hiding heap -> black-stack moves
    if current stack is grey:
        shade(ptr)          // Dijkstra: prevents hiding grey-stack -> black-heap moves
    *slot = ptr
```

Go's concrete assembly barrier (`gcWriteBarrier`, backed by per-P 512-entry `wbBuf` buffers in `mwbbuf.go:35-160`) omits the stack-color branch and unconditionally enqueues both `old` and `new` whenever `writeBarrier.enabled` is set (`mgc.go:239-243`), covers **global variable** stores (`mbarrier.go:104-111`) to avoid global re-scans, and annotates `wbBuf.get1/get2`/`wbBufFlush` with `//go:nowritebarrierrec` and `//go:nosplit` (`mwbbuf.go:117-160`) so no preemption or GC phase change can occur between buffering and writing memory.

**Exhaustive BFS verification (`support/verify_gc_tricolor_and_derived_roots.py`, Section 1)** over a 3-object heap and 2 un-barriered concurrent stacks (scanned once, never rescanned):

| Barrier Mode | Stack Snapshot | States Explored | Lost Object? | Witness / Result |
| :--- | :--- | ---: | :--- | :--- |
| None | Concurrent | 5,248 | **YES** (7 steps) | `S1` writes `C` to black `A.f`, clears `S1.r1` |
| Pure Dijkstra (`shade(new)`) | Concurrent | 9,514 | **YES** (8 steps) | Black `S1` loads `C` from grey `B.f`, clears `B.f = None` → `C` lost |
| Pure Yuasa (`shade(old)`) | Concurrent | 7,886 | **YES** (7 steps) | Grey `S1` stores `C` into black `A.f`, clears `S1.r1` → `C` lost |
| **Go hybrid (grey-stack conditional)** | Concurrent | **38,010** | **NO (0)** | Exhaustively verified complete without stack rescan |
| **Go hybrid (unconditional `old`+`new`)** | Concurrent | **37,730** | **NO (0)** | Exhaustively verified complete without stack rescan |
| **Pure Yuasa SATB** | **Atomic STW** | **8,228** | **NO (0)** | Sound with STW initial root scan (G1 / OCaml 5) |

#### 3.3 The x86-TSO Dekker Store-Buffer Hazard on Conditional Barriers

Gating insertion shading on whether the containing object is already black (`if is_black(obj): shade(ptr)`) is **unsound on x86-TSO without `MFENCE`** (`golang/go` `src/runtime/mbarrier.go:68-93`):

```text
Initially: [slot] = 0 (nil), [slotmark] = 0
Mutator (Core 0): st [slot], ptr;  ld r1, [slotmark]
GC worker (Core 1): st [slotmark], 1;  ld r2, [slot]
```

Because x86-TSO allows loads to bypass older buffered stores to distinct addresses, both cores can observe `r1 == 0 && r2 == 0`: the mutator skips shading while the GC misses `ptr` and blackens the object. Probe Section 2 exhaustively simulates per-core FIFO store buffers and confirms `(0, 0)` is reachable without `MFENCE` (`[(0,0), (0,1), (1,0), (1,1)]`) and eliminated with `MFENCE` (`[(0,1), (1,0), (1,1)]`). Go avoids per-store fences by shading unconditionally regardless of the parent slot's color.

#### 3.4 OpenJDK G1 and OCaml 5 Multicore SATB + Generational Barriers

- **OpenJDK G1 (`src/hotspot/share/gc/g1/g1BarrierSet.inline.hpp:38-155`)**: Pairs a **pre-write SATB barrier** (`write_ref_field_pre`, enqueuing non-null `old` into thread-local `SATBMarkQueue` when active, skipped for `IS_DEST_UNINITIALIZED`/`AS_NO_KEEPALIVE`, and also applied to non-heap stores `oop_store_not_in_heap`) with a **post-write card-table barrier** (`write_ref_field_post`, reading `card_table()` once into a local and dirtying clean cards) plus a **weak/phantom load keep-alive barrier** (`enqueue_preloaded_if_weak`, lines 83–95) so loading a weak referent during concurrent marking preserves the SATB snapshot.
- **OCaml 5 Multicore GC (`Sivaramakrishnan et al. ICFP 2020`, DOI `10.1145/3408995`; `ocaml/ocaml` `d921d1e8...`)**:
  - **STW parallel minor evacuation (`runtime/minor_gc.c:188-285`)**: Per-domain bump-allocated minor heaps evacuate in parallel during brief STW minor pauses. Racing domains resolve object promotion via `try_update_object_header` (`minor_gc.c:188-228`): atomic CAS of header to `In_progress_hd`, relaxed store of forwarding pointer, and `atomic_store_release` of `Promoted_hd` (losers spin until `Promoted_hd` appears).
  - **Concurrent major mark-and-sweep (`runtime/shared_heap.c:41-100`, `runtime/major_gc.c`, `runtime/caml/major_gc.h:23-36`)**: Domain-local size-segregated `struct pool` slabs (`NUM_SIZECLASSES`, `struct caml_heap_state`) avoid global allocator locks. Cyclic 3-color header encoding (`MARKED`/`UNMARKED`/`GARBAGE` in `caml_global_heap_state`) overlaps sweeping with marking across four phases (`Phase_sweep_main`, `Phase_sweep_and_mark_main`, `Phase_mark_final`, `Phase_sweep_ephe`), anchored by STW root scanning (`caml_mark_roots_stw`, `major_gc.c:1832-1848`).
  - **Combined SATB + generational barrier (`runtime/memory.c:306-354`)**: On `!Is_young(obj)`, `write_barrier` returns early if `Is_young(old_val)` (already remembered), calls `caml_darken(Caml_state, old_val, 0)` if `caml_marking_started()` (**Yuasa SATB**), records `Op_val(obj) + field` into `minor_tables->major_ref` if `Is_block_and_young(new_val)` (**generational**), and `caml_modify` executes `atomic_thread_fence(memory_order_acquire)` before `atomic_store_release` of `val`.

---

### 4. Colored-Pointer Load Barriers, Self-Healing References, and VM-Binding Abstractions

Basis: source (`openjdk/jdk` `zAddress.hpp`, `zBarrier.hpp`, `zBarrier.inline.hpp`, `zStoreBarrierBuffer.hpp`; `mmtk/mmtk-core` `vm/mod.rs`, `vm/scanning.rs`, `vm/slot.rs`, `plan/barriers.rs`, `plan/plan_constraints.rs`, `plan/lxr/global.rs`, `plan/concurrent/immix/global.rs`) + documentation (`JEP 376`, `JEP 439`, `JEP 490`) + execution (`support/verify_gc_tricolor_and_derived_roots.py`) + derived

#### 4.1 OpenJDK Generational ZGC: 16-Bit Low-Order Colors, Shift Load Barriers, and Self-Healing

Post-JEP 439/490 OpenJDK ZGC (`4f332731...`) drops legacy JEP 333 high-bit multi-mapping and encodes **16 low-order metadata bits** in every heap `zpointer` (`src/hotspot/share/gc/z/zAddress.hpp:48-196, 246-254`), strictly typing colored `zpointer` values separately from dereferenceable uncolored `zaddress` values:

```text
zpointer low 16 metadata bits (zAddress.hpp:53-73):
  bits [15:12] RRRR : Remapped[00, 01, 10, 11] — load barrier (one-hot intersection of RemappedOldMask & RemappedYoungMask)
  bits [11:10] MM   : MarkedOld[0, 1]          — mark & store barriers
  bits [ 9: 8] mm   : MarkedYoung[0, 1]        — mark & store barriers
  bits [ 7: 6] FF   : Finalizable[0, 1]        — mark & store barriers
  bits [ 5: 4] rr   : Remembered[0, 1]         — store barrier
  bits [ 3: 0] 0000 : Reserved
```

- **Single-instruction speculative x86-64 shift load barrier (`zAddress.hpp:75-129`, `zBarrier.hpp:31-68`)**: On x86-64, address bits start immediately above the active `Remapped` good bit (overlapping high zero remap bits with low zero alignment bits). Compiled `nmethod` load barriers execute one right-shift by the phase's good shift (patched via **nmethod entry barriers**): `null` sets `ZF = 1`, a good pointer shifts out its active `1` bit into `CF = 1` while yielding the exact uncolored `zaddress`, and the slow path runs iff **`CF == 0 && ZF == 0`** (`ja`). Because this scheme only supports 4 single-bit patterns without shifting into non-zero address bits above 8-byte alignment, non-relocation marking and remembered-set tracking move to **store barriers** (`zBarrier.hpp:55-62`). Probe Section 4 exhaustively verifies all 4 phases and all 12 cross-phase stale-pointer traps.
- **Monotonic CAS self-healing & `ZStoreBarrierBuffer` (`zBarrier.inline.hpp:41-108`, `zStoreBarrierBuffer.hpp:33-96`)**: `ZBarrier::self_heal` upgrades stale heap slots via a `memory_order_relaxed` `AtomicAccess::cmpxchg` loop enforcing strict `assert_transition_monotonicity` (metadata bits never regress within a phase), so future loads hit the fast path. `ZStoreBarrierBuffer` batches up to 32 `(_p, _prev)` entries per thread for deferred SATB marking, relocation, and generational remembered-set updates.

#### 4.2 MMTk VM-Binding Abstraction and Compiler–Barrier Coupling

`mmtk/mmtk-core` (`d154f4f0...`) defines the VM–GC boundary via `VMBinding` (`src/vm/mod.rs:57-93`: `VMObjectModel`, `VMScanning`, `VMCollection`, `VMActivePlan`, `VMReferenceGlue`, `VMSlot`, `VMMemorySlice`, inlined via cross-crate LTO) and plan-exported `PlanConstraints` (`src/plan/plan_constraints.rs:10-85`):
- **Barrier selection**: `BarrierSelector::{NoBarrier, ObjectBarrier, FieldBarrier, SATBBarrier}` (`barriers.rs:18-29`); e.g., `CONCURRENT_IMMIX_CONSTRAINTS` (`plan/concurrent/immix/global.rs:59-66`) uses `SATBBarrier` + `needs_log_bit`, while `LXR_CONSTRAINTS` (`plan/lxr/global.rs:85-92`) uses `FieldBarrier` + `rc_enabled` + `needs_field_log_bit`.
- **Tagged-slot & duplicate-scan invariants**: `Slot::load`/`store` (`src/vm/slot.rs:108-146`) must preserve tag bits under benign idempotent duplicate-edge races (flagging FIXME #1033/#1038 where moving-GC forwarding updates and mutator write barriers diverge for tagged/offsetted refs), and `Scanning::UNIQUE_OBJECT_ENQUEUING` (`src/vm/scanning.rs:170-185`, default `false`) documents whether VMs tolerate concurrent duplicate object scans.
- **Deoptimization-vs-write-barrier-elision hazard (`Barrier::object_probable_write`, `barriers.rs:120-136`)**: Compilers elide generational write barriers on newly allocated nursery objects, but HotSpot C2 slowpath allocation can **deoptimize** (hitting a safepoint) before compiled field initialization runs; a generational GC at that safepoint can promote the object to old space, causing unbarriered initializing stores to vanish from the remembered set unless preceded by `object_probable_write(obj)` with no intervening safepoints.

#### 4.3 Cross-Runtime Comparative Matrix

| System | Moving? | Gen? | Concurrent Phases | Write Barrier | Load Barrier | Root Scanning / Rescan |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Go** (`b496a304...`) | No (`heapObjectsCanMove()==false`) | No | Mark & sweep | Hybrid Yuasa+Dijkstra (`wbBuf`, unconditional `old`+`new`, globals; no stack barriers) | None | Per-G concurrent stack scan; **no** STW rescan; conservative async scan |
| **OpenJDK G1** (`4f332731...`) | Yes (region evac) | Yes | Old marking | Pre-write SATB (`SATBMarkQueue`) + post-write card table | Weak/phantom keep-alive only | STW initial-mark snapshot; thread-local poll + C2 strip mining |
| **OpenJDK Gen ZGC** (`4f332731...`) | Yes (concurrent) | Yes | Mark, relocate, remap, stack proc (JEP 376) | Store barrier + 32-entry `ZStoreBarrierBuffer` | Speculative x86 shift (`RRRR`) + CAS `self_heal` | Concurrent `StackWatermark` + nmethod entry barriers |
| **OCaml 5** (`d921d1e8...`) | Minor: STW copy; Major: pools | Yes | Major mark & sweep (3-color rotate) | `caml_modify`: SATB `caml_darken(old)` + `major_ref` + acq fence / rel store | None | STW minor & STW major root mark (`caml_mark_roots_stw`); C shadow roots |
| **MMTk ConcImmix / LXR** (`d154f4f0...`) | Configurable | LXR: Yes | Mark (Immix); RC+evac (LXR) | `SATBBarrier` or `FieldBarrier` | Weak-ref load barrier | VM-owned (`Collection` + `Scanning`) |
| **LLVM Statepoints** (`4d369315...`) | Yes | Agnostic | Agnostic | Frontend-emitted | Frontend-emitted | `(base, derived)` StackMap v3 pairs via `RS4GC` |

---

### 5. Compiler Optimizations and FFI Boundaries That Corrupt GC Invariants

Basis: source (`llvm/docs/Statepoints.md`; `mmtk/mmtk-core` `barriers.rs`; `ocaml/ocaml` `memory.c`, `caml/memory.h`; `golang/go` `mbarrier.go`, `mwbbuf.go`, `pinner.go`) + documentation (`Diwan, Moss & Hudson 1992`) + derived

| Optimization or FFI Pattern | Violated Invariant | Failure Mode | Primary-Source Mitigation |
| :--- | :--- | :--- | :--- |
| **LSR / GEP dropping `base`** | Moving-GC base attribution | Interior/exterior derived pointer loses base or collides with adjacent object. | Non-integral `addrspace(1)` + `RS4GC` `(base, derived)` pairs (`Statepoints.md:297-323`). |
| **Speculative type-changing load** | Non-integral reference opacity | Reads GC ref as raw integer (or vice versa), forging/losing roots. | Restrict `isSafeToSpeculate` (`Statepoints.md:109-115`). |
| **Write-barrier elision across alloc slowpath/deopt** | Generational remembered set | Object promoted during deopt safepoint misses old→young init edges. | `Barrier::object_probable_write` + no-safepoint span (`mmtk/barriers.rs:120-136`). |
| **Preemption inside write barrier** | GC phase & per-P buffer ownership | Preemption between `wbBuf` reserve and store crosses phase change or migrates P. | `//go:nosplit`, `//go:nowritebarrierrec`, `PCDATA_UnsafePoint` (`mwbbuf.go:117-160`, `preempt.go:495-501`). |
| **Counted-loop poll elision** | Bounded TTSP liveness | Multi-second STW stall waiting on `int` loop. | C2 `OuterStripMinedLoop` (`loopnode.cpp:4518-4560`) or Go async preemption (`preempt.go:35-51`). |
| **Raw FFI pointers across moving GC** | Root tracking & relocation | Foreign frame holds stale address after allocating callback moves object. | OCaml `CAMLparam*`/`CAMLlocal*` (`caml/memory.h:290-317`); JNI handles; `NoGC` regions. |
| **Unbarriered FFI heap access (`memcpy` / `*fp = v`)** | SATB, remset, colored pointers | Skips `caml_modify` / G1 SATB / Go `typedmemmove` or dereferences raw ZGC `zpointer`. | Mandatory barrier helpers (`caml_modify`, `typedmemmove`); note OCaml `memory.c:280-304` lacks a formal OCaml/C memory model. |
| **Transitive Go pointers in C / shallow `runtime.Pinner`** | Reachability across un-scanned C heap | `runtime.Pinner.Pin` (`pinner.go:38-41`, per-`mspan` `_KindSpecialPinCounter` at `pinner.go:377-436`) is **shallow**: nested Go pointers are not pinned; forgetting `Unpin()` triggers `pinnerLeakPanic()` on finalization (`pinner.go:73, 444-446`). | Pin every transitively accessed Go object individually or use `runtime/cgo.Handle`. |
| **Cross-heap cycles across independent GCs** | Global reachability | Mutual foreign handles act as permanent strong roots on both sides, leaking cycles. | Unified coordinated marking or statically enforced acyclic cross-heap ownership (see `## Boundaries`). |

---

### 6. Compile-Time Reference Counting, Functional In-Place Reuse, and Cycle Collection

Basis: source (`leanprover/lean4` `src/Lean/Compiler/LCNF/{Passes,ResetReuse,InferBorrow,ExplicitRC,ExpandResetReuse}.lean`, `src/include/lean/lean.h`, `tests/verif/Verif/runtime/RC.lean`; `koka-lang/koka` `src/Backend/C/{Parc,ParcReuse,ParcReuseSpec}.hs`) + documentation (`Ullrich & de Moura IFL 2019`; `Reinking et al. PLDI 2021`; `Bacon & Rajan ECOOP 2001`) + execution (`support/verify_gc_tricolor_and_derived_roots.py`) + derived

#### 6.1 Lean 4 LCNF Impure-Phase Reference Counting & Reset-Reuse

At pinned commit `8009d0a6...`, Lean 4 no longer keeps RC passes under `src/Lean/Compiler/IR/RC.lean`; instead, the **LCNF impure phase** (`src/Lean/Compiler/LCNF/Passes.lean:144-159`) runs: `pushProj` → `insertResetReuse` → `elimDeadVars` → `simpCase` → `inferBorrow` → `explicitBoxing` → `explicitRc` → `expandResetReuse` → `coalesceRC`.

Four compiler invariants couple these passes:
1. **`insertResetReuse` (`LCNF/ResetReuse.lean:18-126`)**: Implements `R`/`D`/`S` from *Counting Immutable Beans* (`Ullrich & de Moura IFL 2019`, DOI `10.1145/3412932.3412935`, `arXiv:1908.05647`). When matched constructor `x` dies before a layout-compatible allocation (`mayReuse`: equal `size`, `usize`, `ssize`; first with `relaxedReuse := false` requiring matching type prefix, then `true`, lines 59–76), emits `reset`/`reuse` while tracking `alreadyFound` to prevent double resets (`lines 40-58`).
2. **`inferBorrow` (`LCNF/InferBorrow.lean:19-49, 104-112`)**: Starts non-exported reference parameters as borrowed and refines to owned for two *correctness* requirements—preserving tail calls (no post-tail-call `dec`) and guaranteeing `reset` targets are owned for exact runtime RC—plus performance heuristics (constructor args, partial applications) overridable by user borrow annotations.
3. **`explicitRc` (`LCNF/ExplicitRC.lean:14-180`)**: Separates killable `LiveVars.vars` from `LiveVars.borrows` and propagates **derived borrows** through projections (`DerivedValMap`), while `collectResetTargets` (`lines 33-50, 115-121, 176-180`) **forbids** treating any `reset` target as a derived borrow so in-place reuse cannot mutate a borrowed parent's field.
4. **`expandResetReuse` (`LCNF/ExpandResetReuse.lean:12-180`)**: Splits `reset`/`reuse` into `resetjp`/`reusejp` hot (`isShared == false`) and cold paths. On the hot path, `eraseProjIncFor` (`lines 71-123`) drops redundant `inc`s on projections (guarding duplicate field projections with a per-field `Mask`), and `partitionSelfSets` (`lines 140-180`) elides self-stores writing back an unchanged projected field.

#### 6.2 Lean 4 Signed 32-Bit Runtime RC and Mechanized Overflow Safety

In `src/include/lean/lean.h:416-420, 630-790`, each `lean_object`'s 32-bit `m_rc` encodes four regimes, verified directly against an unbounded `Nat` model in `tests/verif/Verif/runtime/RC.lean:1-45`:

| `m_rc` Regime | Meaning | Fast-Path Update | Exclusive (`lean_is_exclusive`) |
| :--- | :--- | :--- | :--- |
| `m_rc > 0` | Single-threaded (ST) | Non-atomic unsigned add (`(int)((unsigned)m_rc + (unsigned)add)`) / sub | `true` iff `m_rc == 1` (`lean.h:783-789`) |
| `m_rc == 0` | Persistent / compact region | No-op (`lean_is_persistent`) | `false` |
| `LEAN_RC_STICKY < m_rc < 0` | Multi-threaded (MT), negated | `atomic_fetch_sub_explicit(..., relaxed)` for inc (`lean.h:724-730`) | `false` |
| `<= LEAN_RC_STICKY_DROP` / `LEAN_RC_STICKY` | Saturated (`INT_MIN + 0x20000000` / `+ 0x10000000`, inline cap `LEAN_RC_INC_MAX = 0x10000`) | Drops freeze at `LEAN_RC_STICKY_DROP`; incs freeze at `LEAN_RC_STICKY` (`lean.h:670-709`) | `false` — safely leaks rather than wrapping to `0` (UAF) |

`tests/verif/Verif/runtime/RC.lean` proves `run_spec` (including fractured concurrent interleavings between threshold check and atomic RMW). Probe Section 5 verifies that overflowing `0x7FFFFFFF + 1` lands at `INT_MIN` (`<= LEAN_RC_STICKY_DROP` unsigned) and remains frozen across subsequent drops.

#### 6.3 Perceus (`Koka`) and Cycle Collection (`Bacon & Rajan 2001`)

`Reinking, Xie, de Moura & Leijen (PLDI 2021)` (DOI `10.1145/3453483.3454032`) formalize garbage-free RC with reuse in the linear resource calculus $\lambda^\circ$, implemented in Koka (`koka-lang/koka` `facb7932...`):
- `Backend/C/Parc.hs:10-21, 66-140` visits expression trees in reverse with borrowed/owned environments to emit prompt drops immediately at last use.
- `Backend/C/ParcReuse.hs` (`lines 77-125`) and `ParcReuseSpec.hs` (`parcReuseSpecialize`) pair drops with allocations via reuse tokens and drop specialization, rewriting only `nonMatching` fields.
- Probe Section 5 (`map_inc_fbip` on `[1, 2, 3]`) verifies **3 in-place reuses / 0 fresh allocations** with identical cell addresses when `rc == 1`, **3 fresh disjoint allocations** preserving the immutable alias `[2, 3, 4]` when `rc == 2`, and **0 live objects** after dropping both lists.
- **Cycles (`Bacon & Rajan ECOOP 2001`, DOI `10.1007/3-540-45337-7_12`)**: Strict purely functional DAGs never form cycles; general mutable RC graphs require local **trial deletion** (purple candidate roots → gray trial decrement → white garbage / black external-reference restoration, runnable concurrently) or hybrid RC+tracing (`MMTk LXR`, `plan/lxr/global.rs:85-92`).

---

### 7. Mechanized Verification of Garbage Collectors and Compiler–GC Interfaces

Basis: documentation (Hawblitzel & Petrank POPL 2009; McCreight et al. PLDI 2007, ICFP 2010; Sandberg Ericsson et al. JAR 2019; Gammie et al. PLDI 2015 / AFP `ConcurrentGC`) + source (`leanprover/lean4` `tests/verif/Verif/runtime/RC.lean`) + derived

Mechanized GC verification must establish heap-isomorphism/refinement between abstract mutator state and concrete word-addressed memory across safepoints, barriers, and weak memory. For OS-kernel integration and end-to-end compiler theorems, see `pcc-tal-verve-foundational-certificate-kernels-1996-2016` and `compiler-correctness-theorem-shapes-and-end-to-end-chains`.

| Effort & Venue | Tool | Collector & Memory Model | Compiler–GC Interface | Key Design Choice |
| :--- | :--- | :--- | :--- | :--- |
| **Hawblitzel & Petrank** (`POPL 2009`, DOI `10.1145/1480881.1480935`; LMCS 2010) | Boogie + Z3 | STW mark-sweep & Cheney copying; x86 asm (SC) | Verified x86 collector linked with Bartok/Verve TAL mutator (`pcc-tal-verve-foundational-certificate-kernels-1996-2016`) | Ghost reachability maps & bijection invariants discharged by SMT over raw byte arrays. |
| **McCreight et al.** (`PLDI 2007`, DOI `10.1145/1273442.1250788`) | Coq | STW & incremental/concurrent copying; SC | Abstract mutator/collector Hoare interface | Decouples mutator verification from collector implementation. |
| **McCreight, Chevalier & Tolmach (`GCminor`)** (`ICFP 2010`, DOI `10.1145/1863543.1863575`) | Coq (CompCert) | Copying GC; CompCert SC memory | **`GCminor` IR** extending `Cminor` with explicit GC alloc/rooting (lowered to shadow stacks) | Plugs into CompCert's simulation chain (`compiler-correctness-theorem-shapes-and-end-to-end-chains`). |
| **Sandberg Ericsson, Myreen & Åman Pohjola** (`ITP 2017` / `JAR 2019`, DOI `10.1007/s10817-018-9487-z`) | HOL4 | Generational copying GC; CakeML `wordLang`/`stackLang` (SC) | Integrated end-to-end in bootstrapped CakeML (`compiler-correctness-theorem-shapes-and-end-to-end-chains`) | Avoids general write-barrier/remembered-set proofs by segregating ML mutable refs/arrays into a region excluded from minor collection. |
| **Gammie, Hosking & Engelhardt** (`PLDI 2015`, DOI `10.1145/2737924.2738006`; AFP `ConcurrentGC`) | Isabelle/HOL (`CIMP`) | **Schism** on-the-fly concurrent mark-sweep; **x86-TSO** | Unbounded concurrent mutators + explicit TSO store buffers, handshakes (`ht-NOOP`, `ht-GetRoots`, `ht-GetWork`), phases (`ph-Idle/Init/Mark/Sweep`) | Proves non-interference and completeness directly over x86-TSO store buffers, validating exact `MFENCE`/CAS placement. |
| **Lean 4 Runtime RC** (`8009d0a6...`, `tests/verif/Verif/runtime/RC.lean`) | Lean 4 (`Std.Do`, `bv_decide`) | 32-bit ST/MT/persistent/sticky RC (`lean.h`) | Synchronized via `// sync with` comments to C inline `lean_inc_ref_n`/`lean_dec_ref` | Proves `run_spec` refinement against ideal `Nat` RC including fractured concurrent RMW interleavings. |

**Open synthesis gap**: No single mechanized end-to-end toolchain currently verifies all three simultaneously: (a) aggressive scalar optimizations producing exterior derived pointers with checked stack maps, (b) concurrent relocating load/store barriers, and (c) relaxed hardware memory models (x86-TSO / ARMv8 / RISC-V).

## Boundaries

- **not examined**: Source implementations of V8 + Blink Oilpan (`CppHeap`), OpenJDK Shenandoah, Azul C4/Falcon, GHC RTS, Cranelift user stack maps, WasmGC engines, and Boehm conservative GC; hardware memory models weaker than x86-TSO (AArch64/RISC-V barrier instruction encodings in ZGC, Go, and OCaml 5); throughput/pause-time benchmarks; and historical GC miscompile bug censuses in HotSpot C2, Go SSA, or V8.
- **unknown**: Whether any mechanized proof (Iris/Isabelle/Coq) verifies end-to-end soundness and liveness of a unified multi-collector tracing protocol bridging two independent heaps (e.g., V8 + Oilpan); exact external production adoption and defect rates of LLVM `gc.statepoint` beyond its built-in `"statepoint-example"` and `"coreclr"` strategies.
- **known not to apply**: Legacy JEP 333 high-bit multi-mapped ZGC layouts (`Marked0`/`Marked1`/`Remapped` at bits 42–45) do **not** apply to post-JEP 490 OpenJDK (`4f332731...`, 16 low-order metadata bits + store barriers); legacy Lean 4 paths `src/Lean/Compiler/IR/{RC,ResetReuse,Borrow}.lean` do **not** exist at `8009d0a6...` (migrated to `LCNF/*`); Go's stack-rescan-free hybrid barrier completeness does **not** hold if global stores omit barriers or if made conditional on blackness on x86-TSO without `MFENCE`; Perceus's garbage-free property does **not** apply to cyclic graphs without a cycle collector.
- **unsupported**: Upstream LLVM `Statepoints.md` (`4d369315...`) marks non-X86_64/non-AArch64 targets (lines 699–702), `RS4GC` rewriting of `alloca` in `"gc-live"` (lines 292–295), `ptrtoint`/`inttoptr` round-trips in the abstract model (lines 708–719), and relocations along exceptional `rethrow` edges (lines 745–750) as unsupported/broken; LLVM `"shadow-stack"` does not support multithreading (`GarbageCollection.md:391-396`); Go's `runtime.Pinner` does not support deep/transitive pinning (`pinner.go:38-41`); OCaml 5 explicitly disclaims a formal mixed OCaml/C memory model (`memory.c:297-304`).

## Evidence

All primary-source inspections, bibliographic checks, and probe executions were performed on `2026-11-19`.

### Primary Source Repositories

- **`llvm/llvm-project`** @ `4d369315c397296c4e3fdaff15b7e6500b533d16`:
  `llvm/docs/Statepoints.md:22-116, 151-245, 292-323, 411-508, 513-635, 638-750`; `llvm/docs/GarbageCollection.md:380-396`; `llvm/docs/StackMaps.md:200-280`; `llvm/lib/Transforms/Scalar/RewriteStatepointsForGC.cpp:170-198, 319-435, 679-809, 2221-2335`; `llvm/lib/Transforms/Scalar/PlaceSafepoints.cpp:37-46, 76-106, 147-158`.
- **`openjdk/jdk`** @ `4f33273115381cd7697082fcb1bb2642dae19043`:
  `src/hotspot/share/gc/z/zAddress.hpp:48-259`; `zBarrier.hpp:31-68`; `zBarrier.inline.hpp:37-159`; `zStoreBarrierBuffer.hpp:33-96`; `src/hotspot/share/gc/g1/g1BarrierSet.inline.hpp:38-155`; `src/hotspot/share/runtime/safepointMechanism.hpp:37-97`; `safepointMechanism.inline.hpp:40-79`; `src/hotspot/share/opto/loopnode.cpp:3524-3531, 3712-3720, 3879-3887, 4518-4560, 5750-5757`.
- **`golang/go`** @ `b496a3044e1dcdc3eed0af3e0e89db92f740d764`:
  `src/runtime/mgc.go:5-83, 157-177, 238-244`; `src/runtime/mbarrier.go:24-132, 150-198, 276-328`; `src/runtime/mwbbuf.go:5-160`; `src/runtime/preempt.go:5-52, 442-549`; `src/runtime/pinner.go:12-98, 377-446`.
- **`ocaml/ocaml`** @ `d921d1e86c56baa7b30e890ced455c12255793f5`:
  `runtime/memory.c:280-354`; `runtime/minor_gc.c:188-285`; `runtime/major_gc.c:52-148, 1788-1848`; `runtime/caml/major_gc.h:23-36`; `runtime/shared_heap.c:41-100`; `runtime/caml/memory.h:290-317`.
- **`mmtk/mmtk-core`** @ `d154f4f0dcca27439b920165ce5c948ca18aef24`:
  `src/vm/mod.rs:1-93`; `src/plan/plan_constraints.rs:10-92`; `src/plan/barriers.rs:18-136, 187-442`; `src/vm/scanning.rs:169-195`; `src/vm/slot.rs:108-153`; `src/vm/collection.rs:15-118`; `src/plan/lxr/global.rs:85-92`; `src/plan/concurrent/immix/global.rs:59-66`.
- **`leanprover/lean4`** @ `8009d0a64d2860606c6a5ac5ff6702622b24921e`:
  `src/Lean/Compiler/LCNF/Passes.lean:22-32, 144-159`; `ResetReuse.lean:18-180`; `InferBorrow.lean:19-120`; `ExplicitRC.lean:14-180`; `ExpandResetReuse.lean:12-180`; `src/include/lean/lean.h:220-275, 410-426, 630-790`; `tests/verif/Verif/runtime/RC.lean:1-45`.
- **`koka-lang/koka`** @ `facb7932ce6871fdb063f762a304bd8238f35fba`:
  `src/Backend/C/Parc.hs:10-140`; `src/Backend/C/ParcReuse.hs:77-125`; `src/Backend/C/ParcReuseSpec.hs:14-98`.

### Peer-Reviewed Literature

- Diwan, Moss, and Hudson (PLDI 1992), DOI `10.1145/143095.143140`.
- Dijkstra, Lamport, Martin, Scholten, and Steffens (CACM 1978), DOI `10.1145/359642.359655`.
- Yuasa (J. Syst. Softw. 1990), DOI `10.1016/0164-1212(90)90084-Y`.
- Wilson (IWMM 1992), DOI `10.1007/BFb0017182`.
- Sivaramakrishnan et al. (PACMPL 4 / ICFP 2020), DOI `10.1145/3408995`, `arXiv:2004.11663`.
- Ullrich and de Moura (IFL 2019), DOI `10.1145/3412932.3412935`, `arXiv:1908.05647`.
- Reinking, Xie, de Moura, and Leijen (PLDI 2021), DOI `10.1145/3453483.3454032`.
- Bacon and Rajan (ECOOP 2001), DOI `10.1007/3-540-45337-7_12`.
- Hawblitzel and Petrank (POPL 2009), DOI `10.1145/1480881.1480935` (LMCS 2010: `10.2168/LMCS-6(3:6)2010`).
- McCreight, Shao, Lin, and Li (PLDI 2007), DOI `10.1145/1273442.1250788`.
- McCreight, Chevalier, and Tolmach (ICFP 2010), DOI `10.1145/1863543.1863575`.
- Sandberg Ericsson, Myreen, and Åman Pohjola (JAR 2019), DOI `10.1007/s10817-018-9487-z` (ITP 2017: `10.1007/978-3-319-66107-0_28`).
- Gammie, Hosking, and Engelhardt (PLDI 2015), DOI `10.1145/2737924.2738006`; Isabelle AFP `ConcurrentGC` (`https://www.isa-afp.org/entries/ConcurrentGC.html`).

### Preserved Executable Verification Probe

- Script: `support/verify_gc_tricolor_and_derived_roots.py` (Python 3.10+, stdlib only).
- Execution (`python3 -B support/verify_gc_tricolor_and_derived_roots.py`, `2026-11-19`, exit `0`, ~3.8s user CPU):
  - Tri-color BFS: `none_no_rescan` 7-step witness (5,248 states); `dijkstra_no_rescan` 8-step witness (9,514 states); `yuasa_no_rescan` 7-step witness (7,886 states); `go_hybrid_conditional_no_rescan` 38,010 states / 0 violations; `go_hybrid_unconditional_no_rescan` 37,730 states / 0 violations; `yuasa_with_stw_stack_snapshot` 8,228 states / 0 violations.
  - x86-TSO Dekker litmus: without `MFENCE` `(0,0)` reachable; with `MFENCE` `(0,0)` unreachable.
  - Derived pointers: dropped base → dangling (`True`); exterior pointer mis-attributed to `arrB`; `(base, derived)` statepoint reconstructs interior and exterior reads to `('arrA', 200)`.
  - Generational ZGC shift barrier: 4 phases checked, 100% cross-phase stale traps, CAS self-heal to `0x40000098760`.
  - Perceus / Lean 4 reuse & sticky RC: `rc == 1` → 3 in-place reuses / 0 allocs; `rc > 1` → 3 disjoint allocs preserving alias, 0 live after drop; Lean 4 `0x7FFFFFFF + 1` sticky overflow frozen under drops.

## Revalidation

1. **Re-run the preserved executable probe** (~4 seconds, zero external dependencies):
   ```console
   python3 -B reports/garbage-collection-barriers-safepoints-and-runtime-invariants/support/verify_gc_tricolor_and_derived_roots.py
   ```
   A passing exit code `0` re-verifies the bounded tri-color BFS, x86-TSO Dekker simulation, derived-pointer relocation, ZGC 4-phase shift load barrier, and Perceus/Lean 4 reuse and sticky-RC models; it establishes only those modeled properties, not upstream implementation equivalence.
2. **Diff narrow upstream regions against pinned SHAs**:
   - **LLVM** (`4d369315...`): diff `Statepoints.md` (`Limitations`, `isSafeToSpeculate`, `Supported Architectures`) and `RewriteStatepointsForGC.cpp` (`BDVState`, `findBasePointer`).
   - **OpenJDK** (`4f332731...`): diff `gc/z/{zAddress.hpp, zBarrier.hpp, zStoreBarrierBuffer.hpp}`, `gc/g1/g1BarrierSet.inline.hpp`, and `opto/loopnode.cpp` (`LoopStripMiningIter`).
   - **Go** (`b496a304...`): diff `src/runtime/{mgc.go, mbarrier.go, mwbbuf.go, preempt.go, pinner.go}` for `heapObjectsCanMove`, barrier structure, or precise async-safepoint maps.
   - **OCaml 5** (`d921d1e8...`): diff `runtime/{memory.c, minor_gc.c, major_gc.c, shared_heap.c}` for `caml_modify` and mixed OCaml/C memory-model updates.
   - **MMTk** (`d154f4f0...`): diff `src/vm/{mod.rs, slot.rs, scanning.rs}` (issues #1033/#1038) and `src/plan/barriers.rs`.
   - **Lean 4 & Koka** (`8009d0a6...`, `facb7932...`): diff `LCNF/{Passes,ResetReuse,InferBorrow,ExplicitRC,ExpandResetReuse}.lean`, `lean.h`, `tests/verif/Verif/runtime/RC.lean`, and `Backend/C/Parc*.hs`.
