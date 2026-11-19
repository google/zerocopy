# Read-Copy-Update, `QSBR`/`EBR`, Hazard Pointers, `SeqLock`s, and Safe Memory Reclamation Under Weak Memory and Provenance Models

## Summary

Safe lock-free memory reclamation (SMR) and optimistic read synchronization sit directly on the fault line between hardware memory ordering, operating-system IPI barriers, and strict programming-language abstract machines (ISO C/C++26, Rust/MiniRust). Five load-bearing invariants govern their design and verification:

1. **Linux Kernel RCU Is Formalized by a Context-Free Grace-Period Balance Axiom (`linux-kernel.cat`), Not Mere Pairwise Release-Acquire:** In the Linux Kernel Memory Model (`LKMM`, `Alglave et al., ASPLOS 2018`, `torvalds/linux/tools/memory-model/linux-kernel.cat:134-171`), RCU ordering is defined by a recursive Dyck-like relation `rcu-order` requiring **at least as many grace periods (`Sync-rcu` / `Sync-srcu`) as read-side critical sections (`rcu-rscs^-1`)** along any causal `rcu-link` chain (with `& loc` domain scoping for `SRCU`), enforcing `irreflexive rb as rcu`. A single `synchronize_rcu()` forbids a 1-reader use-after-free cycle, but **cannot** forbid a 2-reader chained cycle unless two grace periods intervene.
2. **Epoch-Based Reclamation (`crossbeam-epoch`) Trades Bounded Memory Under Stalled Readers for Zero-Pointer-Validation Reads—and Contains a Documented C++20/Rust `SeqCst` Fence Shortcut on x86:** `crossbeam-epoch` (`crossbeam-rs/crossbeam`) uses a 3-epoch ring (`SealedBag::is_expired` requires `global_epoch.wrapping_sub(self.epoch) >= 2`). A single stalled or preempted pinned reader freezes `global_epoch` after at most one advancement, causing **100% of subsequent retired objects (`O(N)` unbounded memory)** to remain unreclaimed (`10,000/10,000` leaked in our exact simulation). Furthermore, `crossbeam-epoch/src/internal.rs:421-453` explicitly replaces `(Relaxed store; fence(SeqCst))` in `Local::pin()` on `x86`/`x86_64` (gated by `not(miri)`) with `compare_exchange(..., SeqCst, SeqCst)` + `compiler_fence(SeqCst)`—a hardware-specific optimization that is **formally insufficient** under C++20/Rust abstract fence-to-fence SC synchronization rules.
3. **Hazard Pointers (Michael 2004, C++26 `P2530R3`, `facebook/folly`) Bound Unreclaimed Memory to `O(P * K)` and Eliminate Reader Hardware Fences via Asymmetric `membarrier(2)`:** By publishing per-object hazard slots and validating via `try_protect()`, Hazard Pointers keep unreclaimed objects bounded by the total number of active slots (`18` unreclaimed vs. `10,000` for EBR under a stalled reader). Pairing `asymmetric_thread_fence_light` (`atomic_signal_fence`) on reader paths with Linux `membarrier(MEMBARRIER_CMD_PRIVATE_EXPEDITED)` IPIs (or `mprotect` TLB-shootdown fallback) on bulk reclamation eliminates the per-read `StoreLoad` barrier (`7.72 ns/op` -> `1.23 ns/op`, **`6.27x` speedup** measured live on Linux `7.1.6`, breaking even against `1953.3 ns` `membarrier` calls at ~300 reader ops per reclamation batch).
4. **Optimistic `SeqLock` Reads Over Non-Atomic Fields Trigger Immediate Data-Race UB in C++11/Rust/MiniRust Even When Torn Reads Are Discarded:** Per `Boehm (MSPC 2012)` and `MiniRust` `ConcurrentMemory::Access::races` (`spec/mem/concurrent.md:161-176`), any overlapping Load and Store across threads where at least one access has `Atomicity::None` is **immediate Undefined Behavior**, regardless of whether a subsequent `seq1 != seq2` check discards the value. Live Linux `7.1.6` execution of a Boehm-compliant atomic-word SeqLock observed **`352` real torn intermediate snapshots caught and discarded** (`0` escaped)—confirming that non-atomic payload reads suffer genuine runtime data races. In Rust/MiniRust, sound SeqLocks additionally require per-byte/per-word atomic loads into `MaybeUninit`/frozen storage so torn bit patterns or struct padding bytes do not violate type validity invariants.
5. **ISO C Lifetime-End Pointer Zap Breaks Lock-Free Pointer Validation, While MiniRust Separates Address Comparison From Allocation-ID Provenance:** Under ISO C/C++ lifetime-end pointer zap (`WG14 N2369`, `WG21 P1726`), freeing an object makes even comparing a concurrently loaded pointer indeterminate/UB—breaking hazard-pointer `try_protect()` and lock-free CAS loops. `MiniRust` (`spec/lang/step/operators.md:341-348`, `spec/mem/basic.md:197-225`) resolves comparison zap by comparing raw addresses while ignoring provenance (`compare_ptr`), **yet still enforces strict `AllocId` liveness on dereference**, making ABA-reallocated address dereference with stale provenance immediate UB. Modular mechanized proofs in weak-memory separation logic—from `GPS` (`Tassarotti et al., PLDI 2015`) through `Iris` modular SMR (`Jung et al., OOPSLA 2023`) to `iRC11` general-purpose RCU (`Jung et al., PLDI 2025`)—close the gap between relaxed atomics, RAW SC-fences, and reclamation ownership transfer.

## Applicability

This report synthesizes four primary implementation/specification trees, six peer-reviewed foundational papers, and two ISO standardization suites:

- **Linux kernel (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, `Linux 7.4.0-rc3`):** Authoritative source for `tools/memory-model/linux-kernel.cat` (LKMM RCU/SRCU & plain-access data-race axioms), `include/linux/seqlock.h` (kernel `seqcount_t` barriers and `KCSAN_SEQLOCK_REGION_MAX`), and `kernel/sched/membarrier.c` (`MEMBARRIER_CMD_PRIVATE_EXPEDITED` IPI barriers).
- **Userspace SMR runtimes:**
  - `crossbeam-rs/crossbeam` @ `a28f40fdddb70bea8e5faf0efad9af0be4b9dbea` (`crossbeam-epoch`): Canonical Rust Epoch-Based Reclamation / QSBR implementation (`epoch.rs`, `internal.rs`, `guard.rs`).
  - `facebook/folly` @ `4b2dd6e1f1dda89dd1b5b71f88ce0ce91ec5c39e`: Production C++ implementation that directly informed C++26 `<hazard_pointer>` (`WG21 P2530R3`) and `<rcu>` (`WG21 P2545R4`) (`HazptrHolder.h`, `HazptrDomain.h`, `AsymmetricThreadFence.cpp`, `Rcu.h`).
- **Formal language semantics & verification literature:**
  - `minirust/minirust` @ `063d784186d3252bee242217f218223205c0b568`: Operational specification of `BasicMemory` `AllocId` provenance (`spec/mem/basic.md`), provenance-ignoring `compare_ptr` (`spec/lang/step/operators.md`), and `ConcurrentMemory` data-race UB (`spec/mem/concurrent.md`).
  - `Alglave et al. (ASPLOS 2018)`, `Michael (IEEE TPDS 2004)`, `Boehm (MSPC 2012)`, `Tassarotti, Dreyer, Vafeiadis (PLDI 2015)`, `Jung et al. (OOPSLA 2023)`, and `Jung et al. (PLDI 2025)`.
- **Live execution environment (`Linux 7.1.6 x86_64`, GCC `-O2 -pthread`):** Empirical `membarrier(2)` asymmetric fence latency measurements and concurrent Boehm-compliant SeqLock consistency trials were executed directly on a live Linux `7.1.6` host (`MEMBARRIER_CMD_QUERY = 0x3ff`).

Findings apply to shared-memory lock-free data structures in C, C++11–C++26, Rust, and Linux kernel C across x86-TSO, ARMv8, POWER, and RISC-V weak memory architectures. Latency ratios (`6.27x` asymmetric fence speedup) are specific to the tested x86_64 microarchitecture and thread count, whereas all axiomatic, memory-bound, and abstract-machine UB invariants are architecture-independent.

## Findings

### 1. Linux Kernel Memory Model (`LKMM`) RCU Grace-Period Axioms

#### 1.1 Exact `linux-kernel.cat` Relational Specification
Basis: normative + source (`torvalds/linux/tools/memory-model/linux-kernel.cat:120-226`, `Alglave et al., ASPLOS 2018`, `DOI: 10.1145/3173162.3177156`).

Unlike lock-based critical sections—which establish a total mutual-exclusion order—RCU's fundamental guarantee ("Grace Period Guarantee") is purely temporal and asymmetric: if any part of an RCU read-side critical section (`rcu_read_lock()` .. `rcu_read_unlock()`) executes *before* a grace period (`synchronize_rcu()`) begins, then the entire read-side critical section completes *before* that grace period ends (equivalently, no critical section can span completely across a grace period from before its start to after its end).

In `torvalds/linux/tools/memory-model/linux-kernel.cat:134-171`, `LKMM` encodes this as a recursive context-free relation over `rcu-gp = [Sync-rcu]`, `srcu-gp = [Sync-srcu]`, reversed critical-section edges `rcu-rscsi = rcu-rscs^-1` (running backward from `rcu_read_unlock()` to `rcu_read_lock()`), and causal propagation links `rcu-link = po? ; hb* ; pb* ; prop ; po`:

```cat
/* tools/memory-model/linux-kernel.cat:154-171 */
let rec rcu-order = rcu-gp | srcu-gp |
    (rcu-gp ; rcu-link ; rcu-rscsi) |
    ((srcu-gp ; rcu-link ; srcu-rscsi) & loc) |
    (rcu-rscsi ; rcu-link ; rcu-gp) |
    ((srcu-rscsi ; rcu-link ; srcu-gp) & loc) |
    (rcu-gp ; rcu-link ; rcu-order ; rcu-link ; rcu-rscsi) |
    ((srcu-gp ; rcu-link ; rcu-order ; rcu-link ; srcu-rscsi) & loc) |
    (rcu-rscsi ; rcu-link ; rcu-order ; rcu-link ; rcu-gp) |
    ((srcu-rscsi ; rcu-link ; rcu-order ; rcu-link ; srcu-gp) & loc) |
    (rcu-order ; rcu-link ; rcu-order)
let rcu-fence = po ; rcu-order ; po?
let fence = fence | rcu-fence
let strong-fence = strong-fence | rcu-fence
let rb = prop ; rcu-fence ; hb* ; pb* ; [Marked]
irreflexive rb as rcu
```

Three non-obvious structural consequences follow directly from these exact equations:

1. **Generalized Inter-CPU Strong Fence via Counting Balance (`#GPs >= #CSs`):** Because `rcu-rscsi` goes *backward* in program order (from unlock to lock), each `rcu-rscsi` edge can "step backward in time" by up to one grace period, while each `rcu-gp` steps forward by at least one grace period. The grammar `rcu-order` matches any non-empty sequence of `rcu-gp` and `rcu-rscsi` events linked by `rcu-link` whose count of grace periods is **at least as large as** its count of read-side critical sections (and strictly positive), turning that cross-thread chain into an effective `strong-fence` (`rcu-fence`).
2. **Domain Isolation for Sleepable RCU (`& loc`):** Every `srcu-gp` / `srcu-rscsi` pairing is intersected with `& loc` (`L156, 158, 160, 162`). A `synchronize_srcu(&s1)` provides **zero** ordering against an `srcu_read_lock(&s2)` on a different `struct srcu_struct` instance, whereas global `rcu-gp` / `rcu-rscsi` pairs are un-scoped across the entire kernel.
3. **Executable Counterexample Boundary (`## Evidence`, Execution Probe 2):** Evaluating the exact dynamic-programming closure of `rcu-order` on cyclic `rcu-link` sequences yields:

| Cyclic Sequence of `GP` / `CS` Around `rcu-link` Cycle | `rcu-order` Derivable? | `irreflexive rb` Forbids Cycle? | Operational Interpretation |
| :--- | :---: | :---: | :--- |
| `[GP, CS]` (1 GP, 1 CS) | Yes | **Forbidden** | Classic RCU reclamation safety: reader cannot see post-GP free while reading pre-GP pointer |
| `[GP, CS, CS]` (1 GP, 2 chained CSs) | No | **Allowed** | Single `synchronize_rcu()` cannot order across two overlapping reader critical sections passing a flag |
| `[GP, CS, GP, CS]` (2 GPs, 2 CSs) | Yes | **Forbidden** | Alternating two-grace-period chain closes `rb` |
| `[GP, GP, CS, CS]` (nested 2 GPs, 2 CSs) | Yes | **Forbidden** | Two sequential grace periods dominate two nested/chained CSs |
| `[GP, CS, GP, CS, CS]` (2 GPs, 3 CSs) | No | **Allowed** | Strict deficit (`2 < 3`) permits non-SC execution |
| `[CS, CS]` (0 GPs, 2 CSs) | No | **Allowed** | RCU read-side critical sections alone provide no mutual exclusion or cross-CPU fence |

4. **Plain-Access Data-Race Rules (`linux-kernel.cat:186-226`):** `LKMM` separately flags `mixed-accesses` (`[Plain & W] ; (po-loc \ barrier) ; [Marked]`) and `ww-race | wr-race | rw-race` whenever a `Plain` access conflicts with an external access (`pre-race = ext & ((Plain * M) | ((M \ IW) * Plain))`) without visibility ordering (`wr-vis`, `rw-xbstar`, `ww-vis`). Under RCU, reclaiming (`kfree` / plain reuse write) an object after `synchronize_rcu()` places the reader's plain dereference before the writer's plain deallocation via `rw-xbstar` (`rcu-fence` -> `rb` -> `xbstar`), proving data-race freedom in `LKMM`—whereas accessing an RCU-updated pointer itself *without* `rcu_dereference()` / `READ_ONCE()` triggers a `wr-race` / `rw-race`.

### 2. Epoch-Based Reclamation / `QSBR` (`crossbeam-epoch`) vs. Stalled-Reader Unbounded Memory Growth

#### 2.1 Exact 3-Epoch Protocol and Constants in `crossbeam-rs/crossbeam`
Basis: source (`crossbeam-rs/crossbeam` @ `a28f40fd`, `crossbeam-epoch/src/epoch.rs:17-88`, `crossbeam-epoch/src/internal.rs:64-294,337-555`, `crossbeam-epoch/src/guard.rs:70-120`).

`crossbeam-epoch` implements lock-free Epoch-Based Reclamation (EBR), a user-space realization of Quiescent-State-Based Reclamation (`QSBR`) with explicit `Guard` pinning:

- **Epoch Representation (`epoch.rs:34-87`):** `Epoch { data: u64 }` (or `usize` on 32-bit targets without 64-bit atomics) packs the pin status in bit `0` (`is_pinned = (data & 1) == 1`) and increments epoch generations by `+2` (`wrapping_add(2)`). Signed modular distance is `wrapping_sub(self, rhs) = self.data.wrapping_sub(rhs.data & !1) as i64 >> 1`.
- **Thread-Local Buffering & Collection Constants (`internal.rs:64-179, 340`):**
  - `Bag` holds up to `MAX_OBJECTS = 64` deferred closures (`4` under `miri` or sanitizers, `L65-69`) before `Global::push_bag()` issues `atomic::fence(Ordering::SeqCst)`, tags the bag with `self.epoch.load(Ordering::Relaxed)`, and enqueues a `SealedBag` onto the global Michael–Scott queue (`L191-198`).
  - Every `PINNINGS_BETWEEN_COLLECT = 128` pins (`L340, 461`), `Local::pin()` calls `Global::collect()`, which invokes `try_advance()` and pops up to `COLLECT_STEPS = 8` expired bags (`L178, 208-226`).
  - **2-Epoch Expiration Invariant (`internal.rs:157-161`):** `SealedBag::is_expired(global_epoch)` returns `global_epoch.wrapping_sub(self.epoch) >= 2`. Because a thread pinned in `global_epoch - 1` can still hold pointers loaded before `global_epoch` advanced, only objects retired at least **two** epochs prior are provably unreachable by every pinned participant.
- **Advancement Condition (`internal.rs:237-293`):** `Global::try_advance()` loads `global_epoch`, executes `atomic::fence(Ordering::SeqCst)` (`L244`), iterates the intrusive linked list of all registered `Local` participants, and **aborts without advancing** if any participant either stalls list traversal (`Err(IterError::Stalled)`) or satisfies `local_epoch.is_pinned() && local_epoch.unpinned() != global_epoch` (`L267-269`). Only if every pinned thread has observed `global_epoch` does `try_advance()` execute `atomic::fence(Ordering::Acquire)` (`L281`) and store `global_epoch.successor()` with `Ordering::Release` (`L291`).

#### 2.2 Formal Memory-Model Gap in `crossbeam-epoch` `Local::pin()` on `x86`/`x86_64`
Basis: source (`crossbeam-rs/crossbeam/crossbeam-epoch/src/internal.rs:414-454`) + derived.

Inspecting `Local::pin()` (`internal.rs:414-454`) reveals a subtle, load-bearing divergence between hardware behavior and the C++20/Rust abstract memory model:

```rust
/* crossbeam-epoch/src/internal.rs:421-453 */
if cfg!(all(any(target_arch = "x86", target_arch = "x86_64"), not(miri))) {
    // HACK(stjepang): ... `_.compare_exchange(_, _, SeqCst, SeqCst)` compiles into `lock cmpxchg`.
    // It is not clear that this is permitted by the C++ memory model (SC fences work very
    // differently from SC accesses), but experimental evidence suggests that this works fine.
    let res = self.epoch.compare_exchange(
        Epoch::starting(), new_epoch, Ordering::SeqCst, Ordering::SeqCst);
    atomic::compiler_fence(Ordering::SeqCst);
} else {
    self.epoch.store(new_epoch, Ordering::Relaxed);
    atomic::fence(Ordering::SeqCst);
}
```

- **Why the `else` branch is formally sound:** The collector (`try_advance`) performs `R_rlx(global_epoch); F_sc; R_rlx(local_epoch)`, while `pin()` performs `W_rlx(local_epoch); F_sc; R(shared_ptr)`. Under the C++20/Rust SC total order $S$ (`[atomics.order]`), the two `SeqCst` fences are totally ordered: either `F_sc(pin) <_S F_sc(advance)` (forcing `try_advance` to observe the pinned `local_epoch`) or `F_sc(advance) <_S F_sc(pin)` (forcing `pin` or subsequent loads to observe any stores before `try_advance`).
- **Why the `x86` `not(miri)` shortcut is formally unsound in C++20/Rust (yet works on x86-TSO silicon):** Under C++20, an `SC` RMW (`compare_exchange(..., SeqCst)`) does **not** establish the fence-to-fence StoreLoad ordering rule against `try_advance()`'s `R_rlx(global_epoch); F_sc; R_rlx(local_epoch)` when `try_advance()` performs relaxed loads on `self.epoch` and `local.epoch`! On real x86-64 CPUs, `lock cmpxchg` drains the store buffer just like `mfence` (at lower latency on Intel/AMD microarchitectures), and `compiler_fence(SeqCst)` prevents LLVM reordering—yet formal verifiers and Miri rightly reject this shortcut, which is why `crossbeam-epoch` explicitly guards it with `not(miri)`.

#### 2.3 Stalled-Reader Unbounded Memory Growth vs. Hazard Pointers
Basis: source (`crossbeam-epoch/src/internal.rs:160,267-269`) + execution (Execution Probe 2 in `## Evidence`).

Because EBR tracks *time epochs* rather than *individual object pointers*, a single reader thread that holds a `Guard` while descheduled by the OS, blocked on I/O, or stuck in a long computation pins its `local_epoch` to `E_0`. The global epoch can advance at most once (`E_0 -> E_1`), at which point `local_epoch.unpinned() == E_0 != E_1` causes `try_advance()` to return `E_1` forever. Because `SealedBag::is_expired()` requires `global_epoch - bag.epoch >= 2`, **zero** bags sealed in `E_0` or `E_1` can ever expire.

Our exact simulation (`## Evidence`, Execution Probe 2: 4 threads, `N = 10,000` retirements, `K = 2` hazard slots, `PINNINGS_BETWEEN_COLLECT = 128`, HP batch threshold `64`) quantifies this cliff:

| Scenario (`N = 10,000` retirements) | `crossbeam-epoch` Final Epoch | `crossbeam-epoch` Unreclaimed | Hazard Pointers Unreclaimed | Asymptotic Memory Bound ($P$ threads, $K$ slots, $N$ retirements) |
| :--- | :---: | :---: | :---: | :--- |
| **No stalled reader (`stall_reader=False`)** | `79` | `143` | `16` | EBR: $O(B \cdot P)$ steady state; HP: $O(P \cdot K)$ |
| **1 stalled reader (`stall_reader=True`)** | `1` (frozen) | **`10,000` (100% leaked)** | **`18`** ($2$ protected + $16$ below batch threshold) | **EBR: $\Theta(N)$ unbounded (OOM hazard); HP: strict $O(P \cdot K)$** |

### 3. Hazard Pointers (`Michael 2004`, C++26 `P2530R3`, `facebook/folly`) and Asymmetric `membarrier(2)` Fences

#### 3.1 Fine-Grained Protection Protocol and C++26 Standardization
Basis: normative + source (`Michael, IEEE TPDS 2004`, `DOI: 10.1109/TPDS.2004.8`; `WG21 P2530R3`; `facebook/folly/folly/synchronization/HazptrHolder.h:119-169`, `HazptrDomain.h:597-620`).

Hazard Pointers protect *individual heap allocations* rather than global epochs. In `facebook/folly` (whose design was standardized into C++26 `<hazard_pointer>` via `P2530R3`: `std::hazard_pointer`, `std::hazard_pointer_obj_base<T, D>`, `std::make_hazard_pointer()`), the core reader validation loop is `hazptr_holder::try_protect()` (`HazptrHolder.h:119-154`):

```cpp
/* folly/synchronization/HazptrHolder.h:119-131 */
bool try_protect(T*& ptr, Src src, Func f = {}) noexcept {
  auto* const p = ptr;
  T* const protectedPtr = f(static_cast<T*>(p));
  reset_protection(protectedPtr);                                        // 1. Store p into hazard slot (Relaxed)
  folly::asymmetric_thread_fence_light(std::memory_order_seq_cst);       // 2. Light fence (compiler barrier only!)
  ptr = src();                                                           // 3. Reload source atomic ptr (Acquire)
  if (p != ptr) [[unlikely]] {                                           // 4. Validate pointer unchanged
    reset_protection();
    return false;
  }
  return true;
}
```

On the writer/reclaimer side (`HazptrDomain.h:598-620`), `do_reclamation()` extracts sharded retired lists (`kNumShards` shards reducing contention), executes **`asymmetric_thread_fence_heavy(std::memory_order_seq_cst)`** (`L605-606`), collects the hash set `hs = load_hazptr_vals()` (`L607`), and reclaims every retired node absent from `hs` while deferring only matched nodes.

**Safety Invariant (Store-Load Mutual Observation):** Because `src` is updated (unlinking `p`) *before* `p` enters the retired list and *before* `asymmetric_thread_fence_heavy`, and the reader stores `p` into its hazard slot *before* `asymmetric_thread_fence_light` and *before* reloading `src`:
- Either `light` precedes `heavy` -> the reclaimer's `load_hazptr_vals()` **must** observe `p` and preserve the object; or
- `heavy` precedes `light` -> the reader's `src()` reload **must** observe the updated pointer `ptr != p`, causing `try_protect()` to fail, clear the slot, and retry without ever dereferencing `p`.

#### 3.2 Asymmetric Thread Fences (`membarrier(2)` IPI vs. `mprotect` TLB Shootdown)
Basis: source (`facebook/folly/folly/synchronization/AsymmetricThreadFence.cpp:33-98`, `torvalds/linux/kernel/sched/membarrier.c:10-45`) + execution (Execution Probe 1 in `## Evidence`).

Classical Hazard Pointers (`Michael 2004`) incurred a full hardware `StoreLoad` fence (`mfence` / `dmb ish`) on **every single pointer traversal step**, crippling read-heavy linked-list and tree workloads. `Folly` (and Linux kernel `membarrier(2)`) exploits read/reclamation asymmetry:

1. **Reader Fast Path (`asymmetric_thread_fence_light`):** Emits **zero hardware fence instructions** on Linux (`atomic_signal_fence(memory_order_seq_cst)`—a pure compiler reordering barrier).
2. **Reclaimer Slow Path (`asymmetric_thread_fence_heavy`, `AsymmetricThreadFence.cpp:83-98`):**
   - **Primary Linux path:** Issues `syscall(SYS_membarrier, MEMBARRIER_CMD_PRIVATE_EXPEDITED, 0)` (after one-time process registration via `MEMBARRIER_CMD_REGISTER_PRIVATE_EXPEDITED`). Inside `torvalds/linux/kernel/sched/membarrier.c`, the kernel issues `smp_mb()` before and after dispatching IPIs (`smp_call_function_many`) to every CPU currently executing a thread of the same `mm_struct`, forcing a full hardware barrier on all active peer cores (any descheduled thread already executed a full barrier during `context_switch()`!).
   - **Legacy fallback (`mprotectMembarrier()`, `AsymmetricThreadFence.cpp:40-66`):** When `membarrier(2)` is unavailable, `folly` allocates a 1-page anonymous `dummyPage`, upgrades it to `PROT_READ | PROT_WRITE`, touches `*static_cast<char volatile*>(dummyPage) = 0` to guarantee residency, and downgrades it to `PROT_READ` via `mprotect(2)`—deliberately forcing a synchronous cross-CPU TLB shootdown IPI across every core running the process's threads! (On non-Linux platforms or `__wasi__`, `folly` falls back to symmetric `std::atomic_thread_fence`.)

**Live Linux `7.1.6` Benchmark (`## Evidence`, Execution Probe 1: x86_64, `10,000,000` `try_protect` iterations):**
- Symmetric `atomic_thread_fence(memory_order_seq_cst)`: **`7.72 ns/op`**
- Asymmetric light `atomic_signal_fence(memory_order_seq_cst)`: **`1.23 ns/op`** (**`6.27x` reader speedup**)
- Heavy `syscall(SYS_membarrier, MEMBARRIER_CMD_PRIVATE_EXPEDITED, 0)` (1,000 calls): **`1953.3 ns/call`**

Amortizing one `~1.95 µs` `membarrier(2)` across a reclamation batch breaks even against saving `6.49 ns/op` after just **`~301` reader `try_protect()` operations**—and scales cleanly as reclamation batch thresholds (`folly`'s sharded `kCountThreshold`) grow.

#### 3.3 Userspace RCU (`facebook/folly/Rcu.h` & C++26 `P2545R4` `<rcu>`)
Basis: normative + source (`WG21 P2545R4`, `facebook/folly/folly/synchronization/Rcu.h:134-156,240-265`).

C++26 complements `<hazard_pointer>` with `<rcu>` (`std::rcu_domain`, `std::rcu_default_domain()`, `std::rcu_obj_base<T>`, `std::rcu_retire()`, `std::rcu_synchronize()`). As documented in `folly/Rcu.h:241-262`:
- `std::scoped_lock<rcu_domain>` costs `~5 ns` (vs. `~26 ns` for `folly::SharedMutex::lock_shared`), `rcu_retire()` costs `~150 ns` (queue push), and `rcu_synchronize()` has `~10 ms` latency.
- **Architectural distinction (`P2530R3` vs. `P2545R4`):** Hazard pointers replace *reference counting* (fine-grained per-node protection, readers may safely block/sleep while holding a hazard pointer, strict $O(P \cdot K)$ memory bound, extra validation per pointer hop); RCU replaces *reader-writer locks* (coarse critical-section protection covering entire multi-node traversals with zero per-node fences, but readers must remain short/non-blocking lest grace periods stall and accumulate unbounded retired memory).

### 4. `SeqLock` Optimistic-Read Data-Race UB vs. Atomic Payload and Byte-Freeze Semantics

#### 4.1 Why Classic `SeqLock`s Are Immediate Undefined Behavior in C++11–26, Rust, and MiniRust
Basis: normative + source (`Boehm, MSPC 2012`, `DOI: 10.1145/2247684.2247688`; `minirust/minirust/spec/mem/concurrent.md:136-176`; `torvalds/linux/include/linux/seqlock.h:27-40,210-213,272-281,389-455`) + execution (Execution Probes 1 and 2 in `## Evidence`).

A `SeqLock` (`seqcount_t`) protects multi-word state (e.g., `(sec, nsec)` timestamps or Linux VFS `d_seq` dentry names) by having writers increment an even sequence counter to odd before mutating payload fields and to the next even number afterward, while readers read `s1 = seq` (spinning if odd), speculatively copy the payload, and retry if `s2 = seq != s1`.

Under the C++11/Rust/MiniRust Data-Race-Free (`DRF`) abstract machine, **classic `SeqLock`s with non-atomic payload accesses are unconditionally Undefined Behavior**:

```rust
/* minirust/spec/mem/concurrent.md:164-175 */
fn races(self, other: Self) -> bool {
    if self.ty == AccessType::Load && other.ty == AccessType::Load { return false; }
    if self.atomicity == Atomicity::Atomic && other.atomicity == Atomicity::Atomic { return false; }
    let end_addr = self.addr + self.len.bytes();
    let other_end_addr = other.addr + other.len.bytes();
    end_addr > other.addr && other_end_addr > self.addr
}
```

1. **Discarding Torn Data Does Not Erase UB:** Because the abstract machine defines a data race at the moment two unsynchronized overlapping accesses occur (at least one a store, at least one non-atomic), checking `s1 != s2` afterward and throwing away the speculative result **cannot retroactively repair UB**. As `Boehm (MSPC 2012)` proved, optimizing compilers relying on DRF may legally hoist payload loads outside the sequence window, fold reloads, or execute mis-speculated control flow (including crashing on a torn pointer/enum discriminant *before* reaching the `s1 != s2` check!).
2. **Live Empirical Confirmation (`## Evidence`, Execution Probe 1):** Under 2-thread contention (`500,000` writer updates of `(a, b = 3a + 7)`), our Boehm-compliant atomic-word reader observed `72,523` consistent reads, `119,956` retries, **`352` genuinely torn intermediate pairs `(a, b)` caught and discarded**, and `0` torn escapes. Those `352` torn reads prove concretely that overlapping writer-store / reader-load executions occur routinely in practice.
3. **Linux Kernel `seqcount_t` Pragmatism (`include/linux/seqlock.h:27-40, 210-213, 389-455`):** Linux works around C's DRF rule using explicit hardware/compiler barriers plus KCSAN annotations:
   - Writer (`do_raw_write_seqcount_begin`/`end`, L429–455): `kcsan_nestable_atomic_begin(); s->sequence++; smp_wmb();` ... payload writes ... `smp_wmb(); s->sequence++; kcsan_nestable_atomic_end();`
   - Reader (`__read_seqcount_begin`, L272–281; `do_read_seqcount_retry`, L409–413): `smp_load_acquire(&s->sequence)` (via `__seqprop_sequence`, L210–213), `kcsan_atomic_next(KCSAN_SEQLOCK_REGION_MAX /* 1000 */)`, payload reads, `smp_rmb()`, `kcsan_atomic_next(0)`, `READ_ONCE(s->sequence) != start`.
   - Note that Linux relies on `-fno-strict-aliasing`, `READ_ONCE`/`WRITE_ONCE`, and GCC/Clang kernel assumptions—which are **not** valid in portable ISO C++26 or safe Rust.

#### 4.2 Sound DRF `SeqLock` Protocol in C++26 and Rust/MiniRust (Per-Byte Atomic Freeze)
Basis: normative + derived (`Boehm, MSPC 2012`; `minirust/spec/mem/interface.md:28-41`, `concurrent.md:164-175`).

To satisfy the C++11–26 and Rust/MiniRust memory models without UB:

1. **All Payload Reads and Writes Must Be Atomic (`memory_order_relaxed`):**
   - **Writer:** `seq.store(v + 1, Relaxed); fence(Release);` -> write payload words via `AtomicUsize::store(..., Relaxed)` (or `AtomicU8`) -> `seq.store(v + 2, Release);`. (Note: under C++11, `seq.store(v + 1, Relaxed)` followed by `fence(Release)` prevents payload stores from floating *above* the odd counter store only if the counter store is visible before payload writes; more strictly, Boehm notes `seq.store(v + 1, Release)` is insufficient to prevent *downward* hoisting of payload stores before `v + 1` unless paired with `fence(Release)`—or `seq.store(v + 1, Relaxed); fence(Release)` because a release fence orders *all preceding stores* (`v + 1`) before *all subsequent atomic stores* (`payload`)! Meanwhile, `seq.store(v + 2, Release)` orders all preceding payload stores before publishing the even `v + 2`.)
   - **Reader:** `s1 = seq.load(Acquire);` (spin if odd) -> read payload words via `AtomicUsize::load(..., Relaxed)` -> **`fence(Acquire);`** -> `s2 = seq.load(Relaxed);` (retry if `s1 != s2`). Notice why `seq.load(Acquire)` at the *end* does **not** work! An `Acquire` load prevents subsequent ops from moving *up*, whereas `SeqLock` needs preceding payload loads not to sink *below* `s2 = seq.load()`! In C++11/Rust, **`atomic_thread_fence(Acquire)` before `seq.load(Relaxed)`** (or Boehm's read-don't-modify-write `fetch_add(0, Release)` / `AcqRel` on architectures where fences are weak) establishes the required `LoadLoad` ordering: if `s2` reads the same even value `s1` (meaning the writer's next `v + 1` store has not happened before `s2`), then the acquire fence paired with the writer's `v + 1` release fence prevents any relaxed payload load from reading from that concurrent writer!
2. **Rust / MiniRust Validity & Padding-Byte Hazard (`AbstractByte::Uninit` & `freeze`):** Even when payload words are loaded atomically as raw integers/bytes (`AtomicU8`/`AtomicUsize`), transmuting directly into a typed Rust `T` *before* validating `s1 == s2` is still UB if `T` has invalid bit patterns (`bool`, `NonNull`, `enum` tags) or uninitialized struct padding bytes (`AbstractByte::Uninit` in `minirust/spec/mem/interface.md:28-33`). Sound Rust `SeqLock<T>` implementations must therefore:
   - Restrict `T: Copy` (and for zero-copy/byte-level soundness, ensure `T` has no uninitialized padding bytes or copy into `[MaybeUninit<u8>; size_of::<T>()]` via byte/word atomic loads);
   - Perform **zero** typed inspection of the copied buffer until *after* `fence(Acquire)` + `s2 == s1` succeeds (at which point the buffer is guaranteed to contain a consistent initialized snapshot written before `s1`); and
   - On architectures/models where torn relaxed reads of mixed initialized/uninitialized bytes could propagate `Uninit`/`poison`, require either explicit zero-initialized backing storage (eliminating `Uninit` bytes) or a language-level bytewise `freeze` primitive.

### 5. Pointer Provenance, Lifetime-End Pointer Zap, ABA Hazards, and Weak-Memory Separation-Logic Verification

#### 5.1 ISO C/C++ Pointer-Zap (`N2369`/`P1726`) vs. `MiniRust` `AllocId` Provenance
Basis: normative + source (`WG14 N2369`, `WG21 P1726`, `WG21 P2188`; `minirust/minirust/spec/mem/basic.md:144-226`, `spec/lang/step/operators.md:341-348`) + execution (Execution Probe 2 in `## Evidence`).

Lock-free algorithms routinely load a pointer `p` from an atomic slot, while another thread concurrently unlinks, retires, and frees `*p`—and possibly reallocates a brand-new object at the **exact same virtual address** (`ABA`). Two distinct language-semantics hazards collide here:

1. **ISO C / C++ Lifetime-End Pointer Zap (`N2369` / `P1726`):** Under the literal text of ISO C (`6.2.4p2`: *"The value of a pointer becomes indeterminate when the object it points to reaches the end of its lifetime"*), the moment Thread B calls `free(p)`, Thread A's local register/variable holding `p` is "zapped" to an indeterminate value. Even executing `if (p != ptr)` in `hazptr_holder::try_protect()` (`HazptrHolder.h:126`) or performing `compare_exchange_weak(p, next)` after `p` was freed is technically UB under strict ISO C/C++, allowing optimizing compilers to assume a pointer to a freed allocation cannot equal a newly `malloc()`'d pointer (breaking ABA detection and hazard-pointer validation!). `WG14 N2369` and `WG21 P1726` / `P2188` (McKenney, Michael, Sewell et al.) document how real-world RCU and Hazard Pointer libraries rely on address-level comparison of potentially-zapped pointers remaining well-defined.
2. **`MiniRust` Split Semantics (`operators.md:341-348` vs. `mem/basic.md:197-225`):** `MiniRust` cleanly decouples *pointer comparison* from *dereference provenance*:
   - **Comparison ignores provenance (`compare_ptr`, `operators.md:341-348`):** `left.thin_pointer.addr.cmp(&right.thin_pointer.addr)`. Comparing a pointer whose allocation has been deallocated (`p_old`) against a fresh pointer (`p_new`) is **well-defined** (no pointer-zap UB on `try_protect()` validation or `compare_exchange` address checks!).
   - **Dereference enforces strict `AllocId` liveness (`check_ptr`, `mem/basic.md:206-213`):** Every allocation receives a unique monotonically fresh `AllocId`. `deallocate()` sets `allocation.live = false` (`L179`). Even if the allocator immediately recycles numerical address `0x1000` for a new live allocation `AllocId(1)`, dereferencing `p_old = ThinPointer { addr: 0x1000, provenance: Some(AllocId(0)) }` triggers immediate UB (`throw_ub!("dereferencing pointer to dead allocation")`, `L211-213`).
   - **Consequence for SMR (`## Evidence`, Execution Probe 2):** In Rust/MiniRust, an ABA race that succeeds numerically (`p_old.addr == p_new.addr`) does **not** magically rehabilitate `p_old`'s provenance! A lock-free reader that passes `p != ptr` due to ABA recycling without an SMR guarantee (or versioned tagged pointer) still executes immediate provenance UB upon dereferencing `p_old`—and conversely, a sound SMR (`RCU` / `EBR` / `Hazard Pointers`) must prove that `deallocate(AllocId(0))` **cannot occur** while any thread holds a protected dereferenceable handle to `AllocId(0)`.

#### 5.2 Mechanized Weak-Memory Separation-Logic Verification (`GPS` -> `Iris` -> `iRC11`)
Basis: normative (`Tassarotti et al., PLDI 2015`, `DOI: 10.1145/2737924.2737992`; `Jung et al., OOPSLA 2023`, `DOI: 10.1145/3622827`; `Jung et al., PLDI 2025`, `DOI: 10.1145/3729246`).

Proving memory safety and linearizability of lock-free structures with SMR under weak memory progressed through three landmark verification frameworks:

| Framework / Paper | Memory Model | Core Logical Mechanism | Verified Targets & Scope Boundary |
| :--- | :--- | :--- | :--- |
| **`GPS`** (`Tassarotti, Dreyer, Vafeiadis, PLDI 2015`, `DOI: 10.1145/2737924.2737992`) | C/C++11 Release-Acquire (`RA`) | **Ghosts, Protocols, and Separation**: single-writer state-transition protocols over atomic locations + ghost-state escrow transferring ownership of retired nodes from readers back to the updater after a grace period | First weak-memory proof of a user-space RCU implementation and singly-linked list client; limited to a bespoke single-writer RCU without general modular SMR abstraction |
| **`Iris Modular SMR`** (`Jung, Lee, Choi, Kim, Park, Kang, OOPSLA 2023`, `DOI: 10.1145/3622827`) | Sequentially Consistent (`SC`) in Coq/Iris | **Modular SMR Specifications**: abstract separation-logic predicates separating SMR library verification from client verification—capturing *pointer-protection validation* (`Protect` token for Hazard Pointers) and *optimistic traversal into retired nodes* (for RCU/EBR) | First modular Coq/Iris proofs of **Harris's list**, **Harris–Michael list**, **Chase–Lev work-stealing deque**, and **RDCSS** coupled with Hazard Pointers and RCU |
| **`iRC11` General-Purpose RCU** (`Jung, Park, Lee, Yeon, Kang, PLDI 2025`, `DOI: 10.1145/3729246`) | Relaxed Memory Consistency (`iRC11` on Iris in Coq) | **RAW-Synchronizing SC-Fence Reasoning** (supporting switchable critical sections and Peterson's mutex under RMC) + **Per-Node Incoming Link Histories** (replacing global total link order to support concurrent writers with partially ordered writes) | First mechanized general-purpose RCU library + concurrent-writer client verification under realistic relaxed memory consistency |

### 6. Cross-Scheme Safe Memory Reclamation Trade-Off Matrix
Basis: derived from sections 1–5.

| Mechanism | Reader Overhead | Writer / Reclamation Cost | Stalled-Reader Memory Bound | Readers May Block / Sleep? | ABA Protection? | Weak-Memory & Provenance Pitfall |
| :--- | :--- | :--- | :--- | :---: | :---: | :--- |
| **Linux Kernel RCU** (`torvalds/linux`) | Near-zero (`rcu_read_lock` = preempt count / no-op) | `synchronize_rcu()` grace period (ms) / `call_rcu()` | **Unbounded** (preemptible RCU / RCU CPU stall detector triggers) | Only under `SRCU` (scoped `& loc`) | Yes (within CS) | Requires `rcu_dereference()` (`READ_ONCE` + addr dep); 1 GP cannot bridge 2 chained CSs |
| **EBR / QSBR** (`crossbeam-epoch`) | 1 `SeqCst` fence per outer `pin()` (`lock cmpxchg` hack on x86) | Periodic `try_advance()` scan every `128` pins; `COLLECT_STEPS = 8` | **Unbounded $\Theta(N)$** (1 stalled thread freezes epoch forever) | Technically yes, but freezes all reclamation | Yes (2-epoch delay) | `not(miri)` x86 `CAS(SeqCst)` formally weaker than `F_sc` in C++20/Rust |
| **Hazard Pointers** (`facebook/folly`, C++26 `P2530R3`) | `~1.23 ns` per hop w/ `asymmetric_light` (`~7.72 ns` w/ `SeqCst`) | Sharded batch scan + `~1.95 µs` `membarrier(2)` IPI (or `mprotect`) | **Strict $O(P \cdot K)$** even if readers crash or stall indefinitely | **Yes** (only blocks reclamation of the $\le K$ protected nodes) | **Yes** (cannot reuse protected node) | ISO C pointer-zap UB on `p != ptr` validation; needs fixed slot count $K$ |
| **Userspace RCU** (`facebook/folly/Rcu.h`, C++26 `P2545R4`) | `~5 ns` scoped lock; zero per-node traversal overhead | `~150 ns` `rcu_retire()`; `~10 ms` `rcu_synchronize()` | Unbounded if readers stall indefinitely | Discouraged (stalls grace periods) | Yes (within CS) | Requires explicit domain registration and short non-blocking CSs |
| **`SeqLock`** (`include/linux/seqlock.h`, `Boehm 2012`) | 2 atomic loads + `fence(Acquire)` + atomic payload reads (no writes!) | Single-writer lock + 2 `seq` increments + `fence(Release)` | N/A (in-place mutation; no deferred reclamation) | **No** (stalled writer causes reader livelock) | N/A (version counter detects concurrent write) | **Immediate data-race UB** if payload accesses are non-atomic; Rust needs `MaybeUninit`/bytewise atomic freeze for padding/validity |

## Boundaries

- **`known not to apply` — `memory_order_consume` Dependency Chains:** Although Linux kernel RCU relies heavily on address dependencies (`rcu_dereference()` / `addr` in `linux-kernel.cat:90-94`), C++17–C++26 compilers universally promote `std::memory_order_consume` to `std::memory_order_acquire` because compiler optimization passes do not preserve syntactic dependency chains across IR transformations. Userspace C++26/Rust SMR designs should assume `Acquire` loads rather than `consume`.
- **`known not to apply` — `crossbeam-epoch` x86 `CAS(SeqCst)` Shortcut Under Miri / Formal C++20:** As documented in `crossbeam-epoch/src/internal.rs:421-450`, replacing `store(Relaxed); fence(SeqCst)` with `compare_exchange(..., SeqCst, SeqCst); compiler_fence(SeqCst)` is explicitly disabled under `cfg(miri)` and does not generalize to weakly ordered ISAs (`ARM64`, `POWER`, `RISC-V`) or formal C++20/Rust proofs.
- **`not examined` — Hybrid Epoch + Hazard Reclamation Schemes (`IBR`, `Hyaline`, `PEBR`):** Hybrid schemes such as Interval-Based Reclamation and Pointer-and-Epoch-Based Reclamation (`Kang & Jung, POPL 2020`), which combine EBR fast paths with bounded-memory ejection of stalled readers via OS signals or hazard fallback, were not source-audited in this report.
- **`not examined` — Rust Aliasing Models (`Stacked Borrows` / `Tree Borrows`) on Intrusive Lock-Free Nodes:** While `MiniRust` `BasicMemory` `AllocId` provenance and `ConcurrentMemory` data races were examined directly, the finer-grained per-byte retag/protector rules of `Tree Borrows` when converting `Shared<'g, T>` raw pointers into `&T` references inside `crossbeam-epoch` were not mechanically tested under Miri here.
- **`unknown` — Exact Multi-Core Scalability Crossover of `MEMBARRIER_CMD_PRIVATE_EXPEDITED`:** Our live `1953.3 ns/call` `membarrier(2)` measurement reflects an unloaded single-process environment on Linux `7.1.6`; under high core counts (`64–256` active peer threads across NUMA sockets), IPI broadcast latency increases significantly, shifting the optimal `folly::hazptr_domain` reclamation batch threshold upward.

## Evidence

### Primary Source & Literature Citations

| Subject | Immutable Commit / DOI / Paper ID | File Path & Symbol / Scope | Verified Finding |
| :--- | :--- | :--- | :--- |
| `torvalds/linux` | `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` (`7.4.0-rc3`) | `tools/memory-model/linux-kernel.cat:120-226` (`rcu-order`, `rcu-fence`, `rb`, `data-race`) | Recursive `rcu-order` Dyck balance axiom; `& loc` SRCU isolation; `irreflexive rb as rcu`; plain-access data-race equations |
| `torvalds/linux` | `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` | `include/linux/seqlock.h:27-40,210-213,272-281,389-455`; `kernel/sched/membarrier.c:10-45` | `KCSAN_SEQLOCK_REGION_MAX = 1000`; `smp_load_acquire`/`smp_rmb`/`smp_wmb` barriers; `MEMBARRIER_CMD_PRIVATE_EXPEDITED` IPI ordering |
| `crossbeam-rs/crossbeam` | `a28f40fdddb70bea8e5faf0efad9af0be4b9dbea` | `crossbeam-epoch/src/epoch.rs:34-87`; `src/internal.rs:64-294,340,410-555`; `src/guard.rs:70-120` | LSB pin bit; `MAX_OBJECTS = 64` (`4` in Miri); `COLLECT_STEPS = 8`; `PINNINGS_BETWEEN_COLLECT = 128`; `is_expired` (`>= 2`); x86 `not(miri)` `CAS(SeqCst)` shortcut L421–453 |
| `facebook/folly` | `4b2dd6e1f1dda89dd1b5b71f88ce0ce91ec5c39e` | `folly/synchronization/HazptrHolder.h:119-169`; `HazptrDomain.h:597-620`; `AsymmetricThreadFence.cpp:33-98`; `Rcu.h:134-156,240-265` | `try_protect()` light fence + validate; `do_reclamation()` heavy fence + scan; `membarrier` + `mprotectMembarrier()` TLB shootdown fallback; RCU vs Hazptr latency & trade-offs |
| `minirust/minirust` | `063d784186d3252bee242217f218223205c0b568` | `spec/mem/basic.md:144-226`; `spec/mem/interface.md:28-41`; `spec/mem/concurrent.md:136-176`; `spec/lang/step/operators.md:341-348` | `AbstractByte::Uninit`; `compare_ptr` ignores provenance; `check_ptr` raises UB on dead `AllocId` despite address reuse; `Access::races` raises immediate UB on any non-atomic overlap |
| `Alglave et al.` | `DOI: 10.1145/3173162.3177156` | *ASPLOS 2018* | Formalization of the Linux Kernel Memory Consistency Model (`LKMM`) and RCU grace-period axioms |
| `Michael` | `DOI: 10.1109/TPDS.2004.8` | *IEEE TPDS 2004*, Vol. 15, No. 6, pp. 491–504 | Hazard Pointers SMR algorithm and strict $O(P \cdot K)$ unreclaimed-memory bound |
| `Boehm` | `DOI: 10.1145/2247684.2247688` | *MSPC 2012* | Proof that non-atomic SeqLock reads are UB under C++11 DRF; atomic payload + fence / read-don't-modify-write formulations |
| `Tassarotti, Dreyer, Vafeiadis` | `DOI: 10.1145/2737924.2737992` | *PLDI 2015* | First weak-memory (`RA`) formal verification of RCU using `GPS` (Ghosts, Protocols, Separation) |
| `Jung et al.` | `DOI: 10.1145/3622827` | *OOPSLA 2023* | Modular Coq/Iris SMR specifications for Hazard Pointers & RCU (Harris list, Harris–Michael list, Chase–Lev deque, RDCSS) |
| `Jung et al.` | `DOI: 10.1145/3729246` | *PLDI 2025* (Distinguished Paper) | Mechanized `iRC11` relaxed-memory verification of general-purpose RCU with RAW SC-fence reasoning & per-node incoming link histories |
| `WG21 / WG14 Standards` | `P2530R3`, `P2545R4`, `N2369`, `P1726`, `P2188` | ISO C++26 `<hazard_pointer>` & `<rcu>`; ISO C/C++ Pointer Lifetime-End Zap | Standardization of Hazard Pointers & RCU; characterization of lifetime-end pointer zap conflicts with SMR |

### Execution Evidence (`2026-11-19`, Linux `7.1.6` x86_64, GCC `-O2 -pthread`, Python 3)

1. **Execution Probe 1 — Live `membarrier(2)` Asymmetric Fence Latency & Boehm-Compliant Atomic-Word `SeqLock`:** Compiled with `gcc -O2 -pthread` using `<stdatomic.h>` and `<linux/membarrier.h>`. Part 1 queried `SYS_membarrier(MEMBARRIER_CMD_QUERY, 0)`, registered `MEMBARRIER_CMD_REGISTER_PRIVATE_EXPEDITED`, timed `10,000,000` `try_protect` loops comparing `atomic_thread_fence(memory_order_seq_cst)` against `atomic_signal_fence(memory_order_seq_cst)`, and timed `1,000` `MEMBARRIER_CMD_PRIVATE_EXPEDITED` syscalls. Part 2 ran a writer pthread performing `500,000` updates `(a = i, b = 3*i + 7)` bracketed by `seq_ver` odd/even stores (`fence(Release)` / `store(Release)`) concurrently with a main-thread reader performing `seq_ver.load(Acquire)` -> relaxed atomic loads of `(a, b)` -> `fence(Acquire)` -> `seq_ver.load(Relaxed)`:
   ```text
   === 1. Linux membarrier(2) asymmetric fence probe ===
   MEMBARRIER_CMD_QUERY bitmask = 0x3ff (PRIVATE_EXPEDITED=YES)
   MEMBARRIER_CMD_REGISTER_PRIVATE_EXPEDITED -> 0 (errno=0)
   try_protect w/ SeqCst fence (10M ops):    7.72 ns/op
   try_protect w/ asymmetric light (10M):    1.23 ns/op (speedup 6.27x)
   heavy membarrier(PRIVATE_EXPEDITED) x1k:  1953.3 ns/call

   === 2. Boehm DRF-compliant atomic-word SeqLock consistency probe ===
   SeqLock reader: consistent_reads=72523 retries=119956 torn_caught_and_discarded=352 torn_escaped=0
   ```

2. **Execution Probe 2 — Formal `LKMM` `rcu-order`, Crossbeam EBR vs. Hazard Pointers Memory Bound, and `MiniRust` Provenance/SeqLock Oracle:** Executed in Python 3, implementing (a) exact dynamic-programming grammar closure of `tools/memory-model/linux-kernel.cat:154-171` `rcu-order` over cyclic rotations of `GP`/`CS` chains, (b) exact 3-epoch `crossbeam-epoch` (`PINNINGS_BETWEEN_COLLECT = 128`, `global_epoch - bag.epoch >= 2`) vs. Hazard Pointers ($P=4$, $K=2$, batch threshold `64`) over `N = 10,000` retirements with and without a stalled reader thread, and (c) exact `MiniRust` `BasicMemory::check_ptr` (`spec/mem/basic.md:197-225`), `compare_ptr` (`operators.md:341-348`), and `ConcurrentMemory::Access::races` (`concurrent.md:164-175`):
   ```text
   === 1. LKMM rcu-order Cycle Forbiddance Probe (linux-kernel.cat L154-171) ===
     1 GP + 1 CS (classic RCU UAF litmus)             -> rb_cycle_forbidden=True
     1 GP + 2 CS (chained readers, insufficient GP)   -> rb_cycle_forbidden=False
     2 GP + 2 CS (alternating GP,CS,GP,CS)            -> rb_cycle_forbidden=True
     2 GP + 2 CS (nested GP,GP,CS,CS)                 -> rb_cycle_forbidden=True
     2 GP + 3 CS (insufficient GPs)                   -> rb_cycle_forbidden=False
     0 GP + 2 CS (no grace period)                    -> rb_cycle_forbidden=False

   === 2. EBR/QSBR (crossbeam-epoch) vs Hazard Pointers Stalled-Reader Bound (N=10,000) ===
     stall_reader=False: EBR_unreclaimed=  143 (epoch=79) | HP_unreclaimed= 16
     stall_reader=True : EBR_unreclaimed=10000 (epoch= 1) | HP_unreclaimed= 18

   === 3. MiniRust Provenance (ABA/Zap) & ConcurrentMemory SeqLock Race Oracle ===
     ABA compare_ptr(p_old, p_new)     -> True (allowed in MiniRust; pointer-zap UB in ISO C)
     ABA check_ptr(p_old, 8)           -> UB: dereferencing pointer to dead allocation AllocId(0) even at reused addr 0x1000
     ABA check_ptr(p_new, 8)           -> OK(AllocId(1))
     SeqLock non-atomic read vs write  -> data_race_UB=True
     SeqLock non-atomic read vs atomic -> data_race_UB=True
     SeqLock atomic byte read vs write -> data_race_UB=False
   ```

## Revalidation

To cheaply test whether these findings still hold against newer kernel, library, or language-model revisions:

1. **LKMM & RCU Axiom Diff:** Diff `torvalds/linux/tools/memory-model/linux-kernel.cat` against commit `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` (specifically `rcu-order`, `rb`, and `data-race`) and re-run `herd7` on the 1-GP/1-CS and 1-GP/2-CS RCU litmus tests (`tools/memory-model/litmus-tests/`).
2. **Crossbeam-Epoch Soundness & Collection Diff:** Diff `crossbeam-rs/crossbeam/crossbeam-epoch/src/internal.rs` against commit `a28f40fdddb70bea8e5faf0efad9af0be4b9dbea` to check whether the `not(miri)` x86 `compare_exchange(..., SeqCst)` hack in `Local::pin()` has been replaced with `asm!` or standard `fence(SeqCst)`, or whether stalled-reader mitigation (e.g., hazard/epoch hybrid eviction) has been introduced.
3. **Folly & C++26 Stdlib Check:** Diff `facebook/folly/folly/synchronization/HazptrHolder.h` and `AsymmetricThreadFence.cpp` against `4b2dd6e1f1dda89dd1b5b71f88ce0ce91ec5c39e`, and re-run the `membarrier(2)` asymmetric-fence and atomic-word SeqLock benchmark (Execution Probe 1 above) on target hardware to measure updated `try_protect` vs. `MEMBARRIER_CMD_PRIVATE_EXPEDITED` break-even ratios.
4. **MiniRust Concurrency & Freeze Spec Diff:** Diff `minirust/minirust/spec/mem/concurrent.md`, `spec/mem/basic.md`, and `spec/lang/step/operators.md` against `063d784186d3252bee242217f218223205c0b568` to check whether `Atomicity` has been extended from SC-only to relaxed/acquire/release memory orders or whether an explicit byte-freeze / `atomic_memcpy` primitive has been formalized for `SeqLock`s.
