# Historical Concurrency, Weak Memory, OS Kernel, Storage, and Distributed Verification Failures and Architectural Lessons for Anneal

## Summary

Historical verification failures across weak-memory compilation, concurrent data
structures, verified operating system kernels, crash-safe storage systems, and
distributed consensus protocols rarely stem from arithmetic errors inside a
proof assistant's kernel. Instead, they arise at five recurring structural
seams:

1. **Non-compositional weak-memory lowering and global optimization assumptions**
   (the C/C++11-to-Power and ARMv7/ARMv8 trailing-sync vs. leading-sync/`stlr`
   compilation bugs exposed by Manerkar et al. at MICRO 2016 and repaired in
   `RC11` by Lahav et al. at PLDI 2017, and the failure of thread-local
   uncapped certification in `Promising 1.0` under global value-range and
   register-promotion optimizations resolved by `Promising 2.0` at PLDI 2020).
2. **Unsynchronized reclamation, aliasing-model mismatches, and unsound
   `Send`/`Sync` trait bounds in concurrent Rust** (`crossbeam-epoch` missing
   `SeqCst` barriers and Stacked/Tree Borrows provenance violations in `#462` /
   `#535`, `std::sync::Arc::get_mut` relaxed-memory synchronization bug exposed
   by *RustBelt Meets Relaxed Memory* at POPL 2020, `RwLockReadGuard` unsound
   `Sync` implementation when `T: Send` in `rust-lang/rust#41622` /
   `CVE-2018-1000810`, and the systemic race and lifetime defects in legacy
   `std::sync::mpsc` that forced its replacement by `crossbeam-channel` in
   `rust-lang/rust#93563`).
3. **Missing memory barriers across hardware-software and guest-host rings**
   (weak-memory deadlocks and data races in Linux kernel `qspinlock`,
   `seqlock`, RCU, and VirtIO split/packed ring `VIRTIO_RING_F_EVENT_IDX`
   notification suppression uncovered on ARM64 and RISC-V by `VSync`, `Herd7` /
   `LKMM`, and `GenMC`).
4. **Unmodeled hardware, boot, DMA/IOMMU, TLB, preemption, and crash-recovery
   boundaries in verified kernels and filesystems** (`seL4`, `CertiKOS`,
   `Komodo`, and `SeKVM` assumptions around bootloader setup, non-coherent
   caches, ARMv8 Break-Before-Make [`BBM`] TLB shootdowns, unmodeled DMA
   channels, speculative execution [`Meltdown`/`Spectre`], `seL4` worst-case
   interrupt latency spikes during `CNode` capability revocation requiring
   explicit preemption points, and `FSCQ` crash-safety bugs found by
   `Yggdrasil` in unverified FUSE bindings and non-idempotent multi-crash
   recovery).
5. **Flawed inductive invariants, unverified wire-marshaling codecs, and SMT
   quantifier instability in distributed systems** (Pamela Zave's Alloy
   refutation of all seven published `Chord` DHT ring invariants under churn,
   the UDP packet serialization bottlenecks in `IronFleet` and `Verdi` that
   motivated `Cheerios`, and Z3 E-matching quantifier instability—the "butterfly
   effect"—that dominated proof maintenance in `IronFleet` and `Chapar`).

This report synthesizes the primary-source root causes of each failure class and
maps their architectural lessons onto Anneal's four `trusted/lean/` primitives:
(1) `Language (SemObs : Type)` + `BehaviorCodec L₁ L₂`, (2) `ProductiveOn` +
`InhabitedPre`, (3) positive per-obligation `VerificationResult`, and
(4) `SmallStepMachine` with `EventualBehaviorOf` + `StepResult.externalCall`.
All seven representative failure mechanisms and their corresponding repairs are
mechanized in a standalone 678-line Lean 4.34.1 artifact
([`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean))
with zero `sorryAx` and zero custom axioms.

---

## Applicability

This report applies to:

- **Anneal (`joshlf/anneal`)** at `trusted-core` revision
  `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` (`trusted/lean/Trusted/Refinement.lean`
  and `trusted/lean/Trusted/StepResult.lean`) and `main` revision
  `24367bd1a8c784f2578535954f9915e24894a56f` (`trusted/lean/Trusted.lean` and
  `trusted/lean/Trusted/Attributes.lean`), together with the four-primitive
  refinement architecture (`Language SemObs` + `BehaviorCodec`, `ProductiveOn` +
  `InhabitedPre`, positive per-obligation `VerificationResult`, and
  `SmallStepMachine` with `EventualBehaviorOf` + `StepResult.externalCall`).
- **Lean 4 (`leanprover/lean4`)** at `v4.34.1`
  (`5045d0056413266e57c625dcd7c365b10e377c52`), used to check the standalone
  canary and repair probe in
  `support/concurrency_systems_failure_canaries_probe.lean`.
- **Rust standard library (`rust-lang/rust`)** at
  `d8ef4f3fe7031514cbd7d056b7b058814987ecec` (`library/core/src/sync/atomic.rs`,
  `library/alloc/src/sync.rs`, and `library/std/src/sync/mpsc/mod.rs`), as a
  normative baseline for Rust's C++20-derived atomic memory model and repaired
  `Arc`, `RwLockReadGuard`, and `mpsc` implementations.
- **Primary research and verification postmortems** identified in `REPORT.json`
  across weak memory (`MICRO 2016`, `PLDI 2017`, `POPL 2020`, `PLDI 2020`,
  `ASPLOS 2021`), verified OS kernels and storage (`seL4/l4v`, `OSDI 2016`), and
  distributed systems (`CCR 2012`, `TSE 2017`, `SOSP 2015`, `PLDI 2015`,
  `POPL 2016`).

The subjects in `REPORT.json` are related by **architectural stress-testing and
defect-mode transfer**: historical failures in upstream compilers, concurrent
libraries, verified kernels, storage systems, and distributed verifiers are
analyzed to derive necessary soundness invariants for Anneal's `trusted/` TCB
and `theory/` proof libraries. Exact mechanized claims in
`support/concurrency_systems_failure_canaries_probe.lean` are finite-state or
inductive abstractions capturing the core counterexample traces and repair
invariants; they do not re-execute full Power/ARMv8 silicon, Linux kernel boots,
or multi-node network clusters.

---

## Findings

### 1. Weak-Memory Model & Atomic Compilation Failures

#### 1.1 C/C++11-to-Power and ARMv7/ARMv8 Atomic Compilation Failures (Manerkar et al. MICRO 2016; Lahav et al. PLDI 2017 `RC11`)

- **Historical Context and "Verified" Premise:**
  Following the formalization of the C/C++11 memory model by Batty et al.
  (*POPL 2011*), two families of compiler mappings for sequentially consistent
  (`memory_order_seq_cst` / `Ordering::SeqCst`) atomics on weakly ordered
  non-multi-copy-atomic architectures (IBM POWER and ARMv7) were widely deployed
  and believed to have been mathematically proven sound:
  1. **Leading-sync mapping** (used by GCC and described by Batty et al.):
     $$\mathsf{Load}_{\mathsf{sc}} \mapsto \texttt{hwsync; ld; cmp; bc; isync} \quad (\text{or } \texttt{dmb; ldr; dmb}), \qquad \mathsf{Store}_{\mathsf{sc}} \mapsto \texttt{hwsync; st}$$
  2. **Trailing-sync mapping** (proposed by McKenney & Silvera and implemented
     in LLVM/Clang for Power and ARMv7):
     $$\mathsf{Load}_{\mathsf{sc}} \mapsto \texttt{ld; cmp; bc; isync} \quad (\text{or } \texttt{ldr; dmb}), \qquad \mathsf{Store}_{\mathsf{sc}} \mapsto \texttt{lwsync; st; hwsync} \quad (\text{or } \texttt{dmb; str; dmb})$$
  Concurrently, ARMv8-A introduced dedicated load-acquire (`LDAR`) and
  store-release (`STLR`) instructions explicitly designed by architects so that
  `STLR` followed by `LDAR` would not reorder, enabling a fence-free mapping:
  $$\mathsf{Load}_{\mathsf{sc}} \mapsto \texttt{LDAR}, \qquad \mathsf{Store}_{\mathsf{sc}} \mapsto \texttt{STLR}$$

- **Technical Root-Cause Analysis:**
  1. **Manerkar et al. (*MICRO 2016*, DOI `10.1109/MICRO.2016.7783747`):**
     Using the `PipeCheck` and `CCICheck` tools, Manerkar et al. discovered two
     distinct classes of counterexamples:
     - **Standalone Trailing-Sync Unsoundness under Original C11 (`R` / `2+2W` /
       `Z6.U` litmus variants):** In the original C11 standard (ISO/IEC
       9899:2011 / 14882:2011), the total sequential consistency order $S$ on
       `SeqCst` operations was only required to be consistent with
       happens-before ($\mathsf{hb}$) and modification order ($\mathsf{mo}$)
       separately, without requiring $S \cup \mathsf{hb}$ or $S \cup \mathsf{eco}$
       to be acyclic across mixed release/acquire and `SeqCst` accesses. Under
       the trailing-sync mapping on Power/ARMv7, a `SeqCst` load has *no*
       leading heavyweight fence (`hwsync`/`dmb`) before the load instruction.
       Consequently, a prior non-`SeqCst` release store (`lwsync; st`) in the
       same thread is not ordered by a full barrier before the `SeqCst` load,
       allowing hardware store buffering and non-multi-copy-atomic write
       propagation to produce an execution forbidden by C11!
     - **The Original Proof Loophole:** Why had earlier hand-written proofs
       claimed trailing-sync was sound? Those proofs assumed a strengthened
       intermediate lemma—that every `SeqCst` store is immediately visible to
       all threads in a global order—or only checked pure `SeqCst` programs
       (DRF-SC) rather than mixed `SeqCst` + `Release`/`Acquire`/`Relaxed`
       programs (`Z6.U`).
     - **ABI Linking Hazard (Mixing Leading-Sync GCC and Trailing-Sync LLVM, or
       ARMv7 `dmb` and ARMv8 `LDAR`/`STLR`):** Even more catastrophically, if
       Thread 1 is compiled with a leading-sync compiler (`hwsync; st` for
       `Store(SeqCst)`) and Thread 2 is compiled with a trailing-sync compiler
       (`ld; isync` for `Load(SeqCst)`), then in the classic Store-Buffering
       (`SB`) litmus test:
       $$\text{Thread 1: } x_{\mathsf{sc}} := 1;\; r_0 := y_{\mathsf{sc}} \qquad \parallel \qquad \text{Thread 2: } y_{\mathsf{sc}} := 1;\; r_1 := x_{\mathsf{sc}}$$
       the compiled code has **zero** `hwsync`/`dmb` barrier *between* the
       `Store(SeqCst)` and the subsequent `Load(SeqCst)`! Both stores stay in
       local store buffers while both loads read $0$, yielding $(r_0 = 0, r_1 = 0)$
       and violating sequential consistency even for purely `SeqCst` programs!
       Similarly, on an ARMv8 processor running mixed ARMv7 (`dmb`) and ARMv8
       (`STLR`/`LDAR`) code—or when `STLR` to $x$ is followed by a relaxed/acquire
       read before `STLR` drains—mixing conventions breaks `SeqCst` restoration.
  2. **Lahav et al. (*PLDI 2017*, `RC11`, DOI `10.1145/3062341.3062352`):**
     Lahav et al. proved an even deeper impossibility result: under the
     published C11 specification (including Batty et al.'s 2016 strengthens),
     **even the standard leading-sync Power mapping (`hwsync` before every
     `SeqCst` access) was unsound** for the `Z6.U` litmus test! Specifically,
     C11 required $\mathsf{hb}$ edges and $\mathsf{mo}$ edges to constrain $S$
     in a way that effectively demanded a heavyweight `hwsync` on *both* sides
     of `SeqCst` accesses when interacting with `Release`/`Acquire` RMW chains.
     To repair this without doubling fence overhead on Power/ARM, Lahav et al.
     defined **RC11 (Repaired C11)**:
     - Weakened the overly strong C11 `SeqCst` axiom to require acyclicity of
       $\mathsf{psc} = \mathsf{psc}_{\mathsf{base}} \cup \mathsf{psc}_{\mathsf{f}}$
       (where $\mathsf{psc}_{\mathsf{base}}$ orders `SeqCst` accesses via
       $\mathsf{hb}|_{\text{same-loc}}$ and $\mathsf{eco}$, and `SeqCst` fences
       $\mathsf{F}_{\mathsf{sc}}$ enforce full cross-location ordering
       $\mathsf{hb}; [\mathsf{F}_{\mathsf{sc}}]; \mathsf{hb}; \mathsf{eco}; \mathsf{hb}; [\mathsf{F}_{\mathsf{sc}}]; \mathsf{hb}$).
     - Strengthened relaxed atomics by forbidding $(\mathsf{po} \cup \mathsf{rf})$
       cycles to rule out basic Out-of-Thin-Air (`OOTA`) executions.

- **Mechanized Canary & Repair in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 150–199), `canary_unrepaired_seqcst_mapping_allows_sb_zero_zero`
  exhibits the buffered `(r0 = 0, r1 = 0)` state when `Store(SeqCst)` followed
  by `Load(SeqCst)` lacks a store-to-load drain invariant, and
  `repaired_rc11_seqcst_mapping_forbids_sb_zero_zero` proves that enforcing the
  `RC11` / ARMv8 store-drain ordering guarantees `r0 = 1 ∨ r1 = 1`.
  `Basis: normative specification + source + execution`.

- **Architectural Lessons for Anneal's 4 `trusted/` Primitives:**
  - **Primitive 1 (`Language SemObs` + `Compiles`):** Separate the axiomatic
    source memory model (`L_RC11 : Language SemObs`) from the target ISA memory
    model (`L_ARMv8 : Language SemObs`). Compiler backend lowering of atomics
    must be certified as a **whole-mapping `Compiles L_RC11 L_ARMv8 codec`**
    theorem rather than per-instruction macro templates, because leading-sync
    and trailing-sync mappings are individually sound for pure `SeqCst` only
    when *every* translation unit in the linked crate uses the *same* convention!
  - **Primitive 4 (`StepResult.externalCall` at FFI/ABI Boundaries):** When a
    Rust crate links against external C/C++ or assembly object files via
    `StepResult.externalCall`, the ABI `boundaryInv` must record the target's
    atomic lowering convention (e.g., ARMv8 `STLR`/`LDAR` vs. ARMv8.3 `STLR`/`LDAPR`
    with `DMB ISH` vs. legacy `DMB` barriers) so incompatible leading/trailing
    sync conventions cannot be silently linked together.

---

#### 1.2 Out-of-Thin-Air (`OOTA`) Values and the `Promising 1.0` to `Promising 2.0` Global Optimization Failure (Kang et al. POPL 2017; Lee et al. PLDI 2020)

- **Historical Context and "Verified" Premise:**
  In C/C++11 and Rust (`Ordering::Relaxed`), allowing hardware and compiler
  load-store reordering on relaxed atomics (`x.load(Relaxed); y.store(42, Relaxed)`)
  while forbidding self-justifying "Out-of-Thin-Air" (`OOTA`) cyclic executions
  (such as Thread 1 executing `r1 = x.load(Relaxed); y.store(r1, Relaxed)` and
  Thread 2 executing `r2 = y.load(Relaxed); x.store(r2, Relaxed)` both producing
  `42` when `x = y = 0` initially) was a 15-year open problem.
  `RC11` solved OOTA by forbidding $\mathsf{po} \cup \mathsf{rf}$ cycles, which
  unfortunately *forbids* load-store reordering (`r1 = x.load(Relaxed); y.store(1, Relaxed)`
  cannot be reordered by the compiler or ARM/Power hardware if $\mathsf{po} \cup \mathsf{rf}$
  acyclicity is enforced!).
  To allow load-store reordering without OOTA, Kang et al. (*POPL 2017*,
  **Promising Semantics 1.0**) introduced an operational model in which a thread
  can *promise* a future relaxed write $(y := 1 \text{ at timestamp } t)$ early,
  provided that at every step the thread can **certify** in a thread-local sequential
  simulation against the current global memory that it will eventually fulfill
  all of its outstanding promises.

- **Technical Root-Cause Analysis (Lee et al. *PLDI 2020*, DOI `10.1145/3385412.3386010`):**
  Lee et al. discovered that **Promising 1.0 is unsound for global compiler
  optimizations**—specifically **Global Value-Range Analysis** and **Register
  Promotion** of non-escaping or single-thread-accessed locations:
  1. **Uncapped Thread-Local Certification Violates Global Invariants:**
     Suppose variable $x$ and $y$ are initially $0$, and across the entire
     program no thread ever writes a value outside $\{0, 1\}$ to $x$ unless it
     first reads $x > 1$. Globally, $x \in \{0, 1\}$ is an inductive invariant!
     However, in `Promising 1.0`, to certify an early promise on $y$, a thread's
     local certification run was allowed to make *new speculative promises* or
     interact with future timestamps unconstrained by the global invariant
     $x \le 1$. If a compiler used Global Value-Range Analysis ($x \le 1$) to
     simplify an `else` branch (`if x > 1 { ... }` $\mapsto$ dead code removal),
     a certification path that relied on the dead branch disappeared in the
     optimized program—or conversely, the optimized program enabled a promise
     certification that was impossible in the source program (`Compiles` failure:
     $\llbracket P_{\text{opt}} \rrbracket_{\text{PS1}} \not\subseteq \llbracket P_{\text{src}} \rrbracket_{\text{PS1}}$)!
  2. **ARMv8 Relaxed RMW Compilation Penalty in `Promising 1.0`:**
     In `Promising 1.0`, compiling a `Relaxed` Read-Modify-Write (`fetch_add(1, Relaxed)`)
     to ARMv8 `ldxr`/`stxr` required inserting an unintended control-dependency +
     `isb` or barrier to prevent promises from bypassing the RMW dependency.
  3. **The `Promising 2.0` Repair:**
     Lee et al. replaced uncapped certification with **capped memory
     certification** (restricting certification runs to a closed/capped view of
     existing memory messages so certification cannot invent unbounded future
     values outside the reachable value range) and introduced **release-sequence
     reservation tokens** that validate fence-free `ldxr`/`stxr` compilation of
     `Relaxed` RMWs on ARMv8.

- **Mechanized Canary & Repair in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 200–224), `canary_promising1_uncapped_promise_breaks_global_range_opt`
  and `promising2_capped_memory_preserves_global_range_opt` mechanize the
  distinction between uncapped promise certification and `Promising 2.0` capped
  certification under a global range invariant $v \le 1$.
  `Basis: documentation + source + execution`.

- **Architectural Lessons for Anneal's 4 `trusted/` Primitives:**
  - **Primitive 1 (`Compiles` Transitivity Across Mid-End & Back-End Passes):**
    In Anneal, a mid-end optimization pass (such as Sub-Domain 3's Global Value
    Numbering, Sparse Conditional Constant Propagation, or Correlated Value
    Propagation `CVP`) and a back-end atomic-lowering pass compose by plain
    preorder transitivity (`Preorder.le_trans` on `Compiles`). If the
    intermediate concurrency `Language` (`L_MIR_WMM`) were instantiated with
    `Promising 1.0`, `CVP` (`Compiles L_MIR_WMM L_MIR_WMM idCodec`) would be
    **unprovable**! Anneal must therefore instantiate its weak-memory `Language`
    either with `RC11` (when forbidding load-store reordering on `Relaxed`
    atomics in exchange for simpler axiomatic reasoning) or with `Promising 2.0` /
    `IMM` (when permitting hardware load-store reordering while preserving sound
    global value-range optimizations).

---

#### 1.3 Real-World Rust Concurrent Data Structure & Reclamation Failures (`crossbeam-epoch`, `std::sync::Arc`, `std::sync::mpsc`, `RwLockReadGuard`, `tokio`, `once_cell`, `arc-swap`)

- **Historical Context and Catalog of Failures:**
  Even in Rust—where safe code statically prevents data races via `Send` and
  `Sync`—the foundational concurrent libraries and standard-library primitives
  implemented in `unsafe` Rust have suffered repeated, high-severity soundness
  failures across three dimensions:
  1. **`crossbeam-epoch` Missing `SeqCst` Barriers, Premature Reclamation, and
     Stacked Borrows Aliasing Violations (`crossbeam-rs/crossbeam` issues `#462`,
     `#535`, and `RUSTSEC-2022-0040` / `CVE-2022-23639`):**
     - *Epoch-Based Reclamation (`EBR`) Barrier & Reclamation Bugs:* In
       `crossbeam-epoch`, a reader thread calling `pin()` writes the current
       global epoch `E` into its thread-local `Local`/`Participant` entry,
       executes a `SeqCst` fence, and then loads `Shared<'g, T>` pointers; a
       reclaimer thread calling `try_advance()` scans all registered
       `Participant` epochs and advances the global epoch (freeing garbage bags
       from 3 epochs prior) only if all pinned threads have caught up.
       Historical soundness audits (`#462`, `#535`, and model-checking with
       `CDSChecker`/`GenMC`/`Loom`) exposed cases where either (a) epoch
       advancement or participant registration/unregistration used `Acquire` /
       `Release` instead of a full `Ordering::SeqCst` fence—allowing Store
       Buffering (`SB`) between a thread pinning its local epoch and another
       thread unlinking and retiring a node—or (b) `clone_into_box` / unaligned
       bag drops (`CVE-2022-23639`) and `Guard::defer_unchecked` caused
       use-after-free or unaligned deallocation.
     - *Stacked Borrows vs. Tree Borrows Provenance Conflicts under `Miri`:*
       In `crossbeam-epoch` (`internal.rs`, `sync/list.rs`, `atomic.rs`), a
       participant thread holds a shared reference `&Local` or `&Collector`
       while concurrent threads or deferred destructors mutate intrusive linked
       list pointers or reclaim the containing struct via raw pointers cast from
       `usize`. Under `Miri`'s **Stacked Borrows** model (Jung et al. *POPL
       2020*), creating an intermediate `&T` or `&mut T` reference eagerly
       asserts exclusive or frozen access over the entire pointee span and pops
       aliased raw-pointer tags from the borrow stack, causing immediate UB
       when another thread or deferred closure accesses the same node. Fixing
       `crossbeam-epoch`, `once_cell`, `arc-swap`, and `tokio`'s intrusive task
       lists required systematically replacing `&mut T` / `&T` round-trips with
       raw pointer projections (`addr_of!`, `addr_of_mut!`, `UnsafeCell::raw_get`)
       and motivated **Tree Borrows** (Villani et al. *PLDI 2025*), which makes
       two-phase borrows and deferred writes lazy until an actual conflicting
       write occurs.
  2. **`std::sync::Arc::get_mut` Relaxed-Memory Synchronization Failure
     (Dang et al. *POPL 2020*, "RustBelt Meets Relaxed Memory", DOI
     `10.1145/3371102`):**
     - While mechanizing the soundness of `std::sync::Arc<T>` in the `iRC11`
       weak-memory separation logic on top of `ORC11`, Dang et al. discovered a
       **real weak-memory data-race bug in Rust's standard library
       `Arc::get_mut`**.
     - Specifically, `Arc::drop` decrements the strong reference count with
       `Ordering::Release` and, only when the strong count reaches `1`, executes
       an `Ordering::Acquire` fence before decrementing the weak count and
       deallocating. However, `Arc::get_mut` (which returns `Some(&mut T)` if
       both `strong == 1` and `weak == 1`) previously checked the strong count
       and weak count using `Ordering::Acquire` on the weak count *without*
       synchronizing with prior `Weak::drop` calls that had decremented the weak
       count using `Ordering::Release`! Under weak memory (`RC11` / ARMv8 /
       Power), a thread calling `Arc::get_mut` could obtain `&mut T` and write
       to `T` *without* a happens-before edge from a concurrent thread that had
       just inspected the `Weak` pointer and dropped it, causing a C11/Rust
       weak-memory race (`rust-lang/rust#51780`).
  3. **`RwLockReadGuard` and `MutexGuard` Unsound `Send`/`Sync` Bounds
     (`rust-lang/rust#41622`, `CVE-2018-1000810`):**
     - In Rust `< 1.26.0`, `std::sync::RwLockReadGuard<'a, T>` had:
       ```rust
       unsafe impl<'a, T: ?Sized + Sync> Sync for RwLockReadGuard<'a, T> {} // Correct
       // BUG in std: previously lacked `T: Sync` or allowed `Send`/`Sync` mismatch!
       ```
       Specifically, `RwLockReadGuard<'a, T>` implemented `Sync` without
       requiring `T: Sync` (or `MutexGuard<T>` implemented `Sync` when `T: Send`
       instead of `T: Sync`). Because `RwLockReadGuard<'a, T>` implements
       `Deref<Target = T>`, sharing `&RwLockReadGuard<'a, Cell<i32>>` across two
       threads allowed both threads to call `Deref::deref` concurrently and
       obtain two unsynchronized `&Cell<i32>` references to the same memory,
       triggering an immediate non-atomic data race (`Cell::set`) in 100% safe
       Rust!
  4. **Legacy `std::sync::mpsc` Soundness and Race Failures Leading to Complete
     Replacement (`rust-lang/rust#39364`, `#27700`, replaced in PR `#93563`):**
     - Rust's original `std::sync::mpsc` channel implementation attempted to
       dynamically upgrade a single-producer queue (`oneshot` $\to$ `stream`
       $\to$ `shared` multi-producer queue) in place. That state-machine upgrade
       protocol contained decades-long use-after-free, lost-wakeup, and
       dangling-pointer bugs (`#39364`: race condition during `shared` upgrade
       dropping messages or freeing an active queue while a sender was still
       enqueuing). After years of failed point fixes, `rust-lang/rust#93563`
       (Rust 1.67) deleted the entire legacy `mpsc` implementation and replaced
       it with `crossbeam-channel` (`std::sync::mpmc`).

- **Mechanized Canaries & Repairs in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 226–308):
  - `canary_epoch_pin_without_seqcst_allows_uaf` and
    `repaired_epoch_pin_seqcst_prevents_uaf` mechanize the `crossbeam-epoch`
    Store-Buffering reclamation race and prove that the `SeqCst` barrier
    eliminates `.failed .ub`.
  - `canary_rwlock_read_guard_send_only_permits_data_race` and
    `repaired_rwlock_read_guard_requires_t_sync` mechanize the
    `rust-lang/rust#41622` guard trait-bound bug and its repair.
  `Basis: normative specification + source + execution`.

- **Architectural Lessons for Anneal's 4 `trusted/` Primitives:**
  - **Primitive 4 (`SmallStepMachine` with Allocator Provenance + Weak-Memory
    Views + Tree Borrows):**
    Fraction arithmetic on reference counts (`count == 0` $\implies$ safe to
    free) is **unsound** under weak memory unless the reclaiming thread's view
    covers all prior accesses in every thread that held a fraction! In Anneal's
    `trusted/lean/` memory model (`MemState` in `Trusted/Memory.lean`),
    deallocation (`free` / `StorageDead`) must check that the deallocating
    thread's `curView` dominates both `naWriteTs loc` and `naReadTs loc` (matching
    `ORC11`'s `drf_pre_dealloc` rule), so missing `Acquire` fences in
    `Arc::drop` / `Arc::get_mut` or missing `SeqCst` fences in `crossbeam-epoch`
    immediately transition to `StepResult.failed .ub`.
  - **Primitive 4 (`StepResult.externalCall` for `unsafe impl Send / Sync` Soundness):**
    When a crate writes `unsafe impl<T: Send> Sync for MyGuard<T>`, Anneal must
    not treat `Send` and `Sync` as uninterpreted syntactic marker traits.
    Instead, `unsafe impl Sync for G` generates a positive semantic obligation
    in `VerificationResult` requiring that two concurrent threads holding
    shared `&G` references across `StepResult.externalCall` boundaries satisfy
    `ProductiveOn` (zero `.failed .ub` data races in `MemState`).

---

#### 1.4 Linux Kernel `qspinlock`, `seqlock`, `RCU`, and `VirtIO` Weak-Memory Failures (`VSync` ASPLOS 2021, `Herd7`/`LKMM`, `GenMC`)

- **Historical Context and Catalog of Failures:**
  Operating system kernels and hypervisor I/O rings aggressively avoid
  full memory barriers (`smp_mb()` / `dmb ish`) on hot paths, relying instead on
  asymmetric `Acquire`/`Release` pairs, control dependencies, and address
  dependencies. Automated weak-memory model checkers—specifically **VSync**
  (Oberhauser et al. *ASPLOS 2021*, DOI `10.1145/3445814.3446748`), **Herd7 /
  LKMM** (Alglave et al. *ASPLOS 2018*), and **GenMC** (Kokologiannakis &
  Vafeiadis *CAV 2021*)—uncovered critical correctness and liveness failures in
  production C and Rust systems code:
  1. **VirtIO Split/Packed Ring `VIRTIO_RING_F_EVENT_IDX` Lost-Wakeup Deadlock:**
     - In VirtIO split virtqueues (`drivers/virtio/virtio_ring.c` and Rust
       `virtio-drivers` / `vhost`), to avoid an expensive VM-exit doorbell kick
       on every packet, `VIRTIO_RING_F_EVENT_IDX` lets the host device publish
       `used_event` (the descriptor index at which it wants to be notified) in
       shared memory, while the guest driver publishes `avail.idx`.
     - **The Bug:** The guest driver writes `avail.idx = K` and then reads
       `used_event` to decide whether to kick; concurrently, the host VMM reads
       `avail.idx`, sees no new work, writes `used_event = K` to request a
       wakeup on the next packet, and goes to sleep. This is a textbook
       **Store-Buffering (`SB`)** pattern across guest-host shared memory! If
       either side omits a full `smp_mb()` (`fence(Ordering::SeqCst)` / `dmb ish`)
       between its store and its load—or uses only `smp_wmb()` (`dmb ishst`,
       which orders stores only with stores)—both stores sit in the respective
       CPU store buffers while both loads read the old values: the guest suppresses
       the kick *and* the host goes to sleep, causing a permanent I/O hang
       under high load on ARM64 and RISC-V.
  2. **Linux `qspinlock`, DPDK MCS Lock, and `seL4` CLH Lock Bugs Found by
     `VSync` (*ASPLOS 2021*):**
     - Applying `VSync`'s Adaptive Linear Relaxation (`ALR`) and Await Model
       Checking (`AMC`) under `IMM` / ARMv8 memory models to industrial locks:
       - In **seL4's user-space CLH lock (`libsel4sync`)** and **DPDK's MCS
         lock**, `VSync` discovered missing acquire/release barriers in lock
         handoff and node recycling that permitted critical-section instructions
         from two threads to overlap on ARM64 (mutual-exclusion violation) or
         caused an awaiting thread's spin loop to read a stale predecessor state
         forever (liveness/hang bug).
       - In the **Linux kernel queued spinlock (`qspinlock`)** on ARM64, weak
         ordering between setting the tail pointer via relaxed/release atomics
         and reading the previous holder's locked byte required careful
         `smp_cond_load_acquire` / `atomic_fetch_or_acquire` pairing; historical
         revisions of `qspinlock` suffered from tail-update vs. unlock races
         caught by `Herd7` (`LKMM`) litmus tests.
  3. **`seqlock` (`read_seqbegin` / `read_seqretry`) Reader-Writer Reordering:**
     - In a sequential lock (`Seqlock<T>`), a reader loads an even sequence
       number `seq1 = seq.load(Acquire)`, reads the payload fields `data`, and
       then checks `seq.load(Acquire) == seq1`. Two classic bugs recur in C and
       Rust `seqlock` implementations:
       - **Missing Trailing Read Barrier (`smp_rmb()`):** An `Acquire` load on
         the *second* `seq` check orders *subsequent* accesses after `seq2`, NOT
         *prior* reads of `data` before `seq2`! Without an explicit
         `fence(Ordering::Acquire)` (or `smp_rmb()`) *between* reading `data`
         and reading `seq2`, the CPU or compiler can reorder the read of `data`
         to occur *after* `seq2 == seq1` succeeds, observing torn writer data!
       - **Non-Atomic Reader Data Race UB in C11/Rust:** Even if `seq2 != seq1`
         causes the reader to discard the torn read and retry, in C11 and Rust's
         memory model a concurrent non-atomic read of `data` racing with a
         writer's write is **immediate Undefined Behavior (`StepResult.failed .ub`)**
         before `seq2` is even checked! Sound Rust `Seqlock<T>` implementations
         must therefore perform the optimistic payload read using atomic byte/word
         loads (`AtomicUsize::load(Relaxed)` or `read_volatile` only if mapped
         outside standard non-atomic aliasing rules).

- **Mechanized Canary & Repair in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 310–355), `canary_virtio_event_idx_missing_mb_deadlocks` proves that
  omitting `smp_mb()` on either side of the VirtIO `EVENT_IDX` handshake admits
  the `virtioDeviceAwake = false` lost-wakeup state, while
  `repaired_virtio_event_idx_smp_mb_prevents_lost_wakeup` proves that
  bidirectional `smp_mb()` guarantees `virtioDeviceAwake = true`.
  `Basis: documentation + source + execution`.

- **Architectural Lessons for Anneal's 4 `trusted/` Primitives:**
  - **Primitive 2 (`ProductiveOn` + `InhabitedPre`) & Primitive 4 (`EventualBehaviorOf`):**
    Notice how `VSync`'s Await Model Checking (`AMC`) distinguishes **safety**
    (mutual exclusion) from **await-loop termination** (no lost wakeups or
    spin-loop livelock under fair memory propagation). In Anneal, because
    `Partial.ub` is the top element and `EventualOut.diverges` is distinct from
    `.terminated`, a lost wakeup in `VirtIO` or `qspinlock` manifests either as
    an explicit deadlock state (`StepResult.failed .error`) or as an infinite
    spin loop (`EventualOut.diverges`). Parameterizing `Query := InitState × FairPropagationSchedule`
    with `InhabitedPre pre` and proving that `.diverges` is excluded from
    `(L.sem prog q).val` verifies both barrier safety and spin-loop liveness
    within Anneal's existing four primitives!

---

### 2. Verified OS Kernel, Hypervisor, and Crash-Safe Storage Boundary Failures

#### 2.1 Unverified Boot, Cache/TLB Maintenance, ARMv8 Break-Before-Make (`BBM`), and Unmodeled DMA/IOMMU Assumptions (`seL4`, `CertiKOS`, `Komodo`, `SeKVM`)

- **Historical Context and "Verified" Premise:**
  Landmark formally verified kernels and hypervisors—including **seL4** (`seL4/l4v`
  in Isabelle/HOL, Klein et al. *SOSP 2009* / *TOCS 2014*), **CertiKOS** (Gu et
  al. *OSDI 2016* in Coq + CompCert), **Komodo** (Ferrell et al. *SOSP 2017*
  verified ARM TrustZone monitor in Dafny), and **SeKVM** (Li et al. *USENIX
  Security 2021* verified Linux KVM hypervisor in Coq)—proved full functional
  correctness (`Abstracts` / refinement from C/assembly to an abstract state
  machine) and information-flow non-interference. Yet postmortems and boundary
  audits across all four systems revealed that the primary security and
  correctness failures occurred *at the boundary between the idealized hardware
  model and the physical SoC*:
  1. **Unverified Bootloader and Early MMU Turn-On Code:**
     In `seL4` (`seL4/l4v` at `6b4076aeb35f7803b7c232963e5f996545e3acb5`) and
     early `CertiKOS`/`SeKVM`, the main refinement theorem assumes the kernel
     starts in a post-boot state satisfying a complex global invariant
     (`invs s₀`: disjoint physical frames, valid initial kernel page tables,
     properly initialized capability derivation tree). The ELF loader, initial
     identity-to-high-virtual-address MMU switch, and `.bss`/stack setup were
     originally outside the proof boundary; overlapping linker-script regions or
     missing identity-map TLB invalidations after enabling paging could corrupt
     the initial state before the verified C entry point ever ran (rendering the
     precondition `invs s₀` false!).
  2. **TLB Shootdown Coherence and ARMv8 Break-Before-Make (`BBM`) Faults:**
     Functional kernel specifications model address translation as a pure
     mathematical function $\mathsf{translate}(\mathsf{CR3}/\mathsf{TTBR}, \mathit{va})$
     reading current RAM page tables. On real hardware:
     - **Stale Multi-Core TLB Entries:** When Core A unmaps or downgrades a Page
       Table Entry (`PTE`) and frees the backing physical frame to the kernel
       allocator, Core B's hardware Translation Lookaside Buffer (`TLB`) and
       intermediate paging-structure caches (`PWC`) may retain the old mapping
       until an Inter-Processor Interrupt (`IPI`) shootdown (`invlpg` on x86-64;
       `dsb ishst; tlbi vae1is; dsb ish; isb` on ARMv8-A) completes. Reallocating
       the physical frame before the `tlbi` + `dsb ish` barrier completes creates
       a catastrophic Use-After-Free in physical memory.
     - **ARMv8 Break-Before-Make (`BBM`):** The ARMv8-A architecture reference
       manual mandates that when changing a valid translation's block size (e.g.,
       splitting a 2 MiB huge page into 4 KiB pages or coalescing them), output
       physical address, or cacheability attributes, software *must* first write
       an invalid descriptor (`0`), execute `dsb` + `tlbi` + `dsb`, and only
       then write the new valid descriptor. Overwriting one valid descriptor
       directly with another (which is completely legal in an idealized Coq/Isabelle
       page-table map!) causes the ARMv8 MMU to raise a synchronous hardware
       **TLB Conflict Abort** when multiple TLB entries match the same VA!
  3. **Unmodeled Direct Memory Access (`DMA`), IOMMU/SMMU Bypass, and Non-Coherent
     Caches:**
     CPU-only kernel models assume that physical memory changes only when a CPU
     core executes a store instruction. In reality, PCIe and platform DMA
     controllers read and write physical RAM asynchronously:
     - Without a formally verified **IOMMU / Arm SMMU** page-table configuration
       (as added in `SeKVM` and `seL4`'s VT-d / SMMU extensions), any user-space
       driver granted MMIO access to a DMA-capable device can instruct the
       device to overwrite kernel code or capability tables in physical RAM,
       completely bypassing CPU MMU isolation.
     - On non-cache-coherent ARM/RISC-V buses, CPU caches are not snooped by DMA
       masters. If the kernel or driver fails to clean dirty CPU cache lines
       (`dc cvac`) before starting a device DMA read—or fails to invalidate
       speculative CPU cache lines (`dc ivac`) before reading a completed DMA
       receive buffer—the CPU observes stale data or evicts dirty cache lines on
       top of incoming DMA bytes.

- **Mechanized Canary & Repair in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 357–398), `canary_bbm_violation_or_rogue_dma_triggers_ub` and
  `repaired_external_call_boundary_inv_blocks_rogue_dma_and_bbm` mechanize how
  encoding ARMv8 `BBM` (`!(oldPteValidInTlb && writingNewIncompatiblePte)`) and
  DMA-borrow disjointness (`!dmaRangeOverlapsActiveCpuBorrow`) inside
  `StepResult.externalCall boundaryInv` turns unmodeled hardware hazards into
  explicit `.failed .ub` obligations.
  `Basis: normative specification + source + execution`.

---

#### 2.2 Speculative Execution Side Channels (`Meltdown`/`Spectre`) vs. Architectural ISA Non-Interference Proofs

- **Historical Context and "Verified" Premise:**
  Both `seL4` (Murray et al. *IEEE S&P 2013*) and `CertiKOS` / `Komodo` proved
  machine-checked **information-flow non-interference** (confidentiality) at the
  ISA/C level: secret kernel data or high-security partition state cannot
  influence any architectural observation (`obs`) of an unprivileged user
  process.
- **Technical Root-Cause Analysis (`Meltdown` CVE-2017-5754 & `Spectre` CVE-2017-5753 / CVE-2017-5715):**
  In 2018, `Meltdown` and `Spectre` demonstrated that **every one of those
  verified confidentiality theorems could be bypassed on physical x86-64 and
  ARMv8 out-of-order cores**:
  - In the formal ISA model (`L_isa`), a user-mode load from a supervisor-only
    kernel virtual address traps immediately (`StepResult.terminated` / fault
    handler), never loading the secret byte into a register. On Intel and ARM
    Cortex-A75 cores (`Meltdown`), the load transiently forwarded the secret
    kernel byte from the L1 data cache to a dependent array load
    `probe_array[secret * 4096]` before retirement aborted the faulting
    instruction—leaving a secret-dependent footprint in the microarchitectural
    L1 cache state that user space recovered via `rdtsc` timing (`Flush+Reload`).
  - Similarly, `Spectre-v1` (bounds-check bypass) and `Spectre-v2` (branch
    target injection) caused speculative execution inside verified kernel
    syscalls to fetch secret-indexed cache lines along mispredicted branches
    that were architecturally dead in `L_isa`!
  - Defending `seL4` and Linux required Kernel Page-Table Isolation (`KPTI`,
    unmapping kernel memory while in user mode), speculative store-bypass and
    branch-predictor barriers (`lfence` / `csdb` / `sb`), and cycle/cache-flushing
    partition switches (`seL4` time-protection / `SwitchTo` cache-flush proof
    extensions by Ge et al. *EuroSys 2019*).
  `Basis: documentation + derived`.

---

#### 2.3 `seL4` Worst-Case Interrupt Latency Proofs and Explicit Preemption Points in Capability Revocation (`Blackham et al. RTSS 2011`)

- **Historical Context and Technical Root Cause:**
  To make formal verification of the C implementation tractable without general
  fine-grained kernel lock concurrency, `seL4` executes with **interrupts
  disabled inside kernel mode** (the big-kernel-lock / non-preemptible syscall
  model). While most microkernel fastpath syscalls (`seL4_Call`, `seL4_ReplyRecv`)
  execute in $O(1)$ instructions ($\sim 200$ cycles), **capability revocation
  (`seL4_CNode_Revoke`, `seL4_CNode_Delete`)** and untyped memory retyping must
  recursively traverse and destroy an arbitrarily large Capability Derivation
  Tree (`CDT`) of child capabilities!
  - When Blackham et al. (*RTSS 2011*, *"Timing Analysis of a Protected
    Operating System Kernel"*) and Sewell et al. (*RTAS 2017*) attempted to
    prove a hard real-time **Worst-Case Interrupt Latency (WCIL)** bound for
    `seL4`, they found that an unbounded `CNode_Revoke` loop with interrupts
    masked blocked timer and device interrupts for milliseconds, violating
    hard-real-time deadlines!
  - **The Repair (`preemptionPoint`):** `seL4` had to insert explicit
    **preemption points (`preemptionPoint()`)** inside every recursive step of
    `revoke` and `finaliseSlot`. At each `preemptionPoint()`, the kernel checks
    the hardware interrupt controller for a pending IRQ; if an IRQ is pending,
    the kernel **aborts the syscall mid-traversal** in a consistent intermediate
    invariant state (`invs`), returns an internal restart status so the user-space
    `CNode_Revoke` instruction will re-execute from the current program counter
    after the interrupt is serviced, and unmasks interrupts! Proving that every
    intermediate step before `preemptionPoint()` restores the full global kernel
    invariant (`invs`) and strictly decreases a well-founded measure of
    remaining `CDT` nodes became one of the most intricate parts of the entire
    `seL4/l4v` proof corpus.
  `Basis: documentation + source`.

---

#### 2.4 Crash-Safe Storage Failures: `FSCQ` vs. `Yggdrasil`, Unverified FUSE Bindings, and Non-Idempotent Recovery (`OSDI 2016`)

- **Historical Context and Technical Root Cause:**
  - **FSCQ** (Chen et al. *SOSP 2015*, *"Using Crash Hoare Logic for Certifying
    the FSCQ File System"*) was the first filesystem with a machine-checked Coq
    proof of crash safety, extracted from Coq to Haskell and mounted via
    Haskell-to-C **FUSE** (`Filesystem in Userspace`) bindings.
  - One year later, **Yggdrasil** (Sigurbjarnarson et al. *OSDI 2016*,
    *"Push-Button Verification of File Systems via Crash Refinement"*) introduced
    SMT-based **Crash Refinement** (verifying in Z3 that the set of post-crash +
    recovery disk images of an implementation is a subset of the atomic
    specification's disk images) and audited both `FSCQ`/`DFSCQ` and Linux
    filesystems (`ext4`, `btrfs`), exposing three critical failure modes:
    1. **Bugs in `FSCQ`'s Unverified Haskell/C FUSE Glue:** Because `FSCQ`
       verified its core logic in Coq but trusted the extracted Haskell runtime
       and FUSE C bindings, `Yggdrasil` authors and subsequent audits found bugs
       at the FUSE marshaling boundary (such as integer width mismatches, path
       resolution / error-code translation discrepancies, and FUSE callback
       panics when user-space passed out-of-range offsets that violated implicit
       preconditions of the extracted Haskell code).
    2. **Volatile Disk Write-Cache Reordering (`Flush` / `FUA` Omissions):**
       Naive crash models assume that if a program issues disk block writes
       $W(b_1), W(b_2)$ sequentially, a power failure leaves a *prefix* of those
       writes on disk. In reality, modern NVMe/SATA SSD controllers and OS block
       layers reorder uncommitted volatile write-cache blocks arbitrarily unless
       fenced by an explicit `SYNCHRONIZE CACHE` / `FLUSH` or Force Unit Access
       (`FUA`) barrier (`clwb` + `sfence` on persistent memory `Px86`/`PArm`). A
       write-ahead log that writes its commit header block $b_{\text{commit}}$
       without a prior barrier before flushing its log data blocks $b_{\text{data}}$
       can crash with $b_{\text{commit}}$ persisted on disk while $b_{\text{data}}$
       is lost—causing recovery to replay garbage blocks into the filesystem!
    3. **Non-Idempotent Recovery Under Nested Crashes During `recover()`:**
       Even if a recovery routine `recover()` is proven correct against a
       *single* crash during normal execution, a **second power loss occurring
       in the middle of running `recover()`** will corrupt the disk if
       `recover()` mutates metadata or log entries non-idempotently before
       clearing the log commit flag!

- **Mechanized Canary & Repair in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 400–448), `canary_nested_crash_during_non_idempotent_recovery_corrupts_disk`
  proves that a delta-based WAL recovery routine interrupted by a second crash
  applies the log delta twice (`10 + 5 + 5 = 20 ≠ 15`), while
  `repaired_idempotent_wal_recovery_survives_nested_crashes` proves that
  idempotent physical-state recovery converges to the exact same disk state
  across nested crashes (`repairedRecoverComplete (repairedRecoverInterruptedOnce d) = repairedRecoverComplete d`).
  `Basis: documentation + source + execution`.

- **Architectural Lessons for Anneal's 4 `trusted/` Primitives (Kernel & Storage):**
  - **Primitive 1 (`Language SemObs` with Microarchitectural Leakage `Obs`) &
    Primitive 4 (`SmallStepMachine`):**
    `Meltdown`/`Spectre` and `seL4` WCIL prove that when security or real-time
    latency matters, `Obs` in `SmallStepMachine` cannot be restricted to coarse
    syscall return values. Instantiating `Obs` with microarchitectural events
    (`UArchEvent`: `.pcStep`, `.memReadAddr`, `.cacheLineFetch`) and step-count
    ticks between `preemptionPoint` yields constant-time/leakage preservation and
    bounded interrupt latency directly via `Abstracts` and `Compiles`.
  - **Primitive 2 (`InhabitedPre pre` + `ProductiveOn`) for Boot & Linker State:**
    To prevent the "unverified bootloader assumption" trap where a kernel proof
    assumes an unreachable or violated post-boot invariant `invs s₀`, Anneal
    requires `InhabitedPre pre` (`∃ q, pre q`) and composes the ELF boot stub
    (`elfBootInit`) directly with `main` via `Compiles`/`Abstracts` (as mechanized
    in `canary_uninhabited_pre_vacuously_satisfies_ub_prog` and
    `inhabited_pre_and_productive_on_guarantee_witness` at lines 570–596 of
    `support/concurrency_systems_failure_canaries_probe.lean`).
  - **Primitive 4 (Multi-Crash Closure Inside `SmallStepMachine`):**
    By modeling power failure + volatile disk-buffer subset selection + jump to
    `recover()` as a demonic transition (`StepResult.choice .demonic`) enabled at
    *every* instruction step—**including inside `recover()` itself**—Anneal's
    `EventualBehaviorOf` and `Abstracts` automatically enforce recovery
    idempotence across arbitrary $k \ge 1$ nested crashes without adding any
    storage-specific primitives to `trusted/lean/`.

---

### 3. Distributed System Verification Failures (`Chord`, `IronFleet`, `Verdi`, `Chapar`)

#### 3.1 Pamela Zave's Alloy Refutation of the `Chord` Distributed Hash Table Protocol (`CCR 2012` / `IEEE TSE 2017`)

- **Historical Context and "Verified" Premise:**
  The **Chord** distributed hash table (Stoica et al. *SIGCOMM 2001* / *IEEE/ACM
  ToN 2003*, and Liben-Nowell, Balakrishnan, & Karger *PODC 2002*, which won top
  systems awards and over 15,000 citations) was famous for being accompanied by
  five mathematical theorems and seven published invariants claiming to prove
  that Chord's asynchronous periodic ring-maintenance operations (`join`,
  `stabilize`, `notify`, `fix_fingers`, and successor-list failure recovery
  `rectify`) guarantee **eventual reachability and single-ring connectivity**
  under concurrent node joins and failures (churn).
- **Technical Root-Cause Analysis (Pamela Zave, *ACM SIGCOMM CCR 2012* DOI
  `10.1145/2185376.2185383` & *IEEE TSE 2017* DOI `10.1109/TSE.2017.2655056`):**
  When Pamela Zave formalized the official Chord protocol pseudocode and failure
  assumptions in the **Alloy** relational model checker (checking bounded scopes
  of up to 6 nodes and successor list length $r$), the Alloy Analyzer found
  counterexample traces refuting **every single one of the seven published
  invariants**:
  1. **Ring Partition into Disjoint Sub-Rings ("Loopy" and Split Rings):**
     In a small network where node $A$ joins via node $B$ while node $C$ fails
     and `stabilize`/`notify` messages interleave with successor-list Failover,
     the ring can permanently split into **two disjoint cycles** (e.g., node $0$
     pointing to itself $0 \to 0$ while nodes $1 \leftrightarrow 2$ form a
     separate 2-cycle, or two 2-cycles in a 4-node network) from which `stabilize`
     can *never* recover!
  2. **Why the Original Paper Proofs Failed:**
     The original hand-written proofs reasoned locally ("every live node $n$
     maintains a valid live `successor` pointer in its successor list, and
     `stabilize` moves `predecessor` closer in identifier order") and implicitly
     assumed that local pointer validity implies global graph connectivity. As
     Zave proved in *IEEE TSE 2017* (*"Reasoning About Identifier Spaces: How to
     Make Chord Correct"*), local degree/ordering properties on a circular
     identifier space $\mathbb{Z}_{2^m}$ do *not* rule out multiple disjoint
     cycles or multi-winding "loopy" rings unless the protocol maintains a global
     **structured ring invariant** anchored by a minimum permanent/stable base of
     $r + 1$ nodes and a unified atomic `stabilize-from-successor-list` transition.

- **Mechanized Canary in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 450–482), `canary_chord_local_bijection_allows_partitioned_subrings`
  mechanizes a concrete 3-node Chord state (`0 → 0`, `1 → 2 → 1`) that satisfies
  the local bijective successor/predecessor invariant (`everyNodeHasValidSucc = true`)
  while violating global single-ring connectivity (`isConnectedSingleRing = false`).
  `Basis: documentation + source + execution`.

---

#### 3.2 `IronFleet`, `Verdi`, and `Chapar` Postmortems: The Marshaling Bottleneck (`Cheerios`) and Z3 Quantifier Instability ("The Butterfly Effect")

- **Historical Context and "Verified" Systems Examined:**
  - **IronFleet** (Hawblitzel et al. *SOSP 2015*, DOI `10.1145/2815400.2815428`):
    Verified a Multi-Paxos replicated state machine (`IronRSL`) and sharded
    key-value store (`IronKV`) in **Dafny** (backed by Z3), combining TLA+-style
    global protocol refinement with Floyd-Hoare imperative verification of
    single-node handlers compiled to C#/.NET.
  - **Verdi** (Wilcox et al. *PLDI 2015*, DOI `10.1145/2737924.2737958`; Woos et
    al. *CPP 2016*): Verified the **Raft** consensus protocol in **Coq** using
    Verified System Transformers (`VST`s) and extracted executable OCaml code.
  - **Chapar** (Lesani, Bell, & Chlipala *POPL 2016*, DOI `10.1145/2837614.2837622`):
    Verified causally consistent distributed key-value store algorithms in **Coq**
    with an operational causal-consistency interface extracted to OCaml.

- **Technical Root-Cause Analysis of Engineering & Boundary Failures:**
  1. **The Packet Serialization / Marshaling Bottleneck (Motivating `Cheerios`):**
     - In early **Verdi** (and **Chapar**), the Coq proof verified the abstract
       protocol state transitions over algebraic `Msg` inductive types, while
       the extracted OCaml shim originally relied on OCaml's unverified
       `Marshal.to_bytes` / `Marshal.from_bytes` (or slow s-expression text
       parsers) to convert `Msg` values to UDP wire packets!
     - Relying on unverified `Marshal.from_bytes` on untrusted network sockets
       is a **remote code execution / memory-safety vulnerability** (malformed
       network bytes crash or corrupt the OCaml runtime) and violates the
       refinement assumption that wire deserialization is a partial inverse of
       serialization ($\mathsf{deserialize}(\mathsf{serialize}(m)) = \mathsf{Some}(m)$).
       Conversely, in **IronFleet**, proving in Dafny/Z3 that recursive packet
       parsing and marshaling routines over byte sequences refined abstract message
       types consumed a disproportionate fraction of total proof lines and runtime
       CPU overhead (until `IronFleet` optimized UDP buffer pinning and the UW
       PLSE group developed **Cheerios**—a formally verified, compositional Coq
       serialization library enforcing prefix-free bit/byte stream round-trip
       theorems).
  2. **Z3 SMT Quantifier Instantiation Instability ("The Butterfly Effect"):**
     - In **IronFleet** (and subsequent Dafny/F*/Verus systems later studied in
       **Mariposa** [Zhou et al. *OSDI 2023*]), verification conditions for
       distributed protocols heavily nest universal and existential quantifiers
       over unbounded message histories, sequence slices (`s[..i] + s[i..]`),
       and quorum sets.
     - Because Z3 instantiates universally quantified axioms via heuristic
       **E-matching triggers**, the authors of `IronFleet` documented a severe
       proof-engineering failure mode they termed **solver instability / the
       butterfly effect**: renaming a local variable, reordering two `assert`
       statements, or adding a field to a struct in an unrelated module changes
       Z3's internal term-graph (`e-graph`) ordering and random/tie-breaking
       heuristics, causing a proof that previously verified in 2 seconds to
       trigger an exponential E-matching matching loop and time out after 60+
       seconds!
     - To survive Z3 instability, `IronFleet` had to wrap recursive definitions
       in `opaque` attributes (hiding bodies from Z3 until explicitly revealed
       via `reveal_Foo()`), manually tune `{:trigger ...}` annotations on every
       quantifier, and split proofs into isolated helper lemmas.
  3. **Extraction & Runtime Garbage-Collection Tail-Latency Spikes:**
     - Both `IronFleet` (compiling Dafny $\to$ C# on the .NET CLR) and `Verdi` /
       `Chapar` (extracting Coq $\to$ OCaml) suffered from unverified runtime
       garbage collection pauses and excessive heap allocation when copying
       immutable protocol history sequences, motivating zero-copy mutable Rust
       implementations (as subsequently explored in `Verus` / `IronSync` and
       targeted natively by Anneal).

- **Mechanized Canaries & Repairs in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 484–569):
  - `canary_non_injective_packet_serializer_collides` and
    `repaired_length_prefixed_roundtrip` mechanize how a naive concatenation
    serializer maps two distinct messages `⟨[1], [2, 3]⟩ ≠ ⟨[1, 2], [3]⟩` to the
    same wire packet `[1, 2, 3]` (violating `BehaviorCodec`'s bijection law),
    and prove that a length-prefixed `Cheerios`-style serializer satisfies exact
    round-trip invertibility (`repairedDeserializeLengthPrefixed (repairedSerializeLengthPrefixed m) = some m`).
  - `canary_antecedent_verification_result_explodes_on_false_assumption` and
    `positive_verification_result_isolates_waived_obligation` prove that
    Anneal's positive per-obligation `VerificationResult` completely isolates a
    waived or timed-out SMT obligation (`obWaived`) so it can never contaminate
    or vacuously discharge any other verified obligation (`obSafe.prop`).
  `Basis: documentation + source + execution`.

- **Architectural Lessons for Anneal's 4 `trusted/` Primitives (Distributed Systems):**
  - **Primitive 1 (`BehaviorCodec` Partial-Bijection Law Enforces Wire-Format
    Soundness):**
    Look at the two round-trip laws in Anneal's `BehaviorCodec L_abstract L_wire`:
    $$\mathsf{decodeOut}(\mathsf{encodeOut}(o_1)) = \mathsf{some}\;o_1 \qquad \text{and} \qquad \mathsf{decodeOut}(o_2) = \mathsf{some}\;o_1 \implies \mathsf{encodeOut}(o_1) = o_2$$
    These two equations in `trusted/lean/` **are literally the `Cheerios` /
    `zerocopy` wire-format soundness specification**! Any non-injective serializer
    (where $m_1 \ne m_2$ serialize to the same wire bytes) makes it impossible to
    instantiate `BehaviorCodec`, structurally preventing `Verdi`/`IronFleet`
    marshaling bugs at the type-checking boundary!
  - **Primitive 3 (Positive Per-Obligation `VerificationResult` + Kernel
    Certificate Checking Defeats the Z3 "Butterfly Effect"):**
    Anneal defeats Z3 quantifier instability in two complementary ways:
    1. External SMT/SAT/LIA solvers (`Bitwuzla`, `CaDiCaL`, `cvc5`, `Z3`) are
       used as **untrusted certificate-producing oracles** (emitting `LRAT`,
       `Alethe`, Farkas, or ground instantiation witnesses checked in Lean 4's
       kernel; see Sub-Domain 2), so once a proof certificate is recorded or a
       Lean proof term is elaborated, downstream changes in another function can
       *never* break an existing `.olean` theorem via solver heuristic drift!
    2. Even during interactive development when an engineer temporarily waives a
       slow or timed-out obligation (`ob.id ∈ waived`), Anneal's positive
       disjunction `ob.id ∈ waived ∨ ob.prop` in `VerificationResult` guarantees
       that every non-waived obligation retains its unconditional kernel proof.

---

#### 3.3 Cross-Cutting Synthesis: Historical Failure Modes vs. Anneal's Four `trusted/lean/` Primitives

| Historical Failure Case | Primary Citation / CVE / Issue | Root Cause of Verification or Soundness Failure | Anneal `trusted/lean/` Primitive That Prevents It | Mechanized Canary & Repair Theorem (`support/concurrency_systems_failure_canaries_probe.lean`) |
| :--- | :--- | :--- | :--- | :--- |
| **C/C++11-to-Power & ARMv7/v8 `SeqCst` Compilation Bugs** | Manerkar et al. *MICRO 2016* (`10.1109/MICRO.2016.7783747`); Lahav et al. *PLDI 2017* (`10.1145/3062341.3062352`) | Trailing-sync (`ld; isync` / `ldr; dmb`) and leading-sync (`hwsync; st`) or `STLR`/`LDAR` mappings fail when mixed across ABI boundaries or with `Release`/`Acquire` RMWs (`Z6.U`/`R`/`SB`). | **Primitive 1 (`Language SemObs` + `Compiles`) & Primitive 4 (`externalCall`):** Whole-crate `Compiles L_RC11 L_arch codec` + FFI ABI convention check in `boundaryInv`. | `canary_unrepaired_seqcst_mapping_allows_sb_zero_zero` / `repaired_rc11_seqcst_mapping_forbids_sb_zero_zero` |
| **OOTA & `Promising 1.0` Global Optimization Unsoundness** | Kang et al. *POPL 2017*; Lee et al. *PLDI 2020* (`10.1145/3385412.3386010`) | Uncapped thread-local promise certification in `Promising 1.0` uses unreachable value ranges, breaking Global Value-Range Analysis and Register Promotion. | **Primitive 1 (`Compiles` Transitivity):** Instantiating `L_wmm` with `RC11` or `Promising 2.0` capped certification preserves `Preorder.le_trans` across mid-end `CVP` and backend lowering. | `canary_promising1_uncapped_promise_breaks_global_range_opt` / `promising2_capped_memory_preserves_global_range_opt` |
| **`crossbeam-epoch` Missing `SeqCst` & `Arc::get_mut` Weak-Memory Race** | `crossbeam#462`, `#535`, `CVE-2022-23639`; Dang et al. *POPL 2020* (`10.1145/3371102`, `rust#51780`) | Store buffering between epoch pin and pointer load (or missing `Acquire` sync on `Weak` count in `Arc::get_mut`) allows premature reclamation / UAF under weak memory. | **Primitive 2 (`ProductiveOn`) & Primitive 4 (`SmallStepMachine`):** View-aware deallocation (`curView` covering `naReadTs`/`naWriteTs`) + Tree Borrows tag checks transition UAF to `.failed .ub`. | `canary_epoch_pin_without_seqcst_allows_uaf` / `repaired_epoch_pin_seqcst_prevents_uaf` |
| **`RwLockReadGuard` / `MutexGuard` Unsound `Sync` & Legacy `mpsc`** | `rust#41622` (`CVE-2018-1000810`), `rust#39364`, `rust#93563` | `RwLockReadGuard<'a, T>` implemented `Sync` when `T: Send` (missing `T: Sync`), allowing concurrent `&Cell<T>` data races; `mpsc` state-upgrade races. | **Primitive 3 (`VerificationResult`) & Primitive 4 (`externalCall`):** Semantic multi-thread harness obligations for `unsafe impl Send / Sync` verified against `MemState` race detector. | `canary_rwlock_read_guard_send_only_permits_data_race` / `repaired_rwlock_read_guard_requires_t_sync` |
| **Linux Kernel `VirtIO` `EVENT_IDX`, `qspinlock` & `seqlock` Weak-Memory Bugs** | Oberhauser et al. *ASPLOS 2021* (`VSync`, `10.1145/3445814.3446748`); Alglave et al. *ASPLOS 2018* (`LKMM`) | Missing `smp_mb()` between `avail.idx` write and `used_event` read in VirtIO rings causes `SB` lost-wakeup deadlock; `seqlock` non-atomic read race and missing `smp_rmb()`. | **Primitive 2 (`ProductiveOn` + `InhabitedPre`) & Primitive 4 (`EventualBehaviorOf`):** Distinguishes `.failed .ub` (data race) and `.diverges` (spin/await hang) under fair propagation schedules in `Query`. | `canary_virtio_event_idx_missing_mb_deadlocks` / `repaired_virtio_event_idx_smp_mb_prevents_lost_wakeup` |
| **Verified Kernel Boot, ARMv8 `BBM` TLB, DMA/IOMMU & `Meltdown`/`Spectre` Gaps** | `seL4/l4v`, `CertiKOS` (*OSDI 2016*), `Komodo` (*SOSP 2017*), `SeKVM` (*USENIX Sec 2021*); Blackham et al. *RTSS 2011* | Idealized RAM page-table models omit bootloader setup, ARMv8 Break-Before-Make (`BBM`) TLB aborts, rogue DMA overlapping CPU borrows, speculative cache leakage, and IRQ latency in `CNode_Revoke`. | **Primitive 2 (`InhabitedPre`) & Primitive 4 (`externalCall` + `Obs`):** `boundaryInv` enforces `BBM` and IOMMU/DMA borrow disjointness; `InhabitedPre` + `elfBootInit` proves initial state realizability; `UArchEvent` `Obs` tracks leakage and WCIL ticks. | `canary_bbm_violation_or_rogue_dma_triggers_ub` / `repaired_external_call_boundary_inv_blocks_rogue_dma_and_bbm` / `inhabited_pre_and_productive_on_guarantee_witness` |
| **`FSCQ` / `Yggdrasil` FUSE Glue & Multi-Crash Non-Idempotent Recovery** | Chen et al. *SOSP 2015* (`FSCQ`); Sigurbjarnarson et al. *OSDI 2016* (`Yggdrasil`) | Unverified Haskell/C FUSE bindings panicked on edge-case offsets; non-idempotent WAL recovery corrupted disk blocks when a second crash occurred during `recover()`. | **Primitive 1 (`Abstracts`) & Primitive 4 (`SmallStepMachine`):** Demonic crash transitions enabled at every step (including inside `recover()`) + `externalCall` FFI boundary checks enforce multi-crash idempotence. | `canary_nested_crash_during_non_idempotent_recovery_corrupts_disk` / `repaired_idempotent_wal_recovery_survives_nested_crashes` |
| **`Chord` Ring Partition Under Churn, `Verdi`/`IronFleet` Marshaling & Z3 Instability** | Zave *CCR 2012* / *TSE 2017*; Hawblitzel et al. *SOSP 2015* (`IronFleet`); Wilcox et al. *PLDI 2015* (`Verdi`); Lesani et al. *POPL 2016* (`Chapar`) | Local pointer invariants in `Chord` allowed split sub-rings; unverified/slow packet marshaling (`Cheerios` motivation); Z3 E-matching "butterfly effect" timeouts. | **Primitive 1 (`BehaviorCodec`) & Primitive 3 (`VerificationResult`):** `BehaviorCodec` partial-bijection law requires injective round-trip wire serialization; positive per-obligation `VerificationResult` + kernel certificates isolate solver timeouts. | `canary_chord_local_bijection_allows_partitioned_subrings` / `canary_non_injective_packet_serializer_collides` / `repaired_length_prefixed_roundtrip` / `positive_verification_result_isolates_waived_obligation` |

---

## Boundaries

- **Not examined (Silicon Execution of Litmus Tests and Full Kernel Boots):**
  This investigation did not execute hardware litmus tests on physical IBM
  POWER8/POWER9, ARMv8-A, or RISC-V cores, nor did it replay the full
  Isabelle/HOL `seL4/l4v`, Coq `CertiKOS`/`Verdi`/`FSCQ`/`Chapar`, or Dafny
  `IronFleet` build pipelines. The mechanized probe in
  `support/concurrency_systems_failure_canaries_probe.lean` formalizes the
  distilled mathematical counterexamples and repair invariants in Lean 4.34.1.
- **Known not to apply (`BehaviorCodec` Direct Instantiation on Unquotiented
  Target States):**
  As demonstrated in Section 1.1 and Section 3.2, `BehaviorCodec`'s strict
  partial-bijection law (`decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`)
  intentionally rejects codecs where `L₂.Out` retains unquotiented concrete
  representation noise (such as full weak-memory execution graphs `G₁ ≠ G₂`
  with identical terminal heaps, or clobbered caller-saved scratch registers).
  When abstracting such languages in Anneal, the concrete `Language` must
  either quotient internal representation state in `Out` or first refine to an
  intermediate coarse-grained `Language` over the same `Out` carrier before
  applying `BehaviorCodec`.
- **Known not to apply (Safety on Infinite Reactive Loops via Bare
  `EventualOut.diverges`):**
  In `SmallStepMachine` with `EventualBehaviorOf`, `EventualOut.diverges`
  carries no `List Obs` trace. Consequently, verifying trace safety or
  linearizability of non-terminating event loops (such as OS kernels, VirtIO
  drivers, or Raft/Paxos servers) requires either the **Universal
  Finite-Horizon Query Pattern** (`Query := InitState × (horizon : Nat)`) or an
  explicit prefix-observation extension to `EventualOut`.
- **Not examined (Quantitative Probabilistic Distributed Consensus):**
  Randomized Byzantine consensus protocols (such as Ben-Or, HoneyBadgerBFT, or
  Algorand VRF leader election) require quantitative/probabilistic coupling
  beyond non-deterministic `StepResult.choice .demonic` and are outside the
  scope of this report.

---

## Evidence

1. **Anneal Repository Sources (`joshlf/anneal`):**
   - `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` (`trusted-core` branch):
     - `trusted/lean/Trusted/Refinement.lean` (lines 1–476): `Preorder`,
       `Partial`, `Partial.pure`, `Partial.ub`, `Behavior`, `Language`,
       `Language.SpecOn`, `Language.WellFormedOn`, `Compiles`, `Abstracts`,
       `Compiler.Verified`, `VerificationResultOn`, and `VerificationResult`.
     - `trusted/lean/Trusted/StepResult.lean` (lines 1–201): `StepResult`,
       `PrefixOutcome`, `ExecQuery`, `ExecOut`, `SmallStepMachine`,
       `ReachesPrefix`, and `BehaviorOf`.
   - `24367bd1a8c784f2578535954f9915e24894a56f` (`main` branch):
     - `trusted/lean/Trusted.lean` and `trusted/lean/Trusted/Attributes.lean`
       (lines 1–140): `@[vetted]` and `@[candidate <feature>]` trust-tier
       declaration attributes and `Trusted.candidate` marker.
2. **Rust Standard Library Sources (`rust-lang/rust` at
   `d8ef4f3fe7031514cbd7d056b7b058814987ecec`):**
   - `library/core/src/sync/atomic.rs` (lines 25–155): normative C++20-derived
     atomic memory model contract.
   - `library/alloc/src/sync.rs`: `Arc::drop` and `Arc::get_mut` acquire/release
     synchronization following `rust-lang/rust#51780`.
   - `library/std/src/sync/mpsc/mod.rs`: `crossbeam-channel`-backed (`mpmc`)
     replacement introduced in `rust-lang/rust#93563`.
3. **Standalone Lean 4.34.1 Mechanized Failure Canaries and Repairs Probe:**
   - **Path:**
     [`reports/anneal-concurrency-weak-memory-kernels-storage-verification-failures-2026/support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
   - **Lines:** 678
   - **SHA-256:**
     `6e7eaf3daa9d1b427a53ef3a39335079e1dd54dec63e7fcec680962b09b88181`
   - **Toolchain:** `leanprover/lean4:v4.34.1`
     (`5045d0056413266e57c625dcd7c365b10e377c52`)
   - **Key Mechanized Theorems:**
     - `canary_unrepaired_seqcst_mapping_allows_sb_zero_zero` and
       `repaired_rc11_seqcst_mapping_forbids_sb_zero_zero` (lines 182–198)
     - `canary_promising1_uncapped_promise_breaks_global_range_opt` and
       `promising2_capped_memory_preserves_global_range_opt` (lines 215–223)
     - `canary_epoch_pin_without_seqcst_allows_uaf` and
       `repaired_epoch_pin_seqcst_prevents_uaf` (lines 258–278)
     - `canary_rwlock_read_guard_send_only_permits_data_race` and
       `repaired_rwlock_read_guard_requires_t_sync` (lines 296–307)
     - `canary_virtio_event_idx_missing_mb_deadlocks` and
       `repaired_virtio_event_idx_smp_mb_prevents_lost_wakeup` (lines 335–354)
     - `canary_bbm_violation_or_rogue_dma_triggers_ub` and
       `repaired_external_call_boundary_inv_blocks_rogue_dma_and_bbm` (lines
       380–397)
     - `canary_nested_crash_during_non_idempotent_recovery_corrupts_disk` and
       `repaired_idempotent_wal_recovery_survives_nested_crashes` (lines
       434–446)
     - `canary_chord_local_bijection_allows_partitioned_subrings` (lines
       476–482)
     - `canary_non_injective_packet_serializer_collides` and
       `repaired_length_prefixed_roundtrip` (lines 511–539)
     - `canary_antecedent_verification_result_explodes_on_false_assumption` and
       `positive_verification_result_isolates_waived_obligation` (lines
       554–572)
     - `canary_uninhabited_pre_vacuously_satisfies_ub_prog` and
       `inhabited_pre_and_productive_on_guarantee_witness` (lines 583–596)
   - **Axiom Audit:** Verified via `#guard_msgs in #print axioms` at lines
     600–678 to depend only on `propext` (or zero axioms), with zero `sorryAx`
     and zero custom axioms.
4. **Primary Literature & Postmortem Citations:**
   - Y. A. Manerkar, C. Trippel, D. Lustig, M. Pellauer, and M. Martonosi,
     *"Counterexamples and Proof Loophole for the C/C++ to POWER and ARMv7
     Trailing-Sync Compiler Mappings"*, MICRO-49, 2016, DOI
     `10.1109/MICRO.2016.7783747`.
   - O. Lahav, V. Vafeiadis, J. Kang, C.-K. Hur, and D. Dreyer, *"Repairing
     Sequential Consistency in C/C++11"*, PLDI 2017, DOI
     `10.1145/3062341.3062352`.
   - S.-H. Lee, M. Cho, A. Podkopaev, S. Chakraborty, C.-K. Hur, O. Lahav, and
     V. Vafeiadis, *"Promising 2.0: Global Optimizations in Relaxed Memory
     Concurrency"*, PLDI 2020, DOI `10.1145/3385412.3386010`.
   - H.-H. Dang, J.-O. Kaiser, J.-H. Jourdan, D. Dreyer, and V. Vafeiadis,
     *"RustBelt Meets Relaxed Memory"*, POPL 2020, DOI `10.1145/3371102`.
   - J. Oberhauser et al., *"VSync: Push-Button Verification and Optimization
     for Synchronization Primitives on Weak Memory Models"*, ASPLOS 2021, DOI
     `10.1145/3445814.3446748`.
   - B. Blackham, Y. Shi, S. Chattopadhyay, A. Roychoudhury, and G. Heiser,
     *"Timing Analysis of a Protected Operating System Kernel"*, RTSS 2011, DOI
     `10.1109/RTSS.2011.38`.
   - H. Sigurbjarnarson, J. Bornholt, E. Torlak, and X. Wang, *"Push-Button
     Verification of File Systems via Crash Refinement"*, OSDI 2016, ISBN
     `978-1-931971-33-1`.
   - P. Zave, *"Using Lightweight Modeling to Understand Chord"*, ACM SIGCOMM
     CCR 42(2), 2012, DOI `10.1145/2185376.2185383`, and *"Reasoning About
     Identifier Spaces: How to Make Chord Correct"*, IEEE TSE 43(12), 2017, DOI
     `10.1109/TSE.2017.2655056`.
   - C. Hawblitzel et al., *"IronFleet: Proving Practical Distributed Systems
     Correct"*, SOSP 2015, DOI `10.1145/2815400.2815428`.
   - J. R. Wilcox et al., *"Verdi: A Framework for Implementing and Formally
     Verifying Distributed Systems"*, PLDI 2015, DOI `10.1145/2737924.2737958`.
   - M. Lesani, C. J. Bell, and A. Chlipala, *"Chapar: Certified Causally
     Consistent Distributed Key-Value Stores"*, POPL 2016, DOI
     `10.1145/2837614.2837622`.

---

## Revalidation

To typecheck the standalone Lean 4.34.1 failure-canaries and repairs probe and
verify that all theorems and `#guard_msgs in #print axioms` checks pass with
zero errors and zero warnings, run from the `reference` worktree root:

```bash
lean +leanprover/lean4:v4.34.1 \
  reports/anneal-concurrency-weak-memory-kernels-storage-verification-failures-2026/support/concurrency_systems_failure_canaries_probe.lean
```

Expected output: exit code `0` with empty stdout and stderr.

To verify the SHA-256 digest of the preserved Lean 4.34.1 probe:

```bash
sha256sum \
  reports/anneal-concurrency-weak-memory-kernels-storage-verification-failures-2026/support/concurrency_systems_failure_canaries_probe.lean
# Expected:
# 6e7eaf3daa9d1b427a53ef3a39335079e1dd54dec63e7fcec680962b09b88181  .../concurrency_systems_failure_canaries_probe.lean
```

*Authored by an AI agent acting on joshlf's behalf.*
