# Weak-Memory Semantics, Program Logics, and TCB Integration Trade-Offs for Anneal

## Summary

Adding concurrent weak-memory verification to Anneal (`google/zerocopy@a4f1182901bf9000022b46b6b0ff32159d36c981`) while keeping the Lean 4 trusted computing base (`trusted/lean/` + Pass-1 `TrustedBoundary.lean` rules) minimal, tactic-free, and sound centers on four architectural conclusions:

1. **Operational Promise-Free View Semantics (`ORC11` + `Op-SC2'` + Data-Race Clocks) Is the Minimal Sound Ring-1 TCB:**
   - **Sequential Consistency (`SC-for-DRF`) is unsound** for concurrency primitives using racy `Relaxed` atomics (`Mutex::spin`, `Arc::clone`, `Condvar::notify_one`, `OnceLock` state polling) or validating weak `Acquire`/`Release` ordering (naive SC interleaving masks missing `Acquire` or missing `Acquire` fence bugs).
   - **Axiomatic `RC11` / `IMM` graphs** fit ISA compilation proofs (`x86-TSO`, `Armv8`) but misalign with Anneal's small-step `Step` / `Reaches` / `FnContract` (`EffectMask`) judgment.
   - **Full `Promising 2.1` (`PS2`)** adds thread-local certification machines inside the TCB to allow `Relaxed` load-to-store speculation (`LB+rlx`), which synchronization primitives do not need.
   - **Promise-free view-based operational semantics (`ORC11` `Nat`-interval timestamps + `Op-SC2'` `VClock` SC fences/accesses + non-atomic `lastWr`/`lastRd` race clocks)** strictly over-approximates out-of-thin-air (`OOTA`) freedom without certification machinery, supports `OracleGrade.forwardSim` soundness for primitives without `LB+rlx` dependencies, and compiles cleanly in Pass-1 `Init.Core` Lean 4.
2. **Pass-2 Correspondence Cannot Naively Target Miri's RNG `StoreBuffer`:** `proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`) faithfully models Miri's `128`-entry `StoreBuffer`, `StoreBuffer.last` RMW restriction (completeness gaps), and known 3-thread `SeqCst` over-approximation (`https://github.com/rust-lang/miri/issues/2301`, documented in `rc11-gps-fsl-timestamp-view-pcms-and-miri-store-buffer-completeness-gaps`)—making Miri's weak-memory set incomparable with C++20/Hardware. Pass-2 correspondence splits cleanly: strict bidirectional equivalence for sequential/SC fragments (`weakMemory := false`) and forward simulation / `ORC11` reference correspondence for weak memory.
3. **`0`-TCB `Type 0` View-Shifted Separation Logic Fits Anneal's `WavefrontReclaim` Architecture:** `theory/Anneal/WavefrontReclaim/SpatialPcm.lean` already demonstrates a `0`-axiom, step-index-free `VProp` (`View -> ResTrie ResElem -> Prop`) and frame-preserving `VSepWpOrdRel` under Pass-1 constraints (`0` `omega`, `0` `bv_decide`, `0` `by_cases`, `0` `._unsafe_rec`), directly accommodating `RSL`/`FSL`/`GPS`/`OwnLoc`-style ownership transfer, `Acquire`-fence accumulation (`acq` view), and linear `MustRelease` guard tokens against `mem::forget`.
4. **TCB Surface Integration & Concrete Soundness Traps:** Adding weak memory to `Trusted.Framework` lifts `MirProfileV2`'s `.callerMemoryThreadIsolation` gap (`Instances.lean:253-259`), models OS futex calls via `AssumedStub` + `StubRealizable` (`Framework.lean:180-190`) with wake/wakeup view transfer (matching `Miri.Concurrency.FutexRuntime`), requires relaxing `bodyMixesRefsAndRawPtrsV2` (`Boundary.lean:445`) for `UnsafeCell`, preserves `TreeBorrows` `.cell` invariance while needing vector-clock propagation on `ProtectorEnd` (`FnExit`), and must prevent 6 canonical soundness bugs—3 of which (`Arc::drop` missing `fence(Acquire)`, `SpinLock` missing `Acquire`, and `SeqLock` non-atomic payload race) are verified in `support/WeakMemSpinOnceFenceProbe.lean`.

## Applicability

This synthesis governs extending Anneal (`google/zerocopy@a4f1182901bf9000022b46b6b0ff32159d36c981`) under Pass-1 `TrustedBoundary.lean` rules (`leanprover/lean4` `v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`) and `proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`) targeting Rust `1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) concurrency primitives audited in companion report `rust-concurrency-primitives-mir-capture-and-stdlib-audit`.

Claims from existing reference-corpus studies are explicitly credited and bound to their reported scopes; only behavior implemented in `support/WeakMemSpinOnceFenceProbe.lean` or directly inspected in `google/zerocopy`, `proofs-rs/lean-miri`, and `rust-lang/rust` is presented as `[real measurement]` or `[source inspection]`.

## Findings

### 1. Weak-Memory Semantics Trade-Offs for Anneal's Ring-1 TCB

Basis: derived + source (`Trusted/MirSemantics/{Boundary, Memory, Step}.lean`, `Trusted/Framework.lean`, `Miri/Concurrency/{WeakMemory, AtomicDispatch, GlobalState}.lean`) + literature synthesis from `weak-memory-concurrency-models-hardware-mappings-and-optimizations`, `promising2-relaxed-load-buffering-op-sc2-reduction-and-x86-tso-fence-soundness`, `nat-interval-operational-rc11-promising-eliminations-and-rmw-modification-order-gaps`, `rc11-gps-fsl-timestamp-view-pcms-and-miri-store-buffer-completeness-gaps`, and `c20-p0668r5-operational-seqcst-tree-borrows-fnexit-and-lean4-scope-soundness`.

| Candidate Ring-1 Semantics | OOTA / `LB+rlx` | `Relaxed`, `Acquire`, `Release`, `SeqCst`, Fences | Alignment w/ `Step`/`Reaches`/`EffectMask` | Ring-1 TCB Cost & `Init.*` Pass-1 Fit | Pass-2 `lean-miri` / Hardware Verdict |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **SC Interleaving + Race Clock (`SC-for-DRF`)** | Forbidden (`SC`) | **Unsound for weak atomics:** hides missing `Acquire`, missing `fence(Acquire)` (`Arc::drop`), and `SB` bugs whenever atomic locations race safely in Rust | Native (`Step` interleaving) | Lowest (`Mem + NaClock`), Pass-1 trivial | **Incompatible** with verifying weak-memory orderings; valid *only* for code proven SC-equivalent or non-racing |
| **Axiomatic `RC11` / `IMM` Execution Graphs** | `RC11`: `acyclic(po \| rf)`; `IMM`: `ppo` syntactic deps | Full C++20/RC11 (`psc`, fences, RMW coherence) | **Poor fit:** whole-execution graph predicate clashes with small-step `Step` / `Diverges` / `FnContract` | Moderate (`Fin`-graph acyclicity + `rf`/`mo`/`sc` quantifiers); poor WP ergonomics | Best *ISA backend* theorem (`x86-TSO`, `Armv8`), noting `IMM_s` predates `+rcpc` `LDAPR` |
| **Promise-Free View Operational (`ORC11` + `Op-SC2'` + Data-Race Clocks)** | **Conservative no-OOTA** (forbids speculative promises; sound `forwardSim` over-approx for no-LB code) | Full `Relaxed` / `Acquire` / `Release` / `AcqRel` / `SeqCst` (`P0668R5`+`P0982R1` `VClock`) + `fence` (`cur`/`acq`) + NA data-race UB | **Natural fit:** extends `Step` with demonic message-index `Choice`, `ThreadView`, `MsgPool`, and `NaClock` | **Minimal viable weak-memory TCB:** pure `Nat`/`List` view algebra; zero promise certification machine; zero `._unsafe_rec` | **Recommended Ring-1 target** (`OracleGrade.forwardSim` vs C++20/hardware); exact `Op-SC2'` avoids `https://github.com/rust-lang/miri/issues/2301` 3-thread SC flaw |
| **Full `Promising 2.1` (`PS2` + `capMem`)** | Allows justified `LB+rlx` via capped-memory local certification | Full C++20/Promising + undefined/undef-bit values | Heavy: every step requires nested certification execution | **High TCB bloat:** embeds local interpreter + future-write certificate inside Ring-1 TCB | Unnecessary unless verifying lock-free `Relaxed`-only OOTA idioms or compiler optimization soundness |

**Key Engineering Decisions for View-Based `ORC11` + `Op-SC2'`:**
- **Timestamps (`Nat` `(fromTs, toTs]` vs dense `ℚ`):** Prior corpus analysis (`nat-interval-operational-rc11-*`) proves finite-trace equivalence between half-open `Nat` RMW attachment (`t+1` / disjoint interval splitting) and dense `ℚ`, keeping `View` operations strictly over `Nat` (`Init.Data.Nat.Basic`, avoiding rational arithmetic in TCB).
- **`SeqCst` (`VClock` vs scalar counters):** Prior `P0668R5`+`P0982R1` analysis (`c20-p0668r5-operational-*`) demonstrates that scalar SC write/fence counters are unsound on 4-thread `P_4_acqrel_fence` and mixed `SeqCst`/`Acquire` (`LDAPR`) patterns; `Op-SC2'`'s per-thread-vector `VClock` tracking is required if `Ordering::SeqCst` is admitted (`Once`/`Mutex`/`Arc` use only `Relaxed`/`Acquire`/`Release`, avoiding `SeqCst` initially, though `RwLock`/general users use `SeqCst`).
- **Pass-2 `lean-miri` Boundary (`vendor/lean-miri/Miri/Concurrency/`):** In `AtomicDispatch.lean:177-247` and `WeakMemory.lean:35,120`, Miri enforces `STORE_BUFFER_LIMIT := 128`, restricts RMWs to `StoreBuffer.last`, and uses RNG selection over `fetchChoices`, while permitting the 3-thread `SeqCst` stale-read over-approximation documented in `rc11-gps-fsl-timestamp-view-pcms-and-miri-store-buffer-completeness-gaps` (`https://github.com/rust-lang/miri/issues/2301`). Thus `Miri.Concurrency.WeakMemory` is set-incomparable with C++20/hardware (`Beh_MiriWeak` neither contains nor is contained in `Beh_C++20`). Anneal's Pass-2 correspondence must either lock sequential/SC equivalence against `Miri` (`weakMemory := false`) or prove `forwardSim` from a promise-free `ORC11` Ring-1 kernel against an external `ORC11`/`IMM` reference rather than expecting `biFaultEquiv` against `Miri.Concurrency.WeakMemory`.

---

### 2. Program Logics & `0`-TCB `theory/Anneal/` Layering (`TrustedBoundary.lean`)

Basis: source (`TrustedBoundary.lean:240-340, 733-785`, `WavefrontReclaim/{SpatialPcm.lean, Wavefront.lean}`) + synthesis from `owicki-gries-fsl-gps-cosmo-and-first-order-view-logics-for-weak-memory-rust`, `verus-vstd-views-permissions-prophecies-and-os-verification`, and `unsafecell-cell-refcell-ghostcell-and-oncecell-formal-protocols-in-first-order-separation-logic`.

Under `TrustedBoundary.lean`, `trusted/` (`SourceRole.trusted _`) is **tactic-free** (excluding `byTactic`), while `theory/` (`SourceRole.theory`) permits constructive/classical Lean tactics from `allowedTheoryTacticKinds` (`lines 740-761`) while **banning** `omega`, `bv_decide`, `decide!`, `native_decide`, `sorry`, `grind`, `._unsafe_rec`, and imports outside `Init.Core`/`Std` (`Init.System.*` banned; `Init.Data.Nat.Bitwise.Basic` confined to `Anneal.*`). Any verification logic in `theory/` carries **zero TCB cost** because the Lean 4 kernel (`nanoda_bin`/`con-ron`) expands proofs against `trusted/` definitions.

| Logic / Proof Paradigm | Expressive Fit for Stdlib/Toy Primitives | Compatibility w/ Anneal Pass-1 (`Type 0`, no `._unsafe_rec`, `Init.*`) | Trade-Off Verdict for Anneal `theory/` |
| :--- | :--- | :--- | :--- |
| **`RSL` / `FSL` / `FSL++` / `GPS` + `iRC11` (View-Shifted RA Logics)** | Exact fit for `SpinLock`, `Arc` (`△`/`▽` modalities for `fence(Acquire)` + fractional ownership), `Once`, `SeqLock` (`GPS` monotonic protocols) | **High in first-order `Type 0` form:** step-indexing is unnecessary unless proving impredicative shared closures (`FnOnce` heap invariants with nested locks) | **Primary recommended `0`-TCB logic** (`Type 0` view-indexed PCMs + protocol automata) |
| **Anneal `WavefrontReclaim.SpatialPcm.VProp` Extension** | Already defines `VProp : Type` (`holds : View -> ResTrie ResElem -> Prop` with `upClosed` under `ViewLe` and `ResTrieSub`), `vsep`, `vowns`, `CellFrag` (`.capOnly`/`.authOnly`), and `VSepWpOrdRel` (`vsepWpOrdRel_frame`) | **Already Pass-1 verified in `origin/main`!** (`0` `noncomputable`, `0` `omega`, `0` `decide`, `0` axioms `[ ]` on `SpatialPcm.lean`) | **Immediate reuse path:** generalize fixed `Pos4` `ResTrie` to `(AllocId × Offset)` or `AllocId`-trie + add pending-`acq` view component for `fence(Acquire)` (`FSL` `△`/`▽`) |
| **`Verus` Tokenized State Machines (`tokenized_state_machine!`)** | Proven ergonomic for `Once`, `Mutex`, `RwLock`, `Arc` protocol invariants via linear ghost tokens (`sharding` / `guard` / `invariant`) | Translatable 1:1 into `0`-TCB `ResPCM` / `SpatialPcm` ghost transitions without SMT solvers, verified by explicit frame-preserving updates | **Strong UX complement** to `VProp`: encode protocol states (`INCOMPLETE`/`RUNNING`/`COMPLETE`, `UNLOCKED`/`LOCKED`/`CONTENDED`) as exclusive ghost tokens inside `ResTrie` |
| **Owicki-Gries / Rely-Guarantee (`OGRA`) & `OwnLoc`** | Lightweight per-location invariants (`SpinLock`, `AtomicOnce`) and sequential-collapse `OwnLoc` reasoning inside critical sections | Trivial Pass-1 Lean (`Type 0`); no RA machinery needed for simple non-reentrant primitives | **Best starter automation** for Tier 0 (`RawSpinLock`, `AtomicOnceU64`) inside critical sections (`OwnLoc` lifts sequential `MirWp` proofs) |
| **Full Impredicative Iris (`RefinedRust`)** | Arbitrary recursive locks, higher-order `Once::call_once<F>` with cyclic locks inside `F` | **Fails Pass-1 simplicity:** requires step-indexed guarded recursion (`later` `▷` solver, impredicative `iProp` invariants, heavy tactic machinery) | Defer impredicative step-indexing; handle non-reentrant `Once::call_once` via first-order `FnContract` / parameterized closure invariant `P : Prop` |

---

### 3. Concrete `Trusted.Framework`, `MemoryState`, `UnsafeCell`, `TreeBorrows`, and `futex` Seams

Basis: source (`Trusted/Framework.lean:76-190`, `Trusted/Framework/Instances.lean:245-280`, `Trusted/MirSemantics/{Memory.lean:43-74, Boundary.lean:431-505}`, `theory/Anneal/MiriTreeBorrows/Model.lean:250-320, 827-831`, `vendor/lean-miri/Miri/Concurrency/FutexRuntime.lean:38-97`).

1. **Mapping onto `Trusted.Framework.ExecutionModel` (`Framework.lean:110-132`):**
   - `ExecutionModel (Prog Body Sig Query Ret Mem : Type)` already abstracts `(Query, Ret, Mem)` and carries `oracleGrade : OracleGrade` (`.unbridged | .forwardSim | .biFaultEquiv`), `requiredGaps`, and `DisclosedGap`.
   - `MirProfileV2` (`Instances.lean:253-259`) explicitly isolates callers via `.callerMemoryThreadIsolation "mir_profile_v2"`. A **`ConcurrentMirProfile`** replaces that single-thread isolation gap with a shared `ConcurrentMemState` pairing byte allocations (`MemoryState`), per-location atomic `MsgPool` + non-atomic access clocks (`lastNaWrTid`, `lastNaWrTs`, `lastNaRdClock`), per-thread `ThreadView` (`cur`, `acq`, `sc`), and global `scView`, parameterized by an interleaving schedule / atomic-message `Choice` predicate under `Step`.
2. **`MemoryState` + `UnsafeCell` vs. `!bodyMixesRefsAndRawPtrsV2` (`Boundary.lean:431-447`):**
   - Today `MemoryState` (`{ nextAllocId : AllocId, allocations : List Allocation }`) is purely sequential. Extending it cleanly adds per-allocation or per-byte `(atomicMsgHistory, lastNaClock)` *or* keeps non-atomic bytes in `Allocation` alongside an orthogonal `DataRace` + `MsgPool` shadow map (just as Miri separates `Memory` bytes from `AllocExtra` `{ data_race, weak_memory, borrow_state }`).
   - Crucially, `Boundary.lean:445` blocks bodies having **both** reference locals and raw-pointer locals (`bodyMixesRefsAndRawPtrsV2`). Because `Atomic<T>` (`v: UnsafeCell<T::Storage>`) and `&self -> UnsafeCell::get(&self) -> *mut T` intrinsically convert `&` into `*mut`, concurrent admission must explicitly track `UnsafeCell`-rooted projections/provenance (disabling `&mut`/`&` frozen optimization inside `UnsafeCell` bytes while preserving disjointness outside `UnsafeCell`).
3. **`TreeBorrows` (`MiriTreeBorrows`) + Weak Memory Interaction:**
   - In `theory/Anneal/MiriTreeBorrows/Model.lean:827-831`, `miriCell_all_accesses_preserve_cell` proves that `MiriPerm.cell` (assigned to `UnsafeCell<T>` fields upon retag) remains `.cell` on *every* read/write, local or foreign, protected or unprotected! Thus `Atomic<T>` and `Mutex<T>::data` payloads stay compatible with Tree Borrows under arbitrary concurrent interleavings.
   - **Critical `ProtectorEnd` (`FnExit`) Trap:** Prior analysis (`c20-p0668r5-operational-*`) documents that when a function borrows `&mut T` from `MutexGuard::deref_mut` or passes `&mut T` across an unlocked/synchronizing boundary, Tree Borrows `FnExit` `ProtectorEnd` unprotects tags in step order without writing a vector-clock edge back into `VClock`; conversely, a thread holding a protected `&mut T` across a concurrent foreign write triggers Tree Borrows UB unless mutex lock/unlock happens-before encloses the protector lifetime.
4. **OS `futex` via `AssumedStub` + `StubRealizable` (`Framework.lean:180-190`) & `FutexRuntime`:**
   - `std::sys::sync::{mutex,once,rwlock,condvar}::futex` all terminate in `futex_wait` / `futex_wake` / `futex_wake_all` (`libc::syscall(SYS_futex, ...)`).
   - `Trusted.Framework.AssumedStub` (`{ identity, sig, contract }`) + `StubRealizable` (recording `.assumedExternalCallee` in `VerificationEnvelope.gaps`) fits OS futex calls cleanly *without* embedding Linux kernel scheduler/syscall semantics inside Ring-1 TCB:
     - **`futex_wait(addr, expected)`:** Non-deterministic return (immediate spurious wakeup, value-mismatch immediate return, or blocked until `futex_wake(addr)` happens-before wakeup, acquiring the waking thread's futex-slot clock upon wake!).
     - **`futex_wake(addr)` / `futex_wake_all(addr)`:** Records caller's `cur` view onto the futex queue / wakes `<= 1` (`all`) blocked threads (matching `vendor/lean-miri/Miri/Concurrency/FutexRuntime.lean:41-95` `release`/`acquire` clock handoff!). *Critical subtlety (`rust-std-concurrency-*`):* real Linux futex `wait`/`wake` provides an atomic queue check on `*addr` in kernel space so `Condvar::notify_one` (`fetch_add(Relaxed)` + `futex_wake`) does not miss wakeups; modeling `futex_wait` with a naive non-atomic pre-check without serializing the `(load == expected)` + enqueue step introduces false lost-wakeup counterexamples!

---

### 4. Critical Weak-Memory & Rust Concurrency Soundness Traps (with Pass-1 Lean 4 Probe)

Basis: execution (`support/WeakMemSpinOnceFenceProbe.lean`, checked via Lean `v4.34.1` `-DwarningAsError=true`) + source (`alloc/src/sync.rs:2836-2868`, `std/src/sync/nonpoison/mutex.rs:99-101, 471-477`, `std/src/sys/sync/mutex/futex.rs:32-97`).

Every theorem in `support/WeakMemSpinOnceFenceProbe.lean` (`470` lines, `0` `sorry`, `0` `omega`/`bv_decide`/`by_cases`/`._unsafe_rec`) elaborates under Lean `v4.34.1` (`Init.Core`, `Init.NotationExtra`, `Init.Data.Nat.Basic`, `Init.Data.List.Basic`, `Init.SimpLemmas`):

| Soundness Trap | Concrete Trigger in Stdlib / Toy Code | Verified Lean 4 Theorem / Axiom Footprint (`support/WeakMemSpinOnceFenceProbe.lean`) | Architectural Mitigation |
| :--- | :--- | :--- | :--- |
| **`Release`-RMW -> `Acquire` Fence Sync (`Arc::drop`)** | `Arc::drop` executes `strong.fetch_sub(1, Release)` (`alloc/src/sync.rs:2836`) + `atomic::fence(Acquire)` (`line 64, 2868`) before `drop_slow`. Because `fetch_sub(Release)` has a `Relaxed` read, omitting `fence(Acquire)` leaves `lastNaWrTs ≰ cur[wTid]` on `data`! | `arc_with_fence_ok_42` (`[propext]`): `2142` (`val=42`, zero race) vs `arc_missing_fence_is_dataRace` (`[propext]`): `.fault .dataRace` | Ring-1 semantics **must** retain a pending `acq` view updated on `Relaxed`/`Release` reads and promoted into `cur` by `atomicFence .acq` |
| **Missing `Acquire` on Lock / `Once` Load** | Replacing `Ordering::Acquire` with `Ordering::Relaxed` on `SpinLock::lock` / `try_lock` or `Once::is_completed` breaks critical-section happens-before even when mutual exclusion holds in SC! | `spinlock_acquire_ok` (`[propext]`): `.ok _ 99`; `spinlock_relaxed_bug_is_dataRace` (`[propext]`): `.fault .dataRace`; **`acq_load_syncs_naRead_arbitrary` (`[]` zero axioms!)**: parametric proof across arbitrary thread clocks & messages | Any sound Ring-1 semantics **must** track per-thread `cur` clocks + per-location NA write/read clocks rather than SC interleaving |
| **Seqlock Non-Atomic Payload Data Race** | Reading `[u64; 2]` inside `SeqLock::read` non-atomically (`*data.get()`) while a concurrent writer holds the write section triggers data-race UB *even if* `fence(Acquire)` + `s1 == s2` discards torn values | `seqlock_na_payload_is_dataRace` (`[propext]`): `.fault .dataRace` vs `seqlock_relaxed_payload_no_race` (`[propext]`): `.ok _ 71` with `Relaxed` atomic payload reads + `fence(Acquire)` | Seqlock implementations in Rust (`Relaxed` atomic word reads + `fence(Acquire)`) require mixed-size or word-sized atomic payload ops, never raw non-atomic reads |
| **`mem::forget(guard)` Safe Leak** | `core::mem::forget(mutex.lock())` is **100% safe Rust** (`Guard` is not linear), permanently leaving `Mutex` in `LOCKED`/`CONTENDED` | Tracked in `rust-std-concurrency-*` (`MustRelease` linear obligation) | Functional safety holds under `mem::forget` (`no panic`/`no UB`), whereas lock reclamation/liveness specs must require guard drop or `Mutex` exclusivity; `UnsafeCell` `.cell` invariance still holds (`tb_cell_invariant` `[propext]`) |
| **Out-Of-Thin-Air (`LB+rlx`) & Mixed `SeqCst` / `LDAPR`** | Circular `Relaxed` load-to-store dependencies (`LB+rlx`) & `STLR` -> `LDAPR` (`SB`) on ARMv8.3 | Covered in `promising2-relaxed-*` and `weak-memory-concurrency-*` | Promise-free `ORC11` forbids `LB+rlx` cycles conservatively (`forwardSim`); `Op-SC2'` `VClock` models C++20 `P0668R5` accurately |

## Boundaries

1. **Concrete Witness vs. Universal Equivalence in `support/WeakMemSpinOnceFenceProbe.lean`:** Seven of the eight theorems (`arc_with_fence_ok_42`, `arc_missing_fence_is_dataRace`, `spinlock_acquire_ok`, `spinlock_relaxed_bug_is_dataRace`, `seqlock_na_payload_is_dataRace`, `seqlock_relaxed_payload_no_race`, `tb_cell_invariant`) are concrete deterministic trace reductions (`rfl`) over bounded 2-thread states with latest-message `atomicRmw` and fixed `msgIdx` `atomicLoadAt` (no full `mo` interval search or promise certification); only `acq_load_syncs_naRead_arbitrary` is a universally quantified parametric theorem (for `Acquire` load view-join preservation of `lastNaWrTs ≤ cur[lastNaWrTid]`).
2. **Not Implemented in `google/zerocopy@a4f1182901bf`:** Neither `ConcurrentMirProfile` nor `ORC11`/`Op-SC2'` nor `VProp`-over-`(AllocId × Offset)` exists in `google/zerocopy:main` yet; this report evaluates candidate designs grounded in existing `Trusted.Framework`, `WavefrontReclaim`, `MiriTreeBorrows`, and `vendor/lean-miri` interfaces.
3. **Not Examined:** Progress/starvation fairness proofs under OS thread preemption (only safety, partial correctness, and `MustRelease` structural hooks are scoped), relaxed/weak hardware fences below MIR (`RISC-V RVWMO`, `Power`), and `async`/coroutine suspension across held lock guards.

## Evidence

- `support/WeakMemSpinOnceFenceProbe.lean` (`470` lines, SHA-256 `5c8999b4056160caea39782e08f1614315d84155adc549ef161f206ad6af3a6f`) — Pass-1-compliant Lean `v4.34.1` executable probe (`module prelude` importing only `Init.{Core, NotationExtra, Data.Nat.Basic, Data.List.Basic, SimpLemmas}`; `0` `omega`, `0` `bv_decide`, `0` `by_cases`, `0` `._unsafe_rec`, `0` `sorry`) verified with `lean -DwarningAsError=true` (`7` `[propext]` concrete trace/cell theorems + `1` `[]` zero-axiom parametric theorem `acq_load_syncs_naRead_arbitrary`).
- **Primary Repository Code Inspected:**
  - `google/zerocopy@a4f1182901bf9000022b46b6b0ff32159d36c981`: `anneal/trusted/lean/Trusted/Framework.lean:76-190`, `anneal/trusted/lean/Trusted/Framework/Instances.lean:245-280`, `anneal/trusted/lean/Trusted/MirSemantics/{Memory.lean:43-100, Boundary.lean:425-505, Step.lean:3280-3340}`, `anneal/trusted/audit/TrustedBoundary.lean:240-340, 700-786`, `anneal/theory/Anneal/WavefrontReclaim/{SpatialPcm.lean:1-100,990-1080, Wavefront.lean:1270-1540}`, `anneal/theory/Anneal/MiriTreeBorrows/Model.lean:240-320, 827-831`.
  - `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (vendored in `anneal/vendor/lean-miri`): `Miri/Concurrency/{WeakMemory.lean:35-255, DataRace.lean:1-100, AtomicDispatch.lean:140-250, GlobalState.lean:1-100, FutexRuntime.lean:1-100}`.
- **Cross-Referenced Corpus Reports (`google/zerocopy:reference`):**
  - `rust-concurrency-primitives-mir-capture-and-stdlib-audit` (companion MIR & stdlib primitive census at `a4f1182901bf` & `f8a08b688`)
  - `weak-memory-concurrency-models-hardware-mappings-and-optimizations` (`RC11`, `IMM`, `PS 1.0/2.0/2.1`, `herd7` `LB-data` & `Seqlock`, `Armv8` `LDAPR`)
  - `promising2-relaxed-load-buffering-op-sc2-reduction-and-x86-tso-fence-soundness`
  - `nat-interval-operational-rc11-promising-eliminations-and-rmw-modification-order-gaps`
  - `rc11-gps-fsl-timestamp-view-pcms-and-miri-store-buffer-completeness-gaps`
  - `c20-p0668r5-operational-seqcst-tree-borrows-fnexit-and-lean4-scope-soundness`
  - `owicki-gries-fsl-gps-cosmo-and-first-order-view-logics-for-weak-memory-rust`
  - `rust-std-concurrency-intrinsics-futex-mpmc-scope-and-tls-destructor-semantics`
  - `anneal-concurrent-mir-capture-target-audit-and-lean-miri-closure`
  - `verus-vstd-views-permissions-prophecies-and-os-verification`
  - `unsafecell-cell-refcell-ghostcell-and-oncecell-formal-protocols-in-first-order-separation-logic`

## Revalidation

1. **Kernel-check the Pass-1 Lean `v4.34.1` operational weak-memory probe (`<2s`):**
   ```bash
   lean -DwarningAsError=true \
     reports/anneal-weak-memory-semantics-logics-and-architecture-tradeoffs/support/WeakMemSpinOnceFenceProbe.lean
   ```
   Verifies all `8` theorems elaborate with zero warnings, zero `sorryAx`, and strictly `[propext]` / `[]` axioms under `module prelude` `Init.*`-only imports.

2. **Verify Pass-1 `TrustedBoundary` compatibility and `WavefrontReclaim` / `MirProfileV2` interfaces in `google/zerocopy`:**
   ```bash
   grep -n "callerMemoryThreadIsolation\|AssumedStub\|miriCell_all_accesses_preserve_cell\|structure VSepWpOrdRel" \
     anneal/trusted/lean/Trusted/Framework.lean \
     anneal/trusted/lean/Trusted/Framework/Instances.lean \
     anneal/theory/Anneal/MiriTreeBorrows/Model.lean \
     anneal/theory/Anneal/WavefrontReclaim/Wavefront.lean
   ```
   Confirms whether `ExecutionModel`, `AssumedStub`, `MirProfileV2`, `VProp`/`VSepWpOrdRel`, and `MiriPerm.cell` invariance retain the signatures relied upon by this design analysis.
