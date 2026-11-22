# Weak-Memory Verification Polarity in Rust: Miri Store-Buffer Set-Incomparability, Unbounded RC11/SRA Operational Semantics, and Step-Index-Free GPS/FSL ViewPCMs in 3-Axiom Lean 4

## Summary

Dynamic bug-finders and deductive verifiers sit on **opposite sides of weak-memory approximation polarity**: a bug-finder avoids false alarms when $\mathsf{Beh}_{\text{tool}} \subseteq \mathsf{Beh}_{\text{spec}}$, whereas a deductive verifier avoids false safety proofs only when $\mathsf{Beh}_{\text{target}} \subseteq \mathsf{Beh}_{\text{model}}$. Primary-source analysis of `rust-lang/miri` (`src/concurrency/weak_memory.rs`), `proofs-rs/lean-miri` (`Miri/Concurrency/{WeakMemory,DataRace,AtomicDispatch}.lean`), `rust-lang/rust` (`Arc::drop`, Linux futex shim), `crossbeam-rs/crossbeam` (`SeqLock`, `AtomicCell`, `ArrayQueue`, `crossbeam-epoch`), and `google/zerocopy` (`anneal/trusted/audit/TrustedBoundary.lean`) establishes four core results:

1. **`Miri.Concurrency.WeakMemory` Is Set-Incomparable With C++20/`RC11` (Neither $\subseteq$ Nor $\supseteq$ Holds):**
   - **Under-approximation (`Beh_RC11 ⊈ Beh_MiriWeak`):** Miri's per-location store buffer (`weak_memory.rs`, ported 1-to-1 in `WeakMemory.lean`) omits legal C++20/`RC11` relaxed behaviors along three concrete axes:
     - *128-Write Modification-Order Eviction (`STORE_BUFFER_LIMIT = 128`, `weak_memory.rs:111, 442–445`, `WeakMemory.lean:35, 350–367`):* Appending a 129th store evicts `buffer.oldest`, rendering stores $\ge 128$ writes behind `mo`-latest permanently unreadable even when zero happens-before (`CoWR`) or read-coherence (`CoRR`) edges block them.
     - *Mandatory `buffer.last` RMW / Failed-CAS Reads (`weak_memory.rs:5–7, 280–292, 524–525, 643–675`; `WeakMemory.lean:314–328`):* Because Miri steps threads in a single global timeline and forces every RMW (`readFromLastStore`) and failed `compare_exchange` (`perform_read_on_buffered_latest`) to read exclusively `buffer.last`, a 2-thread, 2-store defective `SeqLock` writer omitting `fence(Release)` after `STAMP.store(1, Relaxed)` passes 100% of Miri schedules when the reader revalidates via `fetch_add(0, Relaxed)` or `compare_exchange`, yet exhibits torn reads (`s1 == 0 ∧ d == 99 ∧ s2 == 0`) under C++20, `RC11`, `SRA`, and ARMv8 hardware.
     - *`SeqCst` Fence Over-Synchronization (`weak_memory.rs:9–28`):* Modeling `fence(SeqCst)` as an `AcqRel` RMW on a single global clock suppresses legal weak behaviors.
   - **Over-approximation on 3+ Threads (`Beh_MiriWeak ⊈ Beh_RC11`, `rust-lang/miri#2301`):** Contrary to `weak_memory.rs:5–7`, `markBeforeSeqCstStore` (`WeakMemory.lean:331–337`) and `filterSeqCst` (`WeakMemory.lean:174–182`) admit **illegal `SeqCst` stale reads** on 3 threads: `T1: y.store(2, Relaxed); x.store(1, SeqCst)` || `T2: r1 = x.load(SeqCst); r2 = y.load(SeqCst)` || `T3: y.store(1, SeqCst); r3 = x.load(SeqCst)` reaches `(r1 = 1, r2 = 2, r3 = 0)`, which is forbidden by C++11, `RC11`, and C++20 `P0668R5`.
   - **Pass-2 Correspondence Consequence:** Even one-way simulation $\mathsf{Beh}_{\text{MiriWeak}} \subseteq \mathsf{Beh}_{\text{RC11View}}$ is **false**. Pass-2 correspondence against `vendor/lean-miri` must instead couple the sequentially consistent restriction $M_{\text{anneal}}^{\text{SC}}$ against `MiriSC` (`weakMemory = false` in `GlobalState.lean` / `AtomicDispatch.lean`) for bidirectional equivalence ($\mathsf{Beh}_{\text{MiriSC}} = \mathsf{Beh}_{\text{AnnealSC}}$ and $\mathsf{Fault}_{\text{MiriSC}} \leftrightarrow \mathsf{Fault}_{\text{AnnealSC}}$), while modeling Linux `futex_wait` with a demonic spurious-wakeup transition without `acquire` clock synchronization (`rust-lang/rust` @ `49d7345362` `linux_like/sync.rs:148` also upgraded `FUTEX_WAIT`'s check load from `Relaxed` to `Acquire`).
2. **Unbounded Timestamp-View Operational `RC11` / `SRA+Fence` Anchor:** A sound concurrent TCB step relation (`Trusted` `candidate:concurrency`) must maintain an **unbounded modification-order message pool** $(\ell, v, t, V_{\text{msg}})$ supporting non-maximal timestamp insertion for `Release`/`Relaxed` writes and coherence-admissible RMW selection, paired with per-thread `(cur, acq, rel)` timestamp views (Lahav et al., POPL 2016 & PLDI 2017) isomorphic to `DataRace.lean`'s `clock`, `fenceAcquire`, and `fenceRelease` (`L121–151`).
3. **Why FSL's $\triangle P$ / $\nabla P$ Fence Modalities Are Mandatory Beyond GPS:** Pure Release-Acquire logics (`GPS`, OOPSLA 2014) attach resources directly to `Release` stores and `Acquire` loads. Production Rust primitives systematically split synchronization across **`Relaxed` accesses + standalone fences** (`SeqLock::validate_read`, `SeqLock::write`, `Arc::drop`, and `crossbeam-epoch::Global::try_advance`), which Fenced Separation Logic (`FSL`, VMCAI 2016) captures via acquire-pending $\triangle P$ (`ReleasedAt reqV P`) and release-prepared $\nabla P$ (`Releasing tv P`).
4. **Step-Index-Free `ViewPCM` Mechanization and Exact `TrustedBoundary.lean` Universe / `._unsafe_rec` Rules:** `TrustedBoundary.lean` (`google/zerocopy` @ `f2efbfd1eb0c`) **already admits `universe u`** (bare level identifiers such as `LawfulPCM (M : Type u)`, with elaborator-inferred instantiation) on intermediate `theory/` declarations, enforcing `levelParams.isEmpty` strictly at root claim and theorem endpoints (`requireClaimProof`). Avoiding step-indexed impredicative `Type 1`+ Kripke worlds keeps first-order protocol proofs (`SeqLock`, `Arc`, `ArrayQueue`, 3-epoch EBR) lightweight in Pass-1 Lean 4 (`v4.34.1`); under `prelude` without `Init.WF`, recursive helpers must use primitive `@Nat.rec` / `@List.rec` (and `noncomputable def` for `Type`-valued list recursors) so Lean does not synthesize rejected `*._unsafe_rec` auxiliaries (`replayedDeclarations: 64, reachableDeclarations: 457, compilerOnlyNames: 0, axioms: ['propext'], replay: True, requireMirWp: false`).

## Applicability

These findings govern concurrent `unsafe` Rust verification, Miri/`lean-miri` correspondence polarity, and `theory/` design across the subjects in `REPORT.json`:

- **Miri and `lean-miri` concurrency engines (`rust-lang/miri` @ `7fa591d7d4` & `bc1b6da0d3`; `proofs-rs/lean-miri` @ `c92d1d9754`; `google/zerocopy` @ `f2efbfd1eb0c`):** Covers `src/concurrency/{weak_memory.rs, data_race.rs}`, `src/shims/unix/linux_like/sync.rs`, and `Miri/Concurrency/{WeakMemory.lean, DataRace.lean, AtomicDispatch.lean, GlobalState.lean}`. Both `7fa591d7d4` and `bc1b6da0d3` exhibit the 128-entry `STORE_BUFFER_LIMIT`, `readFromLastStore`, and `miri#2301` 3-thread `SeqCst` over-approximation; in `rust-lang/rust` @ `49d7345362`, `linux_like/sync.rs:148` uses `Acquire` for `FUTEX_WAIT`'s comparison load (whereas `Miri/Interpreter/LinuxFutex.lean` in `c92d1d9754` models the earlier `Relaxed` check). In single-threaded sequential MIR execution (`!global.raceDetecting`, `AtomicDispatch.lean:107`), `WeakMemory` is inactive.
- **Standard library and `crossbeam` primitives (`rust-lang/rust` @ `8144389c89` & `49d7345362`; `crossbeam-rs/crossbeam` @ `a28f40fddd`):** Covers `alloc::sync::Arc` (`library/alloc/src/rcs/arc.rs`), `SeqLock` (`crossbeam-utils/src/atomic/{seq_lock.rs, seq_lock_wide.rs, atomic_cell.rs}`), Vyukov `ArrayQueue` (`crossbeam-queue/src/array_queue.rs`), and 3-epoch EBR (`crossbeam-epoch/src/internal.rs`).
- **Zero-TCB Lean 4 boundary (`joshlf/anneal` @ `20aa204315`, `google/zerocopy` @ `f2efbfd1eb0c`, and `leanprover/lean4` `v4.34.1` @ `5045d00564`):** Covers `SourceRole.theory` modules audited by `trusted/audit/TrustedBoundary.lean` over `trusted/lean/foundation-lock.json`.
- **Normative Literature:** Lahav et al. `RC11` (PLDI 2017, DOI `10.1145/3062341.3062352`), Lahav et al. `SRA` (POPL 2016, DOI `10.1145/2837614.2837643`), Turon et al. `GPS` (OOPSLA 2014, DOI `10.1145/2660193.2660243`), Doko & Vafeiadis `FSL` (VMCAI 2016, DOI `10.1007/978-3-662-49122-5_20`), and Meyer & Wolff EBR life-cycle types (POPL 2020, DOI `10.1145/3371136`).

## Findings

### 1. Set-Incomparability of Miri's `StoreBuffer`: Completeness Gaps AND the `miri#2301` `SeqCst` Soundness Breach

`Basis: source + derived`

Miri's weak-memory emulator (`src/concurrency/weak_memory.rs:1–92`, adapted from Lidbury & Donaldson's `tsan11`, POPL 2017, DOI `10.1145/3009837.3009857`) asserts at lines 5–7 that it *"will never generate weak memory behaviours forbidden by the C++11 model, but it is incapable of producing all possible weak behaviours allowed by the model."* Direct inspection of `WeakMemory.lean` shows that **both** inclusions between $\mathsf{Beh}_{\text{MiriWeak}}$ and $\mathsf{Beh}_{\text{C++20}} / \mathsf{Beh}_{\text{RC11}}$ fail:

1. **Bounded 128-Write Modification-Order Eviction (`STORE_BUFFER_LIMIT = 128`, `WeakMemory.lean:35, 108–111, 350–367`; `weak_memory.rs:111, 442–445`):**
   `StoreBuffer` holds `oldest` plus `newer` (`newer.length < 128`). On the 129th store, `storeImpl` drops `buffer.oldest` (`oldest := nextOldest`), making stores $\ge 128$ writes behind `mo`-latest permanently unreadable (`Eviction128_TagABA`; notably, `crossbeam-epoch/src/internal.rs:340` sets `PINNINGS_BETWEEN_COLLECT = 128`).
2. **Mandatory `buffer.last` RMW / Failed-CAS Reads + Global Step Order (`BuggySeqLockRmw`, `WeakMemory.lean:314–328`; `weak_memory.rs:524–525, 643–675`):**
   Miri appends stores strictly in global execution order and forces both RMWs (`readFromLastStore`) and failed `compare_exchange` (`perform_read_on_buffered_latest`) to read exclusively `buffer.last`. Consider a 2-thread, 2-store defective `SeqLock` writer omitting `fence(Release)` after `STAMP.store(1, Relaxed)`:
   ```rust
   // Initial: STAMP = 0, DATA = 0
   // Thread 1 (Defective Writer): STAMP.store(1, Relaxed); /* W1 */ DATA.store(99, Relaxed); /* W2 */
   // Thread 2 (Reader):
   let s1 = STAMP.load(Ordering::Acquire);         // R1
   let d  = DATA.load(Ordering::Relaxed);          // R2
   core::sync::atomic::fence(Ordering::Acquire);   // F_acq
   let s2 = STAMP.fetch_add(0, Ordering::Relaxed); // R3 (or compare_exchange(0, 0, Relaxed, Relaxed))
   ```
   - *Legal in `RC11` / `SRA` / C++20 / ARMv8:* `mo(STAMP): init(0) < R3(0) < W1(1)` yields `(s1 = 0, d = 99, s2 = 0)`.
   - *Impossible in `Miri.WeakMemory` (0% of runs):* Reading `d = 99` requires `W1` to already be `STAMP.buffer.last`, so `readFromLastStore` unconditionally returns `1`.
3. **Illegal 3-Thread `SeqCst` Stale Read (`Beh_MiriWeak ⊈ Beh_RC11`, `WeakMemory.lean:150–182, 217–220, 331–370`; `rust-lang/miri#2301`):**
   Consider three threads with initial `x = 0, y = 0`:
   ```text
   T1: y.store(2, Relaxed); x.store(1, SeqCst)
   T2: r1 = x.load(SeqCst); r2 = y.load(SeqCst)
   T3: y.store(1, SeqCst);  r3 = x.load(SeqCst)
   ```
   Execute in global step order:
   1. `T1` runs `y.store(2, Relaxed)`: `y.entries = [init_y(0, isSeqCst=false), W_T1(y,2, isSeqCst=false)]`.
   2. `T3` runs `y.store(1, SeqCst)`: `y.entries = [init_y(0, isSeqCst=true), W_T1(y,2, isSeqCst=false), W_T3(y,1, isSeqCst=true)]`. Because `T3`'s `threadClock` does not dominate `W_T1`'s `storeTimestamp` and `W_T1` has no prior loads, `markBeforeSeqCstStore` (`L331–337`) leaves `W_T1(y,2)` with **`isSeqCst = false`** even though `W_T1(y,2) ->_mo W_T3(y,1)`.
   3. `T3` runs `r3 = x.load(SeqCst)`: reads `init_x` (`r3 = 0`).
   4. `T1` runs `x.store(1, SeqCst)`: appends `W_T1(x,1, isSeqCst=true)` to `x`.
   5. `T2` runs `r1 = x.load(SeqCst)`: reads `W_T1(x,1)` (`r1 = 1`), acquiring `T1`'s `syncClock` (dominating `W_T1(y,2)`, with zero clock for `T3`).
   6. `T2` runs `r2 = y.load(SeqCst)`: `reverseIndexed(y)` is `[W_T3(y,1, isSeqCst=true), W_T1(y,2, isSeqCst=false), init_y(0, isSeqCst=true)]`. `blocksEarlier` (`L150–160`) is `false` on `W_T3(y,1)` and `true` on `W_T1(y,2)`, giving `candidatePrefix = [W_T3(y,1), W_T1(y,2)]`. Because `W_T1(y,2).isSeqCst == false`, `filterSeqCst` (`L174–182`, line 181) **retains `W_T1(y,2)`**, so `rank = 1` returns **`r2 = 2`**.

   Yet `(r1 = 1, r2 = 2, r3 = 0)` is **forbidden** in C++11, `RC11`, and C++20 `P0668R5`: `W_T1(x,1) ->_sw r1 ->_sb r2` gives `(W_T1(x,1), r2) ∈ shb ⊆ S`, `r2 ->_fr W_T3(y,1)` gives `(r2, W_T3(y,1)) ∈ S`, `W_T3(y,1) ->_sb r3` gives `(W_T3(y,1), r3) ∈ S`, and `r3 ->_fr W_T1(x,1)` closes the `S`-cycle.

---

### 2. Unbounded Timestamp Operational `RC11` / `SRA+Fence` Semantics and `MiriSC` Pass-2 Correspondence

`Basis: normative + source + derived`

Lahav et al.'s operational timestamp machine (`SRA`, POPL 2016, DOI `10.1145/2837614.2837643`; `RC11`, PLDI 2017, DOI `10.1145/3062341.3062352`) resolves both under-approximation gaps:

- **Unbounded Non-Maximal Message Pool:** Atomic writes insert $(\ell, v, t, V_{\text{msg}})$ into an eviction-free pool at **any unoccupied modification-order timestamp** $t > V_{\text{cur}}(\ell)$ (adjacent to an existing message iff RMW). In `BuggySeqLockRmw`, Thread 1 inserts `W1 = (STAMP, 1, t = 2, ⊥)` and `W2 = (DATA, 99, t = 1, ⊥)`, allowing Thread 2's RMW `R3` to slot cleanly at `t = 1` (`0 < R3 < W1`) and expose `(s1 = 0, d = 99, s2 = 0)` in 4 steps.
- **View Isomorphism With `DataRace.lean` (`L121–151, 340–414`):** Each thread's location-indexed views $(V_{\text{cur}}, V_{\text{acq}}, V_{\text{rel}})$ mirror `DataRace.lean`'s `(clock, fenceAcquire, fenceRelease)`: `load(Relaxed)` joins $V_{\text{msg}}[\ell \mapsto t]$ into $V_{\text{acq}}$; `load(Acquire)` joins into both $V_{\text{cur}}$ and $V_{\text{acq}}$; `fence(Acquire)` sets $V_{\text{cur}} \leftarrow V_{\text{cur}} \sqcup V_{\text{acq}}$; `fence(Release)` sets $V_{\text{rel}} \leftarrow V_{\text{cur}}$; `store(Relaxed)` publishes $V_{\text{msg}} := V_{\text{rel}}$; and `store(Release)` publishes $V_{\text{msg}} := V_{\text{cur}}$. Non-atomic accesses enforce per-byte happens-before race freedom (`DataRace.lean:417–452`), faulting to `FaultKind.undefined` on any race.
- **Pass-2 Correspondence Architecture (`MiriSC`, Not `Beh_MiriWeak ⊆ Beh_RC11`):** Because $\mathsf{Beh}_{\text{MiriWeak}}$ and $\mathsf{Beh}_{\text{RC11}} / \mathsf{Beh}_{\text{C++20}}$ are set-incomparable (`miri#2301`), Pass-2 correspondence against `vendor/lean-miri` cannot state $\mathsf{Beh}_{\text{MiriWeak}} \subseteq \mathsf{Beh}_{M_{\text{anneal}}}$. Instead, Pass-2 correspondence must enforce **bidirectional equivalence on sequentially consistent schedules** by restricting $M_{\text{anneal}}$ to maximal-timestamp `SC` steps ($M_{\text{anneal}}^{\text{SC}}$) and coupling it against `MiriSC` (`weakMemory = false` in `Miri/Concurrency/{GlobalState,AtomicDispatch}.lean`): $\mathsf{Beh}_{\text{MiriSC}} = \mathsf{Beh}_{\text{AnnealSC}}$ and $\mathsf{Fault}_{\text{MiriSC}} \leftrightarrow \mathsf{Fault}_{\text{AnnealSC}}$. Weak-memory extensions (`ORC11`/`C++20 P0668R5` non-maximal writes, `STime` `SeqCst` ordering, and demonic spurious-wakeup `futex_wait`) are audited separately against the normative C++20/hardware specifications.

---

### 3. Protocol Anatomy of Production Rust Primitives: `SeqLock`, `Arc::drop`, `ArrayQueue`, and EBR

`Basis: source + derived`

1. **`crossbeam` `SeqLock` (`seq_lock.rs:28–93`, `seq_lock_wide.rs:35–140`) & `AtomicCell` `read_volatile` UB (`atomic_cell.rs:1014–1035`):**
   `SeqLock::write` (`seq_lock.rs:48–51`) executes `state.swap(1, Acquire)` + **`fence(Release)`**, mutates payload, and unlocks via `state.store(prev.wrapping_add(2), Release)` (`L90–92`, or `abort()` `L76–82` only when zero writes occurred). Readers call `state.load(Acquire)` (`!= 1`), read payload, and run `fence(Acquire); state.load(Relaxed) == stamp` (`L39–40`; `seq_lock_wide.rs` adds `state_hi` with `Acquire` `state_lo` validation to guard 32-bit wraparound). Crucially, `atomic_cell.rs:1016–1025` uses `ptr::read_volatile(src.cast::<MaybeUninit<T>>())` racing with non-atomic `ptr::write` (`L1052`)—immediate data-race UB under C++20/`RC11`/`DataRace.lean:427`. Sound Rust `SeqLock<T>` implementations must access payload words via `Relaxed` atomic loads and stores, materializing `T` only after `validate_read` succeeds.
2. **`alloc::sync::Arc::drop` (`library/alloc/src/rcs/arc.rs:57–72, 2234–2247, 2976–3026`):**
   Non-final droppers execute `strong.fetch_sub(1, Release) != 1` and return immediately (paying zero `Acquire` cost while extending `strong`'s release sequence, `DataRace.lean:392–401`). The final dropper (`prev == 1`) absorbs that release sequence into `V_acq` via the `Relaxed` read half of `fetch_sub(1, Release)` (`DataRace.lean:644`) and runs `acquire!(strong)` (`atomic::fence(Acquire)`, `arc.rs:60, 3012`) to promote `V_acq` into `V_cur` before `ptr::drop_in_place(&mut (*ptr).data)`.
3. **Vyukov `ArrayQueue<T>` (`crossbeam-queue/src/array_queue.rs:31–40, 148–191, 336–378`):**
   Each `Slot<T>` pairs `stamp: AtomicIndex` with `UnsafeCell<MaybeUninit<T>>`. Producers observe `slot.stamp.load(Acquire) == tail`, claim via `tail.compare_exchange_weak`, write `slot.value` non-atomically, and publish `slot.stamp.store(tail + 1, Release)`; consumers observe `slot.stamp.load(Acquire) == head + 1`, claim `head`, read `slot.value`, and advance `slot.stamp` to `head + one_lap` (`Release`), transferring exclusive `UnsafeCell` ownership across laps without data races.
4. **`crossbeam-epoch` 3-Epoch EBR (`crossbeam-epoch/src/internal.rs:155–162, 237–293, 408–484`):**
   `pin()` stores `global_epoch.pinned()` (`Relaxed`) + `fence(SeqCst)` (`L451–452`); `unpin()` stores `0` (`Release`, `L476`). `try_advance()` (`L237–293`) checks via `local.epoch.load(Relaxed)` (`L263`) that every pinned thread matches `global_epoch`, executes **`fence(Acquire)`** (`L281`) to absorb all prior `unpin()` `Release` views, and increments `global.epoch` (`Release`). `SealedBag::is_expired` (`L160`) frees bags sealed at `e` iff `global_epoch.wrapping_sub(e) >= 2` (Meyer & Wolff, POPL 2020).

---

### 4. Kernel-Checked `GPS`/`FSL` `ViewPCM` Mechanization in Pass-1 3-Axiom Lean 4

`Basis: source + execution + derived`

Iris requires step-indexing ($\triangleright P$) and impredicative heap-stored invariants only when heap locations store higher-order self-referential predicates. Note on `TrustedBoundary.lean` (`google/zerocopy` @ `f2efbfd1eb0c`): `TrustedBoundary.lean` **admits `universe u`** on intermediate `SourceRole.theory` declarations (such as `LawfulPCM (M : Type u)` below, using bare universe identifiers with elaborator-inferred instantiation) while enforcing `levelParams.isEmpty` strictly on root claim and theorem endpoints (`requireClaimProof`). Because `SeqLock`, `Arc`, Vyukov `ArrayQueue`, and 3-epoch EBR are first-order monotone protocols (`GPS` + `FSL`), we mechanize `ThreadViews`, `ReleasedAt` ($\triangle P$), `Releasing` ($\nabla P$), `SeqLock` validation soundness, $N$-way `Arc::drop` synchronization, and 3-epoch EBR reclamation directly in Pass-1 Lean 4 (`v4.34.1`, locked `Init.*` only). Using `@Nat.rec`, `@List.rec`, and `noncomputable def` on `joinAllViews` avoids the hidden `*._unsafe_rec` auxiliaries synthesized by equation-compiler recursion under `prelude` without `Init.WF`. The module below compiles with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` and passes live `TrustedBoundary.lean` `"preflight"` + `"audit"` (`replayedDeclarations: 64, reachableDeclarations: 457, compilerOnlyNames: 0, axioms: ['propext'], replay: True, requireMirWp: false`):

```lean
-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Option.Basic

namespace Anneal.Concur.ViewPCM

abbrev View := Nat → Nat

def emptyView : View := fun _ => 0

def viewLe (v1 v2 : View) : Prop :=
  ∀ loc : Nat, v1 loc ≤ v2 loc

def viewJoin (v1 v2 : View) : View :=
  fun loc => if v1 loc ≤ v2 loc then v2 loc else v1 loc

private theorem nat_le_antisymm (a : Nat) : ∀ {b : Nat}, a ≤ b → b ≤ a → a = b :=
  @Nat.rec (fun a => ∀ {b : Nat}, a ≤ b → b ≤ a → a = b)
    (fun {b} _ hba =>
      match b, hba with
      | 0, _ => rfl
      | Nat.succ k, hba => False.elim (Nat.not_succ_le_zero k hba))
    (fun m ih {b} hab hba =>
      match b, hab, hba with
      | 0, hab, _ => False.elim (Nat.not_succ_le_zero m hab)
      | Nat.succ _, hab, hba =>
        congrArg Nat.succ (ih (Nat.le_of_succ_le_succ hab) (Nat.le_of_succ_le_succ hba)))
    a

theorem viewLe_refl (v : View) : viewLe v v := by
  intro loc
  exact Nat.le_refl (v loc)

theorem viewLe_trans {v1 v2 v3 : View}
    (h12 : viewLe v1 v2) (h23 : viewLe v2 v3) : viewLe v1 v3 := by
  intro loc
  exact Nat.le_trans (h12 loc) (h23 loc)

theorem viewLe_join_left (v1 v2 : View) : viewLe v1 (viewJoin v1 v2) := by
  intro loc
  dsimp [viewJoin]
  cases Decidable.em (v1 loc ≤ v2 loc) with
  | inl h => simp [h]
  | inr h => simp [h]

theorem viewLe_join_right (v1 v2 : View) : viewLe v2 (viewJoin v1 v2) := by
  intro loc
  dsimp [viewJoin]
  cases Decidable.em (v1 loc ≤ v2 loc) with
  | inl h => simp [h]
  | inr h =>
    have hGe : v2 loc ≤ v1 loc := Nat.le_of_not_ge h
    simp [h, hGe]

/-- Per-thread 3-view front matching `DataRace.lean:121-151` (`clock`, `fenceAcquire`, `fenceRelease`). -/
structure ThreadViews where
  cur : View
  acq : View
  rel : View

def applyFenceRelease (tv : ThreadViews) : ThreadViews :=
  { cur := tv.cur, acq := tv.acq, rel := tv.cur }

def applyFenceAcquire (tv : ThreadViews) : ThreadViews :=
  { cur := viewJoin tv.cur tv.acq, acq := tv.acq, rel := tv.rel }

def applyRelaxedLoad (tv : ThreadViews) (msgView : View) : ThreadViews :=
  { cur := tv.cur, acq := viewJoin tv.acq msgView, rel := tv.rel }

def applyAcquireLoad (tv : ThreadViews) (msgView : View) : ThreadViews :=
  { cur := viewJoin tv.cur msgView, acq := viewJoin tv.acq msgView, rel := tv.rel }

universe u

structure LawfulPCM (M : Type u) where
  unit      : M
  op        : M → M → Option M
  unit_left : ∀ a : M, op unit a = some a
  comm      : ∀ a b : M, op a b = op b a

/-- FSL Acquire-Pending Modality `△ P` (`ReleasedAt reqV P`, Doko & Vafeiadis VMCAI 2016). -/
def ReleasedAt (reqV : View) (P : Prop) : Prop :=
  ∀ curV : View, viewLe reqV curV → P

/-- FSL Release-Prepared Modality `∇ P` (`Releasing tv P`), introduced by `fence(Release)`. -/
def Releasing (tv : ThreadViews) (P : Prop) : Prop :=
  ∃ prepView : View, viewLe prepView tv.rel ∧ ReleasedAt prepView P

theorem fence_release_intro (tv : ThreadViews) {P : Prop} (hP : P) :
    Releasing (applyFenceRelease tv) P :=
  ⟨tv.cur, viewLe_refl tv.cur, fun _ _ => hP⟩

theorem relaxed_load_then_fence_acquire_elim
    (tv : ThreadViews) (msgV : View) {P : Prop} (hMsg : ReleasedAt msgV P) :
    P ∧ viewLe msgV (applyFenceAcquire (applyRelaxedLoad tv msgV)).cur := by
  dsimp only [applyRelaxedLoad, applyFenceAcquire]
  have hAcq : viewLe msgV (viewJoin tv.acq msgV) := viewLe_join_right tv.acq msgV
  have hCur : viewLe (viewJoin tv.acq msgV) (viewJoin tv.cur (viewJoin tv.acq msgV)) :=
    viewLe_join_right tv.cur (viewJoin tv.acq msgV)
  have hFull : viewLe msgV (viewJoin tv.cur (viewJoin tv.acq msgV)) := viewLe_trans hAcq hCur
  exact ⟨hMsg _ hFull, hFull⟩

/-- `SeqLock` multi-word snapshot consistency (`seq_lock.rs:28-93`): when `s1` is even,
    every `Relaxed` word read has modification-order stamp bracketed `s1 <= ws <= s2` (via writer
    `fence(Release)` + reader `fence(Acquire)`), and `s1 = s2`, all words belong to snapshot `s1`. -/
def allWordsAtStamp (targetStamp : Nat) (stamps : List Nat) : Prop :=
  @List.rec Nat (fun _ => Prop) True (fun ws _ ih => ws = targetStamp ∧ ih) stamps

def wordsBoundedBetween (lo hi : Nat) (stamps : List Nat) : Prop :=
  @List.rec Nat (fun _ => Prop) True (fun ws _ ih => (lo ≤ ws ∧ ws ≤ hi) ∧ ih) stamps

theorem seqlock_validate_read_sound
    (s1 s2 : Nat) (wordStamps : List Nat)
    (hEven : Nat.beq (Nat.land s1 1) 0 = true)
    (hBounded : wordsBoundedBetween s1 s2 wordStamps)
    (hValid : s1 = s2) :
    allWordsAtStamp s1 wordStamps ∧ Nat.beq (Nat.land s2 1) 0 = true := by
  subst hValid
  refine ⟨?_, hEven⟩
  induction wordStamps with
  | nil => exact True.intro
  | cons ws _ ih =>
    cases hBounded with
    | intro hHead hTail =>
      cases hHead with
      | intro hLo hHi =>
        exact ⟨nat_le_antisymm ws hHi hLo, ih hTail⟩

/-- `Arc::drop` (`arc.rs:2980-3025`) release-sequence join: `fetch_sub(1, Release)` (`Relaxed` read half)
    followed by `acquire!(strong)` (`fence(Acquire)`) synchronizes with ALL `N` prior holders! -/
noncomputable def joinAllViews (views : List View) : View :=
  @List.rec View (fun _ => View) emptyView (fun v _ acc => viewJoin v acc) views

def allViewsSynchronized (curV : View) (views : List View) : Prop :=
  @List.rec View (fun _ => Prop) True (fun v _ ih => viewLe v curV ∧ ih) views

private theorem allViewsSynchronized_of_join_le
    (curV : View) (holderViews : List View)
    (hBase : viewLe (joinAllViews holderViews) curV) :
    allViewsSynchronized curV holderViews := by
  induction holderViews with
  | nil => exact True.intro
  | cons v vs ih =>
    have hLeft : viewLe v (viewJoin v (joinAllViews vs)) := viewLe_join_left v (joinAllViews vs)
    have hRight : viewLe (joinAllViews vs) (viewJoin v (joinAllViews vs)) :=
      viewLe_join_right v (joinAllViews vs)
    exact ⟨viewLe_trans hLeft hBase, ih (viewLe_trans hRight hBase)⟩

theorem arc_drop_last_synchronizes_all
    (tv : ThreadViews) (holderViews : List View) :
    allViewsSynchronized
      (applyFenceAcquire (applyRelaxedLoad tv (joinAllViews holderViews))).cur
      holderViews := by
  apply allViewsSynchronized_of_join_le
  dsimp only [applyRelaxedLoad, applyFenceAcquire]
  exact viewLe_trans
    (viewLe_join_right tv.acq (joinAllViews holderViews))
    (viewLe_join_right tv.cur (viewJoin tv.acq (joinAllViews holderViews)))

/-- Meyer & Wolff (POPL 2020) / `crossbeam-epoch` (`internal.rs:157-161`) 3-epoch grace-period safety. -/
theorem ebr_three_epoch_reclaim_safe
    (retiredEpoch globalEpoch activePin : Nat)
    (hExpired : retiredEpoch + 2 ≤ globalEpoch)
    (hPinLagAtMostOne : globalEpoch ≤ activePin + 1) :
    retiredEpoch < activePin := by
  have hChain : retiredEpoch + 2 ≤ activePin + 1 := Nat.le_trans hExpired hPinLagAtMostOne
  exact Nat.le_of_succ_le_succ hChain

end Anneal.Concur.ViewPCM
```

---

### 5. Evaluation Across the Zero-TCB Verification Rubric

`Basis: source + execution + derived`

| Criterion | Grade | Assessment & Separating Justification |
| :--- | :---: | :--- |
| **`(T1)` 0-TCB Bridge** | **Minimal `RC11`/`P0668R5` Hook + 0-TCB Logic** | `Anneal.Concur.ViewPCM` lives 100% in untrusted `theory/`. `Trusted` `candidate:concurrency` couples its `SC` restriction $M_{\text{anneal}}^{\text{SC}}$ bidirectionally against `vendor/lean-miri` `MiriSC` (`weakMemory = false`), avoiding `Miri.WeakMemory`'s set-incomparability (`miri#2301` + 128-store / `buffer.last` gaps). |
| **`(P1)` Human Spec Auditability** | **Strong** | Specs express logical ownership/snapshots (`Arc` unique drop, `ArrayQueue` FIFO `T: Send`, `SeqLock` authentic snapshot) with zero `View` leakage in `Expected` theorems (Statement-Origin Separation). |
| **`(P2)` Authoring & Day-2 Locality** | **Strong** | Thread-modular `GPS`/`FSL` protocol rules avoid $O(k!)$ interleaving enumeration and remain invariant under backoff/spin tuning (`seq_lock.rs:59`). |
| **`(P3)` Lean 4 (`v4.34.1`) Kernel & `<50ms` LSP** | **Strong** | Step-index-free `View` inequalities with `@Nat.rec`/`@List.rec` avoid `._unsafe_rec`, step-index $\triangleright^n$ unfolding, and impredicative Kripke worlds. |
| **`(P4)` Heterogeneous Composability** | **Strong** | `ReleasedAt reqV P` composes orthogonally with `MaybeUninit<u8>` byte-validity (`SeqLock` torn reads), `UnsafeCell` ranges (`ArrayQueue`), and RAII `Drop` guards. |
| **`(P5)` Failure Legibility** | **Moderate–Strong** | Missing `fence(Acquire)` leaves `msgV` trapped in `tv.acq` (`viewLe msgV tv.cur` unprovable), pinpointing the omitted fence. |
| **`(C1–C2)` Conceptual Minimality** | **Locally Minimal** | Unifies `AcqRel`, fenced `Relaxed`, `Arc` release sequences, and 3-epoch EBR in one `ThreadViews` record + dual `(ReleasedAt, Releasing)`; refuted collapses: (1) `RC11` $\neq$ `Miri.StoreBuffer` (`BuggySeqLockRmw`, `Eviction128_TagABA`, `miri#2301`); (2) `FSL` $\neq$ `GPS` (`Arc::drop` `fetch_sub(Release)` + `fence(Acquire)`); (3) atomic `MaybeUninit` `SeqLock` $\neq$ `read_volatile` (`atomic_cell.rs:1017`). |

## Boundaries

- **`Ordering::Consume` (`memory_order_consume`):** **known not to apply** in Rust (`Ordering` exposes only `Relaxed`, `Acquire`, `Release`, `AcqRel`, `SeqCst`; `DataRace.lean:21–28`, `weak_memory.rs:29`).
- **Load-Buffering (`LB`) Cycles Beyond `RC11` `(sb ∪ rf)+` Acyclicity:** `RC11` forbids `r1 == 1 ∧ r2 == 1` on `LB`, whereas ARMv8/RVWMO hardware permits independent `LB` under plain `ldr`/`str` lowering. Whether Rust's normative specification will adopt Promising Semantics 2.1 / Weakestmo to admit independent `LB` without thin-air UB is **unknown** (`weak_memory.rs:31–37`). Monotone `GPS`/`FSL` `ViewPCM` proofs remain sound across that extension because they rely only on `hb` and `mo`, never `(sb ∪ rf)` acyclicity on `Relaxed` cycles.
- **x86 `lock cmpxchg` Replacement of `fence(SeqCst)` in `crossbeam-epoch`:** `crossbeam-epoch/src/internal.rs:421–450` replaces `fence(SeqCst)` on `x86`/`x86_64` (`not(miri)`) with `compare_exchange(..., SeqCst, SeqCst)` + `compiler_fence(SeqCst)`, which is sound on hardware x86-TSO (`lock cmpxchg` drains the store buffer) but **known not to apply** under portable C++20/`RC11` IR rules (`internal.rs:433–435`).
- **Higher-Order Impredicative Heap-Stored Invariants:** Lock-free structures storing arbitrary heap-quantifying closures are **unsupported** in step-index-free `Type 0` `ViewPCM` without Reynolds defunctionalization (`FuncId` + fuel-indexed `@Nat.rec`); likewise, mixed-size racing atomics without happens-before synchronization are **unsupported** (UB in `weak_memory.rs:64`).
- **POSIX Signal-Handler Weak-Memory Interactions:** POSIX async-signal-handler fence rules were **not examined** in this package.

## Evidence

- **`rust-lang/miri` @ `7fa591d7d4` (`2026-11-20`) & `bc1b6da0d3` (`2026-11-22`):** `src/concurrency/weak_memory.rs` (`L1–92, 107–111, 189–259, 280–292, 339–468, 497–535, 643–676`).
- **`proofs-rs/lean-miri` @ `c92d1d9754` (`2026-11-20`, revalidated in `google/zerocopy` @ `f2efbfd1eb0c` on `2026-11-22`):** `Miri/Concurrency/WeakMemory.lean` (`L35, 108–111, 149–253, 314–380, 421–518`), `Miri/Concurrency/DataRace.lean` (`L21–151, 309–452, 639–653`), `Miri/Concurrency/AtomicDispatch.lean` (`L103–124`), `Miri/Interpreter/LinuxFutex.lean` (`L83`).
- **`rust-lang/rust` @ `8144389c89` (`2026-11-20`) & `49d7345362` (`2026-11-22`):** `library/alloc/src/rcs/arc.rs` (`L57–72, 2234–2247, 2976–3026`), `src/tools/miri/src/shims/unix/linux_like/sync.rs` (`L148`).
- **`crossbeam-rs/crossbeam` @ `a28f40fddd` (`2026-11-20`):** `crossbeam-utils/src/atomic/seq_lock.rs` (`L28–93`), `seq_lock_wide.rs` (`L35–140`), `atomic_cell.rs` (`L1001–1037, 1120–1131`), `crossbeam-queue/src/array_queue.rs` (`L31–40, 143–203, 334–396`), `crossbeam-epoch/src/internal.rs` (`L157–161, 237–293, 340, 408–484`).
- **`joshlf/anneal` @ `20aa204315` (`2026-11-20`), `google/zerocopy` @ `f2efbfd1eb0c` (`2026-11-22`), & `leanprover/lean4` @ `5045d00564` (`v4.34.1`):** `trusted/audit/TrustedBoundary.lean`, `trusted/lean/foundation-lock.json`, `trusted/lean/Trusted/MirSemantics.lean`, and live `TrustedBoundary.lean` `"preflight"` + `"audit"` verification of `Anneal.Concur.ViewPCM` (`replayedDeclarations: 64, reachableDeclarations: 457, compilerOnlyNames: 0, axioms: ['propext'], replay: True, requireMirWp: false`).
- **Literature:** Lahav et al., *RC11*, PLDI 2017 (`10.1145/3062341.3062352`); Lahav et al., *SRA*, POPL 2016 (`10.1145/2837614.2837643`); Lidbury & Donaldson, *Dynamic Race Detection for C++11*, POPL 2017 (`10.1145/3009837.3009857`); Turon et al., *GPS*, OOPSLA 2014 (`10.1145/2660193.2660243`); Doko & Vafeiadis, *FSL*, VMCAI 2016 (`10.1007/978-3-662-49122-5_20`) & *FSL++*, ESOP 2017 (`10.1007/978-3-662-54434-1_17`); Meyer & Wolff, *Pointer Life Cycle Types*, POPL 2020 (`10.1145/3371136`).

## Revalidation

1. **Source Diff (< 1 minute):** Diff `STORE_BUFFER_LIMIT`, `store_impl` (`pop_front`), `read_from_last_store`, `perform_read_on_buffered_latest`, `mark_before_seqcst_store`, and `fetch_store` (`filter`) in `src/concurrency/weak_memory.rs` (`rust-lang/miri`). Unless store history is unbounded, RMW/CAS reads allow non-maximal modification-order insertion, and `miri#2301` is fixed, `Miri.WeakMemory` remains set-incomparable with C++20/`RC11`.
2. **Miri Completeness Gap Probe (`MIRIFLAGS="-Zmiri-many-seeds=0..256" cargo +nightly miri run`):**
   ```rust
   use std::sync::atomic::{AtomicUsize, Ordering, fence};
   use std::thread;

   static STAMP: AtomicUsize = AtomicUsize::new(0);
   static DATA: AtomicUsize = AtomicUsize::new(0);

   fn main() {
       let w = thread::spawn(|| {
           STAMP.store(1, Ordering::Relaxed); // Defective: missing fence(Release)!
           DATA.store(99, Ordering::Relaxed);
       });
       let r = thread::spawn(|| {
           let s1 = STAMP.load(Ordering::Acquire);
           let d = DATA.load(Ordering::Relaxed);
           fence(Ordering::Acquire);
           let s2 = STAMP.fetch_add(0, Ordering::Relaxed);
           // Reachable in RC11 / SRA / ARMv8, yet 0% reachable across all Miri seeds!
           assert!(!(s1 == 0 && d == 99 && s2 == 0));
       });
       w.join().unwrap();
       r.join().unwrap();
   }
   ```
3. **Pass-1 Lean 4 Audit:** Compile `Anneal.Concur.ViewPCM` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` and run `TrustedBoundary.lean` `"preflight"` + `"audit"` (`requireMirWp: false`) to confirm zero banned syntax nodes, zero `._unsafe_rec`, and axioms `⊆ {propext, Quot.sound}`.
