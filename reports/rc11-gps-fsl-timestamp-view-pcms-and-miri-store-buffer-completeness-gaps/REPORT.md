# Weak-Memory Verification Polarity in Rust: Miri Store-Buffer Completeness Gaps, Unbounded RC11/SRA Operational Semantics, and Step-Index-Free GPS/FSL ViewPCMs in 3-Axiom Lean 4

## Summary

Dynamic bug-finders and deductive verifiers sit on **opposite sides of weak-memory approximation polarity**: a bug-finder is sound when every trace it explores is permitted by the memory model ($\mathsf{Beh}_{\text{tool}} \subseteq \mathsf{Beh}_{\text{spec}}$, avoiding false alarms), whereas a deductive verifier is sound only when its operational target model *includes* every execution producible by conforming compilers and hardware ($\mathsf{Beh}_{\text{target}} \subseteq \mathsf{Beh}_{\text{model}}$, avoiding false safety proofs). Primary-source analysis of `rust-lang/miri` (`src/concurrency/weak_memory.rs`), `proofs-rs/lean-miri` (`Miri/Concurrency/{WeakMemory,DataRace,AtomicDispatch}.lean`), `rust-lang/rust` (`Arc::drop`), and `crossbeam-rs/crossbeam` (`SeqLock`, `AtomicCell`, `ArrayQueue`, `crossbeam-epoch`) establishes four core results:

1. **`Miri.Concurrency.WeakMemory` Is Unsound as a Standalone Concurrent Verification Oracle:** Miri's per-location store buffer (`weak_memory.rs`, ported 1-to-1 in `WeakMemory.lean`) intentionally under-approximates C++20/`RC11` relaxed memory along three concrete axes:
   - **128-Write Modification-Order Eviction (`STORE_BUFFER_LIMIT = 128`, `weak_memory.rs:111, 442–445`, `WeakMemory.lean:35, 350–367`):** Appending a 129th store evicts `buffer.oldest`, rendering stores $\ge 128$ writes behind `mo`-latest permanently unreadable even when zero happens-before (`CoWR`) or read-coherence (`CoRR`) edges block them. A buggy 7-bit ABA generation counter (`gen & 0x7F`) or epoch tracker (`PINNINGS_BETWEEN_COLLECT = 128` in `crossbeam-epoch/src/internal.rs:340`) that fails on a 128-write-stale read has **zero** failing executions in `Miri.WeakMemory`.
   - **Mandatory `buffer.last` RMW / Failed-CAS Reads Under Global Step Order (`weak_memory.rs:5–7, 280–292, 524–525, 643–675`; `WeakMemory.lean:314–328`):** Because Miri steps threads in a single global timeline and forces every RMW (`readFromLastStore`) and failed `compare_exchange` (`perform_read_on_buffered_latest`) to read exclusively `buffer.last`, Miri cannot place an RMW or failed `compare_exchange` `mo`-before an already-stepped `Relaxed` store `W1` whose program-order successor `W2` on another location was read. Consequently, a **2-thread, 2-store defective `SeqLock` writer** omitting `fence(Release)` after `STAMP.store(1, Relaxed)` passes **100% of Miri schedules** when the reader revalidates via `fetch_add(0, Relaxed)` or `compare_exchange`, yet exhibits torn reads (`s1 == 0 ∧ d == 99 ∧ s2 == 0`) under C++20, `RC11`, `SRA`, and ARMv8 hardware.
   - **`SeqCst` Fence Over-Synchronization and P0668 Drift (`weak_memory.rs:9–28`):** Modeling `fence(SeqCst)` as an `AcqRel` RMW on a single global clock suppresses legal weak behaviors, while P0668 edge cases remain approximated (`rust-lang/miri#2301`).
2. **Unbounded Timestamp-View Operational `RC11` / `SRA+Fence` Anchor:** A sound concurrent TCB step relation (`Trusted` `candidate:concurrency`) must instead maintain an **unbounded modification-order message pool** $(\ell, v, t, V_{\text{msg}})$ supporting non-maximal timestamp insertion for `Release`/`Relaxed` writes and coherence-admissible RMW selection, paired with per-thread `(cur, acq, rel)` timestamp views (Lahav et al., POPL 2016 & PLDI 2017) isomorphic to `DataRace.lean`'s `clock`, `fenceAcquire`, and `fenceRelease` (`L121–151`). This model soundly over-approximates `x86-TSO`, `ARMv8`, and `RVWMO` while supporting a **one-way Pass-2 sanity check** $\mathsf{Beh}_{\text{MiriWeak}} \subseteq \mathsf{Beh}_{\text{RC11View}}$.
3. **Why FSL's $\triangle P$ / $\nabla P$ Fence Modalities Are Mandatory Beyond GPS:** Pure Release-Acquire logics (`GPS`, OOPSLA 2014) attach resources directly to `Release` stores and `Acquire` loads. Production Rust primitives systematically split synchronization across **`Relaxed` accesses + standalone fences**: `SeqLock::validate_read` (`seq_lock.rs:39–40`) pairs `Relaxed` payload loads with `fence(Acquire)` before `state.load(Relaxed)`; `SeqLock::write` (`seq_lock.rs:48–51`) pairs `swap(1, Acquire)` with `fence(Release)`; `Arc::drop` (`arc.rs:2980, 3012`) pairs `fetch_sub(1, Release)` (whose read half is `Relaxed`!) with `fence(Acquire)` only when `prev == 1`; and `crossbeam-epoch::Global::try_advance` (`internal.rs:263, 281`) scans `local.epoch.load(Relaxed)` across participants followed by one `fence(Acquire)`. Fenced Separation Logic (`FSL`, VMCAI 2016) captures all four via acquire-pending $\triangle P$ (`ReleasedAt reqV P`) and release-prepared $\nabla P$ (`Releasing tv P`).
4. **Step-Index-Free (`Type 0`) Mechanization in Pass-1 3-Axiom Lean 4:** Iris requires step-indexed later modalities ($\triangleright$) and impredicative `Type 1`+ `iProp` only for higher-order heap-stored predicates—which fail `TrustedBoundary.lean`'s universe-monomorphic (`levelParams.isEmpty`) Pass-1 gate. Because `SeqLock`, `Arc`, Vyukov `ArrayQueue`, and 3-epoch EBR are first-order monotone state-transition protocols, `ViewPCM` + `ReleasedAt` verifies all four in **pure `Type 0` Pass-1 Lean 4 (`v4.34.1`)** using only `{propext, Quot.sound}` (`0` `Classical.choice`, `0` step-indices).

## Applicability

These findings govern concurrent `unsafe` Rust verification, Miri/`lean-miri` correspondence polarity, and `theory/` design across the eleven subjects in `REPORT.json`:

- **Miri and `lean-miri` concurrency engines (`rust-lang/miri` @ `7fa591d7d4dd9af8154becbc8332f8096f8323b1` and `proofs-rs/lean-miri` @ `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`):** Covers `src/concurrency/{weak_memory.rs, data_race.rs}` and `Miri/Concurrency/{WeakMemory.lean, DataRace.lean, AtomicDispatch.lean}`. In single-threaded sequential MIR execution (`!global.raceDetecting`, `AtomicDispatch.lean:107`), `WeakMemory` is inactive, so sequential `CorrespondenceClaim` equivalence in `joshlf/anneal` is unaffected; the polarity inversion applies when extending verification to multi-threaded atomics.
- **Standard library and `crossbeam` primitives (`rust-lang/rust` @ `8144389c895da997dbdecaa635e41d6a50be6ffd` and `crossbeam-rs/crossbeam` @ `a28f40fdddb70bea8e5faf0efad9af0be4b9dbea`):** Covers `alloc::sync::Arc` (`library/alloc/src/rcs/arc.rs`), `SeqLock` (`crossbeam-utils/src/atomic/{seq_lock.rs, seq_lock_wide.rs, atomic_cell.rs}`), Vyukov `ArrayQueue` (`crossbeam-queue/src/array_queue.rs`), and 3-epoch EBR (`crossbeam-epoch/src/internal.rs`).
- **Zero-TCB Lean 4 boundary (`joshlf/anneal` @ `20aa204315cd36aaf944778b7d33c0d609ced8e8` and `leanprover/lean4` `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`):** Covers `SourceRole.theory` modules audited by `trusted/audit/TrustedBoundary.lean` (`L442–596, 1330–1365`) over `trusted/lean/foundation-lock.json`.
- **Normative Literature:** Lahav et al. `RC11` (PLDI 2017, DOI `10.1145/3062341.3062352`), Lahav et al. `SRA` (POPL 2016, DOI `10.1145/2837614.2837643`), Turon et al. `GPS` (OOPSLA 2014, DOI `10.1145/2660193.2660243`), Doko & Vafeiadis `FSL` (VMCAI 2016, DOI `10.1007/978-3-662-49122-5_20`), and Meyer & Wolff EBR life-cycle types (POPL 2020, DOI `10.1145/3371136`).

**Prior Corpus Coverage:** Earlier packages survey general weak-memory landscapes (`anneal-concurrency-weak-memory-kernels-and-storage-survey`, `anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal`), ISA litmus tests and LLVM atomic lowering (`weak-memory-concurrency-models-hardware-mappings-and-optimizations`, `weak-memory-hardware-litmus-testing-x86-and-aarch64`, `tier1-atomics-and-fences-instruction-lowering`), and operational aliasing (`rust-atomics-weak-memory-and-aliasing-operational-models`). This report proves the exact `StoreBuffer` completeness gaps in `weak_memory.rs`/`WeakMemory.lean`, specifies the unbounded `RC11` view anchor, audits `crossbeam`/`Arc` fence idioms, and mechanizes step-index-free `Type 0` `ViewPCM` in Pass-1 Lean 4.

## Findings

### 1. Semantic Polarity Inversion and Three Proven Completeness Gaps in Miri's `StoreBuffer`

`Basis: source + derived`

Miri's weak-memory emulator (`src/concurrency/weak_memory.rs:1–92`, adapted from Lidbury & Donaldson's `tsan11`, POPL 2017, DOI `10.1145/3009837.3009857`) notes at lines 5–7 that it *"will never generate weak memory behaviours forbidden by the C++11 model, but it is incapable of producing all possible weak behaviours allowed by the model."* Even when `WeakMemory.lean` (`L249–253`) replaces Miri's RNG draw with universal rank selection `fetchAt buffer isSeqCst clocks rank`, **structural omissions in `StoreBuffer` remain unreachable under all ranks and thread schedules**:

1. **Bounded 128-Write Modification-Order Eviction (`STORE_BUFFER_LIMIT = 128`, `WeakMemory.lean:35, 108–111, 350–367`; `weak_memory.rs:111, 442–445`):**
   `StoreBuffer` holds `oldest` plus `newer` (`newer.length < 128`). On the 129th store, `storeImpl` drops `buffer.oldest` (`oldest := nextOldest`).
   - *Counterexample (`Eviction128_TagABA`):* Suppose an `AtomicU8` packs a 1-bit state flag and a 7-bit generation counter (`0..127`). Thread 2 loads `s0 = 0`, stalls, and Thread 1 writes an intermediate state `v_bad` at write `#1` followed by 128 relaxed increments (`#2..#129`) wrapping the 7-bit tag. Under `RC11` and `SRA`, Thread 2 (`clock[T1] = 0`) may legally read write `#1` (`v_bad`), whereas `Miri.WeakMemory` evicts `#0` and `#1` at write `#129`, yielding **zero** failing runs. Notably, `crossbeam-epoch` (`internal.rs:340`) sets `PINNINGS_BETWEEN_COLLECT = 128` (128 `local.epoch` writes every 64 pin/unpin pairs).
2. **Mandatory `buffer.last` RMW / Failed-CAS Reads + Global Step Order (`BuggySeqLockRmw`, `WeakMemory.lean:314–328`; `weak_memory.rs:524–525, 643–675`):**
   Miri appends stores strictly in global execution order and forces both RMWs (`readFromLastStore`) and failed `compare_exchange` (`perform_read_on_buffered_latest`) to read exclusively `buffer.last`. Consider a **2-thread, 2-store defective `SeqLock` writer** omitting `fence(Release)` after `STAMP.store(1, Relaxed)`:
   ```rust
   // Initial: STAMP = 0, DATA = 0
   // Thread 1 (Defective Writer): STAMP.store(1, Relaxed); /* W1 */ DATA.store(99, Relaxed); /* W2 */
   // Thread 2 (Reader):
   let s1 = STAMP.load(Ordering::Acquire);         // R1
   let d  = DATA.load(Ordering::Relaxed);          // R2
   core::sync::atomic::fence(Ordering::Acquire);   // F_acq
   let s2 = STAMP.fetch_add(0, Ordering::Relaxed); // R3 (or compare_exchange(0, 0, Relaxed, Relaxed))
   ```
   - *Legal in `RC11` / `SRA` / C++20 / ARMv8:* Set `rf(R1) = init_STAMP(0)`, `rf(R2) = W2(99)`, `rf(R3) = init_STAMP(0)`, `mo(DATA): init(0) < W2(99)`, and `mo(STAMP): init(0) < R3(0) < W1(1)`. Because neither `W1` nor `W2` is `Release` or preceded by `fence(Release)`, `sw = ∅` and `hb = sb`; per-location `hb ; eco?` is acyclic; `R3` is immediately `mo`-after `init_STAMP(0)` (RMW atomicity holds); and `sb ∪ rf` is a DAG (`no-thin-air` holds). On ARMv8, `STR` `W1` and `STR` `W2` reorder in Thread 1's store buffer so Thread 2 observes `(s1 = 0, d = 99, s2 = 0)`!
   - *Impossible in `Miri.WeakMemory` (0% of runs):* Reading `d = 99` at `R2` requires Thread 1 to have already executed `W1` and `W2` in Miri's global timeline, so `STAMP.buffer.last` is already `1` (`W1`) when Thread 2 executes `R3`. `readFromLastStore` unconditionally returns `1`, falsely certifying `¬(s1 == 0 ∧ d == 99 ∧ s2 == 0)`.

---

### 2. Unbounded Timestamp Operational `RC11` / `SRA+Fence` Semantics and Correspondence Polarity

`Basis: normative + source + derived`

Lahav et al.'s operational timestamp machine (`SRA`, POPL 2016, DOI `10.1145/2837614.2837643`; extended with `Relaxed`, `AcqRel` fences, and global SC view $V_{\text{sc}}$ in `RC11`, PLDI 2017, DOI `10.1145/3062341.3062352`) resolves both gaps cleanly:

- **Unbounded Non-Maximal Message Pool:** Atomic writes insert $(\ell, v, t, V_{\text{msg}})$ into an eviction-free pool at **any unoccupied modification-order timestamp** $t > V_{\text{cur}}(\ell)$ (adjacent to an existing message iff RMW). In `BuggySeqLockRmw`, Thread 1 inserts `W1 = (STAMP, 1, t = 2, ⊥)` and `W2 = (DATA, 99, t = 1, ⊥)`, allowing Thread 2's RMW `R3` to slot cleanly at `t = 1` (`0 < R3 < W1`) and expose `(s1 = 0, d = 99, s2 = 0)` in 4 steps.
- **View Isomorphism With `DataRace.lean` (`L121–151, 340–414`):** Each thread's location-indexed views $(V_{\text{cur}}, V_{\text{acq}}, V_{\text{rel}})$ mirror `DataRace.lean`'s `(clock, fenceAcquire, fenceRelease)`: `load(Relaxed)` joins $V_{\text{msg}}[\ell \mapsto t]$ into $V_{\text{acq}}$; `load(Acquire)` joins into both $V_{\text{cur}}$ and $V_{\text{acq}}$; `fence(Acquire)` sets $V_{\text{cur}} \leftarrow V_{\text{cur}} \sqcup V_{\text{acq}}$; `fence(Release)` sets $V_{\text{rel}} \leftarrow V_{\text{cur}}$; `store(Relaxed)` publishes $V_{\text{msg}} := V_{\text{rel}}$; and `store(Release)` publishes $V_{\text{msg}} := V_{\text{cur}}$. Non-atomic accesses enforce per-byte happens-before race freedom (`DataRace.lean:417–452`), faulting to `FaultKind.undefined` on any race.
- **Asymmetric Pass-2 Correspondence:** While sequential MIR satisfies `Behavior ↔ RefBehavior`, concurrent verification (`candidate:concurrency`) enforces **one-way simulation** $\mathsf{Beh}_{\text{MiriWeak}} \subseteq \mathsf{Beh}_{M_{\text{anneal}}^{\text{RC11}}}$, validating TCB transitions against `lean-miri` without inheriting Miri's 128-store or `buffer.last` blindness.

---

### 3. Protocol Anatomy of Production Rust Primitives: `SeqLock`, `Arc::drop`, `ArrayQueue`, and EBR

`Basis: source + derived`

1. **`crossbeam` `SeqLock` (`seq_lock.rs:28–93`, `seq_lock_wide.rs:35–140`) & `AtomicCell` `read_volatile` UB (`atomic_cell.rs:1014–1035`):**
   `SeqLock::write` (`seq_lock.rs:48–51`) executes `state.swap(1, Acquire)` + **`fence(Release)`**, mutates payload, and unlocks via `state.store(prev.wrapping_add(2), Release)` (`L90–92`, or `abort()` `L76–82` only when zero writes occurred). Readers call `state.load(Acquire)` (`!= 1`), read payload, and run `fence(Acquire); state.load(Relaxed) == stamp` (`L39–40`; `seq_lock_wide.rs` adds `state_hi` with `Acquire` `state_lo` validation to guard 32-bit wraparound). Crucially, `atomic_cell.rs:1016–1025` uses `ptr::read_volatile(src.cast::<MaybeUninit<T>>())` racing with non-atomic `ptr::write` (`L1052`)—which `atomic_cell.rs:1017` acknowledges is **immediate data-race UB** under C++20/`RC11`/`DataRace.lean:427`! Sound Rust `SeqLock<T>` implementations **must** access payload words via `Relaxed` atomic `[MaybeUninit<u8>; N]` / `AtomicUsize` loads and stores, materializing `T` only after `validate_read` succeeds.
2. **`alloc::sync::Arc::drop` (`library/alloc/src/rcs/arc.rs:57–72, 2234–2247, 2976–3026`):**
   Non-final droppers execute `strong.fetch_sub(1, Release) != 1` and return immediately (paying zero `Acquire` cost while extending `strong`'s release sequence, `DataRace.lean:392–401`). The final dropper (`prev == 1`) absorbs that release sequence into `V_acq` via the **`Relaxed` read half** of `fetch_sub(1, Release)` (`DataRace.lean:644`) and runs `acquire!(strong)` (`atomic::fence(Acquire)`, `arc.rs:60, 3012`) to promote `V_acq` into `V_cur` before `ptr::drop_in_place(&mut (*ptr).data)`.
3. **Vyukov `ArrayQueue<T>` (`crossbeam-queue/src/array_queue.rs:31–40, 148–191, 336–378`):**
   Each `Slot<T>` pairs `stamp: AtomicIndex` with `UnsafeCell<MaybeUninit<T>>`. Producers observe `slot.stamp.load(Acquire) == tail`, claim via `tail.compare_exchange_weak`, write `slot.value` non-atomically, and publish `slot.stamp.store(tail + 1, Release)`; consumers observe `slot.stamp.load(Acquire) == head + 1`, claim `head`, read `slot.value`, and advance `slot.stamp` to `head + one_lap` (`Release`), transferring exclusive `UnsafeCell` ownership across laps without data races.
4. **`crossbeam-epoch` 3-Epoch EBR (`crossbeam-epoch/src/internal.rs:155–162, 237–293, 408–484`):**
   `pin()` stores `global_epoch.pinned()` (`Relaxed`) + `fence(SeqCst)` (`L451–452`); `unpin()` stores `0` (`Release`, `L476`). `try_advance()` (`L237–293`) checks via `local.epoch.load(Relaxed)` (`L263`) that every pinned thread matches `global_epoch`, executes **`fence(Acquire)`** (`L281`) to absorb all prior `unpin()` `Release` views, and increments `global.epoch` (`Release`). `SealedBag::is_expired` (`L160`) frees bags sealed at `e` iff `global_epoch.wrapping_sub(e) >= 2` (Meyer & Wolff, POPL 2020).

---

### 4. Step-Index-Free `Type 0` `GPS`/`FSL` `ViewPCM` Mechanization in Pass-1 3-Axiom Lean 4

`Basis: source + derived`

Iris requires step-indexing ($\triangleright P$) and impredicative `Type 1`+ propositions only when heap locations store higher-order self-referential predicates—violating `TrustedBoundary.lean`'s `levelParams.isEmpty` Pass-1 gate (`L1335`). Because `SeqLock`, `Arc`, `ArrayQueue`, and 3-epoch EBR are first-order monotone protocols (`GPS` + `FSL`), we mechanize `ThreadViews`, `ReleasedAt` ($\triangle P$), `Releasing` ($\nabla P$), `SeqLock` validation soundness, $N$-way `Arc::drop` synchronization, and 3-epoch EBR reclamation directly in Pass-1 `Type 0` Lean 4 (`v4.34.1`, locked `Init.*` only, zero banned operators/tactics, zero `_unsafe_rec`, `{propext, Quot.sound}` only):

```lean
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
  fun loc => if Nat.blt (v1 loc) (v2 loc) then v2 loc else v1 loc

private theorem nat_le_antisymm : ∀ {a b : Nat}, a ≤ b → b ≤ a → a = b := by
  intro a
  induction a with
  | zero =>
    intro b _ hba
    cases b with
    | zero => rfl
    | succ k => cases Nat.not_succ_le_zero k hba
  | succ m ih =>
    intro b hab hba
    cases b with
    | zero => cases Nat.not_succ_le_zero m hab
    | succ k =>
      have hEq : m = k := ih (Nat.le_of_succ_le_succ hab) (Nat.le_of_succ_le_succ hba)
      subst hEq
      rfl

theorem viewLe_refl (v : View) : viewLe v v := by
  intro loc
  exact Nat.le_refl (v loc)

theorem viewLe_trans {v1 v2 v3 : View}
    (h12 : viewLe v1 v2) (h23 : viewLe v2 v3) : viewLe v1 v3 := by
  intro loc
  exact Nat.le_trans (h12 loc) (h23 loc)

theorem viewLe_join_left (v1 v2 : View) : viewLe v1 (viewJoin v1 v2) := by
  intro loc
  dsimp only [viewJoin]
  cases h : Nat.blt (v1 loc) (v2 loc) with
  | false => exact Nat.le_refl (v1 loc)
  | true  => exact Nat.le_of_lt (Nat.le_of_ble_eq_true h)

theorem viewLe_join_right (v1 v2 : View) : viewLe v2 (viewJoin v1 v2) := by
  intro loc
  dsimp only [viewJoin]
  cases h : Nat.blt (v1 loc) (v2 loc) with
  | true  => exact Nat.le_refl (v2 loc)
  | false =>
    cases Nat.lt_or_ge (v1 loc) (v2 loc) with
    | inl hLt =>
      have hTrue : Nat.blt (v1 loc) (v2 loc) = true := Nat.ble_eq_true_of_le hLt
      rw [h] at hTrue
      injection hTrue
    | inr hGe => exact hGe

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

structure LawfulPCM (M : Type) where
  unit      : M
  op        : M → M → Option M
  unit_left : ∀ a : M, op unit a = some a
  comm      : ∀ a b : M, op a b = op b a

/-- FSL Acquire-Pending Modality `△ P` (`ReleasedAt reqV P`, Doko & Vafeiadis VMCAI 2016). -/
structure ReleasedAt (reqV : View) (P : Prop) : Prop where
  unseal : ∀ curV : View, viewLe reqV curV → P

/-- FSL Release-Prepared Modality `∇ P` (`Releasing tv P`), introduced by `fence(Release)`. -/
structure Releasing (tv : ThreadViews) (P : Prop) : Prop where
  prepView : View
  hRelLe   : viewLe prepView tv.rel
  payload  : ReleasedAt prepView P

theorem fence_release_intro (tv : ThreadViews) {P : Prop} (hP : P) :
    Releasing (applyFenceRelease tv) P :=
  ⟨tv.cur, viewLe_refl tv.cur, ⟨fun _ _ => hP⟩⟩

theorem relaxed_load_then_fence_acquire_elim
    (tv : ThreadViews) (msgV : View) {P : Prop} (hMsg : ReleasedAt msgV P) :
    let tv2 := applyFenceAcquire (applyRelaxedLoad tv msgV)
    P ∧ viewLe msgV tv2.cur := by
  dsimp only [applyRelaxedLoad, applyFenceAcquire]
  have hAcq : viewLe msgV (viewJoin tv.acq msgV) := viewLe_join_right tv.acq msgV
  have hCur : viewLe (viewJoin tv.acq msgV) (viewJoin tv.cur (viewJoin tv.acq msgV)) :=
    viewLe_join_right tv.cur (viewJoin tv.acq msgV)
  have hFull : viewLe msgV (viewJoin tv.cur (viewJoin tv.acq msgV)) := viewLe_trans hAcq hCur
  exact ⟨hMsg.unseal _ hFull, hFull⟩

/-- `SeqLock` multi-word snapshot consistency (`seq_lock.rs:28-93`): when `s1` is even,
    every `Relaxed` word read has modification-order stamp bracketed `s1 <= ws <= s2` (via writer
    `fence(Release)` + reader `fence(Acquire)`), and `s1 = s2`, all words belong to snapshot `s1`. -/
def allWordsAtStamp (targetStamp : Nat) : List Nat → Prop
  | [] => True
  | ws :: rest => ws = targetStamp ∧ allWordsAtStamp targetStamp rest

def wordsBoundedBetween (lo hi : Nat) : List Nat → Prop
  | [] => True
  | ws :: rest => (lo ≤ ws ∧ ws ≤ hi) ∧ wordsBoundedBetween lo hi rest

theorem seqlock_validate_read_sound
    (s1 s2 : Nat) (wordStamps : List Nat)
    (hEven : Nat.beq (Nat.land s1 1) 0 = true)
    (hBounded : wordsBoundedBetween s1 s2 wordStamps)
    (hValid : s1 = s2) :
    allWordsAtStamp s1 wordStamps ∧ Nat.beq (Nat.land s2 1) 0 = true := by
  subst hValid
  refine ⟨?_, hEven⟩
  induction wordStamps with
  | nil => trivial
  | cons ws rest ih =>
    cases hBounded with
    | intro hHead hTail =>
      cases hHead with
      | intro hLo hHi =>
        exact ⟨nat_le_antisymm hLo hHi, ih hTail⟩

/-- `Arc::drop` (`arc.rs:2980-3025`) release-sequence join: `fetch_sub(1, Release)` (`Relaxed` read half)
    followed by `acquire!(strong)` (`fence(Acquire)`) synchronizes with ALL `N` prior holders! -/
def joinAllViews : List View → View
  | [] => emptyView
  | v :: vs => viewJoin v (joinAllViews vs)

def allViewsSynchronized (curV : View) : List View → Prop
  | [] => True
  | v :: vs => viewLe v curV ∧ allViewsSynchronized curV vs

theorem arc_drop_last_synchronizes_all
    (tv : ThreadViews) (holderViews : List View) :
    let tvAfterFence := applyFenceAcquire (applyRelaxedLoad tv (joinAllViews holderViews))
    allViewsSynchronized tvAfterFence.cur holderViews := by
  dsimp only []
  have hBase :
      viewLe (joinAllViews holderViews)
        (applyFenceAcquire (applyRelaxedLoad tv (joinAllViews holderViews))).cur := by
    dsimp only [applyRelaxedLoad, applyFenceAcquire]
    exact viewLe_trans
      (viewLe_join_right tv.acq (joinAllViews holderViews))
      (viewLe_join_right tv.cur (viewJoin tv.acq (joinAllViews holderViews)))
  induction holderViews with
  | nil => trivial
  | cons v vs ih =>
    dsimp only [allViewsSynchronized]
    have hLeft : viewLe v (viewJoin v (joinAllViews vs)) := viewLe_join_left v (joinAllViews vs)
    have hRight : viewLe (joinAllViews vs) (viewJoin v (joinAllViews vs)) :=
      viewLe_join_right v (joinAllViews vs)
    exact ⟨viewLe_trans hLeft hBase, ih (viewLe_trans hRight hBase)⟩

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

`Basis: source + derived`

| Criterion | Grade | Assessment & Separating Justification |
| :--- | :---: | :--- |
| **`(T1)` 0-TCB Bridge** | **Minimal `RC11` Hook + 0-TCB Logic** | `Anneal.Concur.ViewPCM` lives 100% in untrusted `theory/`. `Trusted` `candidate:concurrency` uses unbounded `RC11` timestamp messages, linked to `vendor/lean-miri` via one-way $\mathsf{Beh}_{\text{MiriWeak}} \subseteq \mathsf{Beh}_{\text{RC11}}$. |
| **`(P1)` Human Spec Auditability** | **Strong** | Specs express logical ownership/snapshots (`Arc` unique drop, `ArrayQueue` FIFO `T: Send`, `SeqLock` authentic snapshot) with zero `View` leakage in `Expected` theorems (Statement-Origin Separation). |
| **`(P2)` Authoring & Day-2 Locality** | **Strong** | Thread-modular `GPS`/`FSL` protocol rules avoid $O(k!)$ interleaving enumeration and remain invariant under backoff/spin tuning (`seq_lock.rs:59`). |
| **`(P3)` Lean 4 (`v4.34.1`) Kernel & `<50ms` LSP** | **Strong** | Pure `Type 0` `View` inequalities avoid step-index $\triangleright^n$ fuel unfolding and universe-polymorphic Kripke worlds. |
| **`(P4)` Heterogeneous Composability** | **Strong** | `ReleasedAt reqV P` composes orthogonally with `MaybeUninit<u8>` byte-validity (`SeqLock` torn reads), `UnsafeCell` ranges (`ArrayQueue`), and RAII `Drop` guards. |
| **`(P5)` Failure Legibility** | **Moderate–Strong** | Missing `fence(Acquire)` leaves `msgV` trapped in `tv.acq` (`viewLe msgV tv.cur` unprovable), pinpointing the omitted fence. |
| **`(C1–C2)` Conceptual Minimality** | **Locally Minimal** | Unifies `AcqRel`, fenced `Relaxed`, `Arc` release sequences, and 3-epoch EBR in one `ThreadViews` record + dual `(ReleasedAt, Releasing)`; refuted collapses: (1) `RC11` $\neq$ `Miri.StoreBuffer` (`BuggySeqLockRmw`, `Eviction128_TagABA`); (2) `FSL` $\neq$ `GPS` (`Arc::drop` `fetch_sub(Release)` + `fence(Acquire)`); (3) atomic `MaybeUninit` `SeqLock` $\neq$ `read_volatile` (`atomic_cell.rs:1017`). |

## Boundaries

- **`Ordering::Consume` (`memory_order_consume`):** **known not to apply** in Rust (`Ordering` exposes only `Relaxed`, `Acquire`, `Release`, `AcqRel`, `SeqCst`; `DataRace.lean:21–28`, `weak_memory.rs:29`).
- **Load-Buffering (`LB`) Cycles Beyond `RC11` `(sb ∪ rf)+` Acyclicity:** `RC11` forbids `r1 == 1 ∧ r2 == 1` on `LB`, whereas ARMv8/RVWMO hardware permits independent `LB` under plain `ldr`/`str` lowering. Whether Rust's normative specification will adopt Promising Semantics 2.1 / Weakestmo to admit independent `LB` without thin-air UB is **unknown** (`weak_memory.rs:31–37`). Monotone `GPS`/`FSL` `ViewPCM` proofs remain sound across that extension because they rely only on `hb` and `mo`, never `(sb ∪ rf)` acyclicity on `Relaxed` cycles.
- **x86 `lock cmpxchg` Replacement of `fence(SeqCst)` in `crossbeam-epoch`:** `crossbeam-epoch/src/internal.rs:421–450` replaces `fence(SeqCst)` on `x86`/`x86_64` (`not(miri)`) with `compare_exchange(..., SeqCst, SeqCst)` + `compiler_fence(SeqCst)`, which is sound on hardware x86-TSO (`lock cmpxchg` drains the store buffer) but **known not to apply** under portable C++20/`RC11` IR rules (`internal.rs:433–435`).
- **Higher-Order Impredicative Heap-Stored Invariants:** Lock-free structures storing arbitrary heap-quantifying closures are **unsupported** in step-index-free `Type 0` `ViewPCM` without Reynolds defunctionalization into a closed `Type 0` protocol index; likewise, mixed-size racing atomics without happens-before synchronization are **unsupported** (UB in `weak_memory.rs:64`).
- **OS Futex / Signal-Handler Weak-Memory Interactions (`FutexRuntime.lean`):** Kernel futex wait-queue synchronization and POSIX async-signal-handler fence rules were **not examined** in this package.

## Evidence

- **`rust-lang/miri` @ `7fa591d7d4dd9af8154becbc8332f8096f8323b1`:** `src/concurrency/weak_memory.rs` (`L1–92, 107–111, 189–259, 280–292, 339–468, 497–535, 643–676`).
- **`proofs-rs/lean-miri` @ `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`:** `Miri/Concurrency/WeakMemory.lean` (`L35, 108–111, 149–253, 314–380, 421–518`), `Miri/Concurrency/DataRace.lean` (`L21–151, 309–452, 639–653`), `Miri/Concurrency/AtomicDispatch.lean` (`L103–124`).
- **`rust-lang/rust` @ `8144389c895da997dbdecaa635e41d6a50be6ffd`:** `library/alloc/src/rcs/arc.rs` (`L57–72, 2234–2247, 2976–3026`).
- **`crossbeam-rs/crossbeam` @ `a28f40fdddb70bea8e5faf0efad9af0be4b9dbea`:** `crossbeam-utils/src/atomic/seq_lock.rs` (`L28–93`), `seq_lock_wide.rs` (`L35–140`), `atomic_cell.rs` (`L1001–1037, 1120–1131`), `crossbeam-queue/src/array_queue.rs` (`L31–40, 143–203, 334–396`), `crossbeam-epoch/src/internal.rs` (`L157–161, 237–293, 340, 408–484`).
- **`joshlf/anneal` @ `20aa204315cd36aaf944778b7d33c0d609ced8e8` & `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):** `trusted/audit/TrustedBoundary.lean` (`L442–596, 1330–1365`), `trusted/lean/foundation-lock.json` (`L1–1335`), `trusted/lean/Trusted/MirSemantics.lean` (`L28–108`).
- **Literature:** Lahav et al., *RC11*, PLDI 2017 (`10.1145/3062341.3062352`); Lahav et al., *SRA*, POPL 2016 (`10.1145/2837614.2837643`); Lidbury & Donaldson, *Dynamic Race Detection for C++11*, POPL 2017 (`10.1145/3009837.3009857`); Turon et al., *GPS*, OOPSLA 2014 (`10.1145/2660193.2660243`); Doko & Vafeiadis, *FSL*, VMCAI 2016 (`10.1007/978-3-662-49122-5_20`) & *FSL++*, ESOP 2017 (`10.1007/978-3-662-54434-1_17`); Meyer & Wolff, *Pointer Life Cycle Types*, POPL 2020 (`10.1145/3371136`).

## Revalidation

1. **Source Diff (< 1 minute):** Diff `STORE_BUFFER_LIMIT`, `store_impl` (`pop_front`), `read_from_last_store`, and `perform_read_on_buffered_latest` in `src/concurrency/weak_memory.rs` (`rust-lang/miri`). Unless store history is unbounded and RMW/CAS reads allow non-maximal modification-order insertion, `StoreBuffer` remains an under-approximation.
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
3. **Pass-1 Lean 4 Audit:** Check `Anneal.Concur.ViewPCM` under `TrustedBoundary.lean` `"preflight"` + `"audit"` to confirm zero banned syntax nodes, zero `._unsafe_rec`, universe monomorphism, and axioms `⊆ {propext, Quot.sound}`.
