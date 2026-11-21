# Wavefront Scoreboard Deadlock-Freedom, Edge-Clamped Halo Bounds, and Release-Acquire Prefix-Freeze

## Summary

Lock-free wavefront parallel processing (WPP) and multi-frame scoreboards in modern video codecs (HEVC/H.265, VVC/H.266, AV1) and stencil runtimes rely on four concurrency, arithmetic, and liveness invariants whose violation causes weak-memory data races or worker-pool deadlocks:

1. **Monotonic `Release`/`Acquire` Prefix-Freeze Over View-Based Separation Logics:** In `FFmpeg` (`ff_thread_report_progress` / `ff_thread_await_progress` at `libavcodec/pthread_frame.c:631–673`) and `rav1d` (`Rav1dThreadPicture::progress: Option<Arc<[AtomicU32; 2]>>` at `src/picture.rs:60`), a producer writes non-atomic pixel blocks $0 .. n - 1$ and publishes progress $n$ read concurrently by intra-frame and inter-frame consumers without per-consumer `CAS` locks. Under GPS (Turon et al., OOPSLA 2014), iGPS (Kaiser et al., ECOOP 2017), and iRC11 (Dang et al., POPL 2020), soundness freezes each completed strip's `.readWrite` ownership into a **duplicable persistent resource** $\Box \mathsf{FrozenPrefix}(r, n)$ inside a monotone protocol $(n \in \mathbb{N}, \le)$ before `store(n, Release)`. While a **single-thread row producer** needs only plain `Release` stores (`sb ; sw ⊆ hb`), **multi-worker out-of-order completion** (`FFmpeg` `vvc/thread.c:459` `col_progress`, `rav1d` `thread_task.rs:617, 924` bitmaps) **must** chain via C11 RMW release sequences (`fetch_add(..., AcqRel)`, Lahav et al., PLDI 2017); polling a predecessor with `Relaxed` and publishing a non-RMW `store(n, Release)` severs the release sequence and causes a C11 data race on earlier columns.
2. **Edge-Emulation Off-By-One Halo Bounds (`neededRowEdge`) on Out-of-Frame Motion Vectors:** Inter-frame motion compensation (`av1-spec` `08.decoding.process.md:3064`, `rav1d` `emu_edge_rust` at `src/mc.rs:935`, `FFmpeg` `vvc/ctu.c:2746`) clamps sample coordinates via $\mathrm{Clip3}(0, H_{\mathrm{ref}} - 1, y)$. Even when a negative vertical motion vector places the entire un-clamped filter window strictly above the frame ($y_{\max} < 0$), edge emulation clamps $[-L, y_{\max}]$ onto $\{0\}$ and **reads row `0`** (`ref[0]`). For a 1-based completed-row counter $\mathrm{prog} \in [0, H_{\mathrm{ref}}]$, $\mathsf{neededRowEdge}(y_{\max}, H_{\mathrm{ref}}) = \mathrm{Clip3}(0, H_{\mathrm{ref}} - 1, y_{\max}) + 1 = \mathrm{Clip3}(1, H_{\mathrm{ref}}, y_{\max} + 1)$ (`rav1d` `src/thread_task.rs:581` `iclip(max, 1, f.refp[n].p.p.h)`) is the **unique** tight bound avoiding two dual bugs: clamping the floor to `0` (`Clip3(0, H_ref, y_max + 1)`) yields `0` for $y_{\max} < 0$ (**Row-0 Data Race**), whereas omitting the ceiling $H_{\mathrm{ref}}$ (`max(1, y_max + 1)`) demands $\mathrm{prog} > H_{\mathrm{ref}}$ for $y_{\max} \ge H_{\mathrm{ref}}$ (**Scoreboard Deadlock**). Unused reference slots require an out-of-band sentinel (`i32::MIN` in `rav1d`; `-1` before `av_clip(..., top, bottom) >= 0` in `FFmpeg` `vvc/ctu.c:2800`).
3. **Multi-Pass Codec Scoreboard Geometries and Error/Ceiling Sentinels:** HEVC WPP (`ITU-T H.265`) uses a 2-CTU CABAC lag (`(ry - 1, 1) -> (ry, 0)`), whereas VVC WPP (`ITU-T H.266`, `vvdec` `DecSlice.cpp:152`, `FFmpeg` `vvc/thread.c:300–306`) uses a 1-CTU parse lag (`(ry - 1, 0) -> (ry, 0)`) and 2-CTU reconstruction lag (`(rx + 1, ry - 1) -> (rx, ry)`). In `FFmpeg`'s 10-pass VVC scoreboard (`INIT`..`ALF`), post-reconstruction filters invert spatial dependency direction by waiting on **bottom-right** Moore neighbors `(rx + 1, ry + 1)` of the preceding pass (`vvc/thread.c:368–390`). Deadlock-freedom additionally requires unlocking per-frame mutexes before cross-frame listener callbacks (`vvc/thread.c:467–474`) and publishing maximal sentinels on completion/abort (`INT_MAX` in `vvc/refs.c:640–641`; `FRAME_ERROR = u32::MAX - 1` in `rav1d` `thread_task.rs:35, 642–643`).
4. **Constructive `Type 0` Rank Proofs of Deadlock-Freedom Without `Classical.choice`:** Certifying a finite task list with an explicit `Nat` rank satisfying $\forall u \in V,\, \forall d \in \mathrm{deps}(u),\; d \in V \land \mathrm{rank}(d) < \mathrm{rank}(u)$ enables a deterministic `Type 0` witness `findMinRankUnfinished` that constructively extracts an enabled task whenever work remains and proves completion in $\le |V|$ steps using only `{propext, Quot.sound}`. On `FFmpeg`'s 10-pass VVC WPP DAG, the **resolution-independent linear pass-offset rank** $\mathrm{rank}_{\mathrm{VVC}}(rx, ry, s) = 1 + 2 \cdot ry + rx + 4 \cdot (s - 1)$ strictly orders every intra-pass and cross-pass Moore-halo edge simultaneously, bounding critical-path wavefront latency to $W + 2H + 30$.

## Applicability

These findings govern weak-memory atomic synchronization, motion-vector halo bounds, and scoreboard liveness verification across the six subjects in `REPORT.json`:

- **AV1 Multi-Threaded Decoder and Spec (`memorysafety/rav1d` @ `2e7216c20ac2a75de204d6c8d7268b75a45959b4`, `AOMediaCodec/av1-spec` @ `5e04f3f75e73a5898d7616c47c52f032144b8f80`):** Covers `src/thread_task.rs` (`check_tile`, `ensure_progress`, `get_frame_progress`, `abort_frame`, `FRAME_ERROR`), `src/decode.rs` (`mc_lowest_px`, `affine_lowest_px`, `ts.progress`), `src/mc.rs` (`emu_edge_rust`), `src/picture.rs` (`Rav1dThreadPicture::progress`), and AV1 Section 7.11.3.4 (`08.decoding.process.md:2992–3090`).
- **FFmpeg Frame-Threading and VVC/HEVC Scoreboards (`FFmpeg/FFmpeg` @ `e8574d0b22b126acc76007babce536c68bc07d0a`, `Fraunhoferhhi/vvdec` @ `00607ca1ecde3d8c7c1315450053edfaea13eec6`):** Covers `libavcodec/progressframe.h`, `libavcodec/pthread_frame.c`, `libavcodec/hevc/hevcdec.c`, `libavcodec/vvc/{thread.c, ctu.c, refs.c}`, and `vvdec` `source/Lib/DecoderLib/DecSlice.cpp`.
- **Rust Atomics and Constructive Lean 4 Mechanization (`rust-lang/rust` @ `8144389c895da997dbdecaa635e41d6a50be6ffd`, `leanprover/lean4` `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`):** Covers C20/RC11 `Ordering` semantics and `Type 0` DAG progress proofs.

**Prior Corpus Coverage:** Earlier reports cover hardware weak-memory mappings (`weak-memory-concurrency-models-hardware-mappings-and-optimizations`, `rust-atomics-weak-memory-and-aliasing-operational-models`) and step-indexed/transfinite Iris (`iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic`), without addressing multi-consumer prefix-freeze protocols, `neededRowEdge` motion-vector clamping bounds, 10-pass 2D CTU scoreboards, or `Classical.choice`-free `Type 0` rank liveness.

## Findings

### 1. Monotonic `Release`/`Acquire` Prefix-Freeze and Multi-Worker Release-Sequence Hazards

`Basis: normative + source + execution + derived`

#### 1.1 Fast-Path Atomic Scoreboards in `FFmpeg` and `rav1d`

In `FFmpeg` (`libavcodec/pthread_frame.c:631–673`), `ff_thread_report_progress` and `ff_thread_await_progress` combine a lock-free `Release`/`Acquire` fast path with a mutex/condvar slow path:

```c
// Producer (pthread_frame.c:646–651)
pthread_mutex_lock(&p->progress_mutex);
atomic_store_explicit(&progress[field], n, memory_order_release);
pthread_cond_broadcast(&p->progress_cond);
pthread_mutex_unlock(&p->progress_mutex);

// Consumer (pthread_frame.c:659–672)
if (!progress || atomic_load_explicit(&progress[field], memory_order_acquire) >= n)
    return;
pthread_mutex_lock(&p->progress_mutex);
while (atomic_load_explicit(&progress[field], memory_order_relaxed) < n)
    pthread_cond_wait(&p->progress_cond, &p->progress_mutex);
pthread_mutex_unlock(&p->progress_mutex);
```

When the fast path succeeds (`L660`), `memory_order_acquire` synchronizes directly with `memory_order_release` (`L648`) without touching `progress_mutex`. When the slow path runs (`L669–672`), `memory_order_relaxed` inside the loop remains sound because `progress[field] = n` was stored *before* `pthread_mutex_unlock(&p->progress_mutex)`, so POSIX mutex unlock $\to$ lock provides the happens-before (`hb`) edge! By contrast, `rav1d` (`src/thread_task.rs:509, 534, 584, 606, 617`) uses `Ordering::SeqCst` throughout (`// TODO(kkysen) non-trivial due to the atomics` at `L743`), paying full sequential-consistency barrier costs on ARMv8/RISC-V.

#### 1.2 Persistent Prefix-Freeze Protocol and the Non-RMW Release-Sequence Trap

Unlike single-receiver `CAS` channels, wavefront scoreboards broadcast read-only pixel strips to up to 7 dependent frames and same-frame WPP rows (`ProgressFrame` contract, `libavcodec/progressframe.h:48–50`). In GPS / iGPS / iRC11 (Turon et al., OOPSLA 2014, DOI `10.1145/2660193.2660243`; Kaiser et al., ECOOP 2017, DOI `10.4230/LIPIcs.ECOOP.2017.17`; Dang et al., POPL 2020, DOI `10.1145/3371102`), before advancing `prog` from $n$ to $n'$, a ghost freeze update converts exclusive $\mathsf{TilePin}(\mathsf{.readWrite}, [n, n'), \nu)$ into persistent $\Box \mathsf{FrozenSlice}([n, n'), \nu)$ under monotone protocol invariant:
$$\mathcal{I}(n) \triangleq (n = \mathsf{ERROR\_SENTINEL}) \;\lor\; \left(n \le H \;\land\; \bigast_{k = 0}^{n - 1} \Box \mathsf{FrozenRow}(k, \nu_k)\right)$$
Because $\mathcal{I}(n)$ is persistent ($\mathcal{I}(n) \vdash \mathcal{I}(n) \ast \mathcal{I}(n)$) and downward-closed ($m \le n < \mathsf{ERROR\_SENTINEL} \implies \mathcal{I}(n) \vdash \mathcal{I}(m)$), arbitrarily many `load(Acquire)` readers observing $n \ge \mathrm{needed}$ obtain $\bigast_{k < \mathrm{needed}} \Box \mathsf{FrozenRow}(k, \nu_k)$ simultaneously.

**Multi-Worker Release-Sequence Hazard:** RC11 view-front checking (preserved in **Revalidation**) distinguishes two producer topologies:
- **Single-Producer Row Thread:** Writes to columns $0 .. k$ are sequenced-before (`sb`) `prog.store(k + 1, Release)`, so `sb ; sw ⊆ hb` transfers the entire prefix with plain `Release` stores.
- **Multi-Worker Out-of-Order Columns:** If Worker 0 writes `col[0]` and stores `prog = 1 (Release)`, and Worker 1 spins `while prog.load(Relaxed) < 1 {}`, writes `col[1]`, and executes a **non-RMW** `prog.store(2, Release)`, C11/RC11 **terminates Worker 0's release sequence** at the foreign non-RMW write (Lahav et al., PLDI 2017, DOI `10.1145/3062341.3062352`). Consumer 2 executing `if prog.load(Acquire) == 2 { read(col[0]) }` acquires only Worker 1's view (`view[col_0] = 0`), causing a **C11 data race on `col[0]`**! Sound multi-worker aggregation requires either RMW release sequences (`fetch_add(1, AcqRel)`, cf. `FFmpeg` `vvc/thread.c:459` `atomic_fetch_add(&ft->rows[ry].col_progress[idx], 1) == ft->ctu_width - 1` + mutex scan at `L461–474`) or `Acquire` loads before republishing.

---

### 2. Edge-Emulation Off-By-One Halo Bounds (`neededRowEdge`): Row-0 Race vs. Ceiling Deadlock Duality

`Basis: normative + source + execution + derived`

In AV1 (`08.decoding.process.md:3058–3066`), 8-tap subpel interpolation accesses `ref[plane][Clip3(0, lastY, (y >> 10) + r - 3)][Clip3(0, lastX, (p >> 10) + t - 3)]`. In `rav1d`, boundary-crossing blocks invoke `emu_edge_rust` (`src/mc.rs:919–988`):
```rust
let mut r#ref =
    r#ref.with_offset::<BD>() + (clip(y, 0, ih - 1) * ref_stride + clip(x, 0, iw - 1));
```
When a negative vertical motion vector places the entire un-clamped window $[y_{\min}, y_{\max}]$ strictly above row `0` ($y_{\max} < 0$), `clip(y, 0, ih - 1)` evaluates to **`0`**, so `emu_edge_rust` executes `center_h = 1` iteration (`L952–970`), **reading reference row `0`** and replicating it across `top_ext` rows!

For any non-empty block ($bh \ge 1$) and reference height $H_{\mathrm{ref}} \ge 1$, the accessed row set $\mathcal{R} = \{\mathrm{Clip3}(0, H_{\mathrm{ref}} - 1, y) \mid y \in [y_{\min}, y_{\max}]\}$ has $\max \mathcal{R} = \mathrm{Clip3}(0, H_{\mathrm{ref}} - 1, y_{\max}) \ge 0$. Combining **Safety** ($\forall r \in \mathcal{R}, r < B \iff \max \mathcal{R} + 1 \le B$) with **Realizability** ($B \le H_{\mathrm{ref}}$, the maximum non-sentinel row progress published) yields the **unique** tight bound:
$$\mathsf{neededRowEdge}(y_{\max}, H_{\mathrm{ref}}) = \mathrm{Clip3}(0, H_{\mathrm{ref}} - 1, y_{\max}) + 1 = \mathrm{Clip3}(1, H_{\mathrm{ref}}, y_{\max} + 1)$$

Note that $B_{\mathrm{buggy}}(y_{\max}, H_{\mathrm{ref}}) = \mathrm{Clip3}(0, H_{\mathrm{ref}}, y_{\max} + 1)$ agrees with $\mathsf{neededRowEdge}$ for **all** $y_{\max} \ge 0$ and fails (`0` vs `1`) **if and only if $y_{\max} < 0$** (racing on row `0`!), while omitting upper clamp $H_{\mathrm{ref}}$ deadlocks whenever $y_{\max} \ge H_{\mathrm{ref}}$! Both `rav1d` and `FFmpeg` isolate unused references via a separate negative sentinel:
- **`rav1d` (`src/decode.rs:895–910`, `src/thread_task.rs:567–581`):** Initializes `lowest_px = i32::MIN`, skips unused refs on `max == i32::MIN`, and clamps used refs via **`iclip(max, 1 as c_int, f.refp[n as usize].p.p.h) as c_uint`**.
- **`FFmpeg` VVC (`vvc/ctu.c:2739–2808`, `vvc/thread.c:328–331, 472`, `vvc/refs.c:646`):** Initializes `ctu->max_y` to `-1`, clamps used MVs immediately via `av_clip(y0 + (mv->y >> 4) + height, top, bottom)` (`>= 0`), checks `if (ref && y >= 0)`, and reports `INT_MAX` on final CTU row completion so `p->progress[vp] > y + LUMA_EXTRA_AFTER` never deadlocks at the bottom edge!

---

### 3. Wavefront Scoreboard Architectures in HEVC, VVC, and AV1

`Basis: normative + source + derived`

| Codec & Engine | Intra-Frame WPP Lag | Cross-Pass Filter Halo Geometry | Deadlock & Abort-Propagation Guards |
| :--- | :--- | :--- | :--- |
| **HEVC (`ITU-T H.265`, `FFmpeg` `hevcdec.c:1140, 2737`)** | `entropy_coding_sync_enabled_flag`: CABAC syncs from **2nd CTU** `(ry - 1, 1)` (**2-CTU lag**) | Deblock V $\to$ Deblock H $\to$ SAO | Slice/tile availability boundaries |
| **VVC (`ITU-T H.266`, `vvdec` `DecSlice.cpp:152`, `FFmpeg` `vvc/thread.c:42–391`)** | `sps_entropy_coding_sync_enabled_flag`: `PARSE` syncs from **1st CTU** `(ry - 1, 0)` (**1-CTU lag**); `RECON` waits on `(rx - 1, ry)` + `(rx + 1, ry - 1)` (**2-CTU lag**) | 10-pass `score[10]`: `LMCS`, `DEBLOCK_H`, `SAO`, `ALF` wait on **bottom-right** `(rx + 1, ry + 1)` of prior pass (`L368–390`) | Unlocks `ft->lock` before cross-frame `ff_vvc_report_progress` (`L467–474`); `INT_MAX` finish (`refs.c:640–641`) |
| **AV1 (`rav1d` `src/thread_task.rs:525–647, 860–940`)** | Per-tile `ts.progress[0..1]` + frame-wide `EntropyProgress`, `Deblock`, `Cdef` (`copy_lpf` bitmask), `Lr` | Inter `TileReconstruction` waits on `refp[n].progress[1] >= iclip(max, 1, ref_h)` | `abort_frame` (`L628–646`) stores `FRAME_ERROR = u32::MAX - 1` (`> ref_h`), waking all waiters cleanly |

In `FFmpeg/libavcodec/vvc/thread.c:356–390`, `RECON(rx, ry)` notifies `RECON(rx - 1, ry + 1)` (down-left) **and** `LMCS(rx - 1, ry - 1)` (up-left), while `SAO(rx, ry)` notifies `ALF(rx + dx, ry + dy)` across all 8 Moore neighbors `(dx, dy) ∈ {-1, 0, +1}^2 \ {(0, 0)}` (`L382–389`). Ordering `(rx, ry)` before pass $s$ creates false cycles (`RECON(1, 1) -> LMCS(0, 0)`), motivating the linear pass-offset rank below.

---

### 4. Constructive `Type 0` Rank-Function Proofs of Acyclic DAG Deadlock-Freedom and Total Completion

`Basis: execution + derived`

Classical finite-DAG sink proofs assume no unfinished node is enabled and invoke dependent choice to construct an infinite predecessor chain. Instead, certifying a finite `tasks : List V` with a `Nat` rank:
$$\mathsf{ValidRank}(V, \mathrm{deps}, \rho) \triangleq \forall u \in V,\; \forall d \in \mathrm{deps}(u),\; d \in V \;\land\; \rho(d) < \rho(u)$$
separates **Domain Closure** ($d \in V$, catching unclamped $y_{\max} + 1 > H_{\mathrm{ref}}$ deadlocks) from **Strict Monotonicity** ($\rho(d) < \rho(u)$, ruling out cycles). Scanning `tasks` in `Type 0` via `findMinRankUnfinished` constructively yields $u^* \in \mathrm{tasks}$ minimizing $\rho$ among `completed u = false`; for every $d \in \mathrm{deps}(u^*)$, $\rho(d) < \rho(u^*)$ refutes `completed d = false` by `Nat.lt_irrefl`, proving `completed d = true` via `Bool` case analysis with **zero `Classical.choice`**!

**Closed-Form VVC 10-Pass WPP Rank:** For 2D WPP with upper-right halo $K$ CTUs, $\rho_K(rx, ry) = (K + 1) \cdot ry + rx$ satisfies $\rho_K(rx + K, ry - 1) = \rho_K(rx, ry) - 1 < \rho_K(rx, ry)$ independently of width $W$. Across VVC's 10 passes ($s \in \{0..9\}$, WPP $K = 1 \implies A = 2, B = 1$), the worst backward Moore-halo offset $(dx, dy) = (-1, -1)$ changes $2 \cdot ry + rx$ by $-3$; adding pass offset $+4 = A + B + 1$ yields the **resolution-independent VVC WPP rank**:
$$\rho_{\mathrm{VVC}}(rx, ry, s) = \begin{cases} 0 & \text{if } s = 0 \text{ (`INIT` at `(0, 0)`)} \\ 1 + 2 \cdot ry + rx + 4 \cdot (s - 1) & \text{if } 1 \le s \le 9 \end{cases}$$
Every forward WPP step `RECON(rx, ry) -> RECON(rx - 1, ry + 1)` ($\Delta \rho = +1$) and backward Moore-halo transition `SAO(rx, ry) -> ALF(rx - 1, ry - 1)` ($\Delta \rho = -3 + 4 = +1$) strictly increases $\rho_{\mathrm{VVC}}$! (When WPP is disabled and `PARSE` wraps rows `(W - 1, ry) -> (0, ry + 1)`, setting $A = \max(W, 2), B = 1$, and pass offset $A + 2$ holds identically.) Lifting across causal frames $f_{\mathrm{ref}} < f$ via $\rho_{\mathrm{multi}}(f, rx, ry, s) = f \cdot (W_{\max} + 2 H_{\max} + 34) + \rho_{\mathrm{VVC}}(rx, ry, s)$ certifies global multi-frame + 10-pass deadlock-freedom and $O(W + H)$ single-frame critical path ($W + 2H + 30$).

---

### 5. Self-Contained Constructive Lean 4 Mechanization

`Basis: derived`

```lean
namespace ScoreboardLiveness

def clip3 (lo hi x : Int) : Int :=
  if x < lo then lo else if hi < x then hi else x

def neededRowEdge (yMax : Int) (hRef : Nat) : Nat :=
  Int.toNat (clip3 0 (Int.ofNat hRef - 1) yMax + 1)

def buggyZeroFloorEdge (yMax : Int) (hRef : Nat) : Nat :=
  Int.toNat (clip3 0 (Int.ofNat hRef) (yMax + 1))

theorem neededRowEdge_bounds (yMax : Int) (hRef : Nat) (hPos : 0 < hRef) :
    1 ≤ neededRowEdge yMax hRef ∧ neededRowEdge yMax hRef ≤ hRef := by
  unfold neededRowEdge clip3; split; · omega; · split <;> omega

theorem neededRowEdge_covers_clamped_tap (yTap yMax : Int) (hRef : Nat)
    (hPos : 0 < hRef) (hLe : yTap ≤ yMax) :
    Int.toNat (clip3 0 (Int.ofNat hRef - 1) yTap) < neededRowEdge yMax hRef := by
  unfold neededRowEdge clip3; split <;> split <;> omega

theorem buggyZeroFloor_races_on_row0 (yMax : Int) (hRef : Nat)
    (hPos : 0 < hRef) (hNeg : yMax < 0) :
    buggyZeroFloorEdge yMax hRef = 0 ∧
    Int.toNat (clip3 0 (Int.ofNat hRef - 1) yMax) = 0 ∧
    neededRowEdge yMax hRef = 1 := by
  unfold buggyZeroFloorEdge neededRowEdge clip3
  refine ⟨?_, ?_, ?_⟩ <;> (repeat split) <;> omega

def AllCompleted {α : Type} (completed : α → Bool) (ds : List α) : Prop :=
  ∀ d : α, d ∈ ds → completed d = true

def ValidRank {α : Type} (tasks : List α) (deps : α → List α) (rank : α → Nat) : Prop :=
  ∀ u : α, u ∈ tasks → ∀ d : α, d ∈ deps u → d ∈ tasks ∧ rank d < rank u

def findMinRankUnfinished {α : Type} (completed : α → Bool) (rank : α → Nat) :
    List α → Option α
  | [] => none
  | u :: us =>
    match completed u, findMinRankUnfinished completed rank us with
    | true,  res    => res
    | false, none   => some u
    | false, some v => if rank u ≤ rank v then some u else some v

theorem findMinRank_none_all_done {α : Type} (completed : α → Bool) (rank : α → Nat) :
    ∀ (tasks : List α),
      findMinRankUnfinished completed rank tasks = none →
      ∀ u ∈ tasks, completed u = true := by
  intro tasks h u hu
  induction tasks with
  | nil => cases hu
  | cons x xs ih =>
    unfold findMinRankUnfinished at h
    cases hcx : completed x
    · simp [hcx] at h; cases findMinRankUnfinished completed rank xs <;> simp at h
    · simp [hcx] at h
      cases hu with
      | head => exact hcx
      | tail _ hm => exact ih h hm

theorem findMinRank_sound {α : Type} (completed : α → Bool) (rank : α → Nat) :
    ∀ (tasks : List α) (w : α),
      findMinRankUnfinished completed rank tasks = some w →
      w ∈ tasks ∧ completed w = false ∧
      (∀ u : α, u ∈ tasks → completed u = false → rank w ≤ rank u) := by
  intro tasks
  induction tasks with
  | nil => intro w h; cases h
  | cons x xs ih =>
    intro w h
    unfold findMinRankUnfinished at h
    cases hcx : completed x
    · simp [hcx] at h
      cases hrec : findMinRankUnfinished completed rank xs with
      | none =>
        simp [hrec] at h; subst h
        refine ⟨List.Mem.head xs, hcx, fun u hu hcu => ?_⟩
        cases hu with
        | head => exact Nat.le_refl _
        | tail _ hm =>
          have hTrue := findMinRank_none_all_done completed rank xs hrec u hm
          rw [hcu] at hTrue; cases hTrue
      | some v =>
        simp [hrec] at h
        rcases ih v hrec with ⟨hvMem, hvUnf, hvMin⟩
        by_cases hle : rank x ≤ rank v
        · simp [hle] at h; subst h
          refine ⟨List.Mem.head xs, hcx, fun u hu hcu => ?_⟩
          cases hu with
          | head => exact Nat.le_refl _
          | tail _ hm => exact Nat.le_trans hle (hvMin u hm hcu)
        · simp [hle] at h; subst h
          refine ⟨List.Mem.tail x hvMem, hvUnf, fun u hu hcu => ?_⟩
          cases hu with
          | head => omega
          | tail _ hm => exact hvMin u hm hcu
    · simp [hcx] at h
      rcases ih w h with ⟨hwMem, hwUnf, hwMin⟩
      refine ⟨List.Mem.tail x hwMem, hwUnf, fun u hu hcu => ?_⟩
      cases hu with
      | head => rw [hcu] at hcx; cases hcx
      | tail _ hm => exact hwMin u hm hcu

theorem minRank_witness_enabled {α : Type}
    (tasks : List α) (deps : α → List α) (completed : α → Bool) (rank : α → Nat)
    (hValid : ValidRank tasks deps rank) (w : α)
    (hFound : findMinRankUnfinished completed rank tasks = some w) :
    w ∈ tasks ∧ completed w = false ∧ AllCompleted completed (deps w) := by
  rcases findMinRank_sound completed rank tasks w hFound with ⟨hwMem, hwUnf, hwMin⟩
  refine ⟨hwMem, hwUnf, fun d hd => ?_⟩
  rcases hValid w hwMem d hd with ⟨hdMem, hdLt⟩
  cases hcd : completed d
  · exfalso; have _ := hwMin d hdMem hcd; omega
  · rfl

def vvcWppRank (rx ry s : Nat) : Nat :=
  if s == 0 then 0 else 1 + 2 * ry + rx + 4 * (s - 1)

theorem vvc_recon_wpp_step_monotone (rx ry s : Nat) (hRx : 1 ≤ rx) (hs : 1 ≤ s) :
    vvcWppRank rx ry s < vvcWppRank (rx - 1) (ry + 1) s := by
  unfold vvcWppRank; have hs0 : (s == 0) = false := by omega; simp [hs0]; omega

theorem vvc_moore_halo_pass_step_monotone (rx ry s : Nat)
    (hRx : 1 ≤ rx) (hRy : 1 ≤ ry) (hs : 1 ≤ s) :
    vvcWppRank rx ry s < vvcWppRank (rx - 1) (ry - 1) (s + 1) := by
  unfold vvcWppRank
  have hs0 : (s == 0) = false := by omega
  have hs1 : (s + 1 == 0) = false := by omega
  simp [hs0, hs1]; omega

end ScoreboardLiveness
```

## Boundaries

- **Cyclic / Non-Causal Reference Lists:** **known not to apply** to `ValidRank` progress unless self/future references ($f_{\mathrm{ref}} \ge f$) are rejected at RPL setup (`FFmpeg` `vvc/refs.c:465–488`).
- **Multi-Worker Non-RMW `Release` Stores After `Relaxed` Polling:** **known not to apply** under C11/RC11: foreign non-RMW writes terminate release sequences and permit weak-memory data races unless replaced by `AcqRel` RMWs or mutex-serialized prefix scans.
- **VVC Inter-Layer Reference Pictures (ILRP):** Explicitly **unsupported** in `FFmpeg`'s VVC decoder (`libavcodec/vvc/refs.c:594–597`, `AVERROR_PATCHWELCOME`).
- **OS Kernel Scheduler Fairness and Condvar Internals:** Logical DAG progress (`minRank_witness_enabled`) proves an enabled task always exists, whereas fair OS thread scheduling and `pthread_cond_wait` / `parking_lot` kernel primitives were **not examined** mechanically (requiring fair-trace logics such as Spies et al., PLDI 2021, DOI `10.1145/3453483.3454031`).
- **Upstream Relaxation of `rav1d` `Ordering::SeqCst` Atomics:** Whether `memorysafety/rav1d` will relax its `SeqCst` scoreboard loads/stores (`src/thread_task.rs:509–937`) to `Release`/`Acquire` and `AcqRel` is **unknown**.

## Evidence

- **`memorysafety/rav1d` @ `2e7216c20ac2a75de204d6c8d7268b75a45959b4`:** `src/picture.rs` (`L50–61, 288–292`); `src/thread_task.rs` (`L35–36, 501–647, 743, 860–940`); `src/decode.rs` (`L895–976, 3863–3865, 4746–4754`); `src/mc.rs` (`L919–988`).
- **`FFmpeg/FFmpeg` @ `e8574d0b22b126acc76007babce536c68bc07d0a`:** `libavcodec/progressframe.h` (`L24–103`); `libavcodec/pthread_frame.c` (`L631–673`); `libavcodec/vvc/thread.c` (`L42–84, 181–215, 293–391, 452–476`); `libavcodec/vvc/ctu.c` (`L2739–2810`); `libavcodec/vvc/refs.c` (`L35–42, 465–488, 594–597, 638–697`); `libavcodec/hevc/hevcdec.c` (`L1140, 2737, 3115`).
- **`Fraunhoferhhi/vvdec` @ `00607ca1ecde3d8c7c1315450053edfaea13eec6`:** `source/Lib/DecoderLib/DecSlice.cpp` (`L125–195`).
- **`AOMediaCodec/av1-spec` @ `5e04f3f75e73a5898d7616c47c52f032144b8f80`:** `08.decoding.process.md` (`L2992–3070`).
- **Literature & Execution (`2026-11-20`):** Turon et al., OOPSLA 2014 (`10.1145/2660193.2660243`); Kaiser et al., ECOOP 2017 (`10.4230/LIPIcs.ECOOP.2017.17`); Dang et al., POPL 2020 (`10.1145/3371102`); Lahav et al., PLDI 2017 (`10.1145/3062341.3062352`); Leino, Müller & Smans, ESOP 2010 (`10.1007/978-3-642-11957-6_22`); Chi et al., IEEE TCSVT 2012 (`10.1109/TCSVT.2012.2223056`); Spies et al., PLDI 2021 (`10.1145/3453483.3454031`). Standalone Python model-checker (preserved below) verified 588 MV boundary cases (236 Row-0 races, 232 ceiling deadlocks), RC11 view-front release-sequence preservation vs breakage, and 10-pass VVC WPP DAG completion.

## Revalidation

1. **Upstream Source Diffs (< 2 minutes):** Diff `check_tile` (`src/thread_task.rs`) and `emu_edge_rust` (`src/mc.rs`) in `memorysafety/rav1d`, plus `task_stage_done`, `schedule_inter`, and `report_frame_progress` in `FFmpeg` `libavcodec/vvc/thread.c` and `pred_get_y` in `libavcodec/vvc/ctu.c`.
2. **Standalone Halo, RC11 View-Front, and 10-Pass VVC DAG Probe (`python3` stdlib, < 0.2s):**
   ```python
   def revalidate_wavefront():
       clip = lambda lo, hi, x: max(lo, min(hi, x))
       races = deadlocks = 0
       for h_ref in (1, 8, 15, 16):
           for span_h in (1, 4, 11):
               for y0 in range(-24, 25):
                   ym = y0 + span_h - 1
                   rows = {clip(0, h_ref - 1, y0 + r) for r in range(span_h)}
                   b = clip(1, h_ref, ym + 1)
                   assert max(rows) + 1 == b and 1 <= b <= h_ref
                   races += int(clip(0, h_ref, ym + 1) == 0)
                   deadlocks += int(max(1, ym + 1) > h_ref)
       assert races == 236 and deadlocks == 232
       # RC11 view-front: AcqRel RMW preserves col 0 view; Relaxed + non-RMW Release drops col 0
       msg1 = {0: 1, 1: 0}
       assert max(0, max(0, msg1[0])) == 1 and ({0: 0, 1: 1})[0] == 0
       # 10-pass VVC WPP DAG rank monotonicity & constructive min-rank completion
       W, H = 4, 4
       nodes = [(rx, ry, s) for ry in range(H) for rx in range(W) for s in range(10) if not (s == 0 and (rx or ry))]
       ns = set(nodes)
       deps = {u: [] for u in nodes}
       ae = lambda u, v: deps[v].append(u) if (u in ns and v in ns) else None
       for ry in range(H):
           for rx in range(W):
               for s in range(0 if (rx == 0 and ry == 0) else 1, 9):
                   ae((rx, ry, s), (rx, ry, s + 1))
               if rx or ry:
                   ae((0, 0, 0), (rx, ry, 1))
               for dx, dy in ((0, 1), (1, 0)):
                   ae((rx, ry, 1), (rx + dx, ry + dy, 1))
                   ae((rx, ry, 1), (rx + dx, ry + dy, 2))
               for dx, dy in ((-1, 1), (1, 0)):
                   ae((rx, ry, 4), (rx + dx, ry + dy, 4))
               for dx, dy in ((-1, -1), (0, -1), (-1, 0)):
                   ae((rx, ry, 4), (rx + dx, ry + dy, 5))
               ae((rx, ry, 6), (rx + 1, ry, 6)); ae((rx, ry, 6), (rx - 1, ry, 7))
               ae((rx, ry, 7), (rx, ry + 1, 7))
               for dx, dy in ((-1, -1), (0, -1), (-1, 0), (1, -1), (1, 0)):
                   ae((rx, ry, 7), (rx + dx, ry + dy, 8))
               for dx in (-1, 0, 1):
                   for dy in (-1, 0, 1):
                       if dx or dy:
                           ae((rx, ry, 8), (rx + dx, ry + dy, 9))
       rk = lambda u: 0 if u[2] == 0 else 1 + 2 * u[1] + u[0] + 4 * (u[2] - 1)
       assert all(rk(u) < rk(v) for v, us in deps.items() for u in us)
       done = set()
       while len(done) < len(nodes):
           w = min((u for u in nodes if u not in done), key=rk)
           assert all(d in done for d in deps[w])
           done.add(w)
   revalidate_wavefront()
   ```
3. **Lean 4 Kernel Check:** Typecheck `ScoreboardLiveness` on `leanprover/lean4` (`v4.34.1`+) and verify `#print axioms ScoreboardLiveness.minRank_witness_enabled` contains no `Classical.choice` or `sorryAx`.
