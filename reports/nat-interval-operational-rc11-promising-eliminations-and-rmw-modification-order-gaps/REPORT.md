# Promise-Free Operational RC11 Semantics: Half-Open Natural-Number versus Dense Rational Modification-Order Intervals, RMW Adjacency, P0982R1 Release Sequences, and Store-Buffer Completeness Gaps

## Summary

Mechanizing operational C++20/Rust `RC11` concurrency in proof assistants such as Lean 4 without speculative promises (`Local.promises = ∅`) requires encoding per-location modification order ($\mathsf{mo}$) so out-of-order writes can slot before already-stepped writes while atomic read-modify-write (RMW) pairs remain permanently adjacent ($\mathsf{rmw} \subseteq \mathsf{imm}(\mathsf{mo})$). Primary-source inspection of `snu-sf/promising-lib`, `snu-sf/promising-coq` (POPL 2017), `snu-sf/promising2-coq` (PLDI 2020), `kaist-cp/relaxed-memory-separation-logic` (`ORC11`, POPL 2020), `qladevez/rc11` (PLDI 2017), and `rust-lang/miri` establishes five results:

1. **Promise Elimination Requires Non-Maximal `mo` Insertion:** `Local.promises` in `Promising 1.0`/`2.0` exists solely to witness $(\mathsf{sb} \cup \mathsf{rf})^+$ cycles (`LB`). Because `RC11` enforces `acyclic(sb ∪ rf)` (`rc11.v:442–443`), every consistent execution admits a promise-free topological schedule, **provided** writes and RMWs can insert at interior `mo` positions below writes executed earlier in global step order.
2. **Left-Adjacent `(fromTs, toTs]` Intervals vs. Successor `to_w = to_r + 1`:** Point-timestamp pools checking only whether `(ts_r, ts_w)` is *currently* empty violate $\mathsf{rmw} \subseteq \mathsf{imm}(\mathsf{mo})$ when a later out-of-order `store(Relaxed)` lands inside `(ts_r, ts_w)`. Two representations seal adjacency without promises: (a) **half-open intervals** `(fromTs, toTs]` (`fromTs < toTs`, `Cell.v:91–168`) where RMWs set `from_w = to_r` (`Local.v:336–343`), leaving zero gap `(to_r, to_r] = ∅`, and (b) **discrete integer successor pinning** (`to_w = to_r + 1` over `positive`, `orc11/thread.v:370`), exploiting $\neg\exists k \in \mathbb{Z}^+,\; t < k < t + 1$.
3. **Discrete `Nat` Intervals vs. Dense Rational `ℚ` (`DenseOrder`) Intervals:** Over dense dyadic rationals (`lib/DenseOrder.v:33–160`), open gaps `(t_1, t_2]` split infinitely via `DenseOrder.middle`. Over `Nat`, every write interval consumes width $\ge 1$ (`toTs ≥ fromTs + 1`). By finite order-isomorphism, **unbounded nondeterministic `Nat` endpoint selection** (`∃ fromTs toTs : Nat`) achieves **exact finite-trace equivalence** with dense `ℚ` intervals (making `Type 0` `Nat` intervals complete for deductive safety invariants without rationals), whereas greedy (`(maxTs, maxTs + 1]`) or bounded-gap (`gap ≤ G`) `Nat` allocators suffer **modification-order gap exhaustion** after $G$ interior insertions.
4. **Out-of-Order RMW Insertion (`2+2W-RMW`) and `StoreBuffer` Completeness Gaps:** On `2+2W-RMW` (`T1: x.store(2, Rlx); r1 = y.fetch_add(1, Rlx)` $\parallel$ `T2: y.store(2, Rlx); r2 = x.fetch_add(1, Rlx)`), outcome `r1 == 0 ∧ r2 == 0 ∧ x == 2 ∧ y == 2` is valid in `RC11`, `Promising 2.0`, `ARMv8`, and `RVWMO`, and is witnessed in promise-free `Nat` intervals whenever early writes leave gap $\ge 1$ (`(1, 2]`). `rust-lang/miri` (`weak_memory.rs:111, 443–446, 525–526, 669–673`) misses valid `RC11` executions due to `STORE_BUFFER_LIMIT = 128` FIFO eviction and mandatory `read_from_last_store` on RMWs and failed `compare_exchange`.
5. **C++20 `P0982R1` Invalidates Per-Location `rel : Loc → View`:** `qladevez/rc11` (`rc11.v:29–30`), `promising2-coq` (`TView.v:198–209`), and `ORC11` (`orc11/tview.v:38, 233–253`) retain pre-C++20 `rel : Loc → View`, letting same-thread `store(Relaxed)` extend release sequences. Under C++20 `P0982R1` and Rust (`miri/src/concurrency/data_race.rs:7–10, 611–650`), same-thread `store(Relaxed)` resets `released := frel`, while left-adjacent RMWs propagate `released_r ⊔ frel`.

## Applicability

These findings apply to operational weak-memory models, deductive verifiers in Lean 4 and Coq, and dynamic weak-memory interpreters across the thirteen subjects in `REPORT.json`:

- **Promising Mechanizations (`snu-sf/promising-lib` @ `ce6cccb9c26ecdfa0265682a2d3f40cfdbadd433`, `snu-sf/promising-coq` @ `fd9796ede251a2edf0ebf8c938443a30d5eadee9`, `snu-sf/promising2-coq` @ `6b70a57d10666ec66bfa96b7801dd870f9054da9`):** Covers `lib/DenseOrder.v` and `src/lang/{Time.v, Cell.v, Memory.v, TView.v, Local.v, Thread.v}` (Kang et al., POPL 2017, `10.1145/3009837.3009850`; Lee et al., PLDI 2020, `10.1145/3385412.3386010`). Both share `Time.t`, `Interval.mem`, `Cell.Raw.wf`, and `step_update`; `promising2-coq` adds `Message.reserve` and `Memory.cap` certification.
- **Promise-Free and Declarative `RC11` (`kaist-cp/relaxed-memory-separation-logic` @ `6fe1475af1f8c49f8c144a67d9175b5b3e6bc472`, `qladevez/rc11` @ `fad08ae4c6f41c4268e11140e551b5c42ce07224`):** Covers `orc11/{view.v, memory.v, tview.v, thread.v, progress.v}` (Dang et al., POPL 2020, `10.1145/3371102`) and `rc11.v` (Lahav et al., PLDI 2017, `10.1145/3062341.3062352`).
- **Rust, C++20 `P0982R1`, Miri, and Lean 4 (`rust-lang/rust` @ `ec65cd52bba13d491ff65c9d218b39753755c84a`, `rust-lang/miri` @ `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3`, `leanprover/lean4` @ `450d6b121a45a48ffc58a83c921c813dffb259cb`, WG21 `P0982R1`):** Covers `core::sync::atomic`, Miri's `weak_memory.rs` and `data_race.rs`, and `Init`-only `Type 0` Lean 4 interval models.

**Prior Corpus Coverage:** Earlier reports cover ISA lowering (`tier1-atomics-and-fences-instruction-lowering`, `weak-memory-concurrency-models-hardware-mappings-and-optimizations`), aliasing models (`rust-atomics-weak-memory-and-aliasing-operational-models`), Miri polarity and `ViewPCM` logics (`rc11-gps-fsl-timestamp-view-pcms-and-miri-store-buffer-completeness-gaps`), and `SeqCst`/`P0982R1` compilation (`c20-seqcst-fences-release-sequences-thin-air-and-rc11-to-rvwmo-arm-compilation-soundness`). This package isolates the **modification-order timestamp and interval representation** under promise elimination, proving exact finite-trace equivalence vs. online gap exhaustion between `Nat` and `ℚ` intervals, `ORC11` `t + 1` indexing, and `2+2W-RMW`.

## Findings

### 1. Eliminating Promises: Topological `acyclic(sb ∪ rf)` Schedules and Interior `mo` Insertion

`Basis: normative + source + derived`

In `snu-sf/promising2-coq` (`src/lang/Local.v:191–358`, `src/lang/Thread.v:73–105, 202–210`), thread state `Local.mk tview promises` permits speculative `Relaxed` writes via `Local.promise_step` (`Local.v:264–271`) ahead of sequenced-before ($\mathsf{sb}$) predecessors whenever `Thread.consistent` (`Thread.v:202–210`) certifies silent fulfillment (`promises = Memory.bot`) against `Memory.cap`. Promises are required *if and only if* the target semantics admits $(\mathsf{sb} \cup \mathsf{rf})^+$ cycles such as independent Load-Buffering (`LB`: `r0 = x; y = 1 || r1 = y; x = 1` yielding `r0 == 1 ∧ r1 == 1`). Declarative `RC11` (`qladevez/rc11` `rc11.v:425–451`) rules out all $(\mathsf{sb} \cup \mathsf{rf})^+$ cycles via `no_thin_air`:

```coq
(* qladevez/rc11 @ fad08ae4c6f41c4268e11140e551b5c42ce07224: rc11.v:425-451 *)
Definition coherence       := forall x, ~(hb ⋅ (eco ex) ?) x x.
Definition atomicity       := forall x y, ~ ((rmw ex) ⊓ ((rb ex) ⋅ (mo ex))) x y.
Definition SC              := acyclic psc.
Definition no_thin_air     := acyclic ((sb ex) ⊔ (rf ex)).
Definition rc11_consistent := coherence /\ atomicity /\ SC /\ no_thin_air.
```

Because `sb ∪ rf` is a finite DAG in every `RC11`-consistent execution $G$, stepping events along a topological order $\prec_{\text{step}}$ extending $\mathsf{sb} \cup \mathsf{rf}$ executes every thread strictly in program order (`promises = Memory.bot`, as in `orc11/thread.v:77–91`) with every read's $\mathsf{rf}$-source already in memory $M$. However, neither $\mathsf{mo}$ nor $\mathsf{rb} \triangleq \mathsf{rf}^{-1} \cdot \mathsf{mo}$ lies in $(\mathsf{sb} \cup \mathsf{rf})^+$. Along $\prec_{\text{step}}$, a write $w_1 <_{\text{mo}} w_2$ regularly steps **after** $w_2$ ($w_2 \prec_{\text{step}} w_1$). Promise-free operational `RC11` must therefore insert writes and RMWs into **interior modification-order positions** below already-stepped writes, gated only by coherence ($V_{\text{cur}}(\ell) < t$) and RMW adjacency ($\mathsf{rmw} \subseteq \mathsf{imm}(\mathsf{mo})$).

**Operational `fence(SeqCst)` Caveat:** Operational timestamp models (`TView.v:219–236`, `orc11/tview.v:260–275`) update a global timemap $\mathcal{S}$ (`\mathcal{S}' = \mathcal{S} \sqcup V_{\text{cur}}, V'_{\text{cur}} = \mathcal{S}'`), synchronizing naked `fence(SeqCst)` pairs even without shared atomic accesses, whereas declarative `RC11` `psc_fence` (`[F_sc] · (hb ⊔ hb · eco · hb) · [F_sc]`, `rc11.v:242–243`) requires an intervening `hb` or `eco` edge. Deductive safety proofs ($\mathsf{Beh}_{\text{target}} \subseteq \mathsf{Beh}_{\text{model}}$) must not rely on unmediated fence-to-fence synchronization.

---

### 2. Modification-Order Encodings: Point Timestamps, `(fromTs, toTs]` Intervals, and `t + 1` Successors

`Basis: source + execution + derived`

#### 2.1 Unreserved Point Timestamps Violate `rmw ⊆ imm(mo)`

If $M(\ell)$ maps point timestamps $t$ to $(v, V_{\text{rel}})$ and an RMW reading $t_0$ merely checks that $(t_0, t_1) \cap \mathsf{dom}(M(\ell)) = \emptyset$ *at the step of the RMW*, future out-of-order stores break atomicity:
1. From $M(x) = \{0 \mapsto (0, \bot)\}$, Thread 1's `x.fetch_add(1, Rlx)` reads $t_0 = 0$ and inserts $(1, \bot)$ at $t_1 = 10$ since $(0, 10) \cap \{0\} = \emptyset$.
2. Thread 2 ($V_{\text{cur}}(x) = 0$) executes `x.store(99, Rlx)` and inserts $(99, \bot)$ at $t = 5 > V_{\text{cur}}(x)$.
3. Now $0 <_{\text{mo}} 5 <_{\text{mo}} 10$: write $t = 5$ wedges between $t_0 = 0$ and $t_1 = 10$, violating `rc11.v:425–426` `atomicity`.

#### 2.2 Solution A: Pairwise-Disjoint Half-Open Intervals `(from, to]` (`Promising 1.0/2.0`)

`snu-sf/promising-coq` and `snu-sf/promising2-coq` (`src/lang/Time.v:47–116`, `src/lang/Cell.v:87–170`) assign each write a half-open interval $(\mathit{from}, \mathit{to}]$:

```coq
(* snu-sf/promising2-coq @ 6b70a57d10666ec66bfa96b7801dd870f9054da9: src/lang/Time.v:50-54, 89-106 *)
Inductive mem (interval:t) (x:Time.t): Prop :=
| mem_intro (FROM: Time.lt (fst interval) x) (TO: Time.le x (snd interval)).
Definition disjoint (lhs rhs:t): Prop := forall x (LHS: mem lhs x) (RHS: mem rhs x), False.
Lemma disjoint_imm a b c: disjoint (a, b) (b, c).
```

`Cell.Raw.wf` (`Cell.v:91–104`) requires `VOLUME` (`(from, to) = (Time.bot, Time.bot) \/ Time.lt from to`) and pairwise `DISJOINT` across distinct `to` keys. In `Local.program_step` (`Local.v:331–344`), `step_write` leaves `from < to` unconstrained—so choosing `prev_to < from` preserves an open gap `(prev_to, from]`—whereas `step_update` binds `from` of its write to `tsr`, the exact `to` of the read message:

```coq
(* snu-sf/promising2-coq: src/lang/Local.v:341-343 *)
(LOCAL1: Local.read_step lc1 mem1 loc tsr valr releasedr ordr lc2)
(LOCAL2: Local.write_step lc2 sc1 mem1 loc tsr tsw valw releasedr releasedw ordw lc3 sc3 mem3 kind)
```

Because `(from_r, tsr] ∪ (tsr, tsw] = (from_r, tsw]` has zero unoccupied interior around `tsr`, any later write `(from', to']` with `from' < to'` and `tsr < to' <= tsw` satisfies `to' ∈ (tsr, tsw]`, failing `Cell.Raw.add` `DISJOINT` (`Cell.v:162–165`). Thus $\mathsf{rmw} \subseteq \mathsf{imm}(\mathsf{mo})$ holds invariantly.

#### 2.3 Solution B: Discrete Integer Successor Attachment (`ORC11`)

In `kaist-cp/relaxed-memory-separation-logic` (`orc11/view.v:5`, `orc11/memory.v:56, 107–108, 958–965`, `orc11/thread.v:93–99, 367–375`), `ORC11` drops `mfrom` (`orc11/thread.v:93–99`) in favor of `time := positive` ($\mathbb{Z}^+$) point maps `gmap time baseMessage` with successor RMW pinning:

```coq
(* kaist-cp/relaxed-memory-separation-logic @ 6fe1475af1f8c49f: orc11/thread.v:367-374 *)
| PStepU m1 m2 or ow V2 V3 M3 tr v1 v2
      (ISV1 : m1.(mbase).(mval) = VVal v1) (ISV2 : m2.(mbase).(mval) = VVal v2)
      (ADJ: m2.(mto) = (m1.(mto) + 1)%positive) (SAME: m1.(mloc) = m2.(mloc))
      (READ: read_step V1 M1 tr m1 or V2)
      (WRITE: write_step V2 M1 m2 ow (default ∅ m1.(mbase).(mrel)) V3 M3)
```

Discreteness of `positive` ($\neg\exists k,\; t < k < t + 1$) prevents future writes from landing between `m1.mto` and `m1.mto + 1`, while `CellAddIns (DISJ: C !! to = None)` rejects RMWs on `m1` if `m1.mto + 1` is already occupied.

#### 2.4 `Type 0` Lean 4 Half-Open `Nat` Interval Kernel

For `Init`-only `Type 0` Lean 4 formalizations (avoiding quotient rationals $\mathbb{Q}$), half-open `Nat` intervals reduce disjointness to decidable linear inequalities:

```lean
structure MsgInterval (Val View : Type) where
  fromTs   : Nat
  toTs     : Nat
  val      : Val
  released : View

def intervalsDisjoint (f1 t1 f2 t2 : Nat) : Prop :=
  (f1 = 0 ∧ t1 = 0 ∧ ¬(f2 < 0 ∧ 0 ≤ t2)) ∨
  (f2 = 0 ∧ t2 = 0 ∧ ¬(f1 < 0 ∧ 0 ≤ t1)) ∨
  (f1 < t1 ∧ f2 < t2 ∧ (t1 ≤ f2 ∨ t2 ≤ f1))

theorem adjacent_disjoint {a b c : Nat} (hab : a < b) (hbc : b < c) :
    intervalsDisjoint a b b c :=
  Or.inr (Or.inr ⟨hab, hbc, Or.inl (Nat.le_refl b)⟩)

def canInsertPlainWrite (cell : List (MsgInterval Val View))
    (curTs fromTs toTs : Nat) : Prop :=
  curTs < toTs ∧ fromTs < toTs ∧
  ∀ m ∈ cell, intervalsDisjoint fromTs toTs m.fromTs m.toTs

def canAttachRmw (cell : List (MsgInterval Val View))
    (curTs readToTs writeToTs : Nat) : Prop :=
  curTs ≤ readToTs ∧ readToTs < writeToTs ∧
  (∃ m ∈ cell, m.toTs = readToTs) ∧
  ∀ m ∈ cell, intervalsDisjoint readToTs writeToTs m.fromTs m.toTs
```

---

### 3. Discrete `Nat` versus Dense Rational `ℚ` (`DenseOrder`) Intervals: Finite-Trace Equivalence and Gap Exhaustion

`Basis: source + execution + derived`

`snu-sf/promising-lib` (`lib/DenseOrder.v:33–160`) defines `DOAux.t := positive` not with integer order, but with a binary-tree dense order around `xH` (`xO lhs < xH < xI rhs`, isomorphic to $\mathbb{Z}[\frac{1}{2}]_{>0}$) satisfying `middle_spec`: $\forall a < b,\; a < \mathsf{middle}(a, b) < b$ (`L140–160`). Replacing dense `DenseOrder.t` (`ℚ`) with discrete `Nat` (`ℕ`) creates a sharp separation between **offline trace completeness** and **online simulation**:

1. **Finite-Trace Order-Isomorphism Theorem:** Let $\pi_{\mathbb{Q}}$ be any finite promise-free execution over $\mathbb{Q}_{\ge 0}$, and let $0 = q_0 < q_1 < \dots < q_m$ be the sorted set $E$ of all interval endpoints occurring in $\pi_{\mathbb{Q}}$. The rank bijection $\rho : E \to \{0, \dots, m\}$, $\rho(q_i) = i$, preserves strict inequality ($q_i < q_j \iff i < j$), endpoint equality (hence left-adjacent RMW attachment $\mathit{from}_w = \mathit{to}_r$), interval disjointness ($q_{b_1} \le q_{a_2} \lor q_{b_2} \le q_{a_1}$), and view lattice operations ($\rho(\max(q_i, q_j)) = \max(i, j)$). Consequently, when `fromTs` and `toTs` are **unbounded nondeterministic `Nat` parameters**, the set of finite behaviors over `Nat` intervals equals that over `ℚ` intervals. Deductive safety invariants (quantifying universally over all valid timestamp choices) are completely exact over `Nat`.
2. **Online Gap Exhaustion Bound:** Over `ℚ`, committing an early write $W_{\text{hi}}$ at $(1, 2]$ above $[0, 0]$ leaves $(0, 1]$, which accommodates any finite number $K$ of later-stepped RMWs via $q_k = 1 - 2^{-k}$. Over `Nat` (and in `ORC11`'s `t + 1` model), once $W_{\text{hi}}$ commits $\mathit{fromTs} = G$ (e.g., $(G, G + 1]$), each left-adjacent RMW from `0` consumes width $\ge 1$: after **at most $G$** RMWs $(0, 1], \dots, (G - 1, G]$, the $(G + 1)$-th RMW has **zero** disjoint `Nat` choices. Bounded-gap allocators (`fromTs ≤ maxTs + C`) therefore under-approximate `RC11` whenever $> C$ out-of-order operations precede an early write, and `Nat` states cannot forward-simulate `ℚ` states online without global order-preserving re-indexing.

| Modification-Order Model | Carrier | RMW `imm(mo)` Guard | Interior `mo` Capacity | `2+2W-RMW` (`0, 0`)? | Sound Deductive `RC11` Target? |
| :--- | :--- | :--- | :--- | :---: | :---: |
| **Unreserved Point Timestamps** | `Nat` / `ℚ` | Current `(t_r, t_w) = ∅` | Unbounded (wedges RMWs) | Yes (unsoundly) | Incomplete (breaks RMW atomicity) |
| **Miri `StoreBuffer`** (`weak_memory.rs`) | `VecDeque` ($\le 128$) | `read_from_last_store` (`L526`) | `0` for RMWs (tail-only) | **No** (`0%`) | **No** (under-approximates) |
| **Bounded-Gap `Nat` Intervals** | `Nat × Nat` (`gap ≤ C`) | `from_w = to_r` | $\le C$ ops per gap | Iff $C \ge 1$ | **No** (misses chains $> C$) |
| **Unbounded Nondet. `Nat` (`ORC11` / `(f, t]`)** | `positive` / `Nat × Nat` | `to_w = to_r + 1` or `from_w = to_r` | Unbounded (finite traces via $\rho$) | **Yes** | **Yes** (with `P0982R1` `TView`) |
| **Dense Intervals (`Promising` `promises=∅`)** | `DenseOrder.t` ($\cong \mathbb{Z}[\frac{1}{2}]_{>0}$) | `from_w = to_r` | Infinite online (`middle`) | **Yes** | **Yes** (with `P0982R1` `TView`) |

---

### 4. Out-of-Order RMW Insertion (`2+2W-RMW`) and `StoreBuffer` Completeness Gaps

`Basis: source + execution + derived`

Consider symmetric **`2+2W-RMW`** ($x = y = 0$ initially):

```rust
// Thread 1                                  // Thread 2
x.store(2, Ordering::Relaxed);      // W_x2  y.store(2, Ordering::Relaxed);      // W_y2
let r1 = y.fetch_add(1, Relaxed);   // U_y   let r2 = x.fetch_add(1, Relaxed);   // U_x
```

1. **Validity of `r1 == 0 && r2 == 0 && x == 2 && y == 2`:** Setting $\mathsf{mo}(x): W_{x,0}(0) <_{\text{mo}} U_x(0 \to 1) <_{\text{mo}} W_{x,2}(2)$ and $\mathsf{mo}(y): W_{y,0}(0) <_{\text{mo}} U_y(0 \to 1) <_{\text{mo}} W_{y,2}(2)$ satisfies `RC11` ($\mathsf{sw} = \emptyset$, cross-location $\mathsf{hb} = \mathsf{sb}$ has $\mathsf{hb} \cdot \mathsf{eco}^?$ irreflexive, $U_x/U_y$ are $\mathsf{mo}$-adjacent to $W_{x,0}/W_{y,0}$, $\mathsf{psc} = \emptyset$, and $\mathsf{sb} \cup \mathsf{rf}$ is acyclic) and executes on `ARMv8` (`STR; LDADD`) and `RVWMO` (`sw; amoadd.w`). In promise-free `Nat` intervals, stepping `W_x2` and `W_y2` at `(1, 2]` lets `U_y` and `U_x` attach left-adjacently to `[0, 0]` at `(0, 1]`, yielding `r1 == 0 ∧ r2 == 0` with `mo`-maxima `2`.
2. **Why `rust-lang/miri` Misses Valid `RC11` Executions (`weak_memory.rs`):**
   - **Tail-Only RMW and Failed-CAS Reads (`weak_memory.rs:525–533, 647–676`):** `buffered_atomic_rmw` (`L526`) and `perform_read_on_buffered_latest` (`L669`, used for failed `compare_exchange`) call `buffer.read_from_last_store(...)`. Across all $\binom{4}{2} = 6$ schedules of `2+2W-RMW`, whichever of `U_x` or `U_y` runs last executes *after* the opposing `store(2, Relaxed)` has pushed `2` via `buffer.push_back` (`L446`), forcing `read_from_last_store` to return `2` (`0` runs produce `r1 == 0 && r2 == 0`).
   - **128-Write FIFO Eviction (`STORE_BUFFER_LIMIT = 128`, `weak_memory.rs:111, 443–445`):** `if self.buffer.len() >= STORE_BUFFER_LIMIT { self.buffer.pop_front(); }` evicts older modification-order entries once 128 relaxed stores follow, hiding ABA/wraparound bugs whose failure requires reading a $\ge 128$-store-stale value.

---

### 5. C++20 `P0982R1` Release-Sequence Weakening in Promise-Free Interval Machines

`Basis: normative + source + execution + derived`

`qladevez/rc11` (`rc11.v:29–30`), `promising2-coq` (`TView.v:198–209`), and `ORC11` (`orc11/tview.v:38, 232–253`) all maintain per-location `rel : Loc → View`, so a same-thread `store(Relaxed)` inherits `rel[ℓ]` (`write_Rw := Some (default ∅ (𝓥.(rel) !! l) ⊔ Vra ⊔ 𝓥.(frel) ⊔ Rr)`). On `DATA = 42; X.store(1, Release); X.store(2, Relaxed)` $\parallel$ `if X.load(Acquire) == 2 { read(DATA) }`, those models treat `read(DATA)` as synchronized, whereas ISO C++20 `P0982R1` (`[intro.races]`) and Rust (`miri/src/concurrency/data_race.rs:7–10, 611–618`) restrict release sequences strictly to contiguous RMW chains (`[W] · (rf · rmw)^*`), flagging `DataRace` undefined behavior.

Sound C++20/Rust interval machines **omit `rel : Loc → View`**, retaining $(V_{\text{cur}}, V_{\text{acq}}, V_{\text{frel}})$ plus global $\mathcal{S}$:

| Atomic Step on $\ell$ | Interval Guard in $M_\ell$ | Published $V_{\text{msg}}$ | Post-Step $(V'_{\text{cur}}, V'_{\text{acq}}, V'_{\text{frel}})$ |
| :--- | :--- | :--- | :--- |
| **`load(Rlx)`** $(f, t, v, V_m)$ | $V_{\text{cur}}(\ell) \le t$ | — | $V'_{\text{cur}} = V_{\text{cur}}[\ell \sqcup t]$, $\; V'_{\text{acq}} = V_{\text{acq}} \sqcup V_m[\ell \sqcup t]$, $\; V'_{\text{frel}} = V_{\text{frel}}$ |
| **`load(Acq)`** $(f, t, v, V_m)$ | $V_{\text{cur}}(\ell) \le t$ | — | $V'_{\text{cur}} = V_{\text{cur}} \sqcup V_m[\ell \sqcup t]$, $\; V'_{\text{acq}} = V_{\text{acq}} \sqcup V_m[\ell \sqcup t]$, $\; V'_{\text{frel}} = V_{\text{frel}}$ |
| **`store(Rlx)`** $(f, t, v)$ | $V_{\text{cur}}(\ell) < t$, $f < t$, $\mathsf{disj}(f, t)$ | $V_{\text{frel}}[\ell \mapsto t]$ *(breaks RS)* | $V'_{\text{cur}} = V_{\text{cur}}[\ell \mapsto t]$, $\; V'_{\text{acq}} = V_{\text{acq}}[\ell \mapsto t]$, $\; V'_{\text{frel}} = V_{\text{frel}}$ |
| **`store(Rel)`** $(f, t, v)$ | $V_{\text{cur}}(\ell) < t$, $f < t$, $\mathsf{disj}(f, t)$ | $V_{\text{cur}}[\ell \mapsto t]$ | $V'_{\text{cur}} = V_{\text{cur}}[\ell \mapsto t]$, $\; V'_{\text{acq}} = V_{\text{acq}}[\ell \mapsto t]$, $\; V'_{\text{frel}} = V_{\text{frel}}$ |
| **`rmw(ord_r, ord_w)`** $(t_r \to t_w)$ | $V_{\text{cur}}(\ell) \le t_r < t_w$, $\mathsf{disj}(t_r, t_w)$ | $V_{m_r} \sqcup (V^1_{\text{cur}} \text{ if } \mathsf{Rel} \sqsubseteq \mathit{ord}_w \text{ else } V_{\text{frel}})[\ell \mapsto t_w]$ | Apply `load(ord_r)` $\to V^1$, then $V'_{\text{cur/acq}} = V^1_{\text{cur/acq}}[\ell \mapsto t_w]$ |
| **`fence(Acq)` / `fence(Rel)`** | — | — | `Acq`: $V'_{\text{cur}} = V_{\text{cur}} \sqcup V_{\text{acq}}$; $\quad$ `Rel`: $V'_{\text{frel}} = V_{\text{cur}}$ |

## Boundaries

- **Same-Thread `Relaxed` Store Release-Sequence Extension:** **known not to apply** in C++20 and Rust (`P0982R1`, `data_race.rs:611–618`), despite holding in `qladevez/rc11`, `promising-coq`, `promising2-coq`, and `orc11`.
- **Strong Bisimulation Between Fixed-Timestamp `Nat` States and Dense `ℚ` States:** **known not to apply** without global timestamp re-indexing; `Nat` completeness holds for finite traces via unbounded nondeterministic selection.
- **`(sb ∪ rf)^+` Cyclic Load-Buffering (`LB`) Executions:** **unsupported** in promise-free operational `RC11` (`promises = ∅`); verifying `Relaxed` load-to-store reordering optimizations requires `Promising 2.0` (`Thread.v:202–210`).
- **Unsynchronized Mixed-Size Atomic Writes:** **unsupported** (immediate undefined behavior in Rust and Miri, `weak_memory.rs:64`, `data_race.rs:529–544`).
- **Normative Rust Choice on Independent `LB` and Naked `fence(SeqCst)`:** Whether Rust's future specification will adopt Promising-style `LB` relaxation or `RC11` `psc_fence` vs. global-clock `fence(SeqCst)` semantics remains **unknown** (`weak_memory.rs:9–37`).
- **Infinite-Trace Liveness Under Unbounded Out-of-Order Preemption and Device MMIO:** Infinite interior `mo` chains slotting below a fixed `Nat` bound and volatile/MMIO semantics were **not examined**.

## Evidence

- **`snu-sf/promising-lib` @ `ce6cccb9c26ecdfa0265682a2d3f40cfdbadd433`:** `lib/DenseOrder.v` (`L16–31` `IsDense`, `L33–160` `DOAux` dense total order and `middle_spec`).
- **`snu-sf/promising-coq` @ `fd9796ede251a2edf0ebf8c938443a30d5eadee9` & `snu-sf/promising2-coq` @ `6b70a57d10666ec66bfa96b7801dd870f9054da9`:** `src/lang/Time.v` (`L47–116`), `src/lang/Cell.v` (`L87–218`), `src/lang/Memory.v` (`L20–188`), `src/lang/TView.v` (`L160–248`), `src/lang/Local.v` (`L191–358`), `src/lang/Thread.v` (`L73–105, 202–210`).
- **`kaist-cp/relaxed-memory-separation-logic` @ `6fe1475af1f8c49f8c144a67d9175b5b3e6bc472`:** `orc11/view.v` (`L5`), `orc11/memory.v` (`L56, 107–108, 958–965`), `orc11/tview.v` (`L36–48, 197–258`), `orc11/thread.v` (`L77–100, 342–391` `PStepU` `ADJ: m2.(mto) = (m1.(mto) + 1)%positive`).
- **`qladevez/rc11` @ `fad08ae4c6f41c4268e11140e551b5c42ce07224`:** `rc11.v` (`L29–30, 88–112, 232–263, 425–451`).
- **`rust-lang/miri` @ `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3` & `rust-lang/rust` @ `ec65cd52bba13d491ff65c9d218b39753755c84a`:** `src/concurrency/weak_memory.rs` (`L1–112, 423–470, 498–536, 647–677`), `src/concurrency/data_race.rs` (`L7–10, 603–651`), `library/core/src/sync/atomic.rs` (`L25–113`).
- **Literature & Standards:** Kang et al., POPL 2017 (`10.1145/3009837.3009850`); Lahav et al., PLDI 2017 (`10.1145/3062341.3062352`); Lee et al., PLDI 2020 (`10.1145/3385412.3386010`); Dang et al., POPL 2020 (`10.1145/3371102`); WG21 `P0982R1` (2018-10-07).
- **Execution (`2026-11-20`):** Python 3.13 probe verifying point-timestamp wedging, Miri `StoreBuffer` vs. `Nat` intervals on `2+2W-RMW`, $G$-step `Nat` gap exhaustion vs. `ℚ` splitting + $\rho$ projection, and `P0982R1`.

## Revalidation

1. **Upstream Source Diffs (< 1 minute):** Diff `STORE_BUFFER_LIMIT`, `buffered_atomic_rmw`, and `perform_read_on_buffered_latest` in `rust-lang/miri` (`src/concurrency/weak_memory.rs`), `store_relaxed` in `src/concurrency/data_race.rs`, and `orc11/{tview.v, thread.v}` in `kaist-cp/relaxed-memory-separation-logic`.
2. **Standalone Executable Verification Probe (`python3` stdlib, < 0.1s):**

```python
#!/usr/bin/env python3
"""Verify Nat vs Q half-open RC11 intervals, 2+2W-RMW, and P0982R1 release sequences."""
from fractions import Fraction

def intervals_disjoint(i1: tuple, i2: tuple) -> bool:
    f1, t1 = i1
    f2, t2 = i2
    if f1 == t1 and f2 == t2:
        return t1 != t2
    if f1 == t1:
        return not (f2 < t1 <= t2)
    if f2 == t2:
        return not (f1 < t2 <= t1)
    return t1 <= f2 or t2 <= f1

def can_add(cell: dict, frm, to) -> bool:
    return frm < to and all(intervals_disjoint((frm, to), (f2, t2)) for t2, (f2, _) in cell.items())

def miri_reaches_2p2w_rmw() -> bool:
    for sched in (
        ("Wx2", "Uy", "Wy2", "Ux"), ("Wx2", "Wy2", "Uy", "Ux"), ("Wx2", "Wy2", "Ux", "Uy"),
        ("Wy2", "Ux", "Wx2", "Uy"), ("Wy2", "Wx2", "Ux", "Uy"), ("Wy2", "Wx2", "Uy", "Ux"),
    ):
        bx, by, r1, r2 = [0], [0], -1, -1
        for op in sched:
            if op == "Wx2": bx.append(2)
            elif op == "Wy2": by.append(2)
            elif op == "Uy": r1 = by[-1]; by.append(r1 + 1)
            elif op == "Ux": r2 = bx[-1]; bx.append(r2 + 1)
        if r1 == 0 and r2 == 0:
            return True
    return False

def nat_2p2w_rmw(gap: int) -> bool:
    mx, my = {0: (0, 0)}, {0: (0, 0)}
    if not (can_add(mx, gap, gap + 1) and can_add(my, gap, gap + 1)):
        return False
    mx[gap + 1], my[gap + 1] = (gap, 2), (gap, 2)
    uy = [t for t in range(1, gap + 2) if can_add(my, 0, t)]
    ux = [t for t in range(1, gap + 2) if can_add(mx, 0, t)]
    if not (uy and ux):
        return False
    my[uy[0]], mx[ux[0]] = (0, 1), (0, 1)
    return mx[max(mx)][1] == 2 and my[max(my)][1] == 2

def nat_gap_capacity(g: int) -> int:
    cell, cur, n = {0: (0, 0), g + 1: (g, 99)}, 0, 0
    while can_add(cell, cur, cur + 1):
        cell[cur + 1] = (cur, n + 1); cur += 1; n += 1
    return n

def rat_split_and_project_to_nat(k: int) -> int:
    cell = {Fraction(0): (Fraction(0), 0), Fraction(2): (Fraction(1), 99)}
    cur = Fraction(0)
    for idx in range(k):
        nxt = (cur + Fraction(1)) / 2
        assert can_add(cell, cur, nxt)
        cell[nxt] = (cur, idx + 1); cur = nxt
    pts = sorted({q for to, (frm, _) in cell.items() for q in (frm, to)})
    rk = {q: i for i, q in enumerate(pts)}
    nat_cell: dict[int, tuple[int, int]] = {}
    for to, (frm, val) in sorted(cell.items()):
        nf, nt = rk[frm], rk[to]
        assert (nf == 0 and nt == 0) or can_add(nat_cell, nf, nt)
        nat_cell[nt] = (nf, val)
    return len(nat_cell)

def p0982r1_syncs(p0982r1: bool, rmw: bool) -> bool:
    msg1_rel, frel, rel_x = 1, 0, 1
    msg2_rel = max(msg1_rel, frel) if rmw else (frel if p0982r1 else rel_x)
    return msg2_rel >= 1

assert not miri_reaches_2p2w_rmw()
assert not nat_2p2w_rmw(gap=0) and nat_2p2w_rmw(gap=1)
assert [nat_gap_capacity(g) for g in (0, 1, 7, 15)] == [0, 1, 7, 15]
assert rat_split_and_project_to_nat(25) == 27
assert p0982r1_syncs(False, False) and not p0982r1_syncs(True, False) and p0982r1_syncs(True, True)
print("OK")
```
