# Compositional Weak-Memory Program Logics for Rust: OGRA, RSL/FSL/FSL++, GPS/iGPS, Cosmo, iRC11, Zero-Overhead Non-Atomic Collapse, and First-Order View Logics

## Summary

Verifying concurrent `unsafe` Rust under C++20/RC11 weak memory without exposing per-instruction timestamp arithmetic requires matching each synchronization idiom to the weakest sound program logic. Analysis across eight weak-memory logics—`OGRA` (Lahav & Vafeiadis, ICALP 2015), `RSL` (Vafeiadis & Narayan, OOPSLA 2013), `FSL` and `FSL++` (Doko & Vafeiadis, VMCAI 2016; ESOP 2017), `GPS` and `iGPS` (Turon et al., OOPSLA 2014; Kaiser et al., ECOOP 2017), `Cosmo` (Mével et al., ICFP 2020), and `iRC11`/`GPFSL` (Dang et al., POPL 2020; `kaist-cp/relaxed-memory-separation-logic`)—establishes five results:

1. **Five-Tier Expressiveness Hierarchy:**
   - *Classical Owicki-Gries -> `OGRA`:* Standard Owicki-Gries is unsound on Release-Acquire (`SRA`) because Store-Buffering (`SB`) executions violate global-state interleaving; `OGRA` restores soundness via view-partitioned assertions, but requires $O(T^2)$ pairwise non-interference checks and is *incomplete* on coherence-mediated multi-writer idioms without unbounded history ghost state.
   - *`RSL` -> `FSL` -> `FSL++`:* `RSL` binds value-indexed predicates $\mathcal{Q}(v)$ directly to `Release`/`Acquire` accesses. Standalone fences (`Arc::drop`, `SeqLock`) require `FSL`'s acquire-pending ($\triangle P$) and release-prepared ($\nabla P$) modalities, while $N$-holder reference counting (`Arc::drop`) breaks pure value-indexed `FSL` invariants and requires `FSL++` ghost partial commutative monoids (PCMs).
   - *`GPS`/`iGPS` -> `iRC11`/`GPFSL` & `Cosmo`:* `GPS` introduces per-location monotone protocols $(S, \sqsubseteq)$ and Escrows (`[es P ⇝ Q]`), yet `GPS` protocols are *eternal* (forbidding atomic header deallocation) and omit `Relaxed` + `SeqCst` fences. `iRC11`/`GPFSL` indexes assertions by views (`vProp Σ := monPred view_bi_index (iProp Σ)`, `gpfsl/base_logic/vprop.v:20`), adding **cancellable invariants** for atomic reclamation (`ArcInner`) and global SC view invariants for `Chase-Lev`.
2. **Data-Race UB vs. Safe Non-Atomic Races (`iRC11` vs. `Cosmo`):** Multicore OCaml (`Cosmo`) defines racy non-atomic accesses via history-bounding semantics, forcing `Cosmo`'s base logic to expose location write histories $\ell \mapsto_{\text{hist}} H$ and recover sequential points-to only in a derived data-race-free layer. Because Rust (`r[undefined.race]`) treats unsynchronized conflicting non-atomic accesses as immediate UB, `iRC11`/`GPFSL` (`gpfsl/base_logic/na.v:27–44`) internalizes race-freedom directly inside fractional non-atomic ownership $\ell \mapsto_q v$.
3. **Zero-Overhead Non-Atomic Sequential and Lock Collapse (`OwnLoc`):** Exclusive ($q = 1$) or fractional ($0 < q \le 1$) ownership $\ell \mapsto_q v$ encapsulates singleton visible history `{[t := m]}`, write-visibility $t \le V_{\text{cur}}(\ell)$ (`⊒(default ∅ m.(mrel))`, `na.v:32–33`), and read-front containment ($\forall t_r \in \mathsf{rsn}(\ell),\; t_r \le V_{\text{cur}}(\ell)$ when $q = 1$). Every thread-private region and `SpinLock`/`Mutex`/`RwLock` critical section therefore collapses **verbatim to sequential separation logic and functional borrow lifting** with zero exposed views or timestamps.
4. **First-Order `Type 0` View Logics vs. Step-Indexed Higher-Order Iris:** Step-indexing ($\triangleright$) and impredicative `Type 1`+ `uPred` worlds are required *only* when protocols store or quantify impredicatively over heap predicates (`Mutex<Box<dyn FnOnce() + Send>>` without defunctionalization). All concrete first-order protocols (`SpinLock<T>`, `RwLock<T>`, `Arc<T>` over first-order `Own(T)`, `SeqLock<T>`, Treiber stack, Michael-Scott queue, Chase-Lev deque) admit a **step-index-free `Type 0` formulation** over `VProp := View → GhostPCM → Prop`.
5. **Verification Blueprints and Production UB Findings:** Concrete protocol invariants across six Rust structures isolate each structure's minimal logical requirements, recall the `rust-lang/rust#51780` `Acquire` requirement in `Arc::is_unique`, and identify two `ptr::read_volatile` data-race UB hazards in `crossbeam` (`AtomicCell` and `crossbeam-deque`).

## Applicability

These findings govern program-logic selection, mechanization, and library verification across the twelve subjects in `REPORT.json`:

- **Coq Separation-Logic Frameworks:** `kaist-cp/relaxed-memory-separation-logic` @ `6fe1475af1f8c49f8c144a67d9175b5b3e6bc472` (`orc11/tview.v`, `gpfsl/base_logic/{vprop.v, na.v}`, `gpfsl/gps/{protocols.v, escrows.v}`, `gpfsl-examples/{lock, arc, stack, queue, chase_lev}`) and `rocq-iris/iris` @ `2fe2f450add5678d9a2492343c638ccdb428a677` (`iris/bi/monpred.v`).
- **Rust Standard Library and `crossbeam`:** `rust-lang/rust` @ `ec65cd52bba13d491ff65c9d218b39753755c84a` (`library/core/src/sync/atomic.rs`, `library/alloc/src/rcs/arc.rs`) and `crossbeam-rs/crossbeam` @ `a28f40fdddb70bea8e5faf0efad9af0be4b9dbea` (`crossbeam-utils/src/atomic/seq_lock.rs`, `crossbeam-deque/src/deque.rs`).
- **Literature:** `OGRA` (`10.1007/978-3-662-47666-6_25`), `RSL` (`10.1145/2509136.2509532`), `FSL` (`10.1007/978-3-662-49122-5_20`), `FSL++` (`10.1007/978-3-662-54434-1_17`), `GPS` (`10.1145/2660193.2660243`), `iGPS` (`10.4230/LIPIcs.ECOOP.2017.17`), `iRC11` (`10.1145/3371102`), and `Cosmo` (`10.1145/3408978`).

**Prior Corpus Coverage:** Companion package `rc11-gps-fsl-timestamp-view-pcms-and-miri-store-buffer-completeness-gaps` proves Miri's 128-entry `StoreBuffer` eviction and `buffer.last` RMW completeness gaps and defines baseline `View` join combinators, while `c20-seqcst-fences-release-sequences-thin-air-and-rc11-to-rvwmo-arm-compilation-soundness` covers `P0982R1` release sequences, thin-air models, and ISA compilation. Earlier surveys (`anneal-concurrency-weak-memory-kernels-and-storage-survey`, `iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic`, `rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers`) address sequential Rust verifiers and general Iris adequacy. Without duplicating basic timestamp PCMs or Miri store-buffer mechanics, this package analyzes the `OGRA`–`iRC11`/`Cosmo` logic hierarchy, `OwnLoc` sequential collapse, `Type 0` step-index elimination, `Escrow`/`ReleasedAt` discharge, and six concurrent Rust data-structure protocols.

## Findings

### 1. Comparative Taxonomy of Weak-Memory Program Logics (`OGRA` to `iRC11` and `Cosmo`)

`Basis: normative + source + derived`

| Logic | Memory Fragment | Core Assertion & Protocol Mechanism | Standalone Fences | Atomic Deallocation | Step-Index / Universe Cost | Separating Strength or Limitation |
| :--- | :--- | :--- | :---: | :---: | :--- | :--- |
| **`OGRA`** (ICALP 2015) | `SRA` | View-partitioned Hoare outlines + pairwise non-interference | No | No | None (first-order) | $O(T^2)$ non-modular; incomplete on `SRA` without unbounded history variables |
| **`RSL`** (OOPSLA 2013) | C11 `Rlx` + `RA` + `NA` | Value-indexed $\mathsf{Init}(\ell)$, $\mathsf{Rel}(\ell, \mathcal{Q})$, $\mathsf{Acq}(\ell, \mathcal{Q})$, $\mathsf{RMWAcq}(\ell, \mathcal{Q})$ | No | No | None (first-order PCM) | Cannot verify standalone fences (`Arc::drop`) or multi-consumer value reuse |
| **`FSL`** (VMCAI 2016) | C11 `Rlx` + `RA` + fences + `NA` | `RSL` + acquire-pending $\triangle P$ and release-prepared $\nabla P$ | `Acq`, `Rel`, `AcqRel` | No | None (first-order PCM) | Handles fenced message passing; lacks ghost PCMs for $N$-holder `Arc::drop` |
| **`FSL++`** (ESOP 2017) | C11 `Rlx` + `RA` + fences + `CAS` + `NA` | `FSL` + user ghost PCMs + RMW/CAS permission splitting | `Acq`, `Rel`, `AcqRel` | Payload only (atomic eternal) | None (first-order PCM) | Verifies Rust `Arc` payload drop, but cannot reclaim atomic refcount storage |
| **`GPS`** (OOPSLA 2014) | C11 `RA` + `CAS` + `NA` | Per-location monotone protocol $(S, \sqsubseteq)$, SW/CAS rules, Escrows `[es P ⇝ Q]` | No (`RA` only) | Non-atomic only | Metatheory step-indexed; hidden in rules | Clean protocol specs (`SpinLock`, `MSQueue`), but omits `Relaxed`/fences/atomic free |
| **`iGPS`** (ECOOP 2017) | `ORC11` `RA` + `NA` | Shallow Iris `monPred` embedding + single-writer protocol optimization | No (`RA` only) | Non-atomic only | Higher-order `uPred` ($\triangleright$, `Type 1`+) | Decomposes `GPS` into orthogonal Iris ghost algebras and `escrow` invariants |
| **`Cosmo`** (ICFP 2020) | Multicore OCaml (`Rlx`/`RA`/`SC` + safe NA races) | `vProp` (`View → iProp`) + full location write histories $\ell \mapsto_{\text{hist}} H$ | `Acq`, `Rel`, `SeqCst` | GC-managed | Higher-order `uPred` ($\triangleright$, `Type 1`+) | Sound under safe non-atomic data races; sequential $\ell \mapsto v$ is a derived layer |
| **`iRC11` / `GPFSL`** (POPL 2020) | `ORC11` (`NA`, `Rlx`, `RA`, fences, `SC` fences) | `vProp Σ := monPred view (iProp Σ)` + `@{V} P` + `⊔{V} P` + cancellable invariants | `Acq`, `Rel`, `AcqRel`, `SeqCst` | Full (`ArcInner` reclamation) | Higher-order `uPred` ($\triangleright$, `Type 1`+) | Verifies full `Arc`/`Weak` deallocation, `SpinLock`, Treiber, MS queue, Chase-Lev |

#### 1.1 Unsoundness of Classical Owicki-Gries on `SB` and Limits of `OGRA`

Under Sequential Consistency (`SC`), classical Owicki-Gries proves $\neg(r_1 = 0 \wedge r_2 = 0)$ on Store-Buffering ($x :=_{\text{rel}} 1;\; r_1 :=_{\text{acq}} y \parallel y :=_{\text{rel}} 1;\; r_2 :=_{\text{acq}} x$, initial $x = y = 0$) via auxiliary flags $\mathit{done}_1, \mathit{done}_2$ and invariant $(\mathit{done}_1 \Rightarrow x = 1) \wedge (\mathit{done}_2 \Rightarrow y = 1)$. Under `SRA`/`RC11` and hardware store buffers, $r_1 = 0 \wedge r_2 = 0$ is reachable because the two threads touch distinct locations with $\mathsf{sw} = \emptyset$. `OGRA` (Lahav & Vafeiadis, ICALP 2015) restores soundness by restricting cross-thread assertion transfer to `Release`–`Acquire` synchronization edges, yet remains unsuitable for modular Rust verification due to (a) $O(T^2)$ whole-program non-interference checks across threads and (b) deductive incompleteness on `SRA` programs whose safety relies on modification-order coherence (`2+2W` / multi-writer observation chains) without unbounded timestamp ghost state.

#### 1.2 View-Indexed `vProp` Modalities and Cancellable Invariants (`GPFSL` / `iRC11`)

Thread-modular separation logics interpret assertions as monotone predicates over views (`gpfsl/base_logic/vprop.v:20, 36, 42`):
```coq
(* kaist-cp/relaxed-memory-separation-logic @ 6fe1475af1f8: gpfsl/base_logic/vprop.v:20, 36, 42 *)
Definition vProp Σ := monPred view_bi_index (uPredI (iResUR Σ)).
Program Definition view_join_def V P : vProp := MonPred (λ V0, P (V0 ⊔ V)) _.  (* Notation: ⊔{V} P *)
Definition view_at_def V P : vProp := ⎡ P V ⎤.                                  (* Notation: @{V} P *)
```
1. **Objective View-Pinning (`@{V} P`, `vprop.v:88–155`):** Evaluates $P$ at view $V$ independently of the current thread's view (`(@{V} P)(V') ≡ P(V)`), satisfying `view_at_intro : P ⊢ ∃ V, ⊒V ∧ @{V} P` (`L127`), `view_at_elim : ⊒V -∗ @{V} P -∗ P` (`L131`), and `@{V} (P ∗ Q) ⊣⊢ @{V} P ∗ @{V} Q` (`L154`).
2. **Acquire-Pending View-Join (`⊔{V} P` $\equiv \triangle_V P$, `vprop.v:36`):** Holds at $V_0$ iff $P$ holds at $V_0 \sqcup V$. A `Relaxed` load reading a message with release view $V_{\text{msg}}$ establishes $V_{\text{msg}} \sqsubseteq V_{\text{acq}}$ rather than $V_{\text{msg}} \sqsubseteq V_{\text{cur}}$; executing `fence(Acquire)` updates $V'_{\text{cur}} := V_{\text{cur}} \sqcup V_{\text{acq}} \sqsupseteq V_{\text{msg}}$, turning `@{V_msg} P` / `⊔{V_msg} (⊒V_msg -∗ P)` directly into $P$—deriving `FSL`'s $\triangle P \xrightarrow{\text{fence(acq)}} P$ rule algebraically.
3. **Cancellable Atomic Protocols (`iRC11` Beyond `GPS`):** Unlike `GPS`'s persistent per-location protocols, `iRC11` (`gpfsl/gps/model_rules_dealloc.v`) guards protocol invariants with a fractional token $\mathsf{Tok}(\gamma, q)$. When the final `Weak::drop` (`arc.rs:3667–3668`) gathers $q = 1$ and runs `fence(Acquire)` (`⊒ V_all`), it cancels the protocol and recovers `own_loc_prim l 1 C` (`na.v:27`) to deallocate the atomic refcount allocation safely.

---

### 2. Zero-Overhead Non-Atomic Ownership Collapse (`OwnLoc` / $\ell \mapsto_q v$)

`Basis: source + derived`

Rust's data-race UB rule (`r[undefined.race]`) enables `iRC11`/`GPFSL` (`gpfsl/base_logic/na.v:27–44`) to hide all weak-memory histories inside non-atomic points-to $\ell \mapsto_q v$—unlike `Cosmo`, where Multicore OCaml's safe data-race semantics forces base assertions to carry full write histories:
```coq
(* kaist-cp/relaxed-memory-separation-logic @ 6fe1475af1f8: gpfsl/base_logic/na.v:27-33 *)
Definition own_loc_prim l q C : vProp :=
  ∃ rsa rsn ws, ⌜ good_hist C ⌝ ∗ AllocLocal l C ∗ AtRLocal l rsa ∗ AtWLocal l ws ∗
    (∃ Va, NaLocal l rsn Va) ∗ ⎡ hist l q C ∗ atread l q rsa ∗ atwrite l q ws ∗ naread l q rsn ⎤.
Definition own_loc_na_def l q v : vProp :=
  ∃ t m, own_loc_prim l q {[t := m]} ∗ ⌜memval_val_rel m.(mval) v⌝ ∗ ⊒(default ∅ m.(mrel)).
```

At view $V_{\text{cur}}$, $\ell \mapsto_q v$ (`own_loc_na l q v`) bundles four invariants:
1. **Singleton History & Fractional Agreement (`na.v:160–210`):** Authoritative fraction $q \in (0, 1]$ fixes visible history `C = {[t := m]}` with value $v$, satisfying `l ↦{q1 + q2} v ⊣⊢ l ↦{q1} v ∗ l ↦{q2} v` (`L160–170`) and `l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ⌜v1 = v2⌝` (`L195`).
2. **Write-Visibility Horizon (`AllocLocal` + `⊒`):** Enforces $t \le V_{\text{cur}}(\ell)$, ensuring non-atomic reads observe $v$ without write-read races and cannot read stale pre-$t$ messages.
3. **Read-Front Containment (`NaLocal` + `AtRLocal` + `AtWLocal`):** Fractional ghost sets `rsn` and `rsa` record all prior reader timestamps. While $q < 1$ (`&T` shared across threads), concurrent non-atomic reads are race-free; when $q = 1$ is reassembled (`&mut T`, `MutexGuard<T>`, or final `Arc::drop` + `fence(Acquire)`), $\forall t' \in \mathsf{rsn} \cup \mathsf{rsa} \cup \mathsf{ws},\; t' \le V_{\text{cur}}(\ell)$, guaranteeing a fresh non-atomic write at $t_{\text{new}} > V_{\text{cur}}(\ell)$ happens-after all prior accesses.
4. **Timeless Sequential Collapse (`own_loc_na_timeless`, `na.v:176`):** Inside any thread-local block or lock-held critical section, $\{\ell \mapsto_q v\}\;\mathsf{read}_{\text{na}}(\ell)\;\{r.\; r = v \ast \ell \mapsto_q v\}$ and $\{\ell \mapsto v\}\;\mathsf{write}_{\text{na}}(\ell, v')\;\{\ell \mapsto v'\}$ hold **identically to sequential separation logic**. Unlocking (`Release`) seals $\ell \mapsto v'$ into `@{V_rel} (ℓ ↦ v')` (`view_at_intro`), and locking (`Acquire`) restores $\ell \mapsto v'$ via `view_at_elim`—allowing sequential functional borrow/lens lifters to verify critical sections with zero weak-memory obligations.

---

### 3. First-Order `Type 0` View Logics vs. Step-Indexed Higher-Order Iris

`Basis: source + derived`

In `GPFSL` (`gpfsl/gps/escrows.v:14–15, 50`), `[es P ⇝ Q]` embeds `vProp` inside an impredicative Iris invariant, introducing step-index later modalities ($\triangleright$):
```coq
(* kaist-cp/relaxed-memory-separation-logic @ 6fe1475af1f8: gpfsl/gps/escrows.v:14-15, 50 *)
Program Definition escrow_def (P Q: vProp) : vProp :=
  MonPred (λ V, ∃ V0, ⌜V0 ⊑ V⌝ ∗ inv escrowN ((∃ V1, P V1) ∨ Q V0))%I _.
Lemma escrow_elim P Q E: ↑escrowN ⊆ E → (P ∗ P → False) ⊢ [es P ⇝ Q] -∗ ▷ P ={E}=∗ ▷ Q.
```

For verifiers enforcing universe-monomorphic (`Type 0`) proof terms or sub-50ms kernel replay, define a **step-index-free `Type 0` View Logic** over a `Type 0` ghost PCM $(M, \cdot, \varepsilon)$:
$$\mathsf{VProp}_0 \triangleq \{ P : \mathsf{View} \to M \to \mathsf{Prop} \mid \forall V_1 \sqsubseteq V_2,\; a \cdot b \neq \bot \implies P(V_1, a) \implies P(V_2, a \cdot b) \}$$
with $(\mathsf{AtView}\;V_0\;P)(V, m) \triangleq P(V_0, m)$ and $(\mathsf{JoinView}\;V_0\;P)(V, m) \triangleq P(V \sqcup V_0, m)$.

- **`Type 0` Sufficiency (Zero Step-Indices):** Whenever each atomic location $\ell$'s protocol $(S_\ell, \sqsubseteq_\ell)$ interprets states via a stratified `Type 0` predicate $\mathcal{I}_\ell : S_\ell \to \mathsf{View} \to M \to \mathsf{Prop}$ (without quantifying over $\mathsf{VProp}_0$), **escrows, fences, and cancellable protocols require zero step-indices**: a 2-state ghost slot $\gamma \in \{\mathsf{Escrowed}(V_0, m_Q), \mathsf{Claimed}(m_P)\}$ with exclusive token $m_P$ ($m_P \cdot m_P = \bot$) performs deterministic PCM update $\mathsf{Escrowed}(V_0, m_Q) \cdot m_P \rightsquigarrow \mathsf{Claimed}(m_P) \cdot m_Q$ at any view $V \sqsupseteq V_0$, yielding $Q(V, m_Q)$ by monotonicity without $\triangleright$ or Löb induction.
- **Exact Boundary Requiring Step-Indexing:** Step-indexed `uPred` (`Type 1`+) is mandatory iff shared state stores **open-world impredicative heap predicates** whose meaning quantifies over the protocol store itself—such as `Mutex<Box<dyn FnOnce() + Send>>`, `Arc<dyn Sync>`, or semantic `RustBelt` type-system logical relations (Dang et al., POPL 2020) without closed-crate defunctionalization.

---

### 4. Concrete Verification Protocols Across Six Canonical Rust Structures

`Basis: source + normative + execution + derived`

1. **`SpinLock<T>` and Fenced-CAS Lock (`code_spin_lock.v:14–24`, `atomic.rs:4792–4806`):**
   - *Code:* `compare_exchange_weak(false, true, Acquire, Relaxed)` (or `Relaxed, Relaxed` + `fence(Acquire)` at `atomic.rs:4796–4800`) and `store(false, Release)` (`L4804`).
   - *Protocol (`GPS` / `FSL`):* $S = \{\mathsf{Free}(V_{\text{rel}}), \mathsf{Locked}\}$ with $\mathcal{I}(\mathsf{Free}(V_{\text{rel}})) \triangleq (\mathit{val} = \mathsf{false}) \ast \mathsf{AtView}\;V_{\text{rel}}\;(\mathit{data} \mapsto T)$. In the fenced variant, `Relaxed` CAS success yields $\mathsf{JoinView}\;V_{\text{rel}}\;(\mathit{data} \mapsto T)$, discharged by `fence(Acquire)` into plain $\mathit{data} \mapsto T$.
2. **`Arc<T>::drop`, `Weak<T>`, and `is_unique` (`arc.rs:57–72, 1057, 2982–3026, 3656–3668`; `arc/code.v:15–95`):**
   - *Code:* `clone` uses `fetch_add(1, Relaxed)` (`code.v:15–19`); `drop` runs `if strong.fetch_sub(1, Release) != 1 { return; }` (`arc.rs:2986`), executing `acquire!(strong)` (`fence(Acquire)`, `L60, 3018`) only on the $1 \to 0$ transition before `drop_in_place`, followed by `Weak::drop`'s identical `weak.fetch_sub(1, Release) == 1` + `acquire!(weak)` (`L3667–3668`).
   - *Protocol (`FSL++` / `iRC11` Cancellable):* Authoritative counter $(n_{\text{strong}}, \bigsqcup_{i=1}^{k} V_i)$ collects fractional `AtView V_i (data ↦{q_i} v)` on each `Release` decrement across the contiguous RMW release sequence. The final decrement's `Relaxed` read half (`atomic.rs:478–479`) absorbs $V_{\text{all}}$ into $V_{\text{acq}}$ (`JoinView V_all (data ↦{1} v)`), and `fence(Acquire)` yields exclusive `data ↦ v`.
   - *`is_unique` Soundness Bug (`arc/code.v:81–94`, `rust-lang/rust#51780`):* After locking `weak` via `CAS(1, usize::MAX, Acquire, Relaxed)`, reading `strong` **must** use `Acquire` (`arc.rs:1057`, `code.v:89`), not `Relaxed`—otherwise `Arc::get_mut` hands out `&mut T` without synchronizing with a prior thread's `strong.fetch_sub(1, Release)`!
3. **`SeqLock<T>` and the `read_volatile` UB Trap (`seq_lock.rs:28–93`):**
   - *Code:* Writer runs `prev = state.swap(1, Acquire); fence(Release);` (`L48–51`), writes payload, and unlocks via `state.store(prev.wrapping_add(2), Release)` (`L90–92`). Reader checks even `s1 = state.load(Acquire)`, reads payload, and validates `fence(Acquire); state.load(Relaxed) == s1` (`L39–40`).
   - *Protocol (`FSL` $\nabla + \triangle$):* Writer's `fence(Release)` is mandatory because `swap(1, Acquire)` has a `Relaxed` store half; reader's `fence(Acquire)` orders `Relaxed` payload loads before `s2`. By read-read coherence, `s1 == s2` forces every payload load into epoch `s1`.
   - *UB Hazard:* Reading payload via `ptr::read_volatile` (`atomic_cell.rs:1016–1025`) triggers **immediate `r[undefined.race]` UB** against concurrent writes; sound Rust `SeqLock<T>` (`T: Copy`) must use uniform-width `Relaxed` atomic loads into `[MaybeUninit<usize>; K]` and materialize `T` only after `validate_read(s1)` succeeds.
4. **Treiber Stack (`code_treiber.v:14–78`):**
   - `push` writes `n.data` and `n.next` non-atomically (`OwnLoc`) and swings `head` via `CAS(Release, Relaxed)`. `pop` loads `h = head.load(Acquire)` (`L33`), reads immutable `h.next` **non-atomically** via persistent `readonly_ptsto`, and wins `CAS` (`L44`) to claim $\mathsf{PopTok}(h)$, eliminating `[es PopTok(h) ⇝ AtView V_push(h) (h.data ↦ x)]` (`escrows.v:50`) under an active EBR/hazard guard.
5. **Michael-Scott Queue (`code_ms.v:15–76`):**
   - Per-node `link` follows 2-state monotone protocol $\mathsf{Null} \sqsubset \mathsf{Linked}(n', V_{n'})$. `enqueue` (`L36–52`) initializes `n` non-atomically, links `t.link` via `CAS(AcqRel/Release)`, and swings `q.tail` (`Release`). `dequeue` (`L54–64`) requires `Acquire` on *both* `q.head` (`L56`) and `s.link` (`L57`) before `CAS` on `q.head` claims $\mathsf{DeqTok}(n)$ to extract `n.data` via Escrow.
6. **Chase-Lev Work-Stealing Deque (`crossbeam-deque/src/deque.rs:96–115, 420–566, 662–704`; `chase_lev/code.v:57–96`):**
   - *Orderings:* Owner `push` (`L420–454`) loads `front(Acquire)`, writes slot `b`, and runs `fence(Release)` + `back.store(b + 1, Relaxed)`. Owner LIFO `pop` (`L510–564`) runs `back.store(b - 1, Relaxed); fence(SeqCst); f = front.load(Relaxed)`. Thief `steal` (`L662–704`) runs `f = front.load(Acquire); fence(SeqCst); b = back.load(Acquire); front.compare_exchange(f, f + 1, SeqCst, Relaxed)`.
   - *`SeqCst` Necessity (`iRC11` SC View $\mathcal{S}$):* When `front = 0, back = 2` and Thief 1 steals `0` (`front = 1`), omitting `fence(SeqCst)` allows Owner `pop` (`back := 1`) to read stale `front = 0` (claiming slot `1` without CAS!) while Thief 2 reads `front = 1` and stale `back = 2` (winning `CAS(1 -> 2)` to steal slot `1`!). In `orc11/tview.v:260–276`, `sc_fence_tview` ($\mathcal{S}' := V_{\text{acq}} \sqcup \mathcal{S}$) totally orders the two `fence(SeqCst)` steps, preventing double-claim.
   - *`read_volatile` Pre-CAS UB (`deque.rs:96–114, 687`):* `Stealer::steal` calls `buffer.read(f)` (`ptr::read_volatile`) *before* `front.compare_exchange` (`L695`). If `Worker::push` wraps around the ring and calls `write_volatile` on the same slot, `deque.rs:98–111` admits this is **data-race UB**; sound verification requires either post-CAS non-atomic read on non-wrapping/epoch-guarded slots (`chase_lev/code.v:74–75`) or `Relaxed` atomic `MaybeUninit` slot loads.

## Boundaries

- **`Ordering::Consume` (`memory_order_consume`):** **known not to apply** in Rust (`atomic.rs:465–526` exposes only `Relaxed`, `Release`, `Acquire`, `AcqRel`, `SeqCst`).
- **Pure `GPS` / `FSL` Sufficiency for `Chase-Lev` or `ArcInner` Freeing:** **known not to apply** — `Release`/`Acquire` logics without `SeqCst` view invariants ($\mathcal{S}$) permit the Chase-Lev `SB` double-claim bug, and eternal `GPS` protocols cannot deallocate atomic refcount headers without `iRC11` cancellable tokens.
- **Open-World Higher-Order Closures in `Type 0` `VProp_0`:** Storing impredicative heap-quantifying trait objects (`Box<dyn FnOnce() + Send>`) inside a `Type 0` protocol state map without defunctionalization or universe stratification is **unsupported**; step-indexed `iRC11` (`uPred`) is required.
- **Relaxed `Weak` Load in `Arc::try_unwrap_full` (`arc/code.v:117–125`):** Whether `try_unwrap_full` (`Arc::make_mut`) remains sound if `!ᵃᶜ(l + 1)` is weakened to `!ʳˡˣ(l + 1)` is **unknown** (`code.v:117–118`).
- **Fair-Scheduling Liveness and Lock-/Wait-Freedom:** All eight logics establish partial-correctness safety and linearizability; weak-memory liveness and progress guarantees (`orc11/progress.v`) were **not examined** here.

## Evidence

- **`kaist-cp/relaxed-memory-separation-logic` @ `6fe1475af1f8c49f8c144a67d9175b5b3e6bc472`:** `orc11/tview.v` (`L36–60, 197–276`), `gpfsl/base_logic/vprop.v` (`L16–54, 88–155`), `gpfsl/base_logic/na.v` (`L27–49, 100–210`), `gpfsl/gps/escrows.v` (`L14–64`), `gpfsl/gps/protocols.v`, and `gpfsl-examples/{lock/code_spin_lock.v:14–24, arc/code.v:15–125, stack/code_treiber.v:14–78, queue/code_ms.v:15–76, chase_lev/code.v:57–96}`.
- **`rocq-iris/iris` @ `2fe2f450add5678d9a2492343c638ccdb428a677`:** `iris/bi/monpred.v`.
- **`rust-lang/rust` @ `ec65cd52bba13d491ff65c9d218b39753755c84a`:** `library/core/src/sync/atomic.rs` (`L25–63, 465–526, 4792–4910`), `library/alloc/src/rcs/arc.rs` (`L57–72, 1057, 2234, 2982–3026, 3656–3668`).
- **`crossbeam-rs/crossbeam` @ `a28f40fdddb70bea8e5faf0efad9af0be4b9dbea`:** `crossbeam-utils/src/atomic/{seq_lock.rs:28–93, atomic_cell.rs:1016–1025}`, `crossbeam-deque/src/deque.rs` (`L96–115, 420–454, 471–566, 662–704`).
- **Papers:** Lahav & Vafeiadis, ICALP 2015 (`10.1007/978-3-662-47666-6_25`); Vafeiadis & Narayan, OOPSLA 2013 (`10.1145/2509136.2509532`); Turon et al., OOPSLA 2014 (`10.1145/2660193.2660243`); Doko & Vafeiadis, VMCAI 2016 (`10.1007/978-3-662-49122-5_20`) & ESOP 2017 (`10.1007/978-3-662-54434-1_17`); Kaiser et al., ECOOP 2017 (`10.4230/LIPIcs.ECOOP.2017.17`); Dang et al., POPL 2020 (`10.1145/3371102`); Mével et al., ICFP 2020 (`10.1145/3408978`).

## Revalidation

1. **Upstream Diffs (< 1 minute):** Diff `Arc::drop`/`Weak::drop`/`is_unique` in `rust-lang/rust` (`library/alloc/src/rcs/arc.rs`), `Buffer::{read,write}`/`Worker::pop`/`Stealer::steal` in `crossbeam-deque/src/deque.rs`, and `gpfsl/base_logic/{vprop.v, na.v}` in `kaist-cp/relaxed-memory-separation-logic`.
2. **Executable Model Probe (`python3` stdlib, < 0.2s):** Verify Chase-Lev's `SB` double-claim under `Release`/`Acquire` (`GPS`/`FSL`) vs. `SeqCst` fence safety (`iRC11` $\mathcal{S}' := V_{\text{acq}} \sqcup \mathcal{S}$) and `OwnLoc` view containment:
   ```python
   #!/usr/bin/env python3
   """Verify Chase-Lev SB necessity (iRC11 vs RA/FSL) and OwnLoc view containment."""
   def check_chase_lev(use_sc_fence: bool) -> tuple[bool, bool]:
       double_claim, ownloc_violation = False, False
       for owner_sc_first in (True, False):
           for f_owner in (0, 1):
               for b_thief in (2, 1):
                   min_f = 1 if (use_sc_fence and not owner_sc_first) else 0
                   min_b = 3 if (use_sc_fence and owner_sc_first) else 0
                   if f_owner < min_f or (b_thief == 2 and min_b == 3):
                       continue
                   owner_fast_pop = (1 - f_owner) > 0   # len > 0 => pops slot 1 without CAS
                   thief_steals_1 = (b_thief - 1) > 0   # b - f > 0 and wins CAS(1->2) on slot 1
                   if owner_fast_pop and thief_steals_1:
                       double_claim = True
                   if thief_steals_1 and not (1 <= 1):  # push fence(Rel) + back.load(Acq) => t_s1 <= V_cur
                       ownloc_violation = True
       return double_claim, ownloc_violation

   assert check_chase_lev(use_sc_fence=False) == (True, False)
   assert check_chase_lev(use_sc_fence=True) == (False, False)
   print("OK: RA allows Chase-Lev SB double-claim; iRC11 SeqCst fences forbid it with OwnLoc intact.")
   ```
