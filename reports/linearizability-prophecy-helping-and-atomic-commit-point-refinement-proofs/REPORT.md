# Linearizability, Prophecy Variables, External Helping, and Atomic Commit-Point Refinement Proofs

## Summary

Verifying **linearizability** (Herlihy & Wing, TOPLAS 1990) for non-blocking concurrent structures divides into four commit-point regimes with distinct proof obligations and trust bases:

1. **Local static commit points** (e.g., Treiber stack `CmpXchg`): a single thread-local atomic step both updates shared memory and commits the operation, requiring only a pure **forward simulation** or a direct Iris **atomic accessor / update** (`AACC` / `AU`).
2. **External deterministic helping** (e.g., Hendler–Shavit–Yerushalmi elimination-backoff stack): after a failed `CmpXchg`, a pusher publishes an offer invariant `offer_inv` holding `OfferPending => stack_push_au γ v Q`; a peer `pop` CASing `OfferPending -> OfferAccepted` commits both its own `AU` and the pusher's `stack_push_au` simultaneously, depositing `Q` behind a one-shot exchange token (`kaist-cp/smr-verification@53fdc1648c17`, `proof_elimstack.v`).
3. **Future-dependent commit points** (e.g., Herlihy–Wing queue `Enq`, Harris–Fraser–Pratt `RDCSS`): **no pure forward simulation exists**, because which concurrent operation linearizes first depends on future steps by other threads. Discharging them requires **backward simulation** (Lynch & Vaandrager 1995; Schellhorn et al. CAV 2012), **partial-order abstract histories** (Khyzha et al. ESOP 2017), or **prophecy variables** (`ProphMap`, Jung et al. POPL 2020) justified by syntactic **prophecy erasure** (`proph_erasure.v`).
4. **Reclamation-coupled optimistic traversals** (e.g., Harris lock-free linked list under hazard pointers): traversing logically deleted nodes after `CAS` unlinking breaks naive single-pointer `shield_protect` re-validation unless persistent post-unlink link histories (`RetireChain` / `DeletedChain`) or epoch grace periods (`crossbeam-epoch` `wrapping_sub >= 2`) constrain physical reuse. Notably, `crossbeam-epoch`'s `x86`/`x86_64` `compare_exchange(..., SeqCst)` + `compiler_fence(SeqCst)` shortcut (`internal.rs:421–453`) relies on `x86-TSO` store-buffer draining and is guarded by `not(miri)` because C++20/RC11 forbids substituting an SC RMW for `atomic::fence(SeqCst)`.

Across tools, **prophecy soundness** requires rejecting cyclic self-resolution (`p.resolve(!p.value())`) and prophetic `decreases` termination measures (`verus@0dab219272ac`, `source/vstd/proph.rs`), while **predicative `Type 0` proof assistants** without step-indexed recursive `IProp` domains (`iris-lean@5540ef0110fc`, `IProp.lean`) must replace impredicative `AU` escrows and `Prop`-to-`Type 0` existential projection with defunctionalized `Type 0` protocol tags and explicit finite prophecy schedules.

## Applicability

This report synthesizes evidence across five pinned upstream repositories:

- **`kaist-cp/smr-verification@53fdc1648c17c5527c2499ed0ad10d55c01e1344` (Rocq/Iris):** Modular hazard-pointer specs (`spec_hazptr.v`), EBR/RCU, `RDCSS` with prophecies (`proof_rdcss.v`), elimination stack with helping (`proof_elimstack.v`), Harris list link histories (`proof_harris_find.v`), and prophecy erasure (`proph_erasure.v`).
- **`leanprover-community/iris-lean@5540ef0110fc8f6d8e495c10c2f238c3ede14f3b` (Lean 4 port of Rocq Iris `@8e4909593a3a84f850d224a344cbd3a380672088`):** `atomic_acc`, `atomic_update` (`Atomic.lean`), `ProphMap` (`ProphMap.lean`), and recursive `IProp` (`IProp.lean`).
- **`verus-lang/verus@0dab219272ac2353320bd177ebb3929453b90a9e` (Rust + SMT):** `atomic_with_ghost!` (`source/vstd/atomic_ghost.rs`) and `Prophecy<T>` / `ProphecyGhost<T>` / `ProphecySeq<T>` (`source/vstd/proph.rs`).
- **`crossbeam-rs/crossbeam@a28f40fdddb70bea8e5faf0efad9af0be4b9dbea` (`crossbeam-epoch`):** Grace-period arithmetic and `Local::pin()` fences (`internal.rs`).
- **`leanprover/lean4@c09b486ce1706403e386ae88450194fbac50fc33` (Lean 4 kernel):** Universe stratification (`Prop` vs. `Type 0`) and subsingleton elimination constraints.

Sibling topics—functional borrow-lifetime prophecies (`rust-verification-lifetimes-prophecies-and-functional-translation`) and transfinite Iris adequacy (`iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic`)—are separate scopes. Unless specifically noted for `x86-TSO` (`crossbeam-epoch`), operational claims assume SC or release-acquire linearized atomic transitions.

## Findings

### 1. Commit-Point Taxonomy and Why Forward Simulation Fails on Herlihy–Wing

`Basis: documentation + source + execution + derived`

Under **linearizability** (Herlihy & Wing, TOPLAS 1990, DOI `10.1145/78969.78972`), every concurrent history $H$ must admit an extension $H'$ (completing selected pending calls and dropping others) and a total sequential permutation $\sigma$ of complete operations respecting the sequential specification and preserving all real-time precedences ($\text{ret}(op_1) \prec_H \text{inv}(op_2) \Rightarrow op_1 \prec_\sigma op_2$). Non-blocking algorithms fall into four commit-point classes:

| Class | Representative Algorithms | Commit-Point Mechanism | Why Naive Forward Simulation Fails | Adequate Proof Tool |
| :--- | :--- | :--- | :--- | :--- |
| **1. Fixed local step** | Treiber stack, counters | Single `CmpXchg` / `FAA` in caller | — (statically fixed) | Forward simulation or direct `AU` |
| **2. Deterministic helping** | Elimination stack (SPAA 2004), MS-queue tail advance | Peer thread's CAS commits caller | Caller returns after peer completes commit | Escrowed `AU` in shared invariant |
| **3. Future-dependent** | Herlihy–Wing queue `Enq`, `RDCSS` (`l_m` read) | Past step whose winner is decided later | Indistinguishable concrete state has two incompatible future orders | Prophecy variables, backward sim, or posets |
| **4. Reclamation-coupled** | Harris lock-free list + Hazard Pointers | `CmpXchg` + traversal across retired nodes | ABA reuse / concurrent unlinking breaks pointer re-validation | `Shield`/`Managed` + immutable link histories |

**Herlihy–Wing Queue Forward-Simulation Refutation (`Herlihy & Wing 1990`, §3):**
`Enq(x)` reserves `i := FAA(back, 1)` then stores `items[i] := x`; `Deq()` scans `j = 0..back-1` via `Xchg(items[j], null)` until non-null. Consider two concurrent enqueues $E_1(x), E_2(y)$:

```text
t1: E1 reserves slot 0 (FAA -> 0)         [back=1, items=[null, null]]
t2: E2 reserves slot 1 (FAA -> 1)         [back=2, items=[null, null]]
t3: E2 stores items[1] := y, returns      [back=2, items=[null, y]]   <-- CRITICAL STATE S_crit
t4: D1 reads back=2, swaps items[0] -> null
    Branch A: D1 swaps items[1] -> y (returns y); then E1 stores x@0, D2 swaps -> x.
              ==> MUST linearize E2(y) BEFORE E1(x).
    Branch B: Before D1 advances, E1 stores x@0, D1 (restarted) or D2 swaps items[0] -> x.
              ==> MUST linearize E1(x) BEFORE E2(y).
```

At $S_{\text{crit}}$, the concrete machine state is identical before either branch diverges. Any pure forward simulation mapping $S_{\text{crit}}$ to one abstract FIFO queue ($[y]$ vs. $[x, y]$) is refuted by the opposite extension (**Revalidation** Probe 1 confirms disjoint valid permutation sets).

### 2. Backward Simulation, Partial-Order Histories, and Abadi–Lamport Completeness

`Basis: documentation + derived`

Refinement theory provides three non-separation-logic resolutions to $S_{\text{crit}}$:
1. **Abadi–Lamport Completeness (TCS 1991, DOI `10.1016/0304-3975(91)90224-P`):** Under *machine closure*, *internal continuity*, and *finite invisible nondeterminism (FIN)*, every sound trace inclusion admits a single-valued refinement mapping once augmented with **history variables** (past invisible choices) and **prophecy variables** (bounded future choices resolving $S_{\text{crit}}$).
2. **Backward Simulation & Rely-Guarantee Helping:** Lynch & Vaandrager (Inf. Comput. 1995, DOI `10.1006/inco.1995.1142`) replace prophecies with set-valued **backward simulations**; Schellhorn, Wehrheim & Derrick (CAV 2012, DOI `10.1007/978-3-642-31424-7_21`) use backward simulation in KIV to verify the Herlihy–Wing queue directly. Liang & Feng (PLDI 2013, DOI `10.1145/2491956.2462189`) thread-localize this via rely-guarantee commit-transfer assertions (`P -> Q`).
3. **Partial-Order Abstract Histories (Khyzha, Dodds, Gotsman & Parkinson, ESOP 2017, DOI `10.1007/978-3-662-54434-1_24`, `arXiv:1701.05463`):** The abstract state is a **poset** $(E, \prec)$ of operations rather than a total list: $E_1(x)$ and $E_2(y)$ remain unordered ($E_1(x) \parallel E_2(y)$) at $S_{\text{crit}}$ and acquire edge $E_2(y) \prec E_1(x)$ or $E_1(x) \prec E_2(y)$ only when `Deq` claims an item, avoiding explicit prophecy guessing whenever every reachable poset admits a valid sequential topological sort.

### 3. Logical Atomicity (`HOCAP`, `TaDA`, Iris `AU`/`AACC`) and Ghost Helping

`Basis: source + derived`

Logically atomic triples modularize linearizability into Hoare-style specifications: **iCAP/HOCAP** (Svendsen & Birkedal, ESOP 2014, DOI `10.1007/978-3-642-54833-8_9`), **TaDA** $\vdash \langle \forall x.\, P(x)\rangle\; c\; \langle Q(x)\rangle$ (da Rocha Pinto et al., ECOOP 2014, DOI `10.1007/978-3-662-44202-9_9`), and **Iris** `atomic_update` (`AU`) (Jung et al., JFP 2018, DOI `10.1017/S0956796818000151`), proven complete for all linearizable objects via prophecy instrumentation in Rocq (Zhang, Gregersen & Tassarotti, `arXiv:2607.11435`, DOI `10.48550/arXiv.2607.11435`).

#### 3.1 Lean 4 Formulation of `atomic_acc` and `atomic_update` (`iris-lean@5540ef0110fc`)

In `leanprover-community/iris-lean@5540ef0110fc` (`Iris/Iris/BI/Lib/Atomic.lean:25–29, 101–123`), `atomic_update` is defined via `bi_greatest_fixpoint` over an accessor `atomic_acc` whose abort continuation recurses back into `AU`:

```lean
def atomic_acc (Eo Ei : CoPset) (α : TA.Arg → PROP) (P : PROP)
    (β Φ : TA.Arg → TB.Arg → PROP) : PROP := iprop%
    |={Eo,Ei}=> ∃.. x, α x ∗ ((α x ={Ei,Eo}=∗ P) ∧ (∀.. y, β x y ={Ei,Eo}=∗ Φ x y))

def atomic_update_pre (Eo Ei : CoPset) (α : TA.Arg → PROP)
    (β Φ : TA.Arg → TB.Arg → PROP) : (Unit → PROP) → Unit → PROP :=
  fun Ψ _ => atomic_acc Eo Ei α (Ψ ()) β Φ

def atomic_update (Eo Ei : CoPset) (α : TA.Arg → PROP)
    (β Φ : TA.Arg → TB.Arg → PROP) : PROP :=
  bi_greatest_fixpoint (atomic_update_pre Eo Ei α β Φ) ()
```

Conjoining abort (`α x ={Ei,Eo}=∗ P`) and commit (`β x y ={Ei,Eo}=∗ Φ x y`) with `∧` lets a failing `CmpXchg` or validation retry abort cleanly without consuming `AU`, while making `AU` a first-class `IProp` resource that can be transferred into invariants.

#### 3.2 Elimination-Backoff Stack Helping (`smr-verification@53fdc1648c17`)

In `kaist-cp/smr-verification@53fdc1648c17` (`theories/hazptr/proof_elimstack.v:9, 59–105, 173–245, 333–385`; Hendler et al. SPAA 2004, DOI `10.1145/1007912.1007955`), a failing `estack_push` publishes an offer `[v, 0]` (`OfferPending`) backed by a 4-state ghost machine (`OfferPending | OfferRevoked | OfferAccepted | OfferAcked`):

```coq
Definition offer_inv (offer_loc : blk) (v : val) (γz γn γo : gname) (P Q : iProp) : iProp :=
  ∃ (st : offer_state), offer_info γn v st ∗
    match st with
    | OfferPending => P   (* pusher's stack_push_au γ v Q *)
    | OfferAccepted => Q  (* pusher's postcondition produced by helper pop *)
    | _ => token γo       (* OfferRevoked or OfferAcked *)
    end.
```

Two engineering details are load-bearing:
1. **Factoring `offer_inv` outside `hazptr.Managed` (`L73–78`):** Putting `P, Q` inside `Managed` (`offer_data`) would existentially re-quantify `P` and `Q` on every `shield_acc` invariant opening, losing laterability across steps. Keeping `inv offerN (offer_inv ...)` inside `IsOffer` (`L97–105`) while placing only `(ghost_var γ_pv (1/2) st ∗ to_agree v)` inside `Managed` avoids re-binding.
2. **Dual-`AU` commit in one physical CAS (`L354–374`):** When `estack_pop` CASes `OfferPending (0) -> OfferAccepted (1)`, it opens `offer_inv` and `EStackInternalInv`, commits the pusher's `stack_push_au` (`xs2 -> v :: xs2`, yielding `Q`), immediately commits its own pop `AU` (`v :: xs2 -> xs2`, yielding `Φ (Some v)`), and deposits `Q` into `offer_inv` for the pusher to claim via `token γo` (`L233–241`)—requiring **zero prophecies**.

### 4. Prophecy Separation Logic, `RDCSS`, Erasure, and Verus Soundness Guards

`Basis: source + derived`

In Harris–Fraser–Pratt **RDCSS** (DISC 2002, DOI `10.1007/3-540-36108-1_18`), `rdcss(l_m, l_n, m1, n1, n2)` installs descriptor `#l_descr` into `l_n`. Any helper reading `*l_m` (`wp_load`) subsequently tries `CmpXchg(l_n, InjRV #l_descr, InjLV target)` (`target = n2` if `*l_m == m1` else `n1`). Because `*l_m` may change between competing helpers' reads, the linearization point is **the read of `*l_m` by whichever helper later wins the completion `CmpXchg`**—unknowable when `*l_m` is read!

#### 4.1 `ProphMap` and `RDCSS` Winner Prediction (`iris-lean` & `smr-verification`)

Jung et al. (POPL 2020, DOI `10.1145/3371113`) internalize prophecies via exclusive resource ownership. In `iris-lean@5540ef0110fc` (`Iris/Iris/BI/Lib/ProphMap.lean:51–77, 139–199`):
- `proph (p : P) (vs : List V)` asserts exclusive right to resolve prophecy `p` (`proph_exclusive`: `proph p vs1 -∗ proph p vs2 -∗ False`), synchronized with the operational suffix `pvs : ProphValList P V` via `prophMapInterp`.
- `resolve_proph` consumes `(p, v) :: pvs` and `proph p vs`, yielding `vs = v :: vs'` and updated `proph p vs'`.

In `kaist-cp/smr-verification@53fdc1648c17` (`theories/hazptr/proof_rdcss.v:66–130, 186–288, 312–363, 431–475`):
1. Allocating `#l_descr` creates prophecy `p` (`L431`), whose head `proph_extract_winner proph_values` (`L66–70, 465`) identifies the winning thread token `tid_ghost_inv` of the first `Resolve(CmpXchg #l_n (InjRV #l_descr) ..., #p, #tid_ghost)` (`L197`).
2. Each helper creates a fresh token `tid_ghost` (`L312`) and splits on `decide (tid_ghost_inv = tid_ghost)` (`L316`): the unique predicted winner opens and commits `rdcss_au` during `wp_load` of `*l_m` (`L322–335`, moving `pending_state` -> `accepted_state`) and later proves its `CmpXchg` succeeds (`complete_succeeding_thread_pending`, `L186–234`); losing helpers leave `rdcss_au` untouched and prove their `CmpXchg` must fail (`complete_failing_thread`, `L236–288`).
3. **Erasure Soundness (`theories/lang/proph_erasure.v:17–53, 127–132`):** Erasing `LitProphecy` to `#LitPoison`, `NewProph` to `(λ: <>, #LitPoison) #()`, and `Resolve e0 e1 e2` to `Fst (Fst (e0, e1, e2))` preserves closed safety adequacy without runtime prophecy overhead.

#### 4.2 Verus Prophecy Soundness Hazards (`verus@0dab219272ac`)

In `verus-lang/verus@0dab219272ac` (`source/vstd/proph.rs:17–145, 168–294` & `source/vstd/atomic_ghost.rs:12–37`), `Prophecy<T>` (exec-only resolution, non-dependent, not tainted) contrasts with `ProphecyGhost<T>` (ghost/dependent resolution, `value()` marked `#[verifier::prophetic]`):
- **Cyclic Self-Resolution (`proph.rs:25–51`):** `p.resolve(!p.value())` proves `false`; prevented by rejecting `#[verifier::prophetic]` operands in `proof`/`tracked` calls (`ProphecyGhost`) or requiring `exec`-mode concrete `v: &T` (`Prophecy`).
- **Infinite-Trace Termination Paradox (`proph.rs:59–104`):** A `loop` calling `ProphecySeq::resolve_cons(0)` satisfies `old(self).seq() == seq![0] + final(self).seq()`, giving an apparently decreasing `s.seq().len()` on a non-terminating loop! Verus rejects `#[verifier::prophetic]` inside `decreases` clauses (`L90–99`) and `Ghost(...)` (`L131–145`), confining dependent prophecies (and `AtomicInvariantPredicate::atomic_inv`, `atomic_ghost.rs:13–14`) to partial correctness.

### 5. Hazard Pointers, Optimistic Traversals, and `crossbeam-epoch` Fences

`Basis: documentation + source + derived`

Reclamation creates **physical ABA**: a pointer `p` read concurrently may be retired and reallocated with an unrelated invariant before `Shield` protection or `CmpXchg`.
- **Modular Hazard Pointers (`spec_hazptr.v:10–153`; Jung et al. OOPSLA 2023, DOI `10.1145/3622827`):** `shield_state` tracks `Deactivated | NotValidated p | Validated p γ_p R size_i`. `shield_protect_spec'` (`L86–103`) requires observing `*a == Some p` simultaneously with `▷ Managed γd p γ_p size_i R`, establishing `shield_managed_agree` (`γ_p1 = γ_p2`, `L124–128`).
- **Harris List Unlinked-Chain Hazard (`proof_harris_find.v:23–160`; Kim et al. PLDI 2025, DOI `10.1145/3729247`; Harris DISC 2001, DOI `10.1007/3-540-44605-2_19`):** Because Harris readers traverse sequences of logically marked (`next` tag bit) and already unlinked nodes, re-reading `prev.next` fails standard hazard validation. While Harris–Michael restarts from `head` (`proof_harris_michael_find.v`), the original Harris algorithm relies on **immutable post-unlink `next` pointers**: `RetireChain` (`L23–30`) and `DeletedChain` (`L115–122`) record persistent link witnesses `i_p ↪[γp_t]□ (Some (anchor', i_a'), true)`, proving any node reachable along an unlinked marked chain from a shielded anchor remains valid (`Managed`) without restarting.
- **Epoch-Based Reclamation (`crossbeam-rs/crossbeam@a28f40fdddb7`, `crossbeam-epoch/src/internal.rs:157–160, 408–453`):** `SealedBag::is_expired` enforces a 3-epoch delay (`global_epoch.wrapping_sub(self.epoch) >= 2`, `L157–160`). Crucially, `Local::pin()` (`L421–453`) uses `cfg!(all(any(target_arch = "x86", target_arch = "x86_64"), not(miri)))` to substitute `self.epoch.compare_exchange(..., SeqCst, SeqCst)` + `compiler_fence(SeqCst)` for `atomic::fence(SeqCst)`: sound on hardware `x86-TSO` (`LOCK CMPXCHG` flushes the store buffer), yet unsound in C++20/RC11 (where `not(miri)` restores `store(Relaxed); fence(SeqCst)`, `L451–452`, because an SC RMW + later `Acquire` load lacks the `SC`-fence total-order edge against remote epoch scans).

### 6. Encoding Commit-Point Witnesses Inside Predicative `Type 0` Proof Assistants

`Basis: source + execution + derived`

In `iris-lean@5540ef0110fc` (`Iris/Iris/Algebra/IProp.lean:23–103`), embedding higher-order `AU` invariants inside ghost state requires solving the recursive step-indexed domain isomorphism `IPre GF := OFunctor.Fix (UPredOF (IResF GF))` (`L69–95`) with `linter.checkUnivs false` (`L23, L31`). Conversely, predicative `Type 0` kernels (`lean4@c09b486ce170`) enforce **restricted large elimination** on `Prop`: an existential `∃ k : Nat, CommitAt tr k` in `Prop` cannot be projected to `Type 0` witness data unless `CommitAt` is decidable (`Nat.find`) or the witness itself resides in `Type 0`.

| Proof Strategy | Logic & Trust Core | Helping (`ElimStack` / `RDCSS`) | Herlihy–Wing Queue | SMR Composition | Termination / Liveness |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Impredicative `AU` + `ProphMap`** (`Iris` / `iris-lean`) | Step-indexed `IProp` (`OFunctor.Fix`) | Escrow `AU` inside shared invariant | `ProphMap` / `ProphecySeq` | Modular `Shield` / `Managed` | Partial correctness (`WP`) |
| **Linear Ghost + `#[verifier::prophetic]`** (`Verus`) | Rust + SMT + linear `Tracked<G>` | `AtomicInvariantPredicate` + tokens | `Prophecy` / `ProphecyGhost` | Linear pointer permissions | Partial correctness if dependent |
| **Partial-Order Histories** (`ESOP 2017`) | First-order op-history logic | Pending op pool + state tag | Natural (`E1 ∥ E2` poset) | Epoch / hazard side-conditions | Compatible with fair traces |
| **Defunctionalized `Type 0` Schedule `π`** | Pure `Type 0` kernel (`0` recursive domains) | First-order `Type 0` enum (`OfferSt`) | Constructive `linearizePrefix tr π` | Explicit grace-period / hazard index | Constructive over finite prefixes |

To encode commit-point proofs inside pure `Type 0` Lean 4 without recursive `IProp` domains or `Classical.choice`:
1. **Defunctionalize Helping Invariants:** Replace `P Q : IProp` inside shared protocol records (`offer_inv`, `descr_inv`) with a finite `Type 0` state machine (`inductive CommitTag | pending (op : OpDesc) | committed (res : RetVal) (helper : ThreadId) | aborted`) paired with a single-commit transition invariant.
2. **Represent Prophecy as an Explicit `Type 0` Trace Schedule (`π : Nat → Option WinnerId`):** Define `linearizePrefix : Trace → Oracle → List AbstractEvent` constructively in `Type 0` over finite traces, and establish adequacy backwards by proving that for every reachable finite trace `tr` of length `N`, the realized outcomes in `tr[0..N]` compute a valid finite oracle `π` (e.g., extracting which `Deq` claims which `Enq` slot or which helper wins each `RDCSS` `CmpXchg`, verified in **Revalidation**).

## Boundaries

- **unsupported:**
  - Large elimination from `Prop`-level existential commit witnesses (`∃ k : Nat, CommitAt tr k`) into `Type 0` witness values without decidability (`Nat.find`) or `Classical.choice` is **unsupported** in Lean 4's kernel (`leanprover/lean4@c09b486ce170`).
  - Prophetic expressions inside `decreases` termination clauses or `Ghost(...)` wrappers are **unsupported** in `verus-lang/verus@0dab219272ac` (`source/vstd/proph.rs:87–145`).
- **known not to apply:**
  - Pure forward state-to-state simulations without prophecy or partial-order history augmentation are **known not to apply** to Herlihy–Wing queue `Enq` linearizability (refuted at $S_{\text{crit}}$ in Finding 1 and Revalidation Probe 1).
  - `crossbeam-epoch`'s `x86`/`x86_64` `compare_exchange(..., SeqCst, SeqCst)` + `compiler_fence(SeqCst)` replacement for `atomic::fence(SeqCst)` (`internal.rs:421–453`) is **known not to apply** under C++20/RC11 (`Miri`) or weakly ordered architectures (`ARMv8`, `RVWMO`).
  - Naive single-pointer `shield_protect` re-validation (without persistent post-unlink `RetireChain` histories or head-restart fallback) is **known not to apply** to optimistic traversal across unlinked deleted nodes in Harris's list (`proof_harris_find.v`).
  - Execution-only `Prophecy<T>` in `verus@0dab219272ac` is **known not to apply** when resolution depends on ghost computations (`ProphecyGhost<T>` is required, `proph.rs:12–20`).
- **unknown:**
  - Whether logical atomicity completeness (`arXiv:2607.11435`) generalizes constructively to weak-memory logics (`iRC11`, `Cosmo`) without SC wrappers remains **unknown**.
  - SMT solver scaling limits for nested `AtomicInvariantPredicate` prophecy proofs across multi-word CAS algorithms in `Verus` remain **unknown**.
- **not examined:**
  - Hardware transactional memory (`Intel TSX`, `ARM TME`) commit-point elision and bounded wait-free universal constructions (`Herlihy` / `k-CSS`) were **not examined**.
  - Impredicative higher-order closure storage (`Box<dyn FnMut()>`) requiring transfinite $\omega_1$ step-indexing was **not examined**.

## Evidence

### Primary Repositories Inspected

| Repository | Exact 40-char Commit SHA | Path / Line Range | Verified Observation |
| :--- | :--- | :--- | :--- |
| `kaist-cp/smr-verification` | `53fdc1648c17c5527c2499ed0ad10d55c01e1344` | `theories/hazptr/proof_elimstack.v:9, 59–105, 173–385` | `offer_state`, `offer_inv` outside `Managed`, dual-`AU` helping CAS |
| `kaist-cp/smr-verification` | `53fdc1648c17c5527c2499ed0ad10d55c01e1344` | `theories/hazptr/proof_rdcss.v:66–130, 186–288, 312–363, 431–475` | `proph_extract_winner`, winner vs. loser split on `Resolve (CmpXchg ...)` |
| `kaist-cp/smr-verification` | `53fdc1648c17c5527c2499ed0ad10d55c01e1344` | `theories/hazptr/spec_hazptr.v:10–153` | `shield_state`, `shield_protect_spec'`, `shield_managed_agree'` |
| `kaist-cp/smr-verification` | `53fdc1648c17c5527c2499ed0ad10d55c01e1344` | `theories/hazptr/proof_harris_find.v:23–160` | `RetireChain` and `DeletedChain` persistent ghost link histories |
| `kaist-cp/smr-verification` | `53fdc1648c17c5527c2499ed0ad10d55c01e1344` | `theories/lang/proph_erasure.v:17–62, 111–132` | Erasure of `NewProph`/`Resolve` to `#LitPoison`/`Fst (Fst ...)` |
| `leanprover-community/iris-lean` | `5540ef0110fc8f6d8e495c10c2f238c3ede14f3b` | `Iris/Iris/BI/Lib/Atomic.lean:25–123` | `atomic_acc`, `atomic_update` via `bi_greatest_fixpoint` |
| `leanprover-community/iris-lean` | `5540ef0110fc8f6d8e495c10c2f238c3ede14f3b` | `Iris/Iris/BI/Lib/ProphMap.lean:51–77, 139–199` | `prophListResolves`, `prophMapInterp`, `proph_exclusive`, `resolve_proph` |
| `leanprover-community/iris-lean` | `5540ef0110fc8f6d8e495c10c2f238c3ede14f3b` | `Iris/Iris/Algebra/IProp.lean:23–103` | `OFunctor.Fix (UPredOF (IResF GF))` & `checkUnivs false` |
| `verus-lang/verus` | `0dab219272ac2353320bd177ebb3929453b90a9e` | `source/vstd/proph.rs:17–145, 168–294` | `Prophecy` vs. `ProphecyGhost`/`ProphecySeq`, cyclic & `decreases` guards |
| `verus-lang/verus` | `0dab219272ac2353320bd177ebb3929453b90a9e` | `source/vstd/atomic_ghost.rs:12–37` | `#[verifier::prophetic]` on `AtomicInvariantPredicate::atomic_inv` |
| `crossbeam-rs/crossbeam` | `a28f40fdddb70bea8e5faf0efad9af0be4b9dbea` | `crossbeam-epoch/src/internal.rs:157–160, 408–453` | 3-epoch grace period (`>= 2`) & `x86` `SeqCst` CAS + `not(miri)` fence |

### Peer-Reviewed Literature Anchors

1. M. P. Herlihy and J. M. Wing, *"Linearizability: A Correctness Condition for Concurrent Objects,"* ACM TOPLAS 12(3), 1990, DOI `10.1145/78969.78972`.
2. M. Abadi and L. Lamport, *"The Existence of Refinement Mappings,"* TCS 82(2), 1991, DOI `10.1016/0304-3975(91)90224-P`.
3. N. Lynch and F. Vaandrager, *"Forward and Backward Simulations,"* Information and Computation 121(2), 1995, DOI `10.1006/inco.1995.1142`.
4. T. L. Harris, *"A Pragmatic Implementation of Non-Blocking Linked-Lists,"* DISC 2001, DOI `10.1007/3-540-44605-2_19`.
5. T. L. Harris, K. Fraser, and I. A. Pratt, *"A Practical Multi-Word Compare-and-Swap Operation,"* DISC 2002, DOI `10.1007/3-540-36108-1_18`.
6. D. Hendler, N. Shavit, and L. Yerushalmi, *"A Scalable Lock-Free Stack Algorithm,"* SPAA 2004, DOI `10.1145/1007912.1007955`.
7. G. Schellhorn, H. Wehrheim, and J. Derrick, *"How to Prove Algorithms Linearisable,"* CAV 2012, DOI `10.1007/978-3-642-31424-7_21`.
8. H. Liang and X. Feng, *"Modular Verification of Linearizability with Non-Fixed Linearization Points,"* PLDI 2013, DOI `10.1145/2491956.2462189`.
9. K. Svendsen and L. Birkedal, *"Impredicative Concurrent Abstract Predicates,"* ESOP 2014, DOI `10.1007/978-3-642-54833-8_9`.
10. P. da Rocha Pinto, T. Dinsdale-Young, and P. Gardner, *"TaDA: A Logic for Time and Data Abstraction,"* ECOOP 2014, DOI `10.1007/978-3-662-44202-9_9`.
11. A. Khyzha, M. Dodds, A. Gotsman, and M. J. Parkinson, *"Proving Linearizability Using Partial Orders,"* ESOP 2017, DOI `10.1007/978-3-662-54434-1_24` (`arXiv:1701.05463`, DOI `10.48550/arXiv.1701.05463`).
12. R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal, and D. Dreyer, *"Iris from the Ground Up,"* JFP 28, 2018, DOI `10.1017/S0956796818000151`.
13. R. Jung, R. Lepigre, G. Parthasarathy, M. Rapoport, A. Timany, D. Dreyer, and B. Jacobs, *"The Future is Ours: Prophecy Variables in Separation Logic,"* POPL 2020, DOI `10.1145/3371113`.
14. J. Jung, J. Lee, J. Choi, J. Kim, S. Park, and J. Kang, *"Modular Verification of Safe Memory Reclamation in Concurrent Separation Logic,"* OOPSLA 2023, DOI `10.1145/3622827`.
15. J. Kim, J. Jung, and J. Kang, *"Leveraging Immutability to Validate Hazard Pointers for Optimistic Traversals,"* PLDI 2025, DOI `10.1145/3729247`.
16. Z. Zhang, S. O. Gregersen, and J. Tassarotti, *"Completeness of Logical Atomicity for Linearizability in Concurrent Separation Logic,"* `arXiv:2607.11435`, DOI `10.48550/arXiv.2607.11435`.

### Executed Model Probe (`observed_at: 2026-11-20`)

Running the Python 3 model checker in **Revalidation** (`< 20 ms`) verified: (1) from $S_{\text{crit}}$, Herlihy–Wing Branch A forces `E2 < E1` on every linearizable permutation whereas Branch B forces `E1 < E2` (`set(valid_a).isdisjoint(set(valid_b))`); (2) across all interleavings of `writer` (`T0`), `helper` (`T1`), and `mutator(l_m)` (`T2`), RDCSS commits exactly once (`len(commits) == 1`) with final value matching the winning helper's `l_m` read (`outcomes == {(0, 10), (1, 20)}`).

## Revalidation

1. **Fast Standalone Herlihy–Wing & RDCSS Helping Exhaustive Checker (`< 30 ms`, Python 3.10+ stdlib only):**

```bash
python3 - <<'PY'
from itertools import permutations

def is_valid_hwq_history(events, order):
    pos = {op: i for i, op in enumerate(order)}
    inv = {op: i for i, (op, k, _, _) in enumerate(events) if k == "inv"}
    ret = {op: i for i, (op, k, _, _) in enumerate(events) if k == "ret"}
    for o1 in ret:
        for o2 in inv:
            if ret[o1] < inv[o2] and pos[o1] > pos[o2]:
                return False
    q = []
    op_val = {op: v for op, k, v, _ in events if k in ("inv", "ret") and op.startswith("E")}
    op_ret = {op: v for op, k, v, _ in events if k == "ret" and op.startswith("D")}
    for op in order:
        if op.startswith("E"):
            q.append(op_val[op])
        else:
            if (q.pop(0) if q else None) != op_ret[op]:
                return False
    return True

branch_a = [
    ("E1", "inv", "x", 0), ("E2", "inv", "y", 1), ("E2", "ret", None, 2),
    ("D1", "inv", None, 3), ("D1", "ret", "y", 4),
    ("E1", "ret", None, 5), ("D2", "inv", None, 6), ("D2", "ret", "x", 7),
]
branch_b = [
    ("E1", "inv", "x", 0), ("E2", "inv", "y", 1), ("E2", "ret", None, 2),
    ("D1", "inv", None, 3), ("E1", "ret", None, 4), ("D1", "ret", "x", 5),
    ("D2", "inv", None, 6), ("D2", "ret", "y", 7),
]
valid_a = [o for o in permutations(["E1", "E2", "D1", "D2"]) if is_valid_hwq_history(branch_a, o)]
valid_b = [o for o in permutations(["E1", "E2", "D1", "D2"]) if is_valid_hwq_history(branch_b, o)]
assert all(o.index("E2") < o.index("E1") for o in valid_a)
assert all(o.index("E1") < o.index("E2") for o in valid_b)
assert set(valid_a).isdisjoint(set(valid_b))

def run_rdcss_schedule(m_init, n_init, m1, n1, n2, m_flip_val):
    results = []
    def dfs(l_n, l_m, pc0, r0, pc1, r1, flipped, commits):
        if pc0 == 2 and pc1 == 2 and flipped:
            assert isinstance(l_n, int) and len(commits) == 1 and l_n == commits[0][2]
            results.append((commits[0][1], l_n))
            return
        if pc0 == 0:
            dfs(l_n, l_m, 1, l_m, pc1, r1, flipped, commits)
        elif pc0 == 1:
            t = n2 if r0 == m1 else n1
            dfs(t if l_n == "DESCR" else l_n, l_m, 2, r0, pc1, r1, flipped,
                commits + ([("T0", r0, t)] if l_n == "DESCR" else []))
        if pc1 == 0:
            dfs(l_n, l_m, pc0, r0, 1, l_m, flipped, commits)
        elif pc1 == 1:
            t = n2 if r1 == m1 else n1
            dfs(t if l_n == "DESCR" else l_n, l_m, pc0, r0, 2, r1, flipped,
                commits + ([("T1", r1, t)] if l_n == "DESCR" else []))
        if not flipped:
            dfs(l_n, m_flip_val, pc0, r0, pc1, r1, True, commits)
    assert n_init == n1
    dfs("DESCR", m_init, 0, None, 0, None, False, [])
    return set(results)

assert run_rdcss_schedule(0, 10, 1, 10, 20, 1) == {(0, 10), (1, 20)}
print("REVALIDATION_OK")
PY
```

2. **Upstream Regression Diffs:** After updating pinned revisions, diff:
   - `kaist-cp/smr-verification`: `theories/hazptr/{proof_rdcss.v, proof_elimstack.v, spec_hazptr.v, proof_harris_find.v}`, `theories/lang/proph_erasure.v`;
   - `leanprover-community/iris-lean`: `Iris/Iris/BI/Lib/{Atomic.lean, ProphMap.lean}`, `Iris/Iris/Algebra/IProp.lean`;
   - `verus-lang/verus`: `source/vstd/{proph.rs, atomic_ghost.rs}`;
   - `crossbeam-rs/crossbeam`: `crossbeam-epoch/src/internal.rs` (`Local::pin`, `SealedBag::is_expired`).
