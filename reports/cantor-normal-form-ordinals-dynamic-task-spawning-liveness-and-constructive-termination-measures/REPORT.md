# Constructive Cantor Normal Form Ordinals, Dynamic Task-Spawning Liveness, and Termination Measures

## Summary

Proving global termination and starvation-freedom for **unbounded finite-branching dynamic task-spawning systems**—such as work-stealing async executors (`tokio-rs/tokio`), recursive actor or microkernel schedulers, and Dershowitz–Manna multiset rewriting systems—hits four structural boundaries across type universes, ordinal addition semantics, and scheduler fairness:

1. **Fixed `Nat` fuel ($\omega$) and fixed-arity lexicographic tuples $\mathbb{N}^k$ ($\omega^k$) fail on dynamic runtime branching and unbounded task depth.** When stepping a rank-$d$ task dynamically determines the child count $m(S, t) \in \mathbb{N}$ of lower-rank tasks ($d_j < d$), no initial `Nat` fuel bound can exist at $S_0$. Whenever maximum task rank $d$ or nested tree depth is data-dependent rather than statically bounded by $k$, fixed $\mathbb{N}^k$ tuples cannot embed the state space, whereas Dershowitz–Manna multisets over $(\mathbb{N}, <)$ have exact order type $\omega^\omega$ and finitely branching task trees (`Hydra`) have order type $\varepsilon_0$ (Dershowitz & Manna 1979, DOI `10.1145/359138.359142`).
2. **Set-theoretic `Ordinal` types force `Type 1` universe bumps and classical axioms; syntactic Cantor normal form (`CNF`) stays inside constructive `Type 0`.** In Mathlib4 (`leanprover-community/mathlib4@d13f23b723b8a846827a245b89c10fc7d3f11612`), `Ordinal.{u}` (`Mathlib/SetTheory/Ordinal/Basic.lean:80-108`) packages `WellOrder : Type (u + 1)` inside a `Quotient` (`Ordinal.{0} : Type 1`), and `Ordinal.CNF` (`CantorNormalForm.lean:36-73`) lives in a `noncomputable section` using `Quot.sound`, `propext`, and `Classical.choice`, preventing direct storage in `Type 0` states or resource cameras. By contrast, syntactic `Type 0` / `Set` CNF representations—exemplified by `coq-community/hydra-battles` (`T1 : Set` at `T1.v:46-48`, `Hessenberg.v`) and ACL2 `o-p` (`books/ordinals/ordinal-definitions.lisp`, Manolios & Vroon 2005, DOI `10.1007/s10817-005-9023-9`)—remain inside `Type 0`, carry decidable comparison and normal-form checkers (`nf_b`, `compare`), and discharge `WellFounded LT` (`T1_wf`, `T1.v:1793`) constructively via Tait-style strong accessibility (`Acc_strong`, `T1.v:1625-1793`) with zero classical choice or quotient axioms.
3. **Concurrent work-stealing requires commutative Hessenberg natural sum ($\oplus$), not ordinary ordinal addition ($+$).** Standard ordinal addition `T1add` (`T1.v:589-600`) left-absorbs lower terms ($\omega^1 + \omega^2 = \omega^2 = 5 + \omega^2$), so stepping a lower-rank task on one worker while a higher-rank task sits idle on another leaves a global $+$-measure non-decreasing. Hessenberg natural sum `oplus` (`Hessenberg.v:14-26`) is commutative, associative, cancellative, and strictly bi-monotonic (`oplus_strict_mono_r`, `oplus_strict_mono_l`, `Hessenberg.v:764-829`), enabling worker-local ghost-debt framing—provided implementations encode $\omega^a \cdot (n+1) + b$ with exact `S (n1 + n2)` exponent-match merging (`Hessenberg.v:23`) to avoid off-by-one collapse ($\omega \oplus \omega = \omega$).
4. **Composing $\text{CNF}(\omega^\omega)$ task debt with finitary fairness bounds (`Fair Operational Semantics`, PLDI 2023) yields constructive starvation-freedom.** In `tokio-rs/tokio@717c508f9e9ac4317665ff1eb30f29c139ea6363`, `lifo_slot` cache-locality optimizations are capped by `MAX_LIFO_POLLS_PER_TICK = 3` (`worker.rs:272, 783-786`) and `Budget(Some(128))` (`coop/mod.rs:115-117`) to prevent `run_queue` starvation. Pairing constructive `Type 0` CNF task debt with bounded `Nat` fairness turn counters $(\mu_{\text{pool}}, \Delta_{\text{sched}}) \in \text{CNF} \times \mathbb{N}$ establishes total termination across both productive spawns and bounded scheduler delays without Transfinite Iris's classical `ouPred_witness` or Trillium's external `fair_ex` hypothesis.

---

## Applicability

This report applies to designing termination measures, ghost-debt resource algebras, and fair-liveness proofs for:
- **Work-stealing async runtimes and schedulers** (`tokio-rs/tokio@717c508f9e9ac4317665ff1eb30f29c139ea6363`, `multi_thread/worker.rs`, `task/coop/mod.rs`), dynamic actor pools, and interruptible microkernel dispatchers;
- **Constructive dependent-type and first-order provers** (`coq-community/hydra-battles@ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8`, `acl2/acl2@f040a8db474f68e11b5fa980c99b7c1f7be28e54`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `leanprover-community/mathlib4@d13f23b723b8a846827a245b89c10fc7d3f11612`);
- **Concurrent liveness frameworks**, contrasting constructive CNF + finitary counters with `iris/transfinite` (`dde9f199bc09dc5242e3547be7c5049030f4c451`), `iris/trillium` (`d8bc4d31f929b9f5b9ef20a5943c9c923e8844c7`), *Fair Operational Semantics* (Lee et al., PLDI 2023, DOI `10.1145/3591253`), *TaDA Live* (D'Osualdo et al., TOPLAS 2021, DOI `10.1145/3477082`), and *Temporal TLA+* (Lamport, TOPLAS 1994, DOI `10.1145/177492.177726`).

### Cross-References to Adjacent Corpus Reports

- `iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic` covers `iris/transfinite`'s `oofe`/`oupred` interfaces, `siProp_witness` vs. `later_exists`, `ClassicalEpsilon`, LiveActris obligations, and Trillium `fair_ex`; this report focuses on constructive `Type 0` syntactic CNF, Hessenberg sums, and finitary scheduler composition.
- `fuel-step-indexing-clocks-and-tcb-recursion` covers `Init/WF.lean` TCB imports (`Init.Grind.Tactics`), `partial_fixpoint` (`Classical.choice`), and `Nat` fuel polarity; this report establishes the $\omega < \omega^k < \omega^\omega < \varepsilon_0$ expressiveness hierarchy for dynamic spawning.

---

## Findings

### 1. Why Dynamic Task Spawning Defeats Fixed `Nat` Fuel and Fixed-Arity Lexicographic Tuples

Basis: **normative + source + derived**

Consider a scheduler state $S$ holding an active task multiset $M(S)$, where each task $t$ carries rank $\rho(t) \in (D, \prec)$. Executing $t$ replaces it by $m(S, t) \ge 0$ dynamically computed child tasks $t_1, \dots, t_m$ satisfying $\rho(t_j) \prec \rho(t)$. Four order types partition the resulting termination bounds:

| Termination Measure | Order Type | Dynamic Fanout $m(S,t)$? | Data-Dependent Max Rank $d \in \mathbb{N}$? | Nested Recursive Trees? | Defeating System Class |
|---|---|---|---|---|---|
| **Fixed initial `Nat` fuel** $k \in \mathbb{N}$ | $\omega$ | **No** (total tree steps $\le k$ must be known at $S_0$) | **No** | **No** | Rank-2 task reading payload $n \in \mathbb{N}$ at step 1 and spawning $n$ rank-1 tasks |
| **Fixed-arity tuple** $\mathbb{N}^k$ | $\omega^k$ | Yes, up to depth $k-1$ | **No** ($d \ge k$ overflows fixed width) | **No** | Fork-join / recursive pipeline whose depth $D(S)$ scales with input |
| **Polynomial CNF** `List (Nat × Nat)` | $\omega^\omega$ | **Yes** (adds $m \cdot \omega^{d-1}$) | **Yes** (arbitrary finite $d \in \mathbb{N}$) | Bounded per term | Multiset rewriting over $(\mathbb{N}, <)$ (`Dershowitz–Manna 1979`, DOI `10.1145/359138.359142`) |
| **Full syntactic CNF** (`T1` / `o-p`) | $\varepsilon_0$ | **Yes** | **Yes** (transfinite towers) | **Yes** | Kirby–Paris Hydra / arbitrary finitely branching trees (`Hydra_Definitions.v:17-22`) |

By **Dershowitz and Manna (CACM 1979, DOI `10.1145/359138.359142`)**, the multiset ordering $(M_1 \prec_{\text{mul}} M_2)$—removing one $x \in M_2$ and inserting any finite $m \ge 0$ elements $y_1, \dots, y_m \prec x$—embeds strictly into $(\varepsilon_0, <)$ via $\mu(M) = \bigoplus_{x \in M} \omega^{\rho(x)}$: below $\omega^\omega$ when $\rho(t) \in \mathbb{N}$, and below $\varepsilon_0$ when tasks form nested finitely branching trees (`Hydra`). Neither $\omega^\omega$ nor $\varepsilon_0$ embeds into any fixed finite product $\mathbb{N}^k$.

---

### 2. Constructive `Type 0` Syntactic CNF vs. Universe-Bumping Quotient Ordinals

Basis: **source + derived**

#### 2.1 Why `Mathlib.SetTheory.Ordinal` Cannot Live in `Type 0` TCBs

Direct inspection of `leanprover-community/mathlib4@d13f23b723b8a846827a245b89c10fc7d3f11612` identifies three obstacles:

1. **Universe bump (`Mathlib/SetTheory/Ordinal/Basic.lean:80-108`):** `WellOrder : Type (u + 1)` bundles `α : Type u`, and `Ordinal : Type (u + 1) := Quotient Ordinal.isEquivalent`. Even `typeLT ℕ` (`lines 120-122`) has type `Ordinal.{0} : Type 1`, preventing storage inside any `Type 0` state machine, `Type 0` `CMRA` ghost camera, or certificate AST without lifting the surrounding hierarchy to `Type 1`.
2. **Noncomputability and classical axioms (`Basic.lean:65`; `CantorNormalForm.lean:36, 48-73`):** Both files open `noncomputable section`; `Ordinal.CNF b o` (`CantorNormalForm.lean:71-72`) uses classical `Ordinal.log` and `Ordinal.div`/`mod` over `Quotient`, pulling `Quot.sound`, `propext`, and `Classical.choice` and blocking kernel `rfl`/`decide` evaluation.
3. **`Init/WF.lean` (`lean4@5045d005...`, `lines 25-31, 60-64, 98-100`):** `WellFounded.fixF` uses `Acc.rec`, and `Init/WF.lean` imports `Init.Grind.Tactics`; however, `Acc` is constructive in `Prop` when instantiated with an explicit constructive accessibility proof rather than `Classical.choice`.

#### 2.2 Constructive `Type 0` / `Set` CNF (`hydra-battles` & `ACL2`)

| System & Source | Inductive Type (`Type 0` / `Set`) | Normal-Form Invariant | Ordering & Well-Foundedness | Axiom Footprint |
|---|---|---|---|---|
| **`hydra-battles` `T1`** (`T1.v:46-48, 169-188, 536-545, 1625-1793`) | `Inductive T1 : Set := zero \| cons (alpha : T1) (n : nat) (beta : T1)` representing $\omega^\alpha \cdot (n+1) + \beta$ | Boolean computable `nf_b` (`lines 536-542`): `nf_b a && nf_b b && bool_decide (lt a' a)` | Structural `compare` (`lines 169-184`); `LT alpha beta := nf alpha /\ nf beta /\ lt alpha beta`; constructive `T1_wf` via `Acc_strong` (`lines 1625-1793`) | **0 axioms** (`Set`/`Prop`; `transfinite_recursor` eliminates to `Type`) |
| **`ACL2` `o-p`** (`ordinal-definitions.lisp:29-56`; `e0-ordinal.lisp:142-148`; Manolios & Vroon JAR 2005) | Nested dotted pair `((fe . fco) . rst)` (`make-ord`) or `natp` | Recognizer `o-p`: nonzero `o-p` `fe`, `posp` `fco`, `o-p` `rst`, decreasing exponents | Guard-verified `ocmp-aux` (`lines 29-48`) + `e0-ordinal-well-founded-cnf` | Quantifier-free first-order PRA |
| **Polynomial $\omega^\omega$ `CNF_ww`** | `List (Nat × Nat)` (strictly descending `(exp, coeff_m1)` pairs) | `SortedGT` on `exp : Nat` | Lexicographic list `<`; well-founded by nested `Nat`/`List` induction without `Acc_strong` | **0 axioms** (`Type 0`, `DecidableEq`, `rfl`-computable) |

Three invariants govern syntactic `T1`:
- **`nf` is mandatory for well-foundedness (`T1.v:549, 1602-1620`):** Unnormalized terms like `bad_term := cons 1 1 (cons T1omega 2 zero)` (`line 549`) violate strict exponent descent and defeat naive structural induction (`First_attempt.wf_LT`, aborted at `line 1618`). Restricting `LT` to `nf alpha /\ nf beta /\ lt alpha beta` makes `nf_b` a decidable `bool` check (`line 536`) so `T1_wf` trivially discards ill-formed terms (`lines 1796-1802`).
- **Tait's `Acc_strong` for $\varepsilon_0$ (`T1.v:1625-1781`):** Because predecessors of $\omega^\alpha$ can spawn arbitrarily large coefficients $k$ below $\alpha$, `T1.v` proves `Acc LT alpha -> Acc_strong alpha` (`forall n beta, nf (cons alpha n beta) -> Acc LT (cons alpha n beta)`) by triple nested induction (`Acc LT alpha`, Peano `n : nat`, and `Acc LT b` via `beta_Acc` at `lines 1671-1704`), finishing `nf_Acc` (`lines 1771-1778`) by structural induction on `T1`.
- **Simpler $\omega^\omega$ induction:** When task ranks sit in `Nat` ($\alpha < \omega^\omega$), exponents are natural numbers, so `WellFounded` follows from standard Peano induction on `(exp, coeff_m1)` without `Acc_strong`.

---

### 3. The Concurrent Monotonicity Trap: Ordinary Addition ($+$) vs. Hessenberg Natural Sum ($\oplus$)

Basis: **source + execution + derived**

#### 3.1 Left-Absorption Failure of `T1add` / `ob+`

In `T1add` (`T1.v:589-600`) and `ob+` (`ordinal-definitions.lisp:117-130`), when `compare a a' = Lt` ($a < a'$), the left summand is absorbed: `| Lt => cons a' n' b'` (`T1.v:595`). In a **concurrent work-stealing executor**, if Worker 2 steals and steps a rank-1 task ($\omega^1 \to 5$) while Worker 1 leaves a rank-2 task ($\omega^2$) idle:
$$\mu_{+}(S_{\text{before}}) = \omega^1 + \omega^2 = \omega^2 \qquad \text{vs.} \qquad \mu_{+}(S_{\text{after}}) = 5 + \omega^2 = \omega^2$$
The global $+$-measure fails to decrease (`oadd_left_absorption.strict_decrease == false`).

#### 3.2 Hessenberg Natural Sum (`oplus`) and Worker-Local Ghost-Debt Framing

`Hessenberg.v:14-26` defines commutative polynomial-style natural addition:

```coq
(* coq-community/hydra-battles @ ed8e6048..., Hessenberg.v:14-26 *)
Fixpoint oplus (alpha beta : T1) : T1 :=
  let fix oplus_aux beta {struct beta} :=
      match alpha, beta with
        | zero, _ => beta
        | _, zero => alpha
        | cons a1 n1 b1, cons a2 n2 b2 =>
          match compare a1 a2 with
            |  Gt => cons a1 n1 (oplus b1 beta)
            |  Lt => cons a2 n2 (oplus_aux b2)
            |  Eq => cons a1 (S (n1 + n2)%nat) (oplus b1 b2)
          end
      end
  in oplus_aux beta.
```

Four mechanized theorems in `Hessenberg.v` enable concurrent modular proofs:
1. **Exact `S (n1 + n2)` merge (`line 23`):** Because `cons a n b` represents $\omega^a \cdot (n+1) + b$, equal-exponent coefficients sum to $(n_1 + 1) + (n_2 + 1) = (n_1 + n_2 + 1) + 1$. Omitting `S` collapses $\omega \oplus \omega = \omega$.
2. **Normal-form closure & commutativity (`oplus_nf` `lines 261-274`; `oplus_comm` `lines 331-346`):** `nf (alpha o+ beta)` and `alpha o+ beta = beta o+ alpha`.
3. **Strict bi-monotonicity (`oplus_strict_mono_r` `line 764`; `oplus_strict_mono_l` `line 777`; `oplus_strict_mono_bi` `line 821`):** $\beta < \gamma \implies \alpha \oplus \beta < \alpha \oplus \gamma$ and $\beta \oplus \alpha < \gamma \oplus \alpha$, yielding $\omega^1 \oplus \omega^2 = \omega^2 + \omega > \omega^2 + 5 = 5 \oplus \omega^2$.
4. **Local ghost-debt splitting:** Since $(\text{CNF}, \oplus, 0, <)$ is an ordered commutative cancellative monoid, a worker owning task-debt fragment $\omega^d$ locally replaces it with $\bigoplus_{j=1}^m \omega^{\rho(t_j)} < \omega^d$ ($\rho(t_j) < d$) and automatically decreases the global sum $\mu_\oplus(S)$ across concurrent workers without classical `siProp_witness` (`iris/transfinite@dde9f199...`).

---

### 4. Composing CNF Task Measures with Scheduler Fairness and Liveness Logics

Basis: **source + execution + documentation + derived**

#### 4.1 Real-World Work-Stealing Fairness Bounds (`tokio-rs/tokio@717c508f...`)

In `tokio/src/runtime/scheduler/multi_thread/worker.rs` and `tokio/src/task/coop/mod.rs`:
- **LIFO-slot starvation cap (`worker.rs:272, 750-786`):** `core.lifo_slot` accelerates local wakeups, risking indefinite ping-pong starvation of `run_queue` (`lines 777-782`) unless capped at `MAX_LIFO_POLLS_PER_TICK: usize = 3` (`line 272`), which disables `core.lifo_enabled` at `line 784` when `lifo_polls >= 3`.
- **Cooperative poll budget (`coop/mod.rs:97-134`, `worker.rs:718, 758-770`):** Each poll grants `Budget(Some(128))` (`coop/mod.rs:116`). Exhausting `!coop::has_budget_remaining()` pushes pending LIFO tasks to `core.run_queue.push_back_or_overflow` (`worker.rs:761-765`). Wrapping always-ready loops in `tokio::task::coop::unconstrained` (`coop/mod.rs:35-56, 120-122`) sets `Budget(None)`, intentionally breaking fairness.
- **Periodic driver maintenance (`worker.rs:827-844`):** Every `event_interval` ticks, `core.maintenance` yields to drive I/O and timers.

#### 4.2 Lexicographic Composition and Comparative Framework Matrix

Following *Fair Operational Semantics* (Lee et al., PLDI 2023, DOI `10.1145/3591253`), pairing constructive CNF task debt $\mu_{\text{pool}}(S)$ with a finitary scheduler/fairness counter $\Delta_{\text{sched}}(S) \in \mathbb{N}$ via $\Phi(S) = (\mu_{\text{pool}}(S), \Delta_{\text{sched}}(S)) \in \text{CNF} \times \mathbb{N}$ decreases strictly on **both** productive task spawns (where $\mu_{\text{pool}}(S') < \mu_{\text{pool}}(S)$ allows resetting $\Delta_{\text{sched}}$ to any finite budget $F(S') \in \mathbb{N}$) and non-productive scheduler delays (where $\mu_{\text{pool}}$ stays fixed and $\Delta_{\text{sched}}(S') < \Delta_{\text{sched}}(S)$).

| Framework | Reference & Pinned Subject | Universe & Axioms | Dynamic Unbounded Spawning? | Concurrent Modularity | Fairness Mechanism |
|---|---|---|---|---|---|
| **Constructive `Type 0` CNF + Finitary Counters** | `hydra-battles` (`ed8e6048...`), `ACL2` (`f040a8db...`), Lee et al. (PLDI 2023) | `Type 0` / `Set`; **0 classical axioms** | **Yes** ($\omega^\omega$ or $\varepsilon_0$) | **Yes** (commutative cancellative $\oplus$ fragments) | Explicit bounded turn/poll budgets in state |
| **Fixed `Nat` Fuel / $\mathbb{N}^k$** | `Init/WF.lean` (`5045d005...`) | `Type 0`; constructive `Nat` | **No** | Additive `Nat`, no $\omega^d$ splitting | Same |
| **Set-Theoretic `Ordinal.CNF`** | `mathlib4` (`d13f23b7...`) | **`Type 1`**; `Quot.sound`, `propext`, `Classical.choice` | Yes | Injected into `Type 1` | External |
| **Transfinite Iris** | `iris/transfinite` (`dde9f199...`) | Ordinal step-indexed `iProp` | Yes | Breaks `later_exists` (`siProp.v:343`) | Classical **`siProp_witness`** (`ClassicalEpsilon`) |
| **Trillium** | `iris/trillium` (`d8bc4d31...`) | `nat`-Iris + coinductive trace simulation | Model-dependent | Yes | External **`fair_ex`** trace predicate |
| **TaDA Live** | D'Osualdo et al. (TOPLAS 2021, DOI `10.1145/3477082`) | Subjective concurrent separation logic | Layered abstract levels | **Yes** | Subjective liveness obligations |
| **Temporal TLA+** | Lamport (TOPLAS 1994, DOI `10.1145/177492.177726`) | Untyped temporal actions | State-predicate level | Whole-state composition | Weak (`WF_vars`) & strong (`SF_vars`) fairness |

#### 4.3 Executable Verification (`probe_cnf_ordinal_liveness.py`)

Running the inline Python 3.10+ probe (`SHA256: 8eac3214807e4413b98c1d00cfd0944fd1eaeeacbf79f76b9b8a9c6225165ec8` verified below) confirms: (1) `oadd` left-absorption `w^(2) == w^(2)` (`strict_decrease: false`) vs. `oplus` strict drop `w^(2) + w -> w^(2) + 5` (`strict_decrease: true`); (2) off-by-one merge collapse `w o+ w -> w` vs. `w*2`; (3) $\varepsilon_0$ commutativity `a o+ b == b o+ a`; and (4) an adversarial work-stealing dynamic spawn simulation (`MAX_LIFO_POLLS_PER_TICK = 3`, `COOP_BUDGET = 4`, peak **63** concurrent tasks) executing **303** steps (**60** scheduler-flush transitions) with **303 / 303** strict lexicographic `(CNF, Nat)` decreases down to `0`.

---

## Boundaries

- **Ordinals beyond $\varepsilon_0$ (`not examined`):** Ordinal notations for impredicative systems ($\Gamma_0$, Bachmann–Howard ordinals) were **not examined**; syntactic `T1` CNF covers only ordinals $< \varepsilon_0$.
- **Tight amortized latency under randomized work-stealing (`unknown`):** Tight worst-case expectation bounds under randomized PRNG steal victim selection across multi-core `tokio` pools are **unknown** from static source inspection.
- **Left-absorbing `+` for concurrent pools and `tokio::task::coop::unconstrained` (`known not to apply`):** Standard ordinal addition (`T1add` / `ob+`) is **known not to apply** to concurrent multiset pools ($\omega^1 + \omega^2 = 5 + \omega^2$), and starvation-freedom is **known not to apply** to `coop::unconstrained` (`coop/mod.rs:35-56`) futures (`Budget(None)`).
- **Storing `Mathlib.SetTheory.Ordinal.{0}` in `Type 0` or constructive `ouPred_witness` (`unsupported`):** Storing `Ordinal.{0} : Type 1` in `Type 0` structures is **unsupported** by Lean's universe rules (`Basic.lean:80-108`), and witness extraction without classical choice (`ouPred_witness`) is **unsupported** in limit-closed Transfinite Iris (`siProp.v:343-349`).

---

## Evidence

- **`coq-community/hydra-battles` (`ed8e6048018a61b4fe6d7d6f96daf0d63da2eba8`, observed `2026-11-20`):** `T1.v` (`lines 46-48, 169-188, 536-549, 589-600, 1602-1818`), `Hessenberg.v` (`lines 14-26, 261-274, 331-346, 764-829`), `Hydra_Definitions.v` (`lines 17-22`).
- **`acl2/acl2` (`f040a8db474f68e11b5fa980c99b7c1f7be28e54`, observed `2026-11-20`):** `books/ordinals/ordinal-definitions.lisp` (`lines 29-48, 117-130`), `books/ordinals/e0-ordinal.lisp` (`lines 41-54, 78-87, 142-148`).
- **`leanprover-community/mathlib4` (`d13f23b723b8a846827a245b89c10fc7d3f11612`, `v4.34.1`, observed `2026-11-20`):** `Mathlib/SetTheory/Ordinal/Basic.lean` (`lines 65, 80-108, 120-122`), `CantorNormalForm.lean` (`lines 36-73, 142-157, 336-343`).
- **`leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** `src/Init/WF.lean` (`lines 25-31, 60-64, 98-100`).
- **`tokio-rs/tokio` (`717c508f9e9ac4317665ff1eb30f29c139ea6363`, observed `2026-11-20`):** `worker.rs` (`lines 272, 631, 718-844`), `coop/mod.rs` (`lines 33-59, 97-134`).
- **`iris/trillium` (`d8bc4d31f929b9f5b9ef20a5943c9c923e8844c7`) & `iris/transfinite` (`dde9f199bc09dc5242e3547be7c5049030f4c451`).**
- **Literature:** Dershowitz & Manna (CACM 1979, `10.1145/359138.359142`), Manolios & Vroon (JAR 2005, `10.1007/s10817-005-9023-9`), D'Osualdo et al. (TOPLAS 2021, `10.1145/3477082`), Lee et al. (PLDI 2023, `10.1145/3591253`), Lamport (TOPLAS 1994, `10.1145/177492.177726`).
- **Probe Execution (observed `2026-11-20`):** Inline script below exited `0` (`SHA256: 8eac3214807e4413b98c1d00cfd0944fd1eaeeacbf79f76b9b8a9c6225165ec8`), verifying `303 / 303` strict lexicographic decreases down to `0` across `63` peak concurrent tasks.

---

## Revalidation

### 1. Executable Self-Contained CNF & Dynamic Task-Spawning Probe (`python3` 3.10+, Standard Library Only)

Save to `/tmp/probe_cnf_ordinal_liveness.py` and run `python3 /tmp/probe_cnf_ordinal_liveness.py` (expected exit `0`, `strict_lex_decreases == 303`, `final_measure == "0"`, SHA-256 `8eac3214807e4413b98c1d00cfd0944fd1eaeeacbf79f76b9b8a9c6225165ec8`):

```python
#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json
from dataclasses import dataclass
from typing import Union

@dataclass(frozen=True)
class Zero: pass

@dataclass(frozen=True)
class Cons:
    exp: "CNF"; coeff_m1: int; rest: "CNF"

CNF = Union[Zero, Cons]
ZERO, ONE = Zero(), Cons(Zero(), 0, Zero())
OMEGA = Cons(ONE, 0, ZERO)
cnf_nat = lambda n: ZERO if n == 0 else Cons(ZERO, n - 1, ZERO)
cnf_pow = lambda e, c=1, r=ZERO: Cons(e, c - 1, r)

def cmp(a: CNF, b: CNF) -> int:
    if isinstance(a, Zero) and isinstance(b, Zero): return 0
    if isinstance(a, Zero): return -1
    if isinstance(b, Zero): return 1
    if (c := cmp(a.exp, b.exp)) != 0: return c
    if a.coeff_m1 != b.coeff_m1: return -1 if a.coeff_m1 < b.coeff_m1 else 1
    return cmp(a.rest, b.rest)

def nf(a: CNF) -> bool:
    if isinstance(a, Zero): return True
    if a.coeff_m1 < 0 or not nf(a.exp) or not nf(a.rest): return False
    return cmp(a.rest.exp, a.exp) < 0 if isinstance(a.rest, Cons) else True

def oadd(a: CNF, b: CNF) -> CNF:
    if isinstance(a, Zero): return b
    if isinstance(b, Zero): return a
    c = cmp(a.exp, b.exp)
    if c < 0: return b
    if c > 0: return Cons(a.exp, a.coeff_m1, oadd(a.rest, b))
    return Cons(a.exp, a.coeff_m1 + b.coeff_m1 + 1, b.rest)

def oplus(a: CNF, b: CNF, buggy: bool = False) -> CNF:
    if isinstance(a, Zero): return b
    if isinstance(b, Zero): return a
    c = cmp(a.exp, b.exp)
    if c > 0: return Cons(a.exp, a.coeff_m1, oplus(a.rest, b, buggy))
    if c < 0: return Cons(b.exp, b.coeff_m1, oplus(a, b.rest, buggy))
    m = a.coeff_m1 + b.coeff_m1 + (0 if buggy else 1)
    return Cons(a.exp, m, oplus(a.rest, b.rest, buggy))

def pp(a: CNF) -> str:
    if isinstance(a, Zero): return "0"
    out, cur = [], a
    while isinstance(cur, Cons):
        c = cur.coeff_m1 + 1
        if isinstance(cur.exp, Zero): out.append(str(c))
        elif cmp(cur.exp, ONE) == 0: out.append("w" if c == 1 else f"w*{c}")
        else: out.append(f"w^({pp(cur.exp)})" if c == 1 else f"w^({pp(cur.exp)})*{c}")
        cur = cur.rest
    return " + ".join(out)

def sim() -> dict[str, object]:
    w0_q, w0_lifo, w1_q = [(3, 1), (2, 1)], None, [(4, 1)]
    lifo_polls, max_lifo, coop_rem = 0, 3, 4
    def meas() -> CNF:
        m: CNF = ZERO
        for r, s in w0_q + w1_q + ([w0_lifo] if w0_lifo else []):
            t = Cons(cnf_nat(r + 1), 0, cnf_nat(s))
            assert nf(t)
            m = oplus(m, t)
        return m
    steps, delays, max_sz, decs = 0, 0, 0, 0
    ppool, psched = meas(), coop_rem
    while w0_q or w0_lifo or w1_q:
        max_sz = max(max_sz, len(w0_q) + len(w1_q) + (1 if w0_lifo else 0))
        if w0_lifo and lifo_polls < max_lifo and coop_rem > 0:
            r, s = w0_lifo; w0_lifo = None; lifo_polls += 1; coop_rem -= 1
            if s > 1: w0_lifo = (r, s - 1)
            elif r > 0:
                for i in range(2 + (steps % 4)):
                    if i == 0 and lifo_polls < max_lifo: w0_lifo = (r - 1, 2)
                    else: w0_q.append((r - 1, 2))
        elif coop_rem == 0 or lifo_polls >= max_lifo:
            if w0_lifo: w0_q.append(w0_lifo); w0_lifo = None
            lifo_polls, coop_rem = 0, 4
            r, s = w0_q.pop(0) if w0_q else w1_q.pop(0)
            if s > 1: w0_q.append((r, s - 1))
            elif r > 0: w0_q.extend((r - 1, 1) for _ in range(2 + (steps % 3)))
            delays += 1
        else:
            r, s = w0_q.pop(0) if w0_q else w1_q.pop(0); coop_rem -= 1
            if s > 1: w0_q.append((r, s - 1))
            elif r > 0:
                for i in range(2 + (steps % 4)):
                    if i == 0 and lifo_polls < max_lifo: w0_lifo = (r - 1, 2)
                    else: w0_q.append((r - 1, 2))
        steps += 1; cpool, csched = meas(), coop_rem
        c = cmp(cpool, ppool)
        assert c < 0 or (c == 0 and csched < psched)
        decs += 1; ppool, psched = cpool, csched
    assert cmp(ppool, ZERO) == 0
    return {"total_steps": steps, "scheduler_flush_steps": delays, "max_concurrent_tasks": max_sz, "strict_lex_decreases": decs, "final_measure": pp(ppool)}

def main() -> None:
    w1, w2, five = cnf_pow(ONE), cnf_pow(cnf_nat(2)), cnf_nat(5)
    ba, aa, bo, ao = oadd(w1, w2), oadd(five, w2), oplus(w1, w2), oplus(five, w2)
    assert cmp(ba, aa) == 0 and cmp(ao, bo) < 0
    bug, ex = oplus(OMEGA, OMEGA, buggy=True), oplus(OMEGA, OMEGA)
    assert cmp(bug, OMEGA) == 0 and cmp(ex, cnf_pow(ONE, 2)) == 0
    ea, eb = cnf_pow(OMEGA, 2, cnf_pow(cnf_nat(2), 1, ONE)), cnf_pow(cnf_pow(ONE, 1, cnf_nat(1)), 1, cnf_pow(ONE, 3))
    ab, ba_e = oplus(ea, eb), oplus(eb, ea)
    assert nf(ea) and nf(eb) and nf(ab) and cmp(ab, ba_e) == 0
    out = {
        "oadd_left_absorption": {"before": pp(ba), "after": pp(aa), "strict_decrease": cmp(aa, ba) < 0},
        "oplus_bi_monotonic": {"before": pp(bo), "after": pp(ao), "strict_decrease": cmp(ao, bo) < 0},
        "off_by_one_merge_trap": {"buggy_omega_oplus_omega": pp(bug), "exact_omega_oplus_omega": pp(ex)},
        "epsilon0_example": {"a": pp(ea), "b": pp(eb), "a_oplus_b": pp(ab), "commutative": cmp(ab, ba_e) == 0},
        "work_stealing_simulation": sim(),
    }
    raw = json.dumps(out, indent=2); print(raw)
    print("SHA256:", hashlib.sha256(raw.encode()).hexdigest())

if __name__ == "__main__":
    main()
```

### 2. Targeted Upstream Revalidation Checks

- **Lean 4 constructive `Type 0` check:** Verify `#print axioms` on a standalone `CNF_ww` (`List (Nat × Nat)`) natural sum and lexicographic `WellFounded` relation reports zero axioms (`Quot.sound`, `propext`, `Classical.choice` absent).
- **Tokio fairness bound check:** Inspect `MAX_LIFO_POLLS_PER_TICK` in `tokio/src/runtime/scheduler/multi_thread/worker.rs` and `Budget::initial()` in `tokio/src/task/coop/mod.rs` on future Tokio releases.
